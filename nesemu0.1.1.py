#!/usr/bin/env python3
"""AC/ChatGPT NES Emulator 0.8.0 - self-contained Python NES/Famicom core.

Python 3.10+ (including Python 3.14), Windows, macOS Intel/Apple Silicon,
Linux and other Unix desktops with Tk.  No game ROMs or external assets are
included.  Use only ROM dumps that you are legally entitled to use.

This is a clean Python implementation informed by public NES documentation and
FCEUX's documented behaviour.  It is not a byte-for-byte port of FCEUX; FCEUX
is a much larger C/C++ project.  Mappers 0, 1, 2, 3, 4, 7 and 66 are supported.

SPDX-License-Identifier: GPL-2.0-or-later
"""

from __future__ import annotations

from array import array
import math
import os
import sys
import time
import tkinter as tk
from tkinter import filedialog, messagebox


WIDTH = 256
HEIGHT = 240
WINDOW_WIDTH = 600
WINDOW_HEIGHT = 400
# Largest integer zoom that fits the fixed window (padding + controls/status).
SCALE = min((WINDOW_WIDTH - 20) // WIDTH, (WINDOW_HEIGHT - 80) // HEIGHT)
FPS = 60.0988                 # NTSC NES/Famicom refresh rate
CPU_HZ = 1_789_773
CPU_CYCLES_PER_FRAME = CPU_HZ / FPS


class EmulatorError(Exception):
    """A user-facing cartridge or emulation error."""


# Common 2C02 palette (RGB, 64 entries).
NES_PALETTE = (
    (84, 84, 84), (0, 30, 116), (8, 16, 144), (48, 0, 136),
    (68, 0, 100), (92, 0, 48), (84, 4, 0), (60, 24, 0),
    (32, 42, 0), (8, 58, 0), (0, 64, 0), (0, 60, 0),
    (0, 50, 60), (0, 0, 0), (0, 0, 0), (0, 0, 0),
    (152, 150, 152), (8, 76, 196), (48, 50, 236), (92, 30, 228),
    (136, 20, 176), (160, 20, 100), (152, 34, 32), (120, 60, 0),
    (84, 90, 0), (40, 114, 0), (8, 124, 0), (0, 118, 40),
    (0, 102, 120), (0, 0, 0), (0, 0, 0), (0, 0, 0),
    (236, 238, 236), (76, 154, 236), (120, 124, 236), (176, 98, 236),
    (228, 84, 236), (236, 88, 180), (236, 106, 100), (212, 136, 32),
    (160, 170, 0), (116, 196, 0), (76, 208, 32), (56, 204, 108),
    (56, 180, 204), (60, 60, 60), (0, 0, 0), (0, 0, 0),
    (236, 238, 236), (168, 204, 236), (188, 188, 236), (212, 178, 236),
    (236, 174, 236), (236, 174, 212), (236, 180, 176), (228, 196, 144),
    (204, 210, 120), (180, 222, 120), (168, 226, 144), (152, 226, 180),
    (160, 214, 228), (160, 162, 160), (0, 0, 0), (0, 0, 0),
)
NES_RGB = tuple(bytes(rgb) for rgb in NES_PALETTE)


class Cartridge:
    """iNES cartridge plus the most common discrete and ASIC mappers."""

    SUPPORTED_MAPPERS = {0: "NROM", 1: "MMC1", 2: "UxROM", 3: "CNROM",
                         4: "MMC3", 7: "AxROM", 66: "GxROM"}

    def __init__(self) -> None:
        self.path = ""
        self.name = "No ROM"
        self.mapper = 0
        self.mirroring = "horizontal"
        self.four_screen = False
        self.battery = False
        self.prg = bytearray()
        self.chr = bytearray()
        self.prg_window = bytearray(0x8000)
        self.chr_window = bytearray(0x2000)
        self.chr_ram = False
        self.prg_ram = bytearray(0x2000)
        self.reset_mapper()

    def reset_mapper(self) -> None:
        self.bank_select = 0
        self.bank_regs = [0] * 8
        self.prg_mode = 0
        self.chr_mode = 0
        self.chr_bank = 0
        self.prg_bank = 0
        self.mmc1_shift = 0x10
        self.mmc1_control = 0x0C
        self.mmc1_chr0 = 0
        self.mmc1_chr1 = 0
        self.mmc1_prg = 0
        self.irq_latch = 0
        self.irq_counter = 0
        self.irq_reload = False
        self.irq_enabled = False
        self.irq_pending = False
        if self.prg:
            self.sync_banks()

    def load(self, path: str) -> None:
        with open(path, "rb") as rom_file:
            data = rom_file.read()
        if len(data) < 16 or data[:4] != b"NES\x1a":
            raise EmulatorError("This is not a valid iNES .nes ROM.")

        prg_units, chr_units = data[4], data[5]
        flags6, flags7 = data[6], data[7]
        nes2 = (flags7 & 0x0C) == 0x08
        if nes2:
            # Support ordinary NES 2.0 sizes; exponent-encoded giant images are
            # intentionally rejected in this compact implementation.
            if (data[9] & 0x0F) == 0x0F or (data[9] >> 4) == 0x0F:
                raise EmulatorError("Exponent-sized NES 2.0 ROMs are not supported.")
            prg_units |= (data[9] & 0x0F) << 8
            chr_units |= (data[9] >> 4) << 8

        mapper = (flags6 >> 4) | (flags7 & 0xF0)
        if nes2:
            mapper |= (data[8] & 0x0F) << 8
        if mapper not in self.SUPPORTED_MAPPERS:
            supported = ", ".join(str(n) for n in sorted(self.SUPPORTED_MAPPERS))
            raise EmulatorError(f"Mapper {mapper} is not supported yet. Supported: {supported}.")

        offset = 16 + (512 if flags6 & 0x04 else 0)
        prg_size, chr_size = prg_units * 0x4000, chr_units * 0x2000
        if prg_size == 0 or len(data) < offset + prg_size + chr_size:
            raise EmulatorError("The ROM is truncated or has an invalid iNES header.")

        self.path = path
        self.name = os.path.basename(path)
        self.mapper = mapper
        self.battery = bool(flags6 & 0x02)
        self.four_screen = bool(flags6 & 0x08)
        self.mirroring = "vertical" if flags6 & 1 else "horizontal"
        if self.four_screen:
            self.mirroring = "four"
        self.prg = bytearray(data[offset:offset + prg_size])
        offset += prg_size
        self.chr_ram = chr_size == 0
        self.chr = bytearray(0x2000) if self.chr_ram else bytearray(data[offset:offset + chr_size])
        ram_units = data[8] if not nes2 else 1
        self.prg_ram = bytearray(max(1, ram_units) * 0x2000)
        self.reset_mapper()

    @staticmethod
    def _bank_offset(bank: int, size: int, total: int) -> int:
        count = max(1, total // size)
        return (bank % count) * size

    def cpu_read(self, addr: int) -> int:
        if 0x6000 <= addr < 0x8000:
            return self.prg_ram[(addr - 0x6000) % len(self.prg_ram)]
        if addr < 0x8000 or not self.prg:
            return 0
        return self.prg_window[addr - 0x8000]

    def _prg_8k_bank(self, slot: int) -> int:
        count = max(1, len(self.prg) // 0x2000)
        if self.mapper in (0, 3):
            return slot % count
        if self.mapper == 2:
            return ((self.prg_bank * 2 + slot) if slot < 2 else (count - 2 + slot - 2)) % count
        if self.mapper in (7, 66):
            return (self.prg_bank * 4 + slot) % count
        if self.mapper == 1:
            mode, bank16 = (self.mmc1_control >> 2) & 3, self.mmc1_prg & 0x0F
            if mode < 2:
                return ((bank16 & ~1) * 2 + slot) % count
            if mode == 2:
                return (slot if slot < 2 else bank16 * 2 + slot - 2) % count
            return (bank16 * 2 + slot if slot < 2 else count - 2 + slot - 2) % count
        if self.mapper == 4:
            last, second_last = count - 1, count - 2
            mapping = ((second_last, self.bank_regs[7], self.bank_regs[6], last)
                       if self.prg_mode else
                       (self.bank_regs[6], self.bank_regs[7], second_last, last))
            return mapping[slot] % count
        return slot % count

    def _chr_1k_bank(self, slot: int) -> int:
        count = max(1, len(self.chr) // 0x400)
        if self.mapper in (3, 66):
            return (self.chr_bank * 8 + slot) % count
        if self.mapper == 1:
            if self.mmc1_control & 0x10:
                bank4 = self.mmc1_chr0 if slot < 4 else self.mmc1_chr1
                return (bank4 * 4 + (slot & 3)) % count
            return ((self.mmc1_chr0 & ~1) * 4 + slot) % count
        if self.mapper == 4:
            return self._chr_mmc3_bank(slot * 0x400) % count
        return slot % count

    def sync_banks(self) -> None:
        """Materialize active banks so instruction/pattern fetches stay fast."""
        if self.prg:
            for slot in range(4):
                base = self._prg_8k_bank(slot) * 0x2000
                self.prg_window[slot * 0x2000:(slot + 1) * 0x2000] = self.prg[base:base + 0x2000]
        if self.chr:
            for slot in range(8):
                base = self._chr_1k_bank(slot) * 0x400
                self.chr_window[slot * 0x400:(slot + 1) * 0x400] = self.chr[base:base + 0x400]

    def cpu_write(self, addr: int, value: int) -> None:
        value &= 0xFF
        if 0x6000 <= addr < 0x8000:
            self.prg_ram[(addr - 0x6000) % len(self.prg_ram)] = value
            return
        if addr < 0x8000:
            return
        if self.mapper == 2:
            self.prg_bank = value
            self.sync_banks()
        elif self.mapper == 3:
            self.chr_bank = value
            self.sync_banks()
        elif self.mapper == 7:
            self.prg_bank = value & 7
            self.mirroring = "single1" if value & 0x10 else "single0"
            self.sync_banks()
        elif self.mapper == 66:
            self.prg_bank = (value >> 4) & 3
            self.chr_bank = value & 3
            self.sync_banks()
        elif self.mapper == 1:
            if value & 0x80:
                self.mmc1_shift = 0x10
                self.mmc1_control |= 0x0C
                self.sync_banks()
                return
            complete = self.mmc1_shift & 1
            self.mmc1_shift = (self.mmc1_shift >> 1) | ((value & 1) << 4)
            if complete:
                reg = (addr >> 13) & 3
                payload = self.mmc1_shift & 0x1F
                if reg == 0:
                    self.mmc1_control = payload
                    self.mirroring = ("single0", "single1", "vertical", "horizontal")[payload & 3]
                elif reg == 1:
                    self.mmc1_chr0 = payload
                elif reg == 2:
                    self.mmc1_chr1 = payload
                else:
                    self.mmc1_prg = payload
                self.mmc1_shift = 0x10
                self.sync_banks()
        elif self.mapper == 4:
            even = not (addr & 1)
            region = addr & 0xE000
            if region == 0x8000:
                if even:
                    self.bank_select = value & 7
                    self.prg_mode = (value >> 6) & 1
                    self.chr_mode = (value >> 7) & 1
                else:
                    self.bank_regs[self.bank_select] = value
                self.sync_banks()
            elif region == 0xA000 and even and not self.four_screen:
                self.mirroring = "horizontal" if value & 1 else "vertical"
            elif region == 0xC000:
                if even:
                    self.irq_latch = value
                else:
                    self.irq_reload = True
            elif region == 0xE000:
                if even:
                    self.irq_enabled = False
                    self.irq_pending = False
                else:
                    self.irq_enabled = True

    def _chr_mmc3_bank(self, addr: int) -> int:
        slot = (addr & 0x1FFF) // 0x400
        r = self.bank_regs
        if not self.chr_mode:
            banks = (r[0] & 0xFE, r[0] | 1, r[1] & 0xFE, r[1] | 1,
                     r[2], r[3], r[4], r[5])
        else:
            banks = (r[2], r[3], r[4], r[5], r[0] & 0xFE, r[0] | 1,
                     r[1] & 0xFE, r[1] | 1)
        return banks[slot]

    def _chr_address(self, addr: int) -> int:
        addr &= 0x1FFF
        if self.mapper in (3, 66):
            return (self._bank_offset(self.chr_bank, 0x2000, len(self.chr)) + addr) % len(self.chr)
        if self.mapper == 1:
            if self.mmc1_control & 0x10:
                bank = self.mmc1_chr0 if addr < 0x1000 else self.mmc1_chr1
                return (self._bank_offset(bank, 0x1000, len(self.chr)) + (addr & 0x0FFF)) % len(self.chr)
            base = self._bank_offset(self.mmc1_chr0 & ~1, 0x1000, len(self.chr))
            return (base + addr) % len(self.chr)
        if self.mapper == 4:
            base = self._bank_offset(self._chr_mmc3_bank(addr), 0x400, len(self.chr))
            return base + (addr & 0x3FF)
        return addr % len(self.chr)

    def ppu_read(self, addr: int) -> int:
        return self.chr_window[addr & 0x1FFF]

    def ppu_write(self, addr: int, value: int) -> None:
        if self.chr_ram:
            value &= 0xFF
            self.chr[self._chr_address(addr)] = value
            self.chr_window[addr & 0x1FFF] = value

    def clock_scanline(self) -> None:
        if self.mapper != 4:
            return
        if self.irq_counter == 0 or self.irq_reload:
            self.irq_counter = self.irq_latch
            self.irq_reload = False
        else:
            self.irq_counter = (self.irq_counter - 1) & 0xFF
        if self.irq_counter == 0 and self.irq_enabled:
            self.irq_pending = True


class Controller:
    BUTTONS = ("a", "b", "select", "start", "up", "down", "left", "right")

    def __init__(self) -> None:
        self.keys = {name: False for name in self.BUTTONS}
        self.strobe = False
        self.shift = 0

    def set_button(self, name: str, down: bool) -> None:
        if name in self.keys:
            self.keys[name] = down
            if self.strobe:
                self.latch()

    def latch(self) -> None:
        self.shift = sum((1 << i) for i, name in enumerate(self.BUTTONS) if self.keys[name])

    def write(self, value: int) -> None:
        old = self.strobe
        self.strobe = bool(value & 1)
        if self.strobe or old:
            self.latch()

    def read(self) -> int:
        if self.strobe:
            self.latch()
        bit = self.shift & 1
        if not self.strobe:
            self.shift = (self.shift >> 1) | 0x80
        return 0x40 | bit


class Envelope:
    __slots__ = ("control", "start", "divider", "decay")

    def __init__(self) -> None:
        self.control = 0
        self.start = False
        self.divider = 0
        self.decay = 0

    def clock(self) -> None:
        period = self.control & 0x0F
        if self.start:
            self.start = False
            self.decay = 15
            self.divider = period
        elif self.divider:
            self.divider -= 1
        else:
            self.divider = period
            if self.decay:
                self.decay -= 1
            elif self.control & 0x20:
                self.decay = 15

    def output(self) -> int:
        return (self.control & 0x0F) if self.control & 0x10 else self.decay


class PulseChannel:
    __slots__ = ("channel", "enabled", "length", "timer_period", "timer_counter",
                 "sequence", "duty", "envelope", "sweep", "sweep_divider",
                 "sweep_reload")
    DUTY = (
        (0, 1, 0, 0, 0, 0, 0, 0),
        (0, 1, 1, 0, 0, 0, 0, 0),
        (0, 1, 1, 1, 1, 0, 0, 0),
        (1, 0, 0, 1, 1, 1, 1, 1),
    )

    def __init__(self, channel: int) -> None:
        self.channel = channel
        self.enabled = False
        self.length = 0
        self.timer_period = 0
        self.timer_counter = 1
        self.sequence = 0
        self.duty = 0
        self.envelope = Envelope()
        self.sweep = 0
        self.sweep_divider = 0
        self.sweep_reload = False

    def write(self, register: int, value: int, length_table: tuple[int, ...]) -> None:
        if register == 0:
            self.envelope.control = value
            self.duty = value >> 6
        elif register == 1:
            self.sweep = value
            self.sweep_reload = True
        elif register == 2:
            self.timer_period = (self.timer_period & 0x700) | value
        else:
            self.timer_period = (self.timer_period & 0xFF) | ((value & 7) << 8)
            if self.enabled:
                self.length = length_table[value >> 3]
            self.sequence = 0
            self.envelope.start = True

    def set_enabled(self, enabled: bool) -> None:
        self.enabled = enabled
        if not enabled:
            self.length = 0

    def sweep_target(self) -> int:
        change = self.timer_period >> (self.sweep & 7)
        if self.sweep & 8:
            return self.timer_period - change - (1 if self.channel == 1 else 0)
        return self.timer_period + change

    def sweep_muted(self) -> bool:
        return self.timer_period < 8 or self.sweep_target() > 0x7FF

    def clock_timer(self, cycles: int) -> None:
        self.timer_counter -= cycles
        period = (self.timer_period + 1) * 2
        while self.timer_counter <= 0:
            self.timer_counter += period
            self.sequence = (self.sequence + 1) & 7

    def clock_quarter(self) -> None:
        self.envelope.clock()

    def clock_half(self) -> None:
        if self.length and not (self.envelope.control & 0x20):
            self.length -= 1
        divider_zero = self.sweep_divider == 0
        shift = self.sweep & 7
        if divider_zero and (self.sweep & 0x80) and shift and not self.sweep_muted():
            self.timer_period = self.sweep_target() & 0x7FF
        if divider_zero or self.sweep_reload:
            self.sweep_divider = (self.sweep >> 4) & 7
            self.sweep_reload = False
        else:
            self.sweep_divider -= 1

    def output(self) -> int:
        if not self.enabled or not self.length or self.sweep_muted():
            return 0
        if not self.DUTY[self.duty][self.sequence]:
            return 0
        return self.envelope.output()


class TriangleChannel:
    __slots__ = ("enabled", "length", "control", "linear_reload_value",
                 "linear_counter", "linear_reload", "timer_period",
                 "timer_counter", "sequence")
    WAVE = (15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0,
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15)

    def __init__(self) -> None:
        self.enabled = False
        self.length = 0
        self.control = False
        self.linear_reload_value = 0
        self.linear_counter = 0
        self.linear_reload = False
        self.timer_period = 0
        self.timer_counter = 1
        self.sequence = 0

    def write(self, register: int, value: int, length_table: tuple[int, ...]) -> None:
        if register == 0:
            self.control = bool(value & 0x80)
            self.linear_reload_value = value & 0x7F
        elif register == 2:
            self.timer_period = (self.timer_period & 0x700) | value
        elif register == 3:
            self.timer_period = (self.timer_period & 0xFF) | ((value & 7) << 8)
            if self.enabled:
                self.length = length_table[value >> 3]
            self.linear_reload = True

    def set_enabled(self, enabled: bool) -> None:
        self.enabled = enabled
        if not enabled:
            self.length = 0

    def clock_timer(self, cycles: int) -> None:
        self.timer_counter -= cycles
        period = self.timer_period + 1
        while self.timer_counter <= 0:
            self.timer_counter += period
            if self.enabled and self.length and self.linear_counter and self.timer_period > 1:
                self.sequence = (self.sequence + 1) & 31

    def clock_quarter(self) -> None:
        if self.linear_reload:
            self.linear_counter = self.linear_reload_value
        elif self.linear_counter:
            self.linear_counter -= 1
        if not self.control:
            self.linear_reload = False

    def clock_half(self) -> None:
        if self.length and not self.control:
            self.length -= 1

    def output(self) -> int:
        return self.WAVE[self.sequence]


class NoiseChannel:
    __slots__ = ("enabled", "length", "mode", "period_index", "timer_counter",
                 "shift_register", "envelope")
    PERIODS = (4, 8, 16, 32, 64, 96, 128, 160, 202, 254, 380, 508,
               762, 1016, 2034, 4068)

    def __init__(self) -> None:
        self.enabled = False
        self.length = 0
        self.mode = False
        self.period_index = 0
        self.timer_counter = 1
        self.shift_register = 1
        self.envelope = Envelope()

    def write(self, register: int, value: int, length_table: tuple[int, ...]) -> None:
        if register == 0:
            self.envelope.control = value
        elif register == 2:
            self.mode = bool(value & 0x80)
            self.period_index = value & 0x0F
        elif register == 3:
            if self.enabled:
                self.length = length_table[value >> 3]
            self.envelope.start = True

    def set_enabled(self, enabled: bool) -> None:
        self.enabled = enabled
        if not enabled:
            self.length = 0

    def clock_timer(self, cycles: int) -> None:
        self.timer_counter -= cycles
        period = self.PERIODS[self.period_index]
        while self.timer_counter <= 0:
            self.timer_counter += period
            tap = 6 if self.mode else 1
            feedback = (self.shift_register & 1) ^ ((self.shift_register >> tap) & 1)
            self.shift_register = (self.shift_register >> 1) | (feedback << 14)

    def clock_quarter(self) -> None:
        self.envelope.clock()

    def clock_half(self) -> None:
        if self.length and not (self.envelope.control & 0x20):
            self.length -= 1

    def output(self) -> int:
        if not self.enabled or not self.length or (self.shift_register & 1):
            return 0
        return self.envelope.output()


class DMCChannel:
    __slots__ = ("apu", "irq_enabled", "loop", "rate_index", "output_level",
                 "sample_address", "sample_length", "current_address",
                 "bytes_remaining", "sample_buffer", "shift_register",
                 "bits_remaining", "silence", "timer_counter", "irq_flag")
    PERIODS = (428, 380, 340, 320, 286, 254, 226, 214,
               190, 160, 142, 128, 106, 84, 72, 54)

    def __init__(self, apu: APU) -> None:
        self.apu = apu
        self.irq_enabled = False
        self.loop = False
        self.rate_index = 0
        self.output_level = 0
        self.sample_address = 0xC000
        self.sample_length = 1
        self.current_address = 0xC000
        self.bytes_remaining = 0
        self.sample_buffer: int | None = None
        self.shift_register = 0
        self.bits_remaining = 8
        self.silence = True
        self.timer_counter = self.PERIODS[0]
        self.irq_flag = False

    def write(self, register: int, value: int) -> None:
        if register == 0:
            self.irq_enabled = bool(value & 0x80)
            self.loop = bool(value & 0x40)
            self.rate_index = value & 0x0F
            if not self.irq_enabled:
                self.irq_flag = False
        elif register == 1:
            self.output_level = value & 0x7F
        elif register == 2:
            self.sample_address = 0xC000 + value * 64
        else:
            self.sample_length = value * 16 + 1

    def restart(self) -> None:
        self.current_address = self.sample_address
        self.bytes_remaining = self.sample_length
        self.fill_buffer()

    def set_enabled(self, enabled: bool) -> None:
        # Any $4015 write clears the DMC IRQ; a subsequent DMA fetch may assert
        # it again when it consumes the final sample byte.
        self.irq_flag = False
        if not enabled:
            self.bytes_remaining = 0
        elif self.bytes_remaining == 0:
            self.restart()

    def fill_buffer(self) -> None:
        if self.sample_buffer is not None or not self.bytes_remaining or self.apu.bus is None:
            return
        self.sample_buffer = self.apu.bus.read(self.current_address)
        if self.apu.bus.cpu is not None:
            self.apu.bus.cpu.stall += 4
        self.current_address = 0x8000 if self.current_address == 0xFFFF else self.current_address + 1
        self.bytes_remaining -= 1
        if self.bytes_remaining == 0:
            if self.loop:
                self.current_address = self.sample_address
                self.bytes_remaining = self.sample_length
            elif self.irq_enabled:
                self.irq_flag = True

    def clock_timer(self, cycles: int) -> None:
        self.timer_counter -= cycles
        period = self.PERIODS[self.rate_index]
        while self.timer_counter <= 0:
            self.timer_counter += period
            if not self.silence:
                if self.shift_register & 1:
                    if self.output_level <= 125:
                        self.output_level += 2
                elif self.output_level >= 2:
                    self.output_level -= 2
            self.shift_register >>= 1
            self.bits_remaining -= 1
            if self.bits_remaining == 0:
                self.bits_remaining = 8
                if self.sample_buffer is None:
                    self.silence = True
                else:
                    self.silence = False
                    self.shift_register = self.sample_buffer
                    self.sample_buffer = None
                    self.fill_buffer()


class APU:
    """NTSC RP2A03 five-channel sound unit with nonlinear mixing."""

    SAMPLE_RATE = 48_000
    LENGTH_TABLE = (10, 254, 20, 2, 40, 4, 80, 6, 160, 8, 60, 10, 14, 12,
                    26, 14, 12, 16, 24, 18, 48, 20, 96, 22, 192, 24, 72, 26,
                    16, 28, 32, 30)

    def __init__(self) -> None:
        self.bus: Bus | None = None
        self.reg = bytearray(0x18)
        self.samples = array("h")
        self._make_channels()
        self._reset_state()

    def _make_channels(self) -> None:
        self.pulse1 = PulseChannel(1)
        self.pulse2 = PulseChannel(2)
        self.triangle = TriangleChannel()
        self.noise = NoiseChannel()
        self.dmc = DMCChannel(self)

    def _reset_state(self) -> None:
        self.enabled = 0
        self.frame_cycles = 0
        self.frame_irq = False
        self.irq_inhibit = False
        self.five_step = False
        self.frame_reset_delay = 0
        self.cpu_cycles = 0
        self.last_cpu_cycle = 0
        self.sample_phase = 0
        self.hp90_x = self.hp90_y = 0.0
        self.hp440_x = self.hp440_y = 0.0
        self.lp14k = 0.0
        self.hp90_a = math.exp(-2.0 * math.pi * 90.0 / self.SAMPLE_RATE)
        self.hp440_a = math.exp(-2.0 * math.pi * 440.0 / self.SAMPLE_RATE)
        self.lp14k_a = 1.0 - math.exp(-2.0 * math.pi * 14_000.0 / self.SAMPLE_RATE)

    @property
    def irq_pending(self) -> bool:
        return self.frame_irq or self.dmc.irq_flag

    def connect_bus(self, bus: Bus) -> None:
        self.bus = bus

    def sync_to_cpu(self) -> None:
        if self.bus is None or self.bus.cpu is None:
            return
        target = self.bus.cpu.total_cycles
        if target < self.last_cpu_cycle:
            self.last_cpu_cycle = target
        elapsed = target - self.last_cpu_cycle
        if elapsed:
            self.tick(elapsed)
            self.last_cpu_cycle = target

    def reset(self) -> None:
        self.reg[:] = bytes(len(self.reg))
        self.samples = array("h")
        self._make_channels()
        self._reset_state()

    def read_status(self) -> int:
        value = 0
        if self.pulse1.length: value |= 0x01
        if self.pulse2.length: value |= 0x02
        if self.triangle.length: value |= 0x04
        if self.noise.length: value |= 0x08
        if self.dmc.bytes_remaining: value |= 0x10
        if self.frame_irq: value |= 0x40
        if self.dmc.irq_flag: value |= 0x80
        self.frame_irq = False
        return value

    def write(self, addr: int, value: int) -> None:
        value &= 0xFF
        if 0x4000 <= addr <= 0x4013:
            self.reg[addr - 0x4000] = value
        if 0x4000 <= addr <= 0x4003:
            self.pulse1.write(addr & 3, value, self.LENGTH_TABLE)
        elif 0x4004 <= addr <= 0x4007:
            self.pulse2.write(addr & 3, value, self.LENGTH_TABLE)
        elif 0x4008 <= addr <= 0x400B:
            self.triangle.write(addr & 3, value, self.LENGTH_TABLE)
        elif 0x400C <= addr <= 0x400F:
            self.noise.write(addr & 3, value, self.LENGTH_TABLE)
        elif 0x4010 <= addr <= 0x4013:
            self.dmc.write(addr & 3, value)
        elif addr == 0x4015:
            self.enabled = value & 0x1F
            self.pulse1.set_enabled(bool(value & 1))
            self.pulse2.set_enabled(bool(value & 2))
            self.triangle.set_enabled(bool(value & 4))
            self.noise.set_enabled(bool(value & 8))
            self.dmc.set_enabled(bool(value & 0x10))
        elif addr == 0x4017:
            self.five_step = bool(value & 0x80)
            self.irq_inhibit = bool(value & 0x40)
            if self.irq_inhibit:
                self.frame_irq = False
            self.frame_reset_delay = 3 if self.cpu_cycles & 1 else 4

    def _quarter_frame(self) -> None:
        self.pulse1.clock_quarter()
        self.pulse2.clock_quarter()
        self.triangle.clock_quarter()
        self.noise.clock_quarter()

    def _half_frame(self) -> None:
        self.pulse1.clock_half()
        self.pulse2.clock_half()
        self.triangle.clock_half()
        self.noise.clock_half()

    def _clock_frame_counter(self, cycles: int) -> None:
        old = self.frame_cycles
        end = old + cycles
        if self.five_step:
            for point, quarter, half in ((7457, True, False), (14913, True, True),
                                         (22371, True, False), (37281, True, True)):
                if old < point <= end:
                    if quarter: self._quarter_frame()
                    if half: self._half_frame()
            if end >= 37282:
                end -= 37282
        else:
            for point, quarter, half in ((7457, True, False), (14913, True, True),
                                         (22371, True, False), (29829, True, True)):
                if old < point <= end:
                    if quarter: self._quarter_frame()
                    if half: self._half_frame()
            if old < 29829 <= end and not self.irq_inhibit:
                self.frame_irq = True
            if end >= 29830:
                end -= 29830
        self.frame_cycles = end

    def _mix_sample(self) -> int:
        p1, p2 = self.pulse1.output(), self.pulse2.output()
        triangle, noise, dmc = self.triangle.output(), self.noise.output(), self.dmc.output_level
        pulse_sum = p1 + p2
        pulse_out = 95.88 / (8128.0 / pulse_sum + 100.0) if pulse_sum else 0.0
        tnd_input = triangle / 8227.0 + noise / 12241.0 + dmc / 22638.0
        mixed = pulse_out + (159.79 / (1.0 / tnd_input + 100.0) if tnd_input else 0.0)

        hp = self.hp90_a * (self.hp90_y + mixed - self.hp90_x)
        self.hp90_x, self.hp90_y = mixed, hp
        hp2 = self.hp440_a * (self.hp440_y + hp - self.hp440_x)
        self.hp440_x, self.hp440_y = hp, hp2
        self.lp14k += self.lp14k_a * (hp2 - self.lp14k)
        return max(-32768, min(32767, int(self.lp14k * 54_000)))

    def tick(self, cycles: int) -> None:
        remaining = cycles
        while remaining:
            to_sample = (CPU_HZ - self.sample_phase + self.SAMPLE_RATE - 1) // self.SAMPLE_RATE
            step = min(remaining, to_sample)
            if self.frame_reset_delay:
                step = min(step, self.frame_reset_delay)
            self.cpu_cycles += step
            self.pulse1.clock_timer(step)
            self.pulse2.clock_timer(step)
            self.triangle.clock_timer(step)
            self.noise.clock_timer(step)
            self.dmc.clock_timer(step)
            self._clock_frame_counter(step)
            if self.frame_reset_delay:
                self.frame_reset_delay -= step
                if self.frame_reset_delay <= 0:
                    self.frame_reset_delay = 0
                    self.frame_cycles = 0
                    if self.five_step:
                        self._quarter_frame()
                        self._half_frame()
            self.sample_phase += step * self.SAMPLE_RATE
            while self.sample_phase >= CPU_HZ:
                self.sample_phase -= CPU_HZ
                self.samples.append(self._mix_sample())
            remaining -= step
        if len(self.samples) > self.SAMPLE_RATE * 2:
            del self.samples[:-self.SAMPLE_RATE]

    def drain_samples(self) -> bytes:
        if not self.samples:
            return b""
        data = self.samples.tobytes()
        del self.samples[:]
        return data


class PPU:
    def __init__(self, cart: Cartridge) -> None:
        self.cart = cart
        self.nametable = bytearray(0x1000)
        self.palette = bytearray(32)
        self.oam = bytearray(256)
        self.framebuffer = bytearray(WIDTH * HEIGHT * 3)
        self.ctrl = self.mask = self.status = 0
        self.oam_addr = 0
        self.v = self.t = 0
        self.fine_x = 0
        self.write_latch = False
        self.read_buffer = 0
        self.open_bus = 0
        self.scroll_x = self.scroll_y = 0
        self.nmi_requested = False
        self.bg_row_cache: dict[tuple[int, ...], tuple[bytes, bytes]] = {}

    def reset(self) -> None:
        self.ctrl = self.mask = self.status = 0
        self.oam_addr = self.v = self.t = self.fine_x = 0
        self.write_latch = False
        self.read_buffer = self.open_bus = 0
        self.scroll_x = self.scroll_y = 0
        self.nmi_requested = False
        self.bg_row_cache.clear()
        self.framebuffer[:] = bytes(len(self.framebuffer))

    def _mirror_nametable(self, addr: int) -> int:
        index = (addr - 0x2000) & 0x0FFF
        table, offset = index // 0x400, index & 0x3FF
        mode = self.cart.mirroring
        if mode == "four":
            physical = table
        elif mode == "vertical":
            physical = table & 1
        elif mode == "horizontal":
            physical = table >> 1
        elif mode == "single1":
            physical = 1
        else:
            physical = 0
        return physical * 0x400 + offset

    @staticmethod
    def _palette_address(addr: int) -> int:
        index = addr & 0x1F
        if index in (0x10, 0x14, 0x18, 0x1C):
            index -= 0x10
        return index

    def read_memory(self, addr: int) -> int:
        addr &= 0x3FFF
        if addr < 0x2000:
            return self.cart.ppu_read(addr)
        if addr < 0x3F00:
            return self.nametable[self._mirror_nametable(addr)]
        return self.palette[self._palette_address(addr)]

    def write_memory(self, addr: int, value: int) -> None:
        addr &= 0x3FFF
        value &= 0xFF
        if addr < 0x2000:
            self.cart.ppu_write(addr, value)
        elif addr < 0x3F00:
            self.nametable[self._mirror_nametable(addr)] = value
        else:
            self.palette[self._palette_address(addr)] = value & 0x3F

    def cpu_read(self, register: int) -> int:
        reg = register & 7
        if reg == 2:
            value = (self.status & 0xE0) | (self.open_bus & 0x1F)
            self.status &= ~0x80
            self.write_latch = False
            self.nmi_requested = False
        elif reg == 4:
            value = self.oam[self.oam_addr]
        elif reg == 7:
            address = self.v & 0x3FFF
            fetched = self.read_memory(address)
            if address < 0x3F00:
                value = self.read_buffer
                self.read_buffer = fetched
            else:
                value = fetched
                self.read_buffer = self.read_memory(address - 0x1000)
            self.v = (self.v + (32 if self.ctrl & 4 else 1)) & 0x7FFF
        else:
            value = self.open_bus
        self.open_bus = value & 0xFF
        return self.open_bus

    def cpu_write(self, register: int, value: int) -> None:
        reg, value = register & 7, value & 0xFF
        self.open_bus = value
        if reg == 0:
            old = self.ctrl
            self.ctrl = value
            self.t = (self.t & 0xF3FF) | ((value & 3) << 10)
            if not (old & 0x80) and (value & 0x80) and (self.status & 0x80):
                self.nmi_requested = True
        elif reg == 1:
            self.mask = value
        elif reg == 3:
            self.oam_addr = value
        elif reg == 4:
            self.oam[self.oam_addr] = value
            self.oam_addr = (self.oam_addr + 1) & 0xFF
        elif reg == 5:
            if not self.write_latch:
                self.scroll_x = value
                self.fine_x = value & 7
                self.t = (self.t & 0x7FE0) | (value >> 3)
            else:
                self.scroll_y = value
                self.t = (self.t & 0x0C1F) | ((value & 7) << 12) | ((value & 0xF8) << 2)
            self.write_latch = not self.write_latch
        elif reg == 6:
            if not self.write_latch:
                self.t = (self.t & 0x00FF) | ((value & 0x3F) << 8)
            else:
                self.t = (self.t & 0x7F00) | value
                self.v = self.t
            self.write_latch = not self.write_latch
        elif reg == 7:
            self.write_memory(self.v, value)
            self.v = (self.v + (32 if self.ctrl & 4 else 1)) & 0x7FFF

    def start_frame(self) -> None:
        self.status &= ~0xE0
        self.nmi_requested = False
        universal = NES_PALETTE[self.palette[0] & 0x3F]
        self.framebuffer[:] = bytes(universal) * (WIDTH * HEIGHT)

    def enter_vblank(self) -> None:
        self.status |= 0x80
        if self.ctrl & 0x80:
            self.nmi_requested = True

    def _background_pixel(self, x: int, y: int) -> tuple[int, bool]:
        if not (self.mask & 0x08) or (x < 8 and not (self.mask & 0x02)):
            return 0, False
        base = self.ctrl & 3
        wx, wy = x + self.scroll_x, y + self.scroll_y
        nt_x = ((base & 1) + wx // 256) & 1
        nt_y = (((base >> 1) & 1) + wy // 240) & 1
        lx, ly = wx & 0xFF, wy % 240
        nt = nt_y * 2 + nt_x
        tile_x, tile_y = lx >> 3, ly >> 3
        nt_base = 0x2000 + nt * 0x400
        tile = self.read_memory(nt_base + tile_y * 32 + tile_x)
        pattern = (0x1000 if self.ctrl & 0x10 else 0) + tile * 16 + (ly & 7)
        bit = 7 - (lx & 7)
        color = ((self.cart.ppu_read(pattern) >> bit) & 1) | (((self.cart.ppu_read(pattern + 8) >> bit) & 1) << 1)
        if color == 0:
            return 0, False
        attribute = self.read_memory(nt_base + 0x3C0 + (tile_y >> 2) * 8 + (tile_x >> 2))
        shift = ((tile_y & 2) << 1) | (tile_x & 2)
        palette = (attribute >> shift) & 3
        return self.palette[(palette << 2) | color] & 0x3F, True

    def _decoded_bg_row(self, low: int, high: int, palette_base: int) -> tuple[bytes, bytes]:
        palette = self.palette
        key = (low, high, palette[0] & 0x3F,
               palette[palette_base | 1] & 0x3F,
               palette[palette_base | 2] & 0x3F,
               palette[palette_base | 3] & 0x3F)
        cached = self.bg_row_cache.get(key)
        if cached is not None:
            return cached
        choices = key[2:]
        pixels = []
        solid = []
        for bit in range(7, -1, -1):
            value = ((low >> bit) & 1) | (((high >> bit) & 1) << 1)
            pixels.append(choices[value])
            solid.append(bool(value))
        result = bytes(pixels), bytes(solid)
        if len(self.bg_row_cache) > 8192:
            self.bg_row_cache.clear()
        self.bg_row_cache[key] = result
        return result

    def _sprite_line(self, y: int) -> list[tuple[int, int, bool, bool] | None]:
        pixels: list[tuple[int, int, bool, bool] | None] = [None] * WIDTH
        if not (self.mask & 0x10):
            return pixels
        height = 16 if self.ctrl & 0x20 else 8
        visible: list[int] = []
        for i in range(64):
            sy = self.oam[i * 4] + 1
            if sy <= y < sy + height:
                if len(visible) < 8:
                    visible.append(i)
                else:
                    self.status |= 0x20
                    break
        # Reverse drawing means the lowest OAM index wins priority.
        chr_data = self.cart.chr_window
        for i in reversed(visible):
            sy, tile, attr, sx = self.oam[i * 4:i * 4 + 4]
            row = y - (sy + 1)
            if attr & 0x80:
                row = height - 1 - row
            if height == 16:
                table = (tile & 1) * 0x1000
                tile_index = tile & 0xFE
                if row >= 8:
                    tile_index += 1
                    row -= 8
                pattern = table + tile_index * 16 + row
            else:
                pattern = (0x1000 if self.ctrl & 0x08 else 0) + tile * 16 + row
            low, high = chr_data[pattern & 0x1FFF], chr_data[(pattern + 8) & 0x1FFF]
            for px in range(8):
                screen_x = sx + px
                if screen_x >= WIDTH or (screen_x < 8 and not (self.mask & 0x04)):
                    continue
                bit = px if attr & 0x40 else 7 - px
                color = ((low >> bit) & 1) | (((high >> bit) & 1) << 1)
                if color:
                    palette_index = 0x10 | ((attr & 3) << 2) | color
                    pixels[screen_x] = (self.palette[palette_index] & 0x3F,
                                                bool(attr & 0x20), i == 0, True)
        return pixels

    def render_scanline(self, y: int) -> None:
        # Decode in eight-pixel tile runs.  Avoiding four Python method calls
        # per output pixel is what keeps this implementation usable at NTSC
        # speed without numpy, Pillow, pygame or a native extension.
        universal = self.palette[0] & 0x3F
        colors = bytearray([universal]) * WIDTH
        opaque = bytearray(WIDTH)
        mask = self.mask

        if mask & 0x08:
            base_nt = self.ctrl & 3
            world_y = y + self.scroll_y
            nt_y = (((base_nt >> 1) & 1) + world_y // 240) & 1
            local_y = world_y % 240
            tile_y, fine_y = local_y >> 3, local_y & 7
            pattern_table = 0x1000 if self.ctrl & 0x10 else 0
            chr_data = self.cart.chr_window
            nt_bases = tuple(self._mirror_nametable(0x2000 + table * 0x400)
                             for table in range(4))
            nametable = self.nametable
            x = 0
            while x < WIDTH:
                world_x = x + self.scroll_x
                nt_x = ((base_nt & 1) + world_x // 256) & 1
                local_x = world_x & 0xFF
                tile_x, fine_x = local_x >> 3, local_x & 7
                run = min(8 - fine_x, WIDTH - x)
                table = nt_y * 2 + nt_x
                physical_base = nt_bases[table]
                tile = nametable[physical_base + tile_y * 32 + tile_x]
                pattern = pattern_table + tile * 16 + fine_y
                low = chr_data[pattern & 0x1FFF]
                high = chr_data[(pattern + 8) & 0x1FFF]
                attribute = nametable[physical_base + 0x3C0 + (tile_y >> 2) * 8 + (tile_x >> 2)]
                shift = ((tile_y & 2) << 1) | (tile_x & 2)
                palette_base = ((attribute >> shift) & 3) << 2
                tile_colors, tile_opaque = self._decoded_bg_row(low, high, palette_base)
                colors[x:x + run] = tile_colors[fine_x:fine_x + run]
                opaque[x:x + run] = tile_opaque[fine_x:fine_x + run]
                x += run
            if not (mask & 0x02):
                colors[:8] = bytes([universal]) * 8
                opaque[:8] = bytes(8)

        if mask & 0x10:
            sprites = self._sprite_line(y)
            both_layers = (mask & 0x18) == 0x18
            for x, sprite in enumerate(sprites):
                if sprite is None:
                    continue
                sp_color, behind, sprite_zero, _ = sprite
                if sprite_zero and opaque[x] and x != 255 and both_layers:
                    self.status |= 0x40
                if not opaque[x] or not behind:
                    colors[x] = sp_color

        if mask & 1:  # PPUMASK grayscale mode
            for x, color in enumerate(colors):
                colors[x] = color & 0x30
        start = y * WIDTH * 3
        self.framebuffer[start:start + WIDTH * 3] = b"".join(map(NES_RGB.__getitem__, colors))


class Bus:
    def __init__(self, cart: Cartridge, ppu: PPU, apu: APU,
                 controllers: tuple[Controller, Controller]) -> None:
        self.cart, self.ppu, self.apu = cart, ppu, apu
        self.controllers = controllers
        self.cpu: CPU6502 | None = None
        self.ram = bytearray(0x800)
        self.open_bus = 0
        self.apu.connect_bus(self)

    def read(self, addr: int) -> int:
        addr &= 0xFFFF
        if addr < 0x2000:
            value = self.ram[addr & 0x7FF]
        elif addr < 0x4000:
            value = self.ppu.cpu_read(addr)
        elif addr == 0x4015:
            self.apu.sync_to_cpu()
            value = self.apu.read_status()
        elif addr == 0x4016:
            value = self.controllers[0].read()
        elif addr == 0x4017:
            value = self.controllers[1].read()
        elif addr >= 0x4020:
            value = self.cart.cpu_read(addr)
        else:
            value = self.open_bus
        self.open_bus = value & 0xFF
        return self.open_bus

    def write(self, addr: int, value: int) -> None:
        addr &= 0xFFFF
        value &= 0xFF
        self.open_bus = value
        if addr < 0x2000:
            self.ram[addr & 0x7FF] = value
        elif addr < 0x4000:
            self.ppu.cpu_write(addr, value)
        elif 0x4000 <= addr <= 0x4013 or addr in (0x4015, 0x4017):
            self.apu.sync_to_cpu()
            self.apu.write(addr, value)
        elif addr == 0x4014:
            base = value << 8
            for offset in range(256):
                self.ppu.oam[(self.ppu.oam_addr + offset) & 0xFF] = self.read(base + offset)
            if self.cpu is not None:
                self.cpu.stall += 513 + (self.cpu.total_cycles & 1)
        elif addr == 0x4016:
            self.controllers[0].write(value)
            self.controllers[1].write(value)
        elif addr >= 0x4020:
            self.cart.cpu_write(addr, value)


class CPU6502:
    C, Z, I, D, B, U, V, N = 1, 2, 4, 8, 16, 32, 64, 128
    PAGE_CROSS = {"ADC", "AND", "CMP", "EOR", "LDA", "LDX", "LDY", "LAX", "LAS", "ORA", "SBC"}

    # Complete official opcode map plus the stable unofficial instructions used
    # by commercial software.  Each token is mnemonic/address-mode/base-cycles.
    _ROWS = (
        "BRK:imp:7 ORA:izx:6 KIL:imp:2 SLO:izx:8 NOP:zp:3 ORA:zp:3 ASL:zp:5 SLO:zp:5 PHP:imp:3 ORA:imm:2 ASL:acc:2 ANC:imm:2 NOP:abs:4 ORA:abs:4 ASL:abs:6 SLO:abs:6",
        "BPL:rel:2 ORA:izy:5 KIL:imp:2 SLO:izy:8 NOP:zpx:4 ORA:zpx:4 ASL:zpx:6 SLO:zpx:6 CLC:imp:2 ORA:aby:4 NOP:imp:2 SLO:aby:7 NOP:abx:4 ORA:abx:4 ASL:abx:7 SLO:abx:7",
        "JSR:abs:6 AND:izx:6 KIL:imp:2 RLA:izx:8 BIT:zp:3 AND:zp:3 ROL:zp:5 RLA:zp:5 PLP:imp:4 AND:imm:2 ROL:acc:2 ANC:imm:2 BIT:abs:4 AND:abs:4 ROL:abs:6 RLA:abs:6",
        "BMI:rel:2 AND:izy:5 KIL:imp:2 RLA:izy:8 NOP:zpx:4 AND:zpx:4 ROL:zpx:6 RLA:zpx:6 SEC:imp:2 AND:aby:4 NOP:imp:2 RLA:aby:7 NOP:abx:4 AND:abx:4 ROL:abx:7 RLA:abx:7",
        "RTI:imp:6 EOR:izx:6 KIL:imp:2 SRE:izx:8 NOP:zp:3 EOR:zp:3 LSR:zp:5 SRE:zp:5 PHA:imp:3 EOR:imm:2 LSR:acc:2 ALR:imm:2 JMP:abs:3 EOR:abs:4 LSR:abs:6 SRE:abs:6",
        "BVC:rel:2 EOR:izy:5 KIL:imp:2 SRE:izy:8 NOP:zpx:4 EOR:zpx:4 LSR:zpx:6 SRE:zpx:6 CLI:imp:2 EOR:aby:4 NOP:imp:2 SRE:aby:7 NOP:abx:4 EOR:abx:4 LSR:abx:7 SRE:abx:7",
        "RTS:imp:6 ADC:izx:6 KIL:imp:2 RRA:izx:8 NOP:zp:3 ADC:zp:3 ROR:zp:5 RRA:zp:5 PLA:imp:4 ADC:imm:2 ROR:acc:2 ARR:imm:2 JMP:ind:5 ADC:abs:4 ROR:abs:6 RRA:abs:6",
        "BVS:rel:2 ADC:izy:5 KIL:imp:2 RRA:izy:8 NOP:zpx:4 ADC:zpx:4 ROR:zpx:6 RRA:zpx:6 SEI:imp:2 ADC:aby:4 NOP:imp:2 RRA:aby:7 NOP:abx:4 ADC:abx:4 ROR:abx:7 RRA:abx:7",
        "NOP:imm:2 STA:izx:6 NOP:imm:2 SAX:izx:6 STY:zp:3 STA:zp:3 STX:zp:3 SAX:zp:3 DEY:imp:2 NOP:imm:2 TXA:imp:2 XAA:imm:2 STY:abs:4 STA:abs:4 STX:abs:4 SAX:abs:4",
        "BCC:rel:2 STA:izy:6 KIL:imp:2 AHX:izy:6 STY:zpx:4 STA:zpx:4 STX:zpy:4 SAX:zpy:4 TYA:imp:2 STA:aby:5 TXS:imp:2 TAS:aby:5 SHY:abx:5 STA:abx:5 SHX:aby:5 AHX:aby:5",
        "LDY:imm:2 LDA:izx:6 LDX:imm:2 LAX:izx:6 LDY:zp:3 LDA:zp:3 LDX:zp:3 LAX:zp:3 TAY:imp:2 LDA:imm:2 TAX:imp:2 LAX:imm:2 LDY:abs:4 LDA:abs:4 LDX:abs:4 LAX:abs:4",
        "BCS:rel:2 LDA:izy:5 KIL:imp:2 LAX:izy:5 LDY:zpx:4 LDA:zpx:4 LDX:zpy:4 LAX:zpy:4 CLV:imp:2 LDA:aby:4 TSX:imp:2 LAS:aby:4 LDY:abx:4 LDA:abx:4 LDX:aby:4 LAX:aby:4",
        "CPY:imm:2 CMP:izx:6 NOP:imm:2 DCP:izx:8 CPY:zp:3 CMP:zp:3 DEC:zp:5 DCP:zp:5 INY:imp:2 CMP:imm:2 DEX:imp:2 AXS:imm:2 CPY:abs:4 CMP:abs:4 DEC:abs:6 DCP:abs:6",
        "BNE:rel:2 CMP:izy:5 KIL:imp:2 DCP:izy:8 NOP:zpx:4 CMP:zpx:4 DEC:zpx:6 DCP:zpx:6 CLD:imp:2 CMP:aby:4 NOP:imp:2 DCP:aby:7 NOP:abx:4 CMP:abx:4 DEC:abx:7 DCP:abx:7",
        "CPX:imm:2 SBC:izx:6 NOP:imm:2 ISC:izx:8 CPX:zp:3 SBC:zp:3 INC:zp:5 ISC:zp:5 INX:imp:2 SBC:imm:2 NOP:imp:2 SBC:imm:2 CPX:abs:4 SBC:abs:4 INC:abs:6 ISC:abs:6",
        "BEQ:rel:2 SBC:izy:5 KIL:imp:2 ISC:izy:8 NOP:zpx:4 SBC:zpx:4 INC:zpx:6 ISC:zpx:6 SED:imp:2 SBC:aby:4 NOP:imp:2 ISC:aby:7 NOP:abx:4 SBC:abx:4 INC:abx:7 ISC:abx:7",
    )
    OPCODES = tuple(tuple(token.split(":")[:2]) + (int(token.split(":")[2]),)
                    for row in _ROWS for token in row.split())

    def __init__(self, bus: Bus) -> None:
        self.bus = bus
        self.cart = bus.cart
        bus.cpu = self
        self.a = self.x = self.y = 0
        self.sp = 0xFD
        self.status = 0x24
        self.pc = 0
        self.total_cycles = 0
        self.stall = 0
        self.pending_nmi = False
        self.pending_irq = False

    def read(self, addr: int) -> int:
        return self.bus.read(addr)

    def write(self, addr: int, value: int) -> None:
        self.bus.write(addr, value)

    def fetch(self) -> int:
        if self.pc >= 0x8000:
            value = self.cart.prg_window[self.pc - 0x8000]
        else:
            value = self.bus.read(self.pc)
        self.pc = (self.pc + 1) & 0xFFFF
        return value

    def read16(self, addr: int) -> int:
        return self.read(addr) | (self.read((addr + 1) & 0xFFFF) << 8)

    def push(self, value: int) -> None:
        self.write(0x100 | self.sp, value)
        self.sp = (self.sp - 1) & 0xFF

    def pull(self) -> int:
        self.sp = (self.sp + 1) & 0xFF
        return self.read(0x100 | self.sp)

    def set_flag(self, flag: int, condition: bool) -> None:
        self.status = (self.status | flag) if condition else (self.status & ~flag)

    def zn(self, value: int) -> int:
        value &= 0xFF
        self.set_flag(self.Z, value == 0)
        self.set_flag(self.N, bool(value & 0x80))
        return value

    def reset(self) -> None:
        self.a = self.x = self.y = 0
        self.sp = 0xFD
        self.status = self.I | self.U
        self.pc = self.read16(0xFFFC)
        self.total_cycles = 7
        self.stall = 0
        self.pending_nmi = self.pending_irq = False
        if self.pc < 0x8000:
            raise EmulatorError(f"Invalid reset vector ${self.pc:04X}.")

    def request_nmi(self) -> None:
        self.pending_nmi = True

    def request_irq(self) -> None:
        self.pending_irq = True

    def _interrupt(self, vector: int, break_flag: bool = False) -> None:
        self.push(self.pc >> 8)
        self.push(self.pc & 0xFF)
        pushed = (self.status | self.U) & ~self.B
        if break_flag:
            pushed |= self.B
        self.push(pushed)
        self.status = (self.status | self.I | self.U) & ~self.B
        self.pc = self.read16(vector)

    def _address(self, mode: str) -> tuple[int | None, bool]:
        if mode in ("imp", "acc"):
            return None, False
        if mode == "imm":
            address = self.pc
            self.pc = (self.pc + 1) & 0xFFFF
            return address, False
        if mode == "zp":
            return self.fetch(), False
        if mode == "zpx":
            return (self.fetch() + self.x) & 0xFF, False
        if mode == "zpy":
            return (self.fetch() + self.y) & 0xFF, False
        if mode == "abs":
            lo, hi = self.fetch(), self.fetch()
            return lo | (hi << 8), False
        if mode in ("abx", "aby"):
            lo, hi = self.fetch(), self.fetch()
            base = lo | (hi << 8)
            address = (base + (self.x if mode == "abx" else self.y)) & 0xFFFF
            return address, (base & 0xFF00) != (address & 0xFF00)
        if mode == "ind":
            lo, hi = self.fetch(), self.fetch()
            pointer = lo | (hi << 8)
            # NMOS 6502 page-wrap bug, relied upon by NES software.
            return self.read(pointer) | (self.read((pointer & 0xFF00) | ((pointer + 1) & 0xFF)) << 8), False
        if mode == "izx":
            zp = (self.fetch() + self.x) & 0xFF
            return self.read(zp) | (self.read((zp + 1) & 0xFF) << 8), False
        if mode == "izy":
            zp = self.fetch()
            base = self.read(zp) | (self.read((zp + 1) & 0xFF) << 8)
            address = (base + self.y) & 0xFFFF
            return address, (base & 0xFF00) != (address & 0xFF00)
        if mode == "rel":
            offset = self.fetch()
            if offset & 0x80:
                offset -= 0x100
            return (self.pc + offset) & 0xFFFF, False
        raise EmulatorError(f"Internal error: unknown address mode {mode}.")

    def _adc(self, value: int) -> None:
        total = self.a + value + (1 if self.status & self.C else 0)
        result = total & 0xFF
        self.set_flag(self.C, total > 0xFF)
        self.set_flag(self.V, bool((~(self.a ^ value) & (self.a ^ result)) & 0x80))
        self.a = self.zn(result)

    def _compare(self, register: int, value: int) -> None:
        self.set_flag(self.C, register >= value)
        self.zn(register - value)

    def _shift(self, name: str, value: int) -> int:
        old_carry = 1 if self.status & self.C else 0
        if name == "ASL":
            self.set_flag(self.C, bool(value & 0x80)); value = (value << 1) & 0xFF
        elif name == "LSR":
            self.set_flag(self.C, bool(value & 1)); value >>= 1
        elif name == "ROL":
            self.set_flag(self.C, bool(value & 0x80)); value = ((value << 1) | old_carry) & 0xFF
        else:
            self.set_flag(self.C, bool(value & 1)); value = (value >> 1) | (old_carry << 7)
        return self.zn(value)

    def _branch(self, condition: bool, target: int) -> int:
        if not condition:
            return 0
        old = self.pc
        self.pc = target
        return 1 + ((old & 0xFF00) != (target & 0xFF00))

    def _execute(self, name: str, mode: str, addr: int | None) -> int:
        value = self.read(addr) if addr is not None and name not in {
            "STA", "STX", "STY", "SAX", "AHX", "TAS", "SHX", "SHY",
            "JMP", "JSR", "BCC", "BCS", "BEQ", "BMI", "BNE", "BPL", "BVC", "BVS"
        } else 0
        if name == "LDA": self.a = self.zn(value)
        elif name == "LDX": self.x = self.zn(value)
        elif name == "LDY": self.y = self.zn(value)
        elif name == "STA": self.write(addr, self.a)  # type: ignore[arg-type]
        elif name == "STX": self.write(addr, self.x)  # type: ignore[arg-type]
        elif name == "STY": self.write(addr, self.y)  # type: ignore[arg-type]
        elif name == "TAX": self.x = self.zn(self.a)
        elif name == "TAY": self.y = self.zn(self.a)
        elif name == "TXA": self.a = self.zn(self.x)
        elif name == "TYA": self.a = self.zn(self.y)
        elif name == "TSX": self.x = self.zn(self.sp)
        elif name == "TXS": self.sp = self.x
        elif name == "PHA": self.push(self.a)
        elif name == "PHP": self.push(self.status | self.B | self.U)
        elif name == "PLA": self.a = self.zn(self.pull())
        elif name == "PLP": self.status = (self.pull() | self.U) & ~self.B
        elif name == "AND": self.a = self.zn(self.a & value)
        elif name == "ORA": self.a = self.zn(self.a | value)
        elif name == "EOR": self.a = self.zn(self.a ^ value)
        elif name == "BIT":
            self.set_flag(self.Z, not (self.a & value)); self.set_flag(self.V, bool(value & 0x40)); self.set_flag(self.N, bool(value & 0x80))
        elif name == "ADC": self._adc(value)
        elif name == "SBC": self._adc(value ^ 0xFF)
        elif name == "CMP": self._compare(self.a, value)
        elif name == "CPX": self._compare(self.x, value)
        elif name == "CPY": self._compare(self.y, value)
        elif name in ("ASL", "LSR", "ROL", "ROR"):
            if mode == "acc": self.a = self._shift(name, self.a)
            else: self.write(addr, self._shift(name, value))  # type: ignore[arg-type]
        elif name == "INC": self.write(addr, self.zn(value + 1))  # type: ignore[arg-type]
        elif name == "DEC": self.write(addr, self.zn(value - 1))  # type: ignore[arg-type]
        elif name == "INX": self.x = self.zn(self.x + 1)
        elif name == "INY": self.y = self.zn(self.y + 1)
        elif name == "DEX": self.x = self.zn(self.x - 1)
        elif name == "DEY": self.y = self.zn(self.y - 1)
        elif name == "JMP": self.pc = addr  # type: ignore[assignment]
        elif name == "JSR":
            ret = (self.pc - 1) & 0xFFFF; self.push(ret >> 8); self.push(ret); self.pc = addr  # type: ignore[assignment]
        elif name == "RTS": self.pc = ((self.pull() | (self.pull() << 8)) + 1) & 0xFFFF
        elif name == "RTI":
            self.status = (self.pull() | self.U) & ~self.B; self.pc = self.pull() | (self.pull() << 8)
        elif name == "BRK":
            self.pc = (self.pc + 1) & 0xFFFF; self._interrupt(0xFFFE, True)
        elif name == "CLC": self.status &= ~self.C
        elif name == "CLD": self.status &= ~self.D
        elif name == "CLI": self.status &= ~self.I
        elif name == "CLV": self.status &= ~self.V
        elif name == "SEC": self.status |= self.C
        elif name == "SED": self.status |= self.D
        elif name == "SEI": self.status |= self.I
        elif name == "BCC": return self._branch(not self.status & self.C, addr)  # type: ignore[arg-type]
        elif name == "BCS": return self._branch(bool(self.status & self.C), addr)  # type: ignore[arg-type]
        elif name == "BEQ": return self._branch(bool(self.status & self.Z), addr)  # type: ignore[arg-type]
        elif name == "BMI": return self._branch(bool(self.status & self.N), addr)  # type: ignore[arg-type]
        elif name == "BNE": return self._branch(not self.status & self.Z, addr)  # type: ignore[arg-type]
        elif name == "BPL": return self._branch(not self.status & self.N, addr)  # type: ignore[arg-type]
        elif name == "BVC": return self._branch(not self.status & self.V, addr)  # type: ignore[arg-type]
        elif name == "BVS": return self._branch(bool(self.status & self.V), addr)  # type: ignore[arg-type]
        elif name == "SLO": self.write(addr, self._shift("ASL", value)); self.a = self.zn(self.a | self.read(addr))  # type: ignore[arg-type]
        elif name == "RLA": self.write(addr, self._shift("ROL", value)); self.a = self.zn(self.a & self.read(addr))  # type: ignore[arg-type]
        elif name == "SRE": self.write(addr, self._shift("LSR", value)); self.a = self.zn(self.a ^ self.read(addr))  # type: ignore[arg-type]
        elif name == "RRA": self.write(addr, self._shift("ROR", value)); self._adc(self.read(addr))  # type: ignore[arg-type]
        elif name == "SAX": self.write(addr, self.a & self.x)  # type: ignore[arg-type]
        elif name == "LAX": self.a = self.x = self.zn(value)
        elif name == "DCP": self.write(addr, self.zn(value - 1)); self._compare(self.a, self.read(addr))  # type: ignore[arg-type]
        elif name == "ISC": self.write(addr, self.zn(value + 1)); self._adc(self.read(addr) ^ 0xFF)  # type: ignore[arg-type]
        elif name == "ANC": self.a = self.zn(self.a & value); self.set_flag(self.C, bool(self.a & 0x80))
        elif name == "ALR": self.a &= value; self.a = self._shift("LSR", self.a)
        elif name == "ARR":
            self.a &= value; self.a = self._shift("ROR", self.a); self.set_flag(self.C, bool(self.a & 0x40)); self.set_flag(self.V, bool(((self.a >> 6) ^ (self.a >> 5)) & 1))
        elif name == "AXS":
            result = (self.a & self.x) - value; self.set_flag(self.C, result >= 0); self.x = self.zn(result)
        elif name == "XAA": self.a = self.zn(self.x & value)
        elif name == "LAS": self.a = self.x = self.sp = self.zn(value & self.sp)
        elif name in ("AHX", "TAS", "SHX", "SHY"):
            high_mask = (((addr >> 8) + 1) & 0xFF) if addr is not None else 0
            if name == "TAS": self.sp = self.a & self.x; out = self.sp & high_mask
            elif name == "SHX": out = self.x & high_mask
            elif name == "SHY": out = self.y & high_mask
            else: out = self.a & self.x & high_mask
            self.write(addr, out)  # type: ignore[arg-type]
        elif name == "KIL":
            raise EmulatorError(f"CPU jam opcode at ${self.pc - 1:04X}.")
        # NOP intentionally has no effect, including its memory-read variants.
        return 0

    def step(self) -> int:
        if self.stall:
            cycles, self.stall = self.stall, 0
            self.total_cycles += cycles
            return cycles
        if self.pending_nmi:
            self.pending_nmi = False
            self._interrupt(0xFFFA)
            self.total_cycles += 7
            return 7
        if self.pending_irq and not (self.status & self.I):
            self.pending_irq = False
            self._interrupt(0xFFFE)
            self.total_cycles += 7
            return 7

        opcode = self.fetch()
        name, mode, base_cycles = self.OPCODES[opcode]
        address, crossed = self._address(mode)
        extra = self._execute(name, mode, address)
        cycles = base_cycles + extra + (1 if crossed and name in self.PAGE_CROSS else 0)
        self.status = (self.status | self.U) & ~self.B
        self.total_cycles += cycles
        return cycles


class NES:
    def __init__(self) -> None:
        self.cart = Cartridge()
        self.controllers = (Controller(), Controller())
        self.apu = APU()
        self.ppu = PPU(self.cart)
        self.bus = Bus(self.cart, self.ppu, self.apu, self.controllers)
        self.cpu = CPU6502(self.bus)
        self.running = False
        self.paused = False
        self.frame = 0
        self._cycle_fraction = 0.0
        self._cycle_debt = 0

    def load(self, path: str) -> None:
        self.cart.load(path)
        self.reset()
        self.running = True
        self.paused = False

    def reset(self) -> None:
        self.bus.ram[:] = bytes(len(self.bus.ram))
        self.ppu.reset()
        self.apu.reset()
        self.cart.reset_mapper()
        self.cpu.reset()
        self.apu.last_cpu_cycle = self.cpu.total_cycles
        self.frame = 0
        self._cycle_fraction = 0.0
        self._cycle_debt = 0

    def _run_cpu(self, budget: int) -> None:
        budget -= self._cycle_debt
        if budget <= 0:
            self._cycle_debt = -budget
            return
        spent = 0
        while spent < budget:
            cycles = self.cpu.step()
            spent += cycles
        self.apu.sync_to_cpu()
        # IRQ is level-triggered: clearing MMC3/APU state in a handler must
        # deassert the line instead of leaving a stale queued interrupt.
        self.cpu.pending_irq = bool(self.apu.irq_pending or self.cart.irq_pending)
        self._cycle_debt = spent - budget

    def run_frame(self) -> None:
        if not self.running or self.paused:
            return
        self.ppu.start_frame()
        self._cycle_fraction += CPU_CYCLES_PER_FRAME
        frame_budget = int(self._cycle_fraction)
        self._cycle_fraction -= frame_budget
        base, remainder = divmod(frame_budget, 262)

        for scanline in range(240):
            self._run_cpu(base + (1 if scanline < remainder else 0))
            self.ppu.render_scanline(scanline)
            if self.ppu.mask & 0x18:
                self.cart.clock_scanline()
        self._run_cpu(base + (1 if 240 < remainder else 0))  # post-render
        self.ppu.enter_vblank()
        if self.ppu.nmi_requested:
            self.cpu.request_nmi()
            self.ppu.nmi_requested = False
        for scanline in range(241, 261):
            self._run_cpu(base + (1 if scanline < remainder else 0))
        self.ppu.status &= ~0xE0
        self._run_cpu(base + (1 if 261 < remainder else 0))  # pre-render
        self.frame += 1


class AudioOutput:
    """Small mixer-only pygame-ce PCM queue; no SDL window is initialized."""

    CHUNK_SAMPLES = 1024

    def __init__(self) -> None:
        self.available = False
        self.muted = False
        self.paused = False
        self.pending = bytearray()
        self.backend = "Sound unavailable — install pygame-ce"
        self.mixer = None
        self.channel = None
        self.current_sound = None
        self.queued_sound = None
        try:
            os.environ.setdefault("PYGAME_HIDE_SUPPORT_PROMPT", "1")
            # Importing/initializing only the mixer does not create an SDL video
            # application, which matters on macOS preview/beta releases.
            from pygame import mixer
            if mixer.get_init():
                mixer.quit()
            mixer.pre_init(frequency=APU.SAMPLE_RATE, size=-16, channels=1, buffer=512)
            mixer.init(frequency=APU.SAMPLE_RATE, size=-16, channels=1, buffer=512)
            self.mixer = mixer
            self.channel = mixer.Channel(0)
            self.channel.set_volume(0.72)
            self.available = True
            self.backend = "2A03 sound: pygame-ce mixer"
        except Exception as error:
            self.backend = f"Sound unavailable: {error}"

    def push(self, pcm: bytes) -> None:
        if not pcm or not self.available or self.channel is None or self.mixer is None:
            return
        self.pending.extend(pcm)
        chunk_bytes = self.CHUNK_SAMPLES * 2
        # Do not let a slow host turn an audio underrun into seconds of latency.
        if len(self.pending) > chunk_bytes * 6:
            del self.pending[:-chunk_bytes * 3]
        while len(self.pending) >= chunk_bytes:
            if self.channel.get_busy() and self.channel.get_queue() is not None:
                break
            chunk = bytes(self.pending[:chunk_bytes])
            del self.pending[:chunk_bytes]
            sound = self.mixer.Sound(buffer=chunk)
            if not self.channel.get_busy():
                self.current_sound = sound
                self.channel.play(sound)
                if self.paused:
                    self.channel.pause()
            else:
                self.queued_sound = sound
                self.channel.queue(sound)

    def set_muted(self, muted: bool) -> None:
        self.muted = muted
        if self.channel is not None:
            self.channel.set_volume(0.0 if muted else 0.72)

    def set_paused(self, paused: bool) -> None:
        self.paused = paused
        if self.channel is None:
            return
        if paused:
            self.channel.pause()
        else:
            self.channel.unpause()

    def flush(self) -> None:
        self.pending.clear()
        if self.channel is not None:
            self.channel.stop()
        self.current_sound = self.queued_sound = None

    def close(self) -> None:
        self.flush()
        if self.mixer is not None:
            self.mixer.quit()


class GUI:
    KEYMAP_P1 = {
        "x": "a", "z": "b", "Shift_L": "select", "Shift_R": "select",
        "Return": "start", "Up": "up", "Down": "down", "Left": "left", "Right": "right",
    }
    KEYMAP_P2 = {
        "h": "a", "g": "b", "r": "select", "t": "start",
        "w": "up", "s": "down", "a": "left", "d": "right",
    }

    def __init__(self) -> None:
        self.root = tk.Tk()
        self.root.title("ByChatGPT NES Emulator 0.8.0")
        self.root.resizable(False, False)
        self.root.configure(bg="#101827")
        self.nes = NES()
        self.audio = AudioOutput()
        self.next_frame = time.perf_counter()
        self.last_error = ""
        self.held_keys: set[str] = set()
        self.image: tk.PhotoImage | None = None
        self.scaled_image: tk.PhotoImage | None = None

        self._make_menu()
        self.canvas = tk.Canvas(self.root, width=WIDTH * SCALE, height=HEIGHT * SCALE,
                                bg="black", highlightthickness=0)
        self.canvas.pack(padx=10, pady=(10, 4))
        self.image_item = self.canvas.create_image(0, 0, anchor="nw")
        controls = tk.Frame(self.root, bg="#101827")
        controls.pack(fill="x", padx=10, pady=(0, 7))
        button_style = dict(bg="#05080f", fg="#5ec8ff", activebackground="#18263b",
                            activeforeground="white", relief="flat", padx=12, pady=4)
        tk.Button(controls, text="LOAD ROM", command=self.load, **button_style).pack(side="left")
        tk.Button(controls, text="RESET", command=self.reset, **button_style).pack(side="left", padx=6)
        tk.Button(controls, text="PAUSE", command=self.toggle_pause, **button_style).pack(side="left")
        self.mute_text = tk.StringVar(value="MUTE")
        tk.Button(controls, textvariable=self.mute_text, command=self.toggle_mute,
                  **button_style).pack(side="left", padx=6)
        self.status_var = tk.StringVar(value=f"Load a legal .nes ROM  •  {self.audio.backend}")
        tk.Label(self.root, textvariable=self.status_var, bg="#101827", fg="#7dd3fc",
                 anchor="w", font=("TkDefaultFont", 9)).pack(fill="x", padx=10, pady=(0, 9))

        self.root.bind_all("<KeyPress>", self.key_down)
        self.root.bind_all("<KeyRelease>", self.key_up)
        self.root.protocol("WM_DELETE_WINDOW", self.close)
        self._center_window(WINDOW_WIDTH, WINDOW_HEIGHT)
        self._draw_blank()
        self.root.after(1, self.loop)

    def _center_window(self, width: int, height: int) -> None:
        self.root.update_idletasks()
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()
        x = max(0, (sw - width) // 2)
        y = max(0, (sh - height) // 2)
        self.root.geometry(f"{width}x{height}+{x}+{y}")

    def _make_menu(self) -> None:
        menu = tk.Menu(self.root)
        file_menu = tk.Menu(menu, tearoff=False)
        file_menu.add_command(label="Open ROM…", accelerator="Ctrl+O", command=self.load)
        file_menu.add_command(label="Reset", accelerator="Ctrl+R", command=self.reset)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.close)
        menu.add_cascade(label="File", menu=file_menu)
        emu_menu = tk.Menu(menu, tearoff=False)
        emu_menu.add_command(label="Pause / Resume", accelerator="Space", command=self.toggle_pause)
        emu_menu.add_command(label="Mute / Unmute", accelerator="M", command=self.toggle_mute)
        menu.add_cascade(label="Emulation", menu=emu_menu)
        help_menu = tk.Menu(menu, tearoff=False)
        help_menu.add_command(label="Controls", command=self.show_controls)
        help_menu.add_command(label="About", command=self.show_about)
        menu.add_cascade(label="Help", menu=help_menu)
        self.root.config(menu=menu)
        self.root.bind("<Control-o>", lambda _e: self.load())
        self.root.bind("<Control-r>", lambda _e: self.reset())

    def _draw_blank(self) -> None:
        fb = bytearray(WIDTH * HEIGHT * 3)
        for y in range(HEIGHT):
            shade = 8 + y * 16 // HEIGHT
            fb[y * WIDTH * 3:(y + 1) * WIDTH * 3] = bytes((shade, shade + 5, shade + 12)) * WIDTH
        self._present(fb)

    def _present(self, framebuffer: bytearray) -> None:
        # Tk's native binary PPM loader is much faster than 61,440 Canvas items
        # and needs no Pillow/pygame installation.
        ppm = f"P6\n{WIDTH} {HEIGHT}\n255\n".encode("ascii") + bytes(framebuffer)
        self.image = tk.PhotoImage(data=ppm, format="PPM")
        self.scaled_image = self.image.zoom(SCALE, SCALE)
        self.canvas.itemconfigure(self.image_item, image=self.scaled_image)

    def load(self) -> None:
        path = filedialog.askopenfilename(title="Open NES/Famicom ROM",
                                          filetypes=(("NES ROM", "*.nes"), ("All files", "*.*")))
        if not path:
            return
        try:
            self.nes.load(path)
            self.audio.flush()
            mapper_name = Cartridge.SUPPORTED_MAPPERS[self.nes.cart.mapper]
            self.status_var.set(f"{self.nes.cart.name}  •  Mapper {self.nes.cart.mapper} {mapper_name}  •  {self.audio.backend}")
            self.root.title(f"ByChatGPT NES Emulator 0.8.0 — {self.nes.cart.name}")
            self.next_frame = time.perf_counter()
            self.root.focus_force()
        except (OSError, EmulatorError) as error:
            self.nes.running = False
            messagebox.showerror("Could not load ROM", str(error), parent=self.root)

    def reset(self) -> None:
        if not self.nes.cart.prg:
            return
        try:
            self.nes.reset()
            self.audio.flush()
            self.nes.running = True
            self.nes.paused = False
            self.status_var.set(f"{self.nes.cart.name}  •  Reset")
        except EmulatorError as error:
            messagebox.showerror("Reset failed", str(error), parent=self.root)

    def toggle_pause(self) -> None:
        if not self.nes.running:
            return
        self.nes.paused = not self.nes.paused
        self.audio.set_paused(self.nes.paused)
        state = "Paused" if self.nes.paused else "Running"
        self.status_var.set(f"{self.nes.cart.name}  •  {state}")
        self.next_frame = time.perf_counter()

    def toggle_mute(self) -> None:
        self.audio.set_muted(not self.audio.muted)
        self.mute_text.set("UNMUTE" if self.audio.muted else "MUTE")

    def _set_key(self, event: tk.Event, down: bool) -> None:
        keysym = event.keysym
        # Space pauses only when it is not mapped to a controller button.
        if down and keysym == "space":
            self.toggle_pause()
            return
        if down and keysym.lower() == "m":
            self.toggle_mute()
            return
        if keysym in self.KEYMAP_P1:
            self.nes.controllers[0].set_button(self.KEYMAP_P1[keysym], down)
        lower = keysym.lower()
        if lower in self.KEYMAP_P2:
            self.nes.controllers[1].set_button(self.KEYMAP_P2[lower], down)

    def key_down(self, event: tk.Event) -> None:
        if event.keysym in self.held_keys:
            return
        self.held_keys.add(event.keysym)
        self._set_key(event, True)

    def key_up(self, event: tk.Event) -> None:
        self.held_keys.discard(event.keysym)
        self._set_key(event, False)

    def show_controls(self) -> None:
        messagebox.showinfo("Controls", "Player 1\nArrows: D-pad\nZ: B\nX: A\nEnter: Start\nShift: Select\n\n"
                            "Player 2\nWASD: D-pad\nG: B\nH: A\nT: Start\nR: Select\n\nSpace: Pause",
                            parent=self.root)

    def show_about(self) -> None:
        messagebox.showinfo("About", "ByChatGPT NES Emulator 0.8.0\nSingle-file Python 3.14 build\n"
                            "60.0988 FPS NTSC timing\nFive-channel RP2A03 audio at 48 kHz\n"
                            "Mappers 0, 1, 2, 3, 4, 7, 66\n\n"
                            "Clean Python implementation; no ROMs included.", parent=self.root)

    def loop(self) -> None:
        now = time.perf_counter()
        if self.nes.running and not self.nes.paused and now >= self.next_frame:
            try:
                # Avoid a runaway catch-up spiral after moving/minimizing a window.
                frames = 0
                while now >= self.next_frame and frames < 2:
                    self.nes.run_frame()
                    self.audio.push(self.nes.apu.drain_samples())
                    self.next_frame += 1.0 / FPS
                    frames += 1
                if now - self.next_frame > 0.1:
                    self.next_frame = now
                self._present(self.nes.ppu.framebuffer)
            except EmulatorError as error:
                self.nes.paused = True
                if str(error) != self.last_error:
                    self.last_error = str(error)
                    messagebox.showerror("Emulation stopped", str(error), parent=self.root)
        self.root.after(1, self.loop)

    def close(self) -> None:
        self.nes.running = False
        self.audio.close()
        self.root.destroy()

    def run(self) -> None:
        self.root.mainloop()


def main() -> int:
    try:
        GUI().run()
    except tk.TclError as error:
        print(f"GUI error: {error}", file=sys.stderr)
        print("Install/enable Tk for your Python build, then run this file again.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
