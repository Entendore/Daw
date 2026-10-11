#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ScoreDAW — complete single-file edition
=======================================
A hybrid DAW + sheet-music editor in PySide6.

  Piano roll ... draw / move / resize / right-drag erase / Ctrl-drag clone /
                 rubber-band select / velocity lane (drag or ramp selection) /
                 snap grid / scale guide + scale-snap / loop-region ruler /
                 Ctrl+wheel zoom / ghost notes of other tracks / audition
  Score ........ live-engraved grand staff: clefs, key signature, bar numbers,
                 duration-aware spacing, auto whole rests, ties across
                 barlines, beat-grouped beams, key-aware accidentals with
                 measure memory, ledger lines, dots, flags, lyrics,
                 editable noteheads (drag pitch/time, edge resize,
                 double-click add, right-click delete), click-to-seek, zoom
  Tracks ....... per-track waveform, volume, pan, mute, solo, color
  Engine ....... stereo soft-synth (sine/tri/square/saw), ADSR-style
                 envelopes, metronome, sample-accurate playhead,
                 cycle/loop playback, offline WAV render
  Extras ....... undo/redo, JSON projects, MIDI import/export (mido),
                 MusicXML export, articulations (staccato/accent),
                 keyboard shortcuts, dark theme

Run:
    pip install PySide6 mido      # mido optional (MIDI I/O)
    python scoredaw_complete.py

Shortcuts:
    Space play/pause · Home rewind · ←/→ nudge playhead
    Roll: left-drag draw · drag right edge resize · right-drag erase ·
          Ctrl-drag clone or rubber-select · Shift-click add to selection ·
          double-click select same pitch · Del delete · Ctrl+D duplicate ·
          Ctrl+C/V copy/paste · Ctrl+Q quantize · arrows nudge selection
    Score: drag notehead · double-click add · right-click delete ·
           click = seek · Ctrl+wheel zoom
"""

import sys
import math
import json
import array

from PySide6.QtCore import Qt, QTimer, QRectF, QPointF, QLineF
from PySide6.QtGui import (QPainter, QColor, QPen, QFont, QPalette, QPainterPath,
                           QPolygonF, QRawFont, QIcon, QPixmap)
from PySide6.QtWidgets import (QApplication, QMainWindow, QWidget, QSplitter,
                               QScrollArea, QToolBar, QToolButton, QLabel,
                               QLineEdit, QComboBox, QSlider, QSpinBox,
                               QListWidget, QListWidgetItem, QVBoxLayout,
                               QHBoxLayout, QColorDialog, QSizePolicy, QStyle,
                               QFileDialog, QMessageBox, QInputDialog)

try:
    from PySide6.QtMultimedia import QAudioFormat, QAudioSink, QMediaDevices
    HAS_MEDIA = True
except Exception:
    HAS_MEDIA = False

# ============================================================================
# constants & music theory helpers
# ============================================================================
SR = 44100
PITCH_MIN, PITCH_MAX = 21, 108
ROW_H = 14
KEYB_W = 72
BLACK = {1, 3, 6, 8, 10}
PALETTE = ["#53b9ff", "#ff9f43", "#7ee787", "#e0559b",
           "#c8b3ff", "#ffd66e", "#6ee7dc", "#f26d6d"]

_NAT = (0, 2, 4, 5, 7, 9, 11)
_LET = "CDEFGAB"
_STEPS = (0, 0, 1, 1, 2, 3, 3, 4, 4, 5, 5, 6)
SHARP_T = (("F", 5), ("C", 5), ("G", 5), ("D", 5), ("A", 4), ("E", 5), ("B", 4))
FLAT_T = (("B", 4), ("E", 5), ("A", 4), ("D", 5), ("G", 4), ("C", 5), ("F", 4))
SHARP_B = (("F", 3), ("C", 3), ("G", 3), ("D", 3), ("A", 2), ("E", 3), ("B", 2))
FLAT_B = (("B", 2), ("E", 3), ("A", 2), ("D", 3), ("G", 2), ("C", 3), ("F", 3))

KEY_TABLE = [("C major", 0, "major"), ("G major", 1, "major"),
             ("D major", 2, "major"), ("A major", 3, "major"),
             ("E major", 4, "major"), ("B major", 5, "major"),
             ("F♯ major", 6, "major"), ("F major", -1, "major"),
             ("B♭ major", -2, "major"), ("E♭ major", -3, "major"),
             ("A♭ major", -4, "major"), ("D♭ major", -5, "major"),
             ("G♭ major", -6, "major"), ("A minor", 0, "minor"),
             ("E minor", 1, "minor"), ("B minor", 2, "minor"),
             ("F♯ minor", 3, "minor"), ("C♯ minor", 4, "minor"),
             ("G♯ minor", 5, "minor"), ("D minor", -1, "minor"),
             ("G minor", -2, "minor"), ("C minor", -3, "minor"),
             ("F minor", -4, "minor"), ("B♭ minor", -5, "minor"),
             ("E♭ minor", -6, "minor")]


def spell(pitch, fifths):
    """MIDI pitch -> (letter, alter, octave), sharp/flat by key flavour."""
    pc, o = pitch % 12, pitch // 12 - 1
    if pc in _NAT:
        return _LET[_NAT.index(pc)], 0, o
    if fifths >= 0:
        return {1: ("C", 1), 3: ("D", 1), 6: ("F", 1),
                8: ("G", 1), 10: ("A", 1)}[pc] + (o,)
    return {1: ("D", -1), 3: ("E", -1), 6: ("G", -1),
            8: ("A", -1), 10: ("B", -1)}[pc] + (o,)


def key_alters(fifths):
    d = {}
    order = "FCGDAEB" if fifths >= 0 else "BEADGCF"
    a = 1 if fifths >= 0 else -1
    for i in range(min(abs(fifths), 7)):
        d[order[i]] = a
    return d


def di_step(pitch):
    """Diatonic staff step, C0 = 0."""
    return (pitch // 12 - 1) * 7 + _STEPS[pitch % 12]


def step_to_pitch(step, fifths):
    ka = key_alters(fifths)
    li, o = step % 7, step // 7 - 1
    return _NAT[li] + ka.get(_LET[li], 0) + 12 * (o + 1)


def scale_pcs(fifths, mode):
    tonic = (7 * fifths) % 12
    if mode == "minor":
        tonic = (tonic + 9) % 12
    iv = (0, 2, 3, 5, 7, 8, 10) if mode == "minor" else (0, 2, 4, 5, 7, 9, 11)
    return {(tonic + i) % 12 for i in iv}


def dur_type(d):
    table = ((4.0, "whole"), (3.0, "half_dot"), (2.0, "half"),
             (1.5, "quarter_dot"), (1.0, "quarter"), (0.75, "eighth_dot"),
             (0.5, "eighth"), (0.25, "sixteenth"))
    return min(table, key=lambda t: abs(t[0] - d))[1]


# ============================================================================
# data model
# ============================================================================
class Note:
    __slots__ = ("pitch", "start", "dur", "vel", "artic", "lyric")

    def __init__(self, pitch, start, dur, vel=100, artic="", lyric=""):
        self.pitch, self.start, self.dur = int(pitch), float(start), float(dur)
        self.vel, self.artic, self.lyric = int(vel), artic, lyric

    @property
    def end(self):
        return self.start + self.dur


class Track:
    def __init__(self, name, color, wave="sine", volume=0.75, pan=0.0,
                 muted=False, solo=False, notes=None):
        self.name, self.color, self.wave = name, QColor(color), wave
        self.volume, self.pan = float(volume), float(pan)
        self.muted, self.solo = bool(muted), bool(solo)
        self.notes = notes if notes is not None else []


class Project:
    def __init__(self):
        self.bpm = 110.0
        self.beats_per_bar = 4
        self.bars = 8
        self.key_sharps = 0
        self.mode = "major"
        self.loop_region = None                 # (start_beat, end_beat) | None
        self.tracks = []
        self.selected = 0
        self._undo, self._redo = [], []

    # ---- basics -------------------------------------------------------------
    @property
    def total_beats(self):
        return self.bars * self.beats_per_bar

    def region(self):
        if self.loop_region:
            ls, le = self.loop_region
            if le - ls >= 1.0:
                return (float(ls), float(le))
        return None

    def sel(self):
        if 0 <= self.selected < len(self.tracks):
            return self.tracks[self.selected]
        return None

    def changed(self):
        pass                                    # views connect to update()

    # ---- serialization (doubles as the undo snapshot format) ----------------
    def to_dict(self):
        return {"bpm": self.bpm, "bpb": self.beats_per_bar, "bars": self.bars,
                "key": self.key_sharps, "mode": self.mode,
                "loop": list(self.loop_region) if self.loop_region else None,
                "tracks": [{"name": t.name, "color": t.color.name(),
                            "wave": t.wave, "volume": t.volume, "pan": t.pan,
                            "muted": t.muted, "solo": t.solo,
                            "notes": [[n.pitch, round(n.start, 4),
                                       round(n.dur, 4), n.vel, n.artic,
                                       n.lyric] for n in t.notes]}
                           for t in self.tracks]}

    def from_dict(self, d):
        self.bpm = float(d.get("bpm", 110))
        self.beats_per_bar = int(d.get("bpb", 4))
        self.bars = max(1, min(64, int(d.get("bars", 8))))
        self.key_sharps = int(d.get("key", 0))
        self.mode = d.get("mode", "major")
        lp = d.get("loop")
        self.loop_region = tuple(lp) if lp else None
        self.tracks = []
        for t in d.get("tracks", []):
            ns = [Note(*x[:4], x[4] if len(x) > 4 else "",
                       x[5] if len(x) > 5 else "") for x in t.get("notes", [])]
            self.tracks.append(Track(t["name"], t["color"], t.get("wave", "sine"),
                                     t.get("volume", 0.75), t.get("pan", 0.0),
                                     t.get("muted", False), t.get("solo", False),
                                     ns))
        if not self.tracks:
            self.tracks.append(Track("Track 1", PALETTE[0]))
        self.selected = 0

    # ---- undo / redo ----------------------------------------------------------
    def push_undo(self):
        self._undo.append(json.dumps(self.to_dict()))
        if len(self._undo) > 100:
            self._undo.pop(0)
        self._redo.clear()

    def undo(self):
        if not self._undo:
            return False
        self._redo.append(json.dumps(self.to_dict()))
        self.from_dict(json.loads(self._undo.pop()))
        return True

    def redo(self):
        if not self._redo:
            return False
        self._undo.append(json.dumps(self.to_dict()))
        self.from_dict(json.loads(self._redo.pop()))
        return True


def build_demo(p):
    lead = Track("Lead", PALETTE[0], "sine", 0.80, -0.25)
    bass = Track("Bass", PALETTE[1], "saw", 0.50, 0.0)
    keys = Track("Keys", PALETTE[2], "triangle", 0.45, 0.3)

    mel = [(0, 1, 72), (1, 1, 76), (2, 1, 79), (3, 1, 76),
           (4, 1, 77), (5, 1, 81), (6, 2, 79),
           (8, 1, 76), (9, 1, 79), (10, 1, 84), (11, 1, 83),
           (12, 2, 81), (14, 2, 79),
           (16, 1, 72), (17, 1, 76), (18, 1, 79), (19, 1, 76),
           (20, 1, 77), (21, 1, 81), (22, 2, 84),
           (24, 1, 83), (25, 1, 81), (26, 1, 79), (27, 1, 76),
           (28, 4, 72)]
    bs = [(0, 2, 48), (2, 2, 43), (4, 2, 45), (6, 2, 41),
          (8, 2, 48), (10, 2, 40), (12, 2, 41), (14, 2, 43),
          (16, 2, 48), (18, 2, 43), (20, 2, 45), (22, 2, 41),
          (24, 2, 48), (26, 2, 52), (28, 4, 48)]
    ch = [(0, (60, 64, 67)), (4, (60, 65, 69)), (8, (57, 60, 64)),
          (12, (59, 62, 67)), (16, (60, 64, 67)), (20, (60, 65, 69)),
          (24, (57, 60, 64)), (28, (55, 59, 62))]

    for s, d, pi in mel:
        lead.notes.append(Note(pi, s, d))
    for s, d, pi in bs:
        bass.notes.append(Note(pi, s, d, 90))
    for s, tri in ch:
        for pi in tri:
            keys.notes.append(Note(pi, s, 3.75, 80))

    for syl, n in zip("Score DAW sings now for you and me".split(),
                      sorted(lead.notes, key=lambda n: n.start)[:8]):
        n.lyric = syl

    p.tracks = [lead, bass, keys]
    p.selected = 0
    p.bars = 8


# ============================================================================
# audio engine
# ============================================================================
class Engine:
    def __init__(self, project):
        self.project = project
        self.master = 0.9
        self.loop = True
        self.metro = False
        self.playing = False
        self.pos_beats = 0.0
        self.play_from = 0.0
        self.gen_t = 0.0
        self.t0_us = 0
        self.previews = []
        self.audio_ok = False
        self.sink = None
        self.io = None
        if HAS_MEDIA:
            try:
                dev = QMediaDevices.defaultAudioOutput()
                fmt = QAudioFormat()
                fmt.setSampleRate(SR)
                fmt.setChannelCount(2)
                fmt.setSampleFormat(QAudioFormat.SampleFormat.Int16)
                self.sink = QAudioSink(dev, fmt)
                self.sink.setBufferSize(16384)
                self.io = self.sink.start()
                self.audio_ok = (not dev.isNull()) and self.io is not None
            except Exception:
                self.audio_ok = False
        self.timer = QTimer()
        self.timer.setInterval(25)
        self.timer.timeout.connect(self._tick)
        self.timer.start()

    # ---- transport ----------------------------------------------------------
    def play(self):
        if self.playing or not self.audio_ok:
            return
        self.sink.stop()
        self.io = self.sink.start()
        self.t0_us = self.sink.processedUSecs()
        pf = self.pos_beats
        reg = self.project.region()
        if reg:
            pf = min(max(pf, reg[0]), reg[1] - 1e-4)
        self.play_from = pf
        self.gen_t = 0.0
        self.playing = True

    def pause(self):
        if self.playing:
            self.pos_beats = self.playhead_beats()
            self.playing = False

    def stop(self):
        self.playing = False
        reg = self.project.region()
        self.pos_beats = reg[0] if (reg and self.loop) else 0.0

    def set_position(self, beats):
        self.pos_beats = max(0.0, float(beats))
        if self.playing:
            self.playing = False
            self.play()

    def playhead_beats(self):
        if not self.playing:
            return self.pos_beats
        secs = (self.sink.processedUSecs() - self.t0_us) / 1e6
        b = self.play_from + secs * self.project.bpm / 60.0
        reg = self.project.region()
        if reg:
            ls, le = reg
            return ls + (b - ls) % (le - ls)
        total = self.project.total_beats
        return b % total if self.loop else min(b, total)

    def preview(self, pitch, wave, vol=0.8):
        if self.audio_ok:
            self.previews.append((self.gen_t, 0.30, int(pitch), wave, vol))

    def _active(self, tr):
        if tr.muted:
            return False
        if any(t.solo for t in self.project.tracks):
            return tr.solo
        return True

    # ---- rendering ------------------------------------------------------------
    def _tick(self):
        if not self.audio_ok or self.io is None:
            return
        free = self.sink.bytesFree()
        if free < 4096:
            return
        n = min(free // 4, SR // 5)
        buf = self.render_block(self.gen_t, n)
        self.io.write(buf.tobytes())
        self.gen_t += n / SR

    def render_block(self, t0, n, with_previews=True):
        L, R = [0.0] * n, [0.0] * n
        dt = 1.0 / SR
        proj = self.project
        if self.playing:
            bpms = proj.bpm / 60.0
            spb = 1.0 / bpms
            B0 = self.play_from + t0 * bpms
            B1 = B0 + n * dt * bpms
            reg = proj.region()
            if reg:
                ls, le = reg
                Lb = le - ls
            elif self.loop:
                ls, Lb = 0.0, float(proj.total_beats)
            else:
                ls, Lb = 0.0, None

            for tr in proj.tracks:
                if not self._active(tr):
                    continue
                buf = [0.0] * n
                for note in tr.notes:
                    d, amp = note.dur, note.vel / 127.0
                    if note.artic == "staccato":
                        d = min(d, max(0.14, d * 0.5))
                    elif note.artic == "accent":
                        amp *= 1.45
                    if amp <= 0 or d <= 1e-9:
                        continue
                    if reg:
                        d = min(d, max(0.05, le - note.start))
                        if note.start >= le:
                            continue
                    f = 440.0 * 2.0 ** ((note.pitch - 69) / 12.0)
                    if Lb:
                        k0 = int(math.floor((B0 - note.start - d) / Lb))
                        k1 = int(math.ceil((B1 - note.start) / Lb))
                    else:
                        if not (note.start < B1 and note.start + d > B0):
                            continue
                        k0 = k1 = 0
                    for k in range(k0, k1 + 1):
                        os_ = note.start + (k * Lb if Lb else 0.0)
                        oe = os_ + d
                        if oe <= B0 or os_ >= B1:
                            continue
                        gs = t0 + (os_ - B0) * spb
                        self._tone(buf, max(gs, t0), min(gs + d * spb, t1),
                                   gs, gs + d * spb, t0, dt, f, tr.wave, amp)
                ang = (max(-1.0, min(1.0, tr.pan)) + 1) * math.pi / 4
                gl, gr = math.cos(ang), math.sin(ang)
                for i in range(n):
                    v = buf[i] * tr.volume
                    L[i] += v * gl
                    R[i] += v * gr

            if self.metro:
                anchor = ls
                nb = int(le - ls) if reg else int(proj.total_beats)
                k0 = 0 if Lb is None else int(math.floor((B0 - anchor) / Lb) - 1)
                k1 = 0 if Lb is None else int(math.ceil((B1 - anchor) / Lb) + 1)
                for k in range(k0, k1 + 1):
                    for b in range(nb):
                        tb = anchor + b + (k * Lb if Lb else 0.0)
                        if tb < B0 or tb >= B1:
                            continue
                        self._click(L, R, n, t0 + (tb - B0) * spb,
                                    (tb - anchor) % proj.beats_per_bar == 0)

        if with_previews:
            for pv in self.previews[:]:
                ps, pd, pitch, wav, amp = pv
                if ps + pd < t0 - 0.05:
                    self.previews.remove(pv)
                    continue
                if ps < t0 + n / SR and ps + pd > t0:
                    f = 440.0 * 2.0 ** ((pitch - 69) / 12.0)
                    self._tone(L, max(ps, t0), min(ps + pd, t0 + n / SR),
                               ps, ps + pd, t0, dt, f, wav, amp)
                    self._tone(R, max(ps, t0), min(ps + pd, t0 + n / SR),
                               ps, ps + pd, t0, dt, f, wav, amp)

        m = self.master
        out = array.array("h", bytes(4 * n))
        for i in range(n):
            l, r = L[i] * m, R[i] * m
            out[2 * i] = int(math.tanh(l) * 31000.0)
            out[2 * i + 1] = int(math.tanh(r) * 31000.0)
        return out

    @staticmethod
    def _click(L, R, n, t, hi):
        i0 = int(t * SR)
        for j in range(200):
            i = i0 + j
            if 0 <= i < n:
                tt = j / SR
                v = math.sin(6.2832 * (2300 if hi else 1500) * tt) \
                    * 0.5 * math.exp(-tt * 180)
                L[i] += v
                R[i] += v

    @staticmethod
    def _tone(out, s, e, a, b, t0, dt, f, wave, amp):
        i0 = max(0, int((s - t0) / dt))
        i1 = min(len(out), int((e - t0) / dt) + 1)
        atk, rel, two = 0.006, 0.05, 6.283185307179586
        for i in range(i0, i1):
            t = t0 + i * dt
            env = amp
            tt = t - a
            if tt < atk:
                env *= tt / atk
            rem = b - t
            if rem < rel:
                env *= max(0.0, rem) / rel
            if env <= 0:
                continue
            fr = (f * t) % 1.0
            if wave == "sine":
                v = (math.sin(two * f * t) + 0.3 * math.sin(2 * two * f * t)) * 0.72
            elif wave == "square":
                v = 0.66 if fr < 0.5 else -0.66
            elif wave == "saw":
                v = (2.0 * fr - 1.0) * 0.8
            else:
                v = 4.0 * abs(fr - 0.5) - 1.0
            out[i] += v * env

    # ---- offline render (WAV export) ------------------------------------------
    def render_offline(self, path):
        import wave as wavmod
        was = (self.playing, self.loop)
        self.playing = False
        self.loop = False
        self.play_from = 0.0
        total = self.project.total_beats * 60.0 / self.project.bpm + 1.0
        wf = wavmod.open(path, "wb")
        wf.setnchannels(2)
        wf.setsampwidth(2)
        wf.setframerate(SR)
        try:
            self.playing = True
            n, t = 8192, 0.0
            while t < total:
                wf.writeframes(self.render_block(t, n, False).tobytes())
                t += n / SR
        finally:
            self.playing = False
            self.loop = was[1]
            if was[0]:
                self.play()
        wf.close()


# ============================================================================
# piano roll
# ============================================================================
class PianoRoll(QWidget):
    RULER_H, VEL_H = 22, 64

    def __init__(self, proj, engine):
        super().__init__()
        self.proj, self.engine = proj, engine
        self.beat_w = 84.0
        self.snap = 0.25
        self.default_dur = 1.0
        self.scale_guide = True
        self.snap_to_scale = False
        self.selection = set()
        self.cur_artic = ""
        self._mode = None
        self._note = None
        self._off_b = _off_p = 0.0
        self._last_prev = None
        self._rubber = None
        self._rubber_add = False
        self._erase_pushed = False
        self._r_x0 = self._r_anchor = 0.0
        self._r_pushed = False
        self._vel_list = None
        self.hover_pitch = None
        self.setMouseTracking(True)

    # ---- geometry -----------------------------------------------------------
    def rows_h(self):
        return (PITCH_MAX - PITCH_MIN + 1) * ROW_H

    def lane_top(self):
        return self.RULER_H + self.rows_h()

    def resize_to_project(self):
        self.setFixedSize(int(KEYB_W + self.proj.total_beats * self.beat_w + 80),
                          self.lane_top() + self.VEL_H)
        self.update()

    def _pitch_at(self, y):
        rel = y - self.RULER_H
        if 0 <= rel < self.rows_h():
            return PITCH_MAX - int(rel // ROW_H)
        return None

    def _beat_at(self, x):
        return (x - KEYB_W) / self.beat_w

    def _snapv(self, v):
        return round(v / self.snap) * self.snap if self.snap > 0 else v

    def _hit(self, x, y):
        tr = self.proj.sel()
        if not tr:
            return None
        b, p = self._beat_at(x), self._pitch_at(y)
        for n in reversed(tr.notes):
            if n.pitch == p and n.start <= b <= n.end:
                return n
        return None

    def _nearest_scale(self, pitch):
        pcs = scale_pcs(self.proj.key_sharps, self.proj.mode)
        if pitch % 12 in pcs:
            return pitch
        for d in (1, 2):
            if (pitch - d) % 12 in pcs:
                return pitch - d
            if (pitch + d) % 12 in pcs:
                return pitch + d
        return pitch

    def _scroll_area(self):
        w = self.parent()
        while w is not None and not isinstance(w, QScrollArea):
            w = w.parent()
        return w

    def zoom_by(self, factor, anchor_x=None):
        old = self.beat_w
        self.beat_w = max(28.0, min(240.0, self.beat_w * factor))
        if abs(self.beat_w - old) < 1e-6:
            return
        beat = max(0.0, (anchor_x or 0.0) - KEYB_W) / old
        self.resize_to_project()
        sa = self._scroll_area()
        if sa and anchor_x is not None:
            sa.horizontalScrollBar().setValue(
                int(KEYB_W + beat * self.beat_w - anchor_x))

    def wheelEvent(self, e):
        if e.modifiers() & Qt.KeyboardModifier.ControlModifier:
            self.zoom_by(1.15 if e.angleDelta().y() > 0 else 1 / 1.15,
                         e.position().x())
            e.accept()
            return
        super().wheelEvent(e)

    # ---- painting -------------------------------------------------------------
    def paintEvent(self, _):
        p = QPainter(self)
        W, H = self.width(), self.height()
        bw, proj = self.beat_w, self.proj
        rt, lt = self.RULER_H, self.lane_top()
        bpb, bars = proj.beats_per_bar, proj.bars
        p.fillRect(0, 0, W, H, QColor("#232529"))

        pcs = scale_pcs(proj.key_sharps, proj.mode)
        for pitch in range(PITCH_MIN, PITCH_MAX + 1):
            y = rt + (PITCH_MAX - pitch) * ROW_H
            p.fillRect(KEYB_W, y, W - KEYB_W, ROW_H,
                       QColor("#2b2e35") if (pitch % 12) in BLACK
                       else QColor("#30333b"))
            if self.scale_guide and (pitch % 12) in pcs:
                p.fillRect(KEYB_W, y, W - KEYB_W, ROW_H, QColor(96, 150, 255, 30))
            if pitch == self.hover_pitch:
                p.fillRect(KEYB_W, y, W - KEYB_W, ROW_H, QColor(255, 255, 255, 16))

        for bar in range(bars):
            if bar % 2 == 1:
                p.fillRect(int(KEYB_W + bar * bpb * bw), rt, int(bpb * bw),
                           self.rows_h(), QColor(255, 255, 255, 7))
        for b in range(int(proj.total_beats) + 1):
            x = int(KEYB_W + b * bw)
            p.setPen(QPen(QColor("#4a4e58") if b % bpb == 0
                          else QColor("#3a3d45"), 1))
            p.drawLine(x, rt, x, lt)

        reg = proj.region()
        if reg and self.engine.loop:
            x1, x2 = KEYB_W + reg[0] * bw, KEYB_W + reg[1] * bw
            p.fillRect(QRectF(x1, rt, x2 - x1, self.rows_h()),
                       QColor(232, 184, 75, 24))
            p.setPen(QPen(QColor("#e8b84b"), 1))
            p.drawLine(int(x1), rt, int(x1), lt)
            p.drawLine(int(x2), rt, int(x2), lt)

        for i, tr in enumerate(proj.tracks):                 # ghost notes
            if i == proj.selected:
                continue
            c = QColor(tr.color)
            c.setAlpha(60)
            for n in tr.notes:
                p.fillRect(QRectF(KEYB_W + n.start * bw,
                                  rt + (PITCH_MAX - n.pitch) * ROW_H + 2,
                                  max(5.0, n.dur * bw - 2), ROW_H - 4), c)

        tr = proj.sel()
        ph = self.engine.playhead_beats()
        if tr:
            for n in tr.notes:
                y = rt + (PITCH_MAX - n.pitch) * ROW_H
                r = QRectF(KEYB_W + n.start * bw + 1, y + 2,
                           max(6.0, n.dur * bw - 2), ROW_H - 4)
                col = QColor(tr.color)
                if self.engine.playing and n.start <= ph < n.end:
                    col = col.lighter(155)
                p.setPen(QPen(QColor("#15161a"), 1))
                p.setBrush(col)
                p.drawRoundedRect(r, 3, 3)
                if n.artic:
                    p.setPen(Qt.PenStyle.NoPen)
                    p.setBrush(QColor(0, 0, 0, 170))
                    gx = r.right() - 5
                    if n.artic == "staccato":
                        p.drawEllipse(QPointF(gx, r.top() + 3.5), 1.6, 1.6)
                    else:
                        p.drawPolygon(QPolygonF([QPointF(gx - 2.6, r.top() + 2),
                                                 QPointF(gx + 1.4, r.top() + 2),
                                                 QPointF(gx - 0.6, r.top() + 6)]))
        if tr and self.selection:
            p.setPen(QPen(QColor("#ffffff"), 1))
            p.setBrush(Qt.BrushStyle.NoBrush)
            for n in self.selection:
                p.drawRect(QRectF(KEYB_W + n.start * bw,
                                  rt + (PITCH_MAX - n.pitch) * ROW_H + 1,
                                  max(6.0, n.dur * bw) - 1, ROW_H - 2))
        if self._rubber:
            x0, y0, x1, y1 = self._rubber
            p.setPen(QPen(QColor("#7ee787"), 1, Qt.PenStyle.DashLine))
            p.setBrush(QColor(126, 231, 135, 28))
            p.drawRect(QRectF(QPointF(x0, y0), QPointF(x1, y1)).normalized())

        xph = int(KEYB_W + ph * bw)
        p.setPen(QPen(QColor("#ff5566"), 2))
        p.drawLine(xph, rt, xph, lt)

        # ---- ruler -----------------------------------------------------------
        p.fillRect(0, 0, W, self.RULER_H, QColor("#1b1c20"))
        p.setPen(QPen(QColor("#111114"), 1))
        p.drawLine(0, self.RULER_H - 1, W, self.RULER_H - 1)
        if reg and self.engine.loop:
            x1, x2 = KEYB_W + reg[0] * bw, KEYB_W + reg[1] * bw
            p.fillRect(QRectF(x1, 0, x2 - x1, self.RULER_H),
                       QColor(232, 184, 75, 60))
            p.setPen(QPen(QColor("#e8b84b"), 2))
            p.drawLine(int(x1), 0, int(x1), self.RULER_H)
            p.drawLine(int(x2), 0, int(x2), self.RULER_H)
        f = QFont(self.font())
        f.setPointSize(7)
        for b in range(int(proj.total_beats) + 1):
            x = int(KEYB_W + b * bw)
            if b % bpb == 0:
                p.setPen(QPen(QColor("#8a90a0"), 1))
                p.drawLine(x, 8, x, self.RULER_H - 1)
                p.setFont(f)
                p.setPen(QColor("#c9cdd6"))
                p.drawText(QPointF(x + 3, 9), str(b // bpb + 1))
            else:
                p.setPen(QPen(QColor("#4a4e58"), 1))
                p.drawLine(x, self.RULER_H - 5, x, self.RULER_H - 1)
        p.setPen(QPen(QColor("#ff5566"), 2))
        p.drawLine(xph, 0, xph, 6)
        p.setBrush(QColor("#ff5566"))
        p.setPen(Qt.PenStyle.NoPen)
        p.drawPolygon(QPolygonF([QPointF(xph - 5, 0), QPointF(xph + 5, 0),
                                 QPointF(xph, 7)]))

        # ---- keyboard gutter ---------------------------------------------------
        for pitch in range(PITCH_MIN, PITCH_MAX + 1):
            y = rt + (PITCH_MAX - pitch) * ROW_H
            if pitch == self.hover_pitch:
                p.fillRect(0, y, KEYB_W, ROW_H, QColor("#f4f1e8"))
            elif (pitch % 12) in BLACK:
                p.fillRect(0, y, int(KEYB_W * 0.62), ROW_H, QColor("#141518"))
            else:
                p.fillRect(0, y, KEYB_W, ROW_H, QColor("#e6e3dc"))
                p.setPen(QPen(QColor("#b9b6ae"), 1))
                p.drawLine(0, y, KEYB_W, y)
            if pitch % 12 == 0 or pitch == self.hover_pitch:
                f2 = QFont(self.font())
                f2.setPointSize(7)
                f2.setBold(pitch == self.hover_pitch)
                p.setFont(f2)
                if pitch == self.hover_pitch:
                    letter, alter, oc = spell(pitch, proj.key_sharps)
                    txt = "%s%s%d" % (letter,
                                      "♯" if alter == 1
                                      else "♭" if alter == -1 else "", oc)
                else:
                    txt = "C%d" % (pitch // 12 - 1)
                p.setPen(QColor("#222222" if pitch == self.hover_pitch
                                else "#555555"))
                p.drawText(QRectF(2, y, KEYB_W - 8, ROW_H),
                           Qt.AlignmentFlag.AlignVCenter
                           | Qt.AlignmentFlag.AlignLeft, txt)
        p.setPen(QPen(QColor("#111111"), 1))
        p.drawLine(KEYB_W, rt, KEYB_W, lt)

        # ---- velocity lane ------------------------------------------------------
        p.fillRect(0, lt, W, self.VEL_H, QColor("#17181c"))
        p.setPen(QPen(QColor("#111114"), 1))
        p.drawLine(0, lt, W, lt)
        f3 = QFont(self.font())
        f3.setPointSize(7)
        p.setFont(f3)
        p.setPen(QColor("#6f7480"))
        p.drawText(QPointF(6, lt + 14), "VEL")
        mid = lt + self.VEL_H / 2
        p.setPen(QPen(QColor("#2c2f36"), 1, Qt.PenStyle.DashLine))
        p.drawLine(KEYB_W, int(mid), W, int(mid))
        if tr:
            for n in sorted(tr.notes, key=lambda n: n.start):
                x = KEYB_W + n.start * bw
                h = (n.vel / 127.0) * (self.VEL_H - 10)
                p.fillRect(QRectF(x - 1.5, lt + self.VEL_H - 4 - h, 3, h),
                           QColor(tr.color))
            if self.selection:
                p.setPen(QPen(QColor("#ffffff"), 1))
                p.setBrush(Qt.BrushStyle.NoBrush)
                for n in self.selection:
                    h = (n.vel / 127.0) * (self.VEL_H - 10)
                    p.drawRect(QRectF(KEYB_W + n.start * bw - 3,
                                      lt + self.VEL_H - 4 - h - 1, 6, h + 2))

    # ---- velocity lane helper -------------------------------------------------
    def _lane_apply(self, y):
        lt = self.lane_top()
        v = max(1, min(127, int((lt + self.VEL_H - 4 - y)
                                / (self.VEL_H - 10) * 127)))
        if self._vel_list:
            rs = self._vel_list
            if len(rs) == 1:
                rs[0].vel = v
            else:
                v0 = rs[0].vel
                for i, n in enumerate(rs):
                    n.vel = max(1, min(127, int(v0 + (v - v0) * i / (len(rs) - 1))))
        else:
            tr = self.proj.sel()
            if tr:
                best, bd = None, 7.0
                for n in tr.notes:
                    d = abs(KEYB_W + n.start * self.beat_w - self._vx)
                    if d < bd:
                        best, bd = n, d
                if best:
                    best.vel = v

    # ---- mouse ------------------------------------------------------------------
    def mousePressEvent(self, e):
        x, y = e.position().x(), e.position().y()
        lt = self.lane_top()
        tr = self.proj.sel()
        mods = e.modifiers()

        if y < self.RULER_H:                                  # ruler
            if e.button() == Qt.MouseButton.LeftButton:
                self._r_x0, self._r_pushed = x, False
                self._mode = "ruler"
            elif e.button() == Qt.MouseButton.RightButton and self.proj.loop_region:
                self.proj.push_undo()
                self.proj.loop_region = None
                self.update()
            return

        if y >= lt:                                           # velocity lane
            if e.button() != Qt.MouseButton.LeftButton or not tr:
                return
            self._vx = x
            self.proj.push_undo()
            if self.selection:
                self._vel_list = sorted(self.selection,
                                        key=lambda n: (n.start, n.pitch))
            else:
                self._vel_list = None
            self._mode = "vel"
            self._lane_apply(y)
            self.update()
            return

        if x < KEYB_W:                                        # keyboard audition
            pk = self._pitch_at(y)
            if pk and tr:
                self.engine.preview(pk, tr.wave, tr.volume)
            return

        if e.button() == Qt.MouseButton.RightButton:          # eraser sweep
            n = self._hit(x, y)
            self._erase_pushed = False
            if n:
                self.proj.push_undo()
                self._erase_pushed = True
                tr.notes.remove(n)
                self.selection.discard(n)
                self.update()
            self._mode = "erase"
            return

        if e.button() != Qt.MouseButton.LeftButton:
            return

        n = self._hit(x, y)
        if mods & Qt.KeyboardModifier.ControlModifier and n is not None:
            group = sorted(self.selection, key=lambda m: m.start) \
                if n in self.selection and len(self.selection) > 1 else [n]
            self.proj.push_undo()
            clones = []
            for m in group:
                c = Note(m.pitch, m.start, m.dur, m.vel, m.artic, m.lyric)
                tr.notes.append(c)
                clones.append(c)
            ref = clones[group.index(n)]
            self.selection = set(clones)
            self._note, self._mode = ref, "move"
            self._off_b = ref.start - self._beat_at(x)
            self._off_p = ref.pitch - self._pitch_at(y)
            self.engine.preview(ref.pitch, tr.wave, tr.volume)
            self.update()
            return

        if mods & Qt.KeyboardModifier.ControlModifier and n is None:
            self._rubber = [x, y, x, y]
            self._rubber_add = bool(mods & Qt.KeyboardModifier.ShiftModifier)
            self._mode = "rubber"
            return

        if mods & Qt.KeyboardModifier.ShiftModifier and n is not None:
            self.selection.symmetric_difference_update({n})
            self.engine.preview(n.pitch, tr.wave, tr.volume)
            self.update()
            return

        if n is not None:
            if n not in self.selection:
                self.selection = {n}
            self.proj.push_undo()
            self._note = n
            edge = KEYB_W + (n.start + n.dur) * self.beat_w
            if x > edge - 8:
                self._mode = "resize"
            else:
                self._mode = "move"
                self._off_b = n.start - self._beat_at(x)
                self._off_p = n.pitch - self._pitch_at(y)
            self.engine.preview(n.pitch, tr.wave, tr.volume)
            self.update()
            return

        b = self._snapv(self._beat_at(x))                     # create
        if b < 0 or b >= self.proj.total_beats:
            return
        pitch = self._pitch_at(y)
        if self.snap_to_scale:
            pitch = self._nearest_scale(pitch)
        self.proj.push_undo()
        n = Note(pitch, b, self.default_dur, 100, self.cur_artic)
        tr.notes.append(n)
        self.selection = {n}
        self._note, self._mode = n, "resize"
        self.engine.preview(pitch, tr.wave, tr.volume)
        self.update()

    def mouseMoveEvent(self, e):
        x, y = e.position().x(), e.position().y()
        mode = self._mode

        if mode == "rubber":
            self._rubber[2], self._rubber[3] = x, y
            self.update()
            return
        if mode == "erase":
            tr = self.proj.sel()
            n = self._hit(x, y) if tr else None
            if n:
                if not self._erase_pushed:
                    self.proj.push_undo()
                    self._erase_pushed = True
                tr.notes.remove(n)
                self.selection.discard(n)
                self.update()
            return
        if mode == "vel":
            self._lane_apply(y)
            self.update()
            return
        if mode in ("ruler", "loop-new"):
            if mode == "ruler":
                if abs(x - self._r_x0) <= 4:
                    return
                if not self._r_pushed:
                    self.proj.push_undo()
                    self._r_pushed = True
                a = max(0.0, min(float(self.proj.total_beats),
                                 round(self._beat_at(self._r_x0))))
                self.proj.loop_region = (a, a)
                self._r_anchor = a
                self._mode = "loop-new"
            b = max(0.0, min(float(self.proj.total_beats),
                             round(self._beat_at(x))))
            ls, le = min(self._r_anchor, b), max(self._r_anchor, b)
            self.proj.loop_region = (ls, max(ls + 1.0, le))
            self.update()
            return
        if mode in ("move", "resize") and self._note is not None:
            n, tr = self._note, self.proj.sel()
            if not tr:
                return
            if mode == "move":
                nb = max(0.0, self._snapv(self._beat_at(x) + self._off_b))
                np_ = max(PITCH_MIN, min(PITCH_MAX,
                                         self._pitch_at(y) + int(self._off_p)))
                if np_ != n.pitch:
                    n.pitch = np_
                    if self._last_prev != np_:
                        self.engine.preview(np_, tr.wave, tr.volume)
                        self._last_prev = np_
                n.start = min(nb, self.proj.total_beats - 0.05)
            else:
                d = self._beat_at(x) - n.start
                d = max(self.snap, round(d / self.snap) * self.snap) \
                    if self.snap > 0 else max(0.05, d)
                n.dur = d
                self.default_dur = d
            self.update()
            return

        hp = self._pitch_at(y)                                # idle hover
        if hp != self.hover_pitch:
            self.hover_pitch = hp
            self.update()
        if self._hit(x, y) and x > KEYB_W + (self._hit(x, y).start
                                             + self._hit(x, y).dur) * self.beat_w - 8:
            self.setCursor(Qt.CursorShape.SizeHorCursor)
        else:
            self.setCursor(Qt.CursorShape.ArrowCursor)

    def mouseReleaseEvent(self, e):
        if self._mode == "rubber":
            x0, y0, x1, y1 = self._rubber
            self._rubber = None
            tr = self.proj.sel()
            if tr:
                bx0, bx1 = sorted((x0, x1))
                by0, by1 = sorted((y0, y1))
                sel = set()
                for n in tr.notes:
                    nx0 = KEYB_W + n.start * self.beat_w
                    nx1 = nx0 + max(6.0, n.dur * self.beat_w)
                    ny0 = self.RULER_H + (PITCH_MAX - n.pitch) * ROW_H
                    if nx0 < bx1 and nx1 > bx0 and ny0 < by1 and ny0 + ROW_H > by0:
                        sel.add(n)
                self.selection = self.selection | sel if self._rubber_add else sel
        elif self._mode in ("ruler", "loop-new"):
            if self._mode == "ruler" and not self._r_pushed:
                b = max(0.0, self._snapv(self._beat_at(e.position().x())))
                self.engine.set_position(min(b, self.proj.total_beats))
        if self._note is not None and self._mode == "resize":
            self.default_dur = self._note.dur
        self._mode = None
        self._note = None
        self._vel_list = None
        self._last_prev = None
        self.setCursor(Qt.CursorShape.ArrowCursor)
        self.update()

    def mouseDoubleClickEvent(self, e):
        n = self._hit(e.position().x(), e.position().y())
        tr = self.proj.sel()
        if n and tr:
            self.selection = {m for m in tr.notes if m.pitch == n.pitch}
            self.engine.preview(n.pitch, tr.wave, tr.volume)
            self.update()
            return
        super().mouseDoubleClickEvent(e)


# ============================================================================
# engraved score view
# ============================================================================
class ScoreView(QWidget):
    GAP, BAR_W, NBARS = 8, 190, 4
    LEFT, TOP, BASS_OFF, SYS_H = 70, 64, 86, 224

    def __init__(self, proj, engine, roll):
        super().__init__()
        self.proj, self.engine, self.roll = proj, engine, roll
        self.zoom = 1.0
        self.clef_font = self._find_clef_font(int(self.GAP * 6.6))
        self.setMouseTracking(True)

    @staticmethod
    def _find_clef_font(size):
        for fam in ("Bravura", "Segoe UI Symbol", "DejaVu Sans", "Symbola",
                    "FreeSerif", "Noto Music", "Apple Symbols"):
            f = QFont(fam)
            f.setPixelSize(size)
            try:
                rf = QRawFont.fromFont(f)
                if rf.supportsCharacter(0x1D11E) and rf.supportsCharacter(0x1D122):
                    return f
            except Exception:
                pass
        return None

    # ---- geometry -------------------------------------------------------------
    def _bars_count(self):
        return self.proj.bars

    def resize_to_project(self):
        systems = max(1, math.ceil(self._bars_count() / self.NBARS))
        self.setFixedSize(int((self.LEFT + self.NBARS * self.BAR_W + 30) * self.zoom),
                          int((self.TOP + systems * self.SYS_H + 40) * self.zoom))
        self.update()

    def set_zoom(self, z):
        self.zoom = max(0.5, min(2.5, float(z)))
        self.resize_to_project()

    def wheelEvent(self, e):
        if e.modifiers() & Qt.KeyboardModifier.ControlModifier:
            self.set_zoom(self.zoom * (1.15 if e.angleDelta().y() > 0 else 1 / 1.15))
            e.accept()
            return
        super().wheelEvent(e)

    def _mx(self, e):
        return e.position().x() / self.zoom

    def _my(self, e):
        return e.position().y() / self.zoom

    def _staff_y(self, pitch, clef, y0):
        ref = 30 if clef == "treble" else 18
        bottom = y0 + 4 * self.GAP if clef == "treble" \
            else y0 + self.BASS_OFF + 4 * self.GAP
        return bottom - (di_step(pitch) - ref) * self.GAP / 2.0

    def _pos(self, n, y0):
        clef = "treble" if n.pitch >= 60 else "bass"
        ref = 30 if clef == "treble" else 18
        return self._staff_y(n.pitch, clef, y0), di_step(n.pitch) - ref, clef

    def _colx(self, col, frac):
        inset = 90 if col == 0 else 16
        return self.LEFT + col * self.BAR_W + inset + frac * (self.BAR_W - inset - 12)

    def _beat_at_s(self, mx):
        bpb = self.proj.beats_per_bar
        col = max(0, min(self.NBARS - 1, int((mx - self.LEFT) // self.BAR_W)))
        inset = 90 if col == 0 else 16
        frac = (mx - self.LEFT - col * self.BAR_W - inset) / (self.BAR_W - inset - 12)
        return col, max(0.0, min(0.999, frac))

    def _pieces(self, n):
        bpb = self.proj.beats_per_bar
        out, s, end, guard = [], n.start, n.end, 0
        while s < end - 1e-6 and guard < 32:
            guard += 1
            bar = int(s // bpb)
            be = min(end, (bar + 1) * bpb)
            out.append((s, be - s))
            s = be
        return out or [(n.start, n.dur)]

    def _note_x(self, ps):
        bpb = self.proj.beats_per_bar
        bar = int(ps // bpb)
        frac = (ps - bar * bpb) / bpb
        return self._colx(bar % self.NBARS, frac), bar

    def _ph_geom(self):
        bpb = self.proj.beats_per_bar
        ph = self.engine.playhead_beats()
        bar = min(int(ph // bpb), self._bars_count() - 1)
        frac = (ph - bar * bpb) / bpb
        y0 = self.TOP + (bar // self.NBARS) * self.SYS_H
        return self._colx(bar % self.NBARS, frac), y0, y0 + self.BASS_OFF + 4 * self.GAP

    # ---- engraving helpers ------------------------------------------------------
    def _whole_rest(self, p, x, y0):
        g = self.GAP
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor("#141414"))
        p.fillRect(QRectF(x, y0 + g, g * 1.7, g * 0.55), QColor("#141414"))

    def _flag(self, p, x, y, up, count, col):
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor(col).darker(135))
        g = self.GAP
        d = 1 if up else -1
        for i in range(count):
            off = i * g * 1.1 * d
            path = QPainterPath(QPointF(x, y + off))
            path.cubicTo(x + g * 1.5, y + off + g * 0.9 * d,
                         x + g * 1.1, y + off + g * 2.1 * d,
                         x + g * 1.9, y + off + g * 2.6 * d)
            path.lineTo(x, y + off + g * 1.6 * d)
            path.closeSubpath()
            p.drawPath(path)

    def _beam(self, p, sx, ty, sx2, ty2, offset, col):
        t = self.GAP * 0.5
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(col)
        p.drawPolygon(QPolygonF([QPointF(sx, ty + offset),
                                 QPointF(sx2, ty2 + offset),
                                 QPointF(sx2, ty2 + offset + t),
                                 QPointF(sx, ty + offset + t)]))

    def _brace(self, p, x, y, h):
        f = QFont("Georgia")
        f.setPixelSize(int(h * 0.86))
        p.setFont(f)
        p.setPen(QPen(QColor("#1a1a1a"), 1))
        p.save()
        p.translate(x, y + h * 0.02)
        p.scale(0.5, 1.0)
        p.drawText(QPointF(0, int(h * 0.88)), "{")
        p.restore()

    def _clefs(self, p, x, y0):
        g, black = self.GAP, QColor("#1a1a1a")
        gy = y0 + 3 * g
        fy = y0 + self.BASS_OFF + g
        if self.clef_font:
            p.setFont(self.clef_font)
            p.setPen(QPen(black, 1))
            p.drawText(QPointF(x, gy + g * 1.35), "\U0001D11E")
            p.drawText(QPointF(x + 2, fy + g * 1.0), "\U0001D122")
        else:
            pen = QPen(black, 2.0)
            pen.setCapStyle(Qt.PenCapStyle.RoundCap)
            p.setPen(pen)
            p.setBrush(Qt.BrushStyle.NoBrush)
            path = QPainterPath(QPointF(x + 4, gy + 2.3 * g))
            path.cubicTo(x - 3, gy + 1.0 * g, x + 13, gy + 0.4 * g, x + 8, gy - 0.9 * g)
            path.cubicTo(x + 4, gy - 2.0 * g, x + 14, gy - 2.4 * g, x + 8, gy - 3.3 * g)
            p.drawPath(path)
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(black)
            p.drawEllipse(QPointF(x + 5, gy + 1.0 * g), 2.6, 2.1)
            p.drawEllipse(QPointF(x + 6, fy - 0.1 * g), 3.4, 2.7)
            pen = QPen(black, 2.2)
            pen.setCapStyle(Qt.PenCapStyle.RoundCap)
            p.setPen(pen)
            p.setBrush(Qt.BrushStyle.NoBrush)
            path = QPainterPath(QPointF(x + 5.5, fy - 0.4 * g))
            path.cubicTo(x + 12, fy - 1.6 * g, x + 7, fy - 2.6 * g, x, fy - 2.3 * g)
            p.drawPath(path)
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(black)
            p.drawEllipse(QPointF(x + 15, fy - g * 0.5 - 2), 1.5, 1.5)
            p.drawEllipse(QPointF(x + 15, fy + g * 0.5 + 2), 1.5, 1.5)

    def _keysig(self, p, x, y0):
        k = self.proj.key_sharps
        if k == 0:
            return
        g = self.GAP
        glyph = "♯" if k >= 0 else "♭"
        seq = (SHARP_T, SHARP_B) if k >= 0 else (FLAT_T, FLAT_B)
        f = QFont("DejaVu Sans")
        f.setPixelSize(int(g * 2.0))
        p.setFont(f)
        p.setPen(QPen(QColor("#1a1a1a"), 1))
        for staff_i, (tab, clef) in enumerate(zip(seq, ("treble", "bass"))):
            yy = y0 + (0 if staff_i == 0 else self.BASS_OFF)
            for i in range(abs(k)):
                lt_, oc = tab[i]
                py = self._staff_y(_NAT[_LET.index(lt_)] + 12 * (oc + 1), clef, yy)
                p.drawText(QPointF(x + i * 9, py + g * 0.72), glyph)

    def _time_sig(self, p, x, y0):
        g = self.GAP
        f = QFont("Georgia")
        f.setPixelSize(int(g * 3.4))
        f.setBold(True)
        p.setFont(f)
        p.setPen(QPen(QColor("#1a1a1a"), 1))
        bpb = self.proj.beats_per_bar
        p.drawText(QRectF(x, y0 - 2, 26, 2 * g), Qt.AlignmentFlag.AlignCenter, str(bpb))
        p.drawText(QRectF(x, y0 + 2 * g - 2, 26, 2 * g),
                   Qt.AlignmentFlag.AlignCenter, "4")

    def _chains(self):
        """Runs of adjacent equal eighths/16ths within a bar, beat and staff."""
        bpb = self.proj.beats_per_bar
        chains = []
        for tr in self.proj.tracks:
            ns = sorted((n for n in tr.notes if n.dur in (0.5, 0.25)),
                        key=lambda n: (n.start, n.pitch))
            cur = []
            for n in ns:
                if (cur and abs(cur[-1].end - n.start) < 1e-6
                        and cur[-1].dur == n.dur
                        and (cur[-1].pitch >= 60) == (n.pitch >= 60)
                        and int(cur[-1].start) == int(n.start)
                        and int(cur[-1].start // bpb) == int(n.start // bpb)):
                    cur.append(n)
                else:
                    if len(cur) >= 2:
                        chains.append(cur)
                    cur = [n]
            if len(cur) >= 2:
                chains.append(cur)
        return chains

    # ---- painting ----------------------------------------------------------------
    def paintEvent(self, _):
        p = QPainter(self)
        p.scale(self.zoom, self.zoom)
        p.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        p.setRenderHint(QPainter.RenderHint.TextAntialiasing, True)
        W, H = self.width() / self.zoom, self.height() / self.zoom
        black, paper = QColor("#1a1a1a"), QColor("#faf7f0")
        proj = self.proj
        bpb, bars = proj.beats_per_bar, proj.bars
        systems = max(1, math.ceil(bars / self.NBARS))

        p.fillRect(0, 0, W, H, QColor("#191a1e"))
        p.setPen(QPen(QColor("#000000"), 1))
        p.setBrush(paper)
        p.drawRoundedRect(QRectF(10, 10, W - 20, H - 20), 6, 6)
        p.setBrush(Qt.BrushStyle.NoBrush)

        f = QFont("Georgia", 13)
        f.setBold(True)
        p.setFont(f)
        p.setPen(QPen(black, 1))
        p.drawText(QPointF(self.LEFT + 8, 36), "Untitled Score")
        p.setFont(QFont("Georgia", 9))
        p.drawText(QPointF(self.LEFT + 8, 52),
                   "♩ = %g   ·   %d tracks   ·   4/4"
                   % (proj.bpm, len(proj.tracks)))

        reg = proj.region() if self.engine.loop else None
        for s in range(systems):
            y0 = self.TOP + s * self.SYS_H
            yb = y0 + self.BASS_OFF
            nb = min(self.NBARS, bars - s * self.NBARS)
            x_end = self.LEFT + nb * self.BAR_W
            p.setPen(QPen(black, 1))
            for k in range(5):
                p.drawLine(self.LEFT, y0 + k * self.GAP, int(x_end), y0 + k * self.GAP)
                p.drawLine(self.LEFT, yb + k * self.GAP, int(x_end), yb + k * self.GAP)
            if reg:
                ls, le = reg
                for bar in range(s * self.NBARS, min((s + 1) * self.NBARS, bars)):
                    b0, b1 = bar * bpb, (bar + 1) * bpb
                    if le <= b0 or ls >= b1:
                        continue
                    fa = max(0.0, (ls - b0) / bpb)
                    fb = min(1.0, (le - b0) / bpb)
                    xa = self._colx(bar % self.NBARS, fa)
                    xb = self._colx(bar % self.NBARS, fb)
                    p.fillRect(QRectF(xa, y0, xb - xa, self.BASS_OFF + 4 * self.GAP),
                               QColor(232, 184, 75, 26))
            for c in range(nb):
                bar = s * self.NBARS + c
                bx = self.LEFT + c * self.BAR_W
                p.setPen(QPen(black, 1))
                p.drawLine(bx, y0, bx, yb + 4 * self.GAP)
                p.setPen(QPen(QColor("#8a8578"), 1))
                p.setFont(QFont("Georgia", 7))
                p.drawText(QPointF(bx + 3, y0 - 6), str(bar + 1))
                b0, b1 = bar * bpb, (bar + 1) * bpb          # whole rests, empty bars
                ht = hb = False
                for tr in proj.tracks:
                    for n in tr.notes:
                        if n.start < b1 and n.end > b0:
                            if n.pitch >= 60:
                                ht = True
                            else:
                                hb = True
                if not ht:
                    self._whole_rest(p, bx + 18, y0)
                if not hb:
                    self._whole_rest(p, bx + 18, y0 + self.BASS_OFF)
            p.setPen(QPen(black, 1.6))
            p.drawLine(int(x_end), y0, int(x_end), yb + 4 * self.GAP)
            if s == systems - 1:
                p.setPen(QPen(black, 4))
                p.drawLine(int(x_end - 7), y0, int(x_end - 7), yb + 4 * self.GAP)
            self._brace(p, self.LEFT - 28, y0, self.BASS_OFF + 4 * self.GAP)
            self._clefs(p, self.LEFT + 6, y0)
            self._keysig(p, self.LEFT + 44, y0)
            if s == 0:
                self._time_sig(p, self.LEFT + 44 + abs(proj.key_sharps) * 9 + 12, y0)

        beam_of = {}                                          # beams
        for chn in self._chains():
            for i, n in enumerate(chn):
                beam_of[id(n)] = (chn, i)

        ph = self.engine.playhead_beats()
        playing = self.engine.playing
        sel = self.roll.selection if self.roll else set()
        pieces_of = {}
        entries = []
        for ti, tr in enumerate(proj.tracks):
            for n in tr.notes:
                if n.start >= bars * bpb:
                    continue
                pcs = self._pieces(n)
                pieces_of[id(n)] = pcs
                for idx, (ps, pd) in enumerate(pcs):
                    entries.append((ps, pd, n, idx, tr))
        entries.sort(key=lambda t: (t[0], t[2].pitch))

        self._acc_mem = {}
        prev_bar = -1
        for ps, pd, n, idx, tr in entries:
            bar = int(ps // bpb)
            if bar != prev_bar:
                self._acc_mem = {}
                prev_bar = bar
            y0 = self.TOP + (bar // self.NBARS) * self.SYS_H
            x = self._colx(bar % self.NBARS, (ps - bar * bpb) / bpb)
            self._draw_note(p, x, y0, n, ps, pd, idx, len(pieces_of[id(n)]),
                            tr, beam_of.get(id(n)),
                            playing and ps <= ph < ps + pd, n in sel)

        if playing or ph > 0:
            x, yt, yb2 = self._ph_geom()
            p.fillRect(QRectF(x - 4, yt - 6, 8, (yb2 - yt) + 12),
                       QColor(224, 72, 79, 40))
            p.setPen(QPen(QColor("#e0484f"), 2))
            p.drawLine(int(x), yt - 6, int(x), yb2 + 6)

    def _draw_note(self, p, x, y0, n, ps, pd, idx, npieces, tr, beaminfo,
                   sounding, selected):
        g = self.GAP
        black, paper = QColor("#141414"), QColor("#faf7f0")
        cy, rs, clef = self._pos(n, y0)
        dt_ = dur_type(pd)
        hw, hh = g * 1.34, g * 0.94
        col = QColor(tr.color).darker(120)
        col.setAlpha(110 + int(140 * min(127, n.vel) / 127.0))
        bottom = y0 + 4 * g if clef == "treble" else y0 + self.BASS_OFF + 4 * g
        first = idx == 0

        p.setPen(QPen(black, 1.2))                            # ledger lines
        rng = (range(10, rs + 1, 2) if rs > 8 else
               range(-2, rs - 1, -2) if rs < 0 else ())
        for k in rng:
            yy = bottom - k * g / 2
            p.drawLine(QLineF(x - hw, yy, x + hw, yy))

        letter, alter, _ = spell(n.pitch, self.proj.key_sharps)   # accidental
        memo = (clef, letter, n.pitch // 12)
        in_effect = self._acc_mem.get(memo,
                                      key_alters(self.proj.key_sharps).get(letter, 0))
        if alter != in_effect:
            f = QFont("DejaVu Sans")
            f.setPixelSize(int(g * 2.1))
            p.setFont(f)
            p.setPen(QPen(black, 1))
            p.drawText(QPointF(x - hw - 10, cy + g * 0.75),
                       {1: "♯", -1: "♭", 0: "♮"}[alter])
            self._acc_mem[memo] = alter

        if sounding:                                          # glow
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QColor(255, 205, 80, 150))
            p.save()
            p.translate(x, cy)
            p.rotate(-20)
            p.drawEllipse(QRectF(-hw * 0.95, -hh * 0.95, hw * 1.9, hh * 1.9))
            p.restore()

        hollow = dt_ in ("whole", "half", "half_dot")         # notehead
        p.setPen(QPen(col, 1.4))
        p.setBrush(paper if hollow else col)
        p.save()
        p.translate(x, cy)
        p.rotate(-20)
        w = hw * 1.25 if dt_ == "whole" else hw
        p.drawEllipse(QRectF(-w / 2, -hh / 2, w, hh))
        p.restore()
        if selected and first:
            p.setPen(QPen(QColor("#ffb63d"), 1.6))
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.drawEllipse(QRectF(-w / 2 - 2.5, -hh / 2 - 2.5, w + 5, hh + 5))

        if dt_.endswith("_dot"):                              # augmentation dot
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(col)
            dy = -g * 0.22 if rs % 2 == 0 else 0.0
            p.drawEllipse(QPointF(x + hw * 0.95 + 2.5, cy + dy), 1.7, 1.7)

        if dt_ == "whole":
            return
        stem = g * 3.4                                        # stem
        up = rs < 4
        sx = x + hw * 0.44 if up else x - hw * 0.44
        ty = cy - stem if up else cy + stem
        p.setPen(QPen(col, 1.6))
        p.drawLine(QLineF(sx, cy, sx, ty))

        if idx < npieces - 1:                                 # tie to next piece
            ps2 = ps + pd
            x2, _ = self._note_x(ps2)
            cy2 = cy
            d = 1.0 if up else -1.0
            path = QPainterPath(QPointF(x + hw * 0.5, cy + d * 0.45 * g))
            path.cubicTo(x + hw + g * 0.8, cy + d * 1.5 * g,
                         x2 - hw - g * 0.8, cy2 + d * 1.5 * g,
                         x2 - hw * 0.5, cy2 + d * 0.45 * g)
            p.setPen(QPen(col, 1.3))
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.drawPath(path)
        elif beaminfo is not None and dt_ in ("eighth", "sixteenth"):
            chn, bi = beaminfo                                # beam to next
            if bi + 1 < len(chn):
                n2 = chn[bi + 1]
                pcs2 = self._pieces(n2)
                if len(pcs2) == 1:
                    x2, bar2 = self._note_x(pcs2[0][0])
                    y02 = self.TOP + (bar2 // self.NBARS) * self.SYS_H
                    cy2, rs2, _ = self._pos(n2, y02)
                    up2 = rs2 < 4
                    sx2 = x2 + hw * 0.44 if up2 else x2 - hw * 0.44
                    ty2 = cy2 - stem if up2 else cy2 + stem
                    bc = QColor(tr.color).darker(135)
                    bc.setAlpha(col.alpha())
                    self._beam(p, sx, ty, sx2, ty2, 0.0, bc)
                    if chn[0].dur == 0.25:
                        self._beam(p, sx, ty, sx2, ty2, g * 0.9, bc)
                return
        if dt_ in ("eighth", "eighth_dot"):                   # lone flag
            self._flag(p, sx, ty, up, 1, tr.color)
        elif dt_ == "sixteenth":
            self._flag(p, sx, ty, up, 2, tr.color)

        if first and n.artic == "staccato":                   # articulations
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QColor(tr.color).darker(150))
            p.drawEllipse(QPointF(x, cy + (-g * 0.85 if up else g * 0.85)), 1.8, 1.8)
        elif first and n.artic == "accent":
            pen = QPen(QColor(tr.color).darker(150), 1.8)
            pen.setCapStyle(Qt.PenCapStyle.RoundCap)
            p.setPen(pen)
            dy = -g * 1.35 if up else g * 1.35
            p.drawLine(QLineF(x - 4.5, cy + dy, x + 4.5, cy + dy))
            p.drawLine(QLineF(x + 4.5, cy + dy, x + 1.0,
                              cy + dy - 3.2 * (1 if up else -1)))
            p.drawLine(QLineF(x + 1.0, cy + dy - 3.2 * (1 if up else -1),
                              x - 4.5, cy + dy))

        if first and n.lyric:                                 # lyrics
            f = QFont("Georgia", 10)
            p.setFont(f)
            p.setPen(QPen(QColor("#222"), 1))
            ty_l = bottom + 3.4 * g
            p.drawText(QRectF(x - 34, ty_l - 12, 68, 14),
                       Qt.AlignmentFlag.AlignCenter, n.lyric)

    # ---- score editing -------------------------------------------------------------
    def _editable_hit(self, mx, my):
        tr = self.proj.sel()
        if not tr:
            return None, None
        g = self.GAP
        best, zone, bd = None, None, 1e9
        for n in tr.notes:
            for ps, _pd in self._pieces(n):
                x, bar = self._note_x(ps)
                y0 = self.TOP + (bar // self.NBARS) * self.SYS_H
                cy, _, _ = self._pos(n, y0)
                hw, hh = g * 1.34, g * 0.94
                if abs(my - cy) <= hh * 1.4 and x - hw <= mx <= x + hw * 1.5:
                    d = abs(mx - x) + abs(my - cy)
                    if d < bd:
                        best = n
                        zone = "resize" if mx > x + hw * 0.55 else "move"
                        bd = d
        return best, zone

    def mousePressEvent(self, e):
        mx, my = self._mx(e), self._my(e)
        tr = self.proj.sel()
        if e.button() == Qt.MouseButton.RightButton:
            n, _ = self._editable_hit(mx, my)
            if n and tr:
                self.proj.push_undo()
                tr.notes.remove(n)
                if self.roll:
                    self.roll.selection.discard(n)
                self.update()
            return
        if e.button() != Qt.MouseButton.LeftButton:
            return
        n, zone = self._editable_hit(mx, my)
        if n and tr:
            if e.modifiers() & Qt.KeyboardModifier.ShiftModifier:
                if self.roll:
                    self.roll.selection.symmetric_difference_update({n})
                self.update()
                return
            if self.roll:
                self.roll.selection = {n}
            self.proj.push_undo()
            self._s_note, self._s_mode = n, zone
            self._s_step = di_step(n.pitch)
            self._s_graby = my
            bpb = self.proj.beats_per_bar
            col, frac = self._beat_at_s(mx)
            self._s_off = n.start - (col * bpb + frac * bpb)
            self.engine.preview(n.pitch, tr.wave, tr.volume)
            self.update()
            return
        if self.roll:
            self.roll.selection.clear()
        bpb = self.proj.beats_per_bar
        col, frac = self._beat_at_s(mx)
        systems = max(1, math.ceil(self._bars_count() / self.NBARS))
        s = max(0, min(systems - 1, int(max(0, my - self.TOP)) // self.SYS_H))
        bar = min(s * self.NBARS + col, self._bars_count() - 1)
        self.engine.set_position(round((bar * bpb + frac * bpb) * 4) / 4.0)
        self.update()

    def mouseMoveEvent(self, e):
        mx, my = self._mx(e), self._my(e)
        if getattr(self, "_s_mode", None) and getattr(self, "_s_note", None):
            tr = self.proj.sel()
            if not tr:
                return
            snap = (self.roll.snap if self.roll else 0.25) or 0.25
            bpb = self.proj.beats_per_bar
            col, frac = self._beat_at_s(mx)
            beat = col * bpb + frac * bpb
            n = self._s_note
            if self._s_mode == "move":
                n.start = max(0.0, min(self.proj.total_beats - 0.25,
                                       round((beat + self._s_off) / snap) * snap))
                dstep = int(round((self._s_graby - my) / (self.GAP / 2.0)))
                if dstep:
                    np_ = max(PITCH_MIN, min(PITCH_MAX,
                                             step_to_pitch(self._s_step + dstep,
                                                           self.proj.key_sharps)))
                    if np_ != n.pitch:
                        n.pitch = np_
                        self.engine.preview(np_, tr.wave, tr.volume)
            else:
                bar = min(int(n.start // bpb), self._bars_count() - 1)
                d = round((beat - n.start) / snap) * snap
                n.dur = max(snap, min(d, (bar + 1) * bpb - n.start))
                if self.roll:
                    self.roll.default_dur = n.dur
            self.update()
            return
        n, zone = self._editable_hit(mx, my)
        self.setCursor(Qt.CursorShape.SizeHorCursor if zone == "resize"
                       else Qt.CursorShape.SizeAllCursor if n
                       else Qt.CursorShape.ArrowCursor)

    def mouseReleaseEvent(self, _):
        self._s_mode = None
        self._s_note = None

    def mouseDoubleClickEvent(self, e):
        mx, my = self._mx(e), self._my(e)
        tr = self.proj.sel()
        if not tr or mx < self.LEFT:
            return
        bpb = self.proj.beats_per_bar
        col, frac = self._beat_at_s(mx)
        systems = max(1, math.ceil(self._bars_count() / self.NBARS))
        s = max(0, min(systems - 1, int(max(0, my - self.TOP)) // self.SYS_H))
        bar = min(s * self.NBARS + col, self._bars_count() - 1)
        y0 = self.TOP + s * self.SYS_H
        clef = "treble" if my < y0 + self.BASS_OFF / 2 else "bass"
        ref = 30 if clef == "treble" else 18
        bottom = y0 + 4 * self.GAP if clef == "treble" \
            else y0 + self.BASS_OFF + 4 * self.GAP
        step = int(round(ref + (bottom - my) * 2.0 / self.GAP))
        pitch = max(PITCH_MIN, min(PITCH_MAX,
                                   step_to_pitch(step, self.proj.key_sharps)))
        qb = max(0.0, min(self.proj.total_beats - 0.25, round((bar * bpb
                                                               + frac * bpb) * 4) / 4))
        dur = self.roll.default_dur if self.roll else 1.0
        self.proj.push_undo()
        n = Note(pitch, qb, dur, 100)
        tr.notes.append(n)
        if self.roll:
            self.roll.selection = {n}
        self.engine.preview(pitch, tr.wave, tr.volume)
        self.update()


# ============================================================================
# track panel
# ============================================================================
class TrackPanel(QWidget):
    def __init__(self, proj, engine, parent=None):
        super().__init__(parent)
        self.proj, self.engine = proj, engine
        self.setMinimumWidth(250)
        v = QVBoxLayout(self)
        v.setContentsMargins(10, 10, 10, 10)
        v.setSpacing(6)

        cap = QLabel("TRACKS")
        cap.setStyleSheet("color:#9aa0ac;font-weight:600;letter-spacing:2px;")
        v.addWidget(cap)

        self.listw = QListWidget()
        self.listw.currentRowChanged.connect(self._sel_changed)
        v.addWidget(self.listw, 1)

        row = QHBoxLayout()
        b_add = QToolButton()
        b_add.setText("+ Add")
        b_del = QToolButton()
        b_del.setText("− Del")
        b_add.clicked.connect(self._add)
        b_del.clicked.connect(self._del)
        row.addWidget(b_add)
        row.addWidget(b_del)
        row.addStretch(1)
        v.addLayout(row)

        def lbl(t):
            l = QLabel(t)
            l.setStyleSheet("color:#8a90a0;font-size:11px;")
            return l

        v.addWidget(lbl("NAME"))
        self.name = QLineEdit()
        self.name.editingFinished.connect(self._name_ed)
        v.addWidget(self.name)

        v.addWidget(lbl("INSTRUMENT (WAVEFORM)"))
        self.wave = QComboBox()
        self.wave.addItems(["sine", "triangle", "square", "saw"])
        self.wave.currentTextChanged.connect(self._wave_ch)
        v.addWidget(self.wave)

        v.addWidget(lbl("VOLUME"))
        self.vol = QSlider(Qt.Orientation.Horizontal)
        self.vol.setRange(0, 100)
        self.vol.valueChanged.connect(self._vol_ch)
        v.addWidget(self.vol)

        v.addWidget(lbl("PAN"))
        self.pan = QSlider(Qt.Orientation.Horizontal)
        self.pan.setRange(-50, 50)
        self.pan.valueChanged.connect(self._pan_ch)
        v.addWidget(self.pan)

        row2 = QHBoxLayout()
        self.mute = QToolButton()
        self.mute.setText("Mute")
        self.mute.setCheckable(True)
        self.mute.toggled.connect(self._mute_ch)
        self.solo = QToolButton()
        self.solo.setText("Solo")
        self.solo.setCheckable(True)
        self.solo.toggled.connect(self._solo_ch)
        colb = QToolButton()
        colb.setText("Color…")
        colb.clicked.connect(self._color)
        row2.addWidget(self.mute)
        row2.addWidget(self.solo)
        row2.addWidget(colb)
        row2.addStretch(1)
        v.addLayout(row2)

        hint = QLabel("Space play · right-drag erase · Ctrl-drag clone / select\n"
                      "drag ruler = loop · click score = seek · F1-style hints in menus")
        hint.setStyleSheet("color:#6f7480;font-size:10px;")
        hint.setWordWrap(True)
        v.addWidget(hint)
        self.refresh()

    def refresh(self):
        lw = self.listw
        lw.blockSignals(True)
        lw.clear()
        for tr in self.proj.tracks:
            tag = ""
            if tr.muted:
                tag += "  (muted)"
            if tr.solo:
                tag += "  (solo)"
            it = QListWidgetItem(tr.name + tag)
            pm = QPixmap(12, 12)
            pm.fill(tr.color)
            it.setIcon(QIcon(pm))
            lw.addItem(it)
        r = min(self.proj.selected, len(self.proj.tracks) - 1)
        if r >= 0:
            lw.setCurrentRow(r)
        lw.blockSignals(False)
        self.load_editor()

    def load_editor(self):
        tr = self.proj.sel()
        for w in (self.name, self.wave, self.vol, self.pan, self.mute, self.solo):
            w.setEnabled(tr is not None)
        if not tr:
            return
        for w, val in ((self.name, tr.name), (self.wave, tr.wave),
                       (self.vol, int(tr.volume * 100)),
                       (self.pan, int(tr.pan * 50)),
                       (self.mute, tr.muted), (self.solo, tr.solo)):
            w.blockSignals(True)
            if isinstance(w, QSlider):
                w.setValue(val)
            elif isinstance(w, QComboBox):
                w.setCurrentText(val)
            elif isinstance(w, QToolButton):
                w.setChecked(val)
            else:
                w.setText(val)
            w.blockSignals(False)

    def _sel_changed(self, row):
        if row < 0:
            return
        self.proj.selected = row
        self.load_editor()

    def _add(self):
        self.proj.push_undo()
        tr = Track("Track %d" % (len(self.proj.tracks) + 1),
                   PALETTE[len(self.proj.tracks) % len(PALETTE)])
        self.proj.tracks.append(tr)
        self.proj.selected = len(self.proj.tracks) - 1
        self.refresh()

    def _del(self):
        if len(self.proj.tracks) <= 1:
            return
        self.proj.push_undo()
        i = max(0, self.proj.selected)
        self.proj.tracks.pop(i)
        self.proj.selected = min(i, len(self.proj.tracks) - 1)
        self.refresh()

    def _name_ed(self):
        tr = self.proj.sel()
        if tr:
            tr.name = self.name.text().strip() or tr.name
            self.refresh()

    def _wave_ch(self, t):
        tr = self.proj.sel()
        if tr:
            tr.wave = t

    def _vol_ch(self, v):
        tr = self.proj.sel()
        if tr:
            tr.volume = v / 100.0

    def _pan_ch(self, v):
        tr = self.proj.sel()
        if tr:
            tr.pan = v / 50.0

    def _mute_ch(self, on):
        tr = self.proj.sel()
        if tr:
            tr.muted = on
            self.refresh()

    def _solo_ch(self, on):
        tr = self.proj.sel()
        if tr:
            tr.solo = on
            self.refresh()

    def _color(self):
        tr = self.proj.sel()
        if not tr:
            return
        c = QColorDialog.getColor(tr.color, self, "Track color")
        if c.isValid():
            self.proj.push_undo()
            tr.color = c
            self.refresh()


# ============================================================================
# file I/O — MIDI & MusicXML
# ============================================================================
def export_midi_file(proj, path):
    import mido
    mid = mido.MidiFile(ticks_per_beat=480)
    t0 = mido.MidiTrack()
    mid.tracks.append(t0)
    t0.append(mido.MetaMessage("set_tempo",
                               tempo=mido.bpm2tempo(proj.bpm), time=0))
    t0.append(mido.MetaMessage("time_signature", numerator=proj.beats_per_bar,
                               denominator=4, time=0))
    GM = {"sine": 80, "triangle": 73, "square": 81, "saw": 87}
    for ch, tr in enumerate(proj.tracks[:16]):
        mt = mido.MidiTrack()
        mid.tracks.append(mt)
        mt.append(mido.Message("program_change", channel=ch,
                               program=GM.get(tr.wave, 0), time=0))
        mt.append(mido.Message("control_change", channel=ch, control=7,
                               value=int(tr.volume * 127), time=0))
        mt.append(mido.Message("control_change", channel=ch, control=10,
                               value=int((tr.pan + 1) / 2 * 127), time=0))
        evs = []
        for n in tr.notes:
            evs.append((n.start, n.pitch, n.vel, True))
            evs.append((n.end, n.pitch, 0, False))
        evs.sort(key=lambda e: (round(e[0] * 480), 0 if not e[3] else 1))
        last = 0
        for tick, pitch, vel, on in evs:
            t = round(tick * 480)
            mt.append(mido.Message("note_on" if on else "note_off", channel=ch,
                                   note=pitch, velocity=vel, time=t - last))
            last = t
    mid.save(path)


def import_midi_file(proj, path, quant=0.25):
    import mido
    mid = mido.MidiFile(path)
    tpb = mid.ticks_per_beat or 480
    chans = {}
    bpm = None
    for mt in mid.tracks:
        t = 0
        active = {}
        for msg in mt:
            t += msg.time
            if msg.type == "set_tempo":
                bpm = mido.tempo2bpm(msg.tempo)
            elif msg.type in ("note_on", "note_off"):
                if msg.channel == 9:
                    continue
                if msg.type == "note_on" and msg.velocity > 0:
                    active.setdefault((msg.channel, msg.note), []).append(t)
                else:
                    starts = active.get((msg.channel, msg.note))
                    if starts:
                        s = starts.pop(0)
                        sb = round(s / tpb / quant) * quant
                        eb = round(t / tpb / quant) * quant
                        tr = chans.setdefault(
                            msg.channel,
                            Track("Ch %d" % (msg.channel + 1),
                                  PALETTE[msg.channel % len(PALETTE)]))
                        tr.notes.append(Note(msg.note, round(sb, 4),
                                             max(quant, round(eb - sb, 4)),
                                             min(127, msg.velocity)))
    if not chans:
        return 0
    proj.tracks = list(chans.values())
    proj.selected = 0
    if bpm:
        proj.bpm = max(40, min(240, int(bpm)))
    end = max((n.end for tr in proj.tracks for n in tr.notes), default=0)
    proj.bars = max(1, min(64, int(math.ceil(end / proj.beats_per_bar))))
    return sum(len(t.notes) for t in proj.tracks)


def export_musicxml(proj, path):
    bpb, bars = proj.beats_per_bar, proj.bars
    DIV = 4
    ka = key_alters(proj.key_sharps)
    Q = lambda d: max(0.25, round(d * 4) / 4)

    def durtype(q):
        for v, t, dd in ((4.0, "whole", 0), (3.0, "half", 1), (2.0, "half", 0),
                         (1.5, "quarter", 1), (1.0, "quarter", 0),
                         (0.75, "eighth", 1), (0.5, "eighth", 0),
                         (0.25, "16th", 0)):
            if abs(q - v) < 1e-6:
                return t, dd
        return "quarter", 0

    out = ['<?xml version="1.0" encoding="UTF-8"?>',
           '<!DOCTYPE score-partwise PUBLIC "-//Recordare//DTD MusicXML 4.0 '
           'Partwise//EN" "http://www.musicxml.org/dtds/partwise.dtd">',
           '<score-partwise version="4.0">',
           ' <part-list><score-part id="P1"><part-name>ScoreDAW</part-name>'
           '</score-part></part-list>', ' <part id="P1">']

    for bar in range(bars):
        out.append('  <measure number="%d">' % (bar + 1))
        if bar == 0:
            out.append('   <attributes><divisions>%d</divisions>'
                       '<key><fifths>%d</fifths><mode>%s</mode></key>'
                       '<time><beats>%d</beats><beat-type>4</beat-type></time>'
                       '<staves>2</staves>'
                       '<clef number="1"><sign>G</sign><line>2</line></clef>'
                       '<clef number="2"><sign>F</sign><line>4</line></clef>'
                       '</attributes>' % (DIV, proj.key_sharps, proj.mode, bpb))
        if bar == 0:
            out.append('   <direction placement="above"><direction-type>'
                       '<metronome><beat-unit>quarter</beat-unit>'
                       '<per-minute>%g</per-minute></metronome></direction-type>'
                       '<sound tempo="%g"/></direction>' % (proj.bpm, proj.bpm))
        b0, b1 = bar * bpb, (bar + 1) * bpb
        for staff, (lo, hi) in enumerate(((60, 200), (0, 60)), start=1):
            evs = {}
            for tr in proj.tracks:
                for n in tr.notes:
                    if not (lo <= n.pitch < hi) or n.start >= b1 or n.end <= b0:
                        continue
                    s = max(n.start, b0) - b0
                    d = Q(min(n.end, b1) - max(n.start, b0))
                    evs.setdefault(round(s, 3), []).append((d, n))
            if not evs:
                continue
            mem = {}
            cursor = 0.0
            for sb_ in sorted(evs):
                if sb_ > cursor + 1e-6:
                    t, dd = durtype(Q(sb_ - cursor))
                    out.append('    <note><rest/><duration>%d</duration>'
                               '<voice>%d</voice><type>%s</type>%s'
                               '<staff>%d</staff></note>'
                               % (max(1, round((sb_ - cursor) * DIV)), staff, t,
                                  "<dot/>" * dd, staff))
                elif sb_ < cursor - 1e-6:
                    out.append('    <backup><duration>%d</duration></backup>'
                               % max(1, round((cursor - sb_) * DIV)))
                grp = sorted(evs[sb_], key=lambda x: x[1].pitch)
                for gi, (d, n) in enumerate(grp):
                    letter, alter, oc = spell(n.pitch, proj.key_sharps)
                    in_ef = mem.get((letter, oc), ka.get(letter, 0))
                    acc = ""
                    if alter != in_ef:
                        acc = "<accidental>%s</accidental>" \
                              % {1: "sharp", -1: "flat", 0: "natural"}[alter]
                    mem[(letter, oc)] = alter
                    art = ""
                    if n.artic:
                        art = ("<notations><%s/></notations>"
                               % ("staccato" if n.artic == "staccato" else "accent"))
                    lyr = ""
                    if gi == 0 and n.lyric:
                        s = n.lyric
                        a, b = s.startswith("-"), s.endswith("-")
                        sy = ("middle" if a and b else "begin" if b
                              else "end" if a else "single")
                        lyr = ('<lyric><syllabic>%s</syllabic><text>%s</text>'
                               '</lyric>' % (sy, s.strip("-")))
                    t, dd = durtype(d)
                    out.append('    <note>%s<pitch><step>%s</step>%s'
                               '<octave>%d</octave></pitch>'
                               '<duration>%d</duration><voice>%d</voice>'
                               '<type>%s</type>%s%s<staff>%d</staff>%s%s</note>'
                               % ("<chord/>" if gi > 0 else "", letter,
                                  "<alter>%d</alter>" % alter if alter else "", oc,
                                  max(1, round(d * DIV)), staff, t, "<dot/>" * dd,
                                  acc, staff, art, lyr))
                cursor = sb_ + max(d for d, _ in grp)
            if cursor < bpb - 1e-6:
                t, dd = durtype(Q(bpb - cursor))
                out.append('    <note><rest/><duration>%d</duration>'
                           '<voice>%d</voice><type>%s</type>%s'
                           '<staff>%d</staff></note>'
                           % (max(1, round((bpb - cursor) * DIV)), staff, t,
                              "<dot/>" * dd, staff))
            if staff == 1:
                out.append('    <backup><duration>%d</duration></backup>'
                           % (bpb * DIV))
        out.append("  </measure>")
    out += [" </part>", "</score-partwise>", ""]
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(out))


# ============================================================================
# main window
# ============================================================================
class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("ScoreDAW — piano roll + sheet music")
        self.proj = Project()
        build_demo(self.proj)
        self.engine = Engine(self.proj)
        self.clipboard = []

        self.roll = PianoRoll(self.proj, self.engine)
        self.roll.resize_to_project()
        self.score = ScoreView(self.proj, self.engine, self.roll)
        self.score.resize_to_project()

        self.roll_scroll = QScrollArea()
        self.roll_scroll.setWidget(self.roll)
        self.roll_scroll.setWidgetResizable(False)
        self.roll_scroll.setStyleSheet("QScrollArea{border:none;background:#202127;}")
        self.score_scroll = QScrollArea()
        self.score_scroll.setWidget(self.score)
        self.score_scroll.setWidgetResizable(False)
        self.score_scroll.setStyleSheet("QScrollArea{border:none;background:#202127;}")

        split = QSplitter(Qt.Orientation.Horizontal)
        right = QSplitter(Qt.Orientation.Vertical)
        right.addWidget(self.roll_scroll)
        right.addWidget(self.score_scroll)
        right.setSizes([520, 420])
        split.addWidget(TrackPanel(self.proj, self.engine))
        split.addWidget(right)
        split.setSizes([260, 1140])
        split.setHandleWidth(5)
        self.setCentralWidget(split)

        self._toolbar()
        self._menus()
        self.timer = QTimer(self)
        self.timer.setInterval(30)
        self.timer.timeout.connect(self._tick)
        self.timer.start()
        self.resize(1440, 900)

    # ---- toolbar ---------------------------------------------------------------
    def _toolbar(self):
        tb = QToolBar("Transport")
        tb.setMovable(False)
        self.addToolBar(tb)
        st = self.style()

        self.btn_play = QToolButton()
        self.btn_play.setIcon(st.standardIcon(QStyle.StandardPixmap.SP_MediaPlay))
        self.btn_play.setToolTip("Play / Pause (Space)")
        self.btn_play.clicked.connect(self._toggle)
        b_stop = QToolButton()
        b_stop.setIcon(st.standardIcon(QStyle.StandardPixmap.SP_MediaStop))
        b_stop.clicked.connect(self._stop)
        b_home = QToolButton()
        b_home.setIcon(st.standardIcon(QStyle.StandardPixmap.SP_MediaSkipBackward))
        b_home.clicked.connect(lambda: self.engine.set_position(0))
        for b in (self.btn_play, b_stop, b_home):
            b.setAutoRaise(True)
            tb.addWidget(b)
        tb.addSeparator()

        tb.addWidget(QLabel(" Key "))
        self.key_cb = QComboBox()
        for label, _f, _m in KEY_TABLE:
            self.key_cb.addItem(label)
        self.key_cb.currentIndexChanged.connect(self._key_changed)
        tb.addWidget(self.key_cb)

        tb.addWidget(QLabel(" Tempo "))
        self.bpm = QSpinBox()
        self.bpm.setRange(40, 240)
        self.bpm.setValue(int(self.proj.bpm))
        self.bpm.setSuffix(" BPM")
        self.bpm.valueChanged.connect(lambda v: setattr(self.proj, "bpm", float(v)))
        tb.addWidget(self.bpm)

        self.bars = QSpinBox()
        self.bars.setRange(1, 64)
        self.bars.setValue(self.proj.bars)
        self.bars.setPrefix("Bars: ")
        self.bars.valueChanged.connect(self._bars_changed)
        tb.addWidget(self.bars)

        tb.addSeparator()
        tb.addWidget(QLabel(" Snap "))
        self.snap = QComboBox()
        self.snap.addItems(["1/4", "1/8", "1/16", "1/32", "Off"])
        self.snap.setCurrentIndex(2)
        self.snap.currentIndexChanged.connect(
            lambda i: setattr(self.roll, "snap", [1.0, 0.5, 0.25, 0.125, 0.0][i]))
        tb.addWidget(self.snap)

        self.loop = QToolButton()
        self.loop.setText("Loop")
        self.loop.setCheckable(True)
        self.loop.setChecked(True)
        self.loop.toggled.connect(lambda on: setattr(self.engine, "loop", on))
        tb.addWidget(self.loop)

        self.metro = QToolButton()
        self.metro.setText("Metro")
        self.metro.setCheckable(True)
        self.metro.toggled.connect(lambda on: setattr(self.engine, "metro", on))
        tb.addWidget(self.metro)

        self.sc = QToolButton()
        self.sc.setText("Scale-snap")
        self.sc.setCheckable(True)
        self.sc.toggled.connect(lambda on: setattr(self.roll, "snap_to_scale", on))
        tb.addWidget(self.sc)

        self.guide = QToolButton()
        self.guide.setText("Scale guide")
        self.guide.setCheckable(True)
        self.guide.setChecked(True)
        self.guide.toggled.connect(lambda on: (setattr(self.roll, "scale_guide", on),
                                               self.roll.update()))
        tb.addWidget(self.guide)

        tb.addSeparator()
        tb.addWidget(QLabel(" Vol "))
        vol = QSlider(Qt.Orientation.Horizontal)
        vol.setRange(0, 100)
        vol.setValue(90)
        vol.setFixedWidth(110)
        vol.valueChanged.connect(lambda v: setattr(self.engine, "master", v / 100.0))
        tb.addWidget(vol)

        self.pos_lbl = QLabel("  Bar 1 · Beat 1  ")
        self.pos_lbl.setStyleSheet("font-family:Consolas,monospace;"
                                   "font-weight:600;color:#7ee787;padding:0 8px;")
        tb.addWidget(self.pos_lbl)
        stretch = QWidget()
        stretch.setSizePolicy(QSizePolicy.Policy.Expanding,
                              QSizePolicy.Policy.Preferred)
        tb.addWidget(stretch)

    def _menus(self):
        mb = self.menuBar()
        mf = mb.addMenu("&File")
        mf.addAction("New", self.new_project)
        mf.addAction("Open…", self.open_json)
        mf.addAction("Save…", self.save_json)
        mf.addSeparator()
        mf.addAction("Export MIDI…", self.export_midi)
        mf.addAction("Import MIDI…", self.import_midi)
        mf.addAction("Export MusicXML…", self.export_xml)
        mf.addSeparator()
        mf.addAction("Export WAV…", self.export_wav)
        me = mb.addMenu("&Edit")
        me.addAction("Undo\tCtrl+Z", self._undo)
        me.addAction("Redo\tCtrl+Y", self._redo)
        me.addSeparator()
        me.addAction("Copy\tCtrl+C", self.copy_sel)
        me.addAction("Paste at playhead\tCtrl+V", self.paste_clip)
        me.addAction("Duplicate\tCtrl+D", self.duplicate_sel)
        me.addAction("Quantize\tCtrl+Q", self.quantize_sel)
        me.addSeparator()
        am = me.addMenu("Articulation (selection)")
        for label, val in (("— none", ""), ("Staccato", "staccato"),
                           ("Accent", "accent")):
            am.addAction(label, lambda v=val: self.set_artic(v))
        lm = me.addMenu("Lyrics")
        lm.addAction("Type lyrics for selection…\tCtrl+T", self.edit_lyrics)

    # ---- project actions --------------------------------------------------------
    def _key_changed(self, i):
        _label, f, m = KEY_TABLE[i]
        self.proj.push_undo()
        self.proj.key_sharps, self.proj.mode = f, m
        self.score.update()

    def _bars_changed(self, v):
        self.proj.push_undo()
        self.proj.bars = v
        self._after_struct_change()

    def _after_struct_change(self):
        self.roll.selection.clear()
        self.roll.resize_to_project()
        self.score.resize_to_project()
        self.update()

    def new_project(self):
        self.proj.push_undo()
        self.proj.from_dict({"bpm": 110, "bars": 8, "tracks": [
            {"name": "Track 1", "color": PALETTE[0], "wave": "sine",
             "volume": 0.75, "notes": []}]})
        self._after_struct_change()

    def save_json(self):
        path, _ = QFileDialog.getSaveFileName(self, "Save project", "",
                                              "ScoreDAW project (*.json)")
        if path:
            with open(path, "w") as f:
                json.dump(self.proj.to_dict(), f)
            self.statusBar().showMessage("Saved %s" % path, 4000)

    def open_json(self):
        path, _ = QFileDialog.getOpenFileName(self, "Open project", "",
                                              "ScoreDAW project (*.json)")
        if not path:
            return
        try:
            with open(path) as f:
                d = json.load(f)
        except Exception as ex:
            QMessageBox.warning(self, "Open", "Could not load:\n%s" % ex)
            return
        self.proj.push_undo()
        self.proj.from_dict(d)
        self._after_struct_change()

    def export_midi(self):
        try:
            import mido  # noqa: F401
        except ImportError:
            QMessageBox.warning(self, "Export MIDI",
                                "The mido package is required:\n\npip install mido")
            return
        path, _ = QFileDialog.getSaveFileName(self, "Export MIDI", "",
                                              "MIDI file (*.mid)")
        if path:
            export_midi_file(self.proj, path)
            self.statusBar().showMessage("Exported %s" % path, 4000)

    def import_midi(self):
        try:
            import mido  # noqa: F401
        except ImportError:
            QMessageBox.warning(self, "Import MIDI",
                                "The mido package is required:\n\npip install mido")
            return
        path, _ = QFileDialog.getOpenFileName(self, "Import MIDI", "",
                                              "MIDI file (*.mid *.midi)")
        if not path:
            return
        self.proj.push_undo()
        cnt = import_midi_file(self.proj, path)
        self._after_struct_change()
        QMessageBox.information(self, "Import MIDI",
                                "Imported %d notes" % cnt)

    def export_xml(self):
        path, _ = QFileDialog.getSaveFileName(self, "Export MusicXML", "",
                                              "MusicXML (*.musicxml *.xml)")
        if not path:
            return
        try:
            export_musicxml(self.proj, path)
        except Exception as ex:
            QMessageBox.warning(self, "Export", "MusicXML export failed:\n%s" % ex)
            return
        self.statusBar().showMessage("Exported %s" % path, 4000)

    def export_wav(self):
        path, _ = QFileDialog.getSaveFileName(self, "Export WAV", "",
                                              "WAV audio (*.wav)")
        if not path:
            return
        try:
            self.engine.render_offline(path)
        except Exception as ex:
            QMessageBox.warning(self, "Export", "WAV render failed:\n%s" % ex)
            return
        QMessageBox.information(self, "Export", "Rendered to:\n%s" % path)

    # ---- edit actions -------------------------------------------------------------
    def _sel_notes(self):
        return sorted(self.roll.selection, key=lambda n: (n.start, n.pitch))

    def copy_sel(self):
        sel = self._sel_notes()
        if not sel:
            return
        base = min(n.start for n in sel)
        self.clipboard = [(round(n.start - base, 4), n.pitch, n.dur, n.vel,
                           n.artic, n.lyric) for n in sel]
        self.statusBar().showMessage("Copied %d note(s)" % len(sel), 2500)

    def paste_clip(self):
        if not self.clipboard:
            return
        tr = self.proj.sel()
        if not tr:
            return
        at = round(self.engine.playhead_beats() / (self.roll.snap or 0.25)) \
            * (self.roll.snap or 0.25)
        self.proj.push_undo()
        made = []
        for rel, pitch, dur, vel, artic, lyric in self.clipboard:
            b = at + rel
            if b >= self.proj.total_beats:
                continue
            c = Note(pitch, b, dur, vel, artic, lyric)
            tr.notes.append(c)
            made.append(c)
        self.roll.selection = set(made)
        self.statusBar().showMessage("Pasted %d note(s)" % len(made), 2500)

    def duplicate_sel(self):
        sel = self._sel_notes()
        if not sel:
            return
        tr = self.proj.sel()
        span = max(math.ceil((max(n.end for n in sel)
                              - min(n.start for n in sel)) * 4) / 4,
                   self.roll.snap or 0.25)
        self.proj.push_undo()
        new = []
        for n in sel:
            c = Note(n.pitch, n.start + span, n.dur, n.vel, n.artic, n.lyric)
            tr.notes.append(c)
            new.append(c)
        self.roll.selection = set(new)

    def quantize_sel(self):
        sel = self._sel_notes()
        if not sel:
            return
        s = self.roll.snap or 0.25
        self.proj.push_undo()
        for n in sel:
            n.start = max(0.0, round(n.start / s) * s)

    def set_artic(self, a):
        sel = self._sel_notes()
        if not sel:
            return
        self.proj.push_undo()
        for n in sel:
            n.artic = a

    def edit_lyrics(self):
        sel = self._sel_notes()
        if not sel:
            self.statusBar().showMessage("Select notes first", 3000)
            return
        cur = " ".join(n.lyric for n in sel).strip()
        text, ok = QInputDialog.getText(
            self, "Lyrics",
            "%d note(s) selected — syllables separated by spaces\n"
            "(end a syllable with '-' for a hyphen):" % len(sel), text=cur)
        if not ok:
            return
        self.proj.push_undo()
        syl = text.split()
        for i, n in enumerate(sel):
            n.lyric = syl[i] if i < len(syl) else ""

    def _undo(self):
        if self.proj.undo():
            self._after_struct_change()

    def _redo(self):
        if self.proj.redo():
            self._after_struct_change()

    # ---- transport / tick ------------------------------------------------------------
    def _toggle(self):
        eng = self.engine
        if eng.playing:
            eng.pause()
        else:
            if eng.playhead_beats() >= self.proj.total_beats - 1e-6:
                eng.set_position(0)
            eng.play()
        self._play_icon()

    def _stop(self):
        self.engine.stop()
        self._play_icon()

    def _play_icon(self):
        st = self.style()
        self.btn_play.setIcon(st.standardIcon(
            QStyle.StandardPixmap.SP_MediaPause if self.engine.playing
            else QStyle.StandardPixmap.SP_MediaPlay))

    def _tick(self):
        eng, proj = self.engine, self.proj
        beats = eng.playhead_beats()
        self.pos_lbl.setText("  Bar %d · Beat %d  "
                             % (int(beats // proj.beats_per_bar) + 1,
                                int(beats % proj.beats_per_bar) + 1))
        self.roll.update()
        self.score.update()
        if eng.playing:
            x = KEYB_W + beats * self.roll.beat_w
            sb = self.roll_scroll.horizontalScrollBar()
            if x < sb.value() + 30 or x > sb.value() + sb.pageStep() - 90:
                sb.setValue(int(x - sb.pageStep() * 0.4))

    def keyPressEvent(self, e):
        k = e.key()
        mod = e.modifiers()
        sel = self.roll.selection
        if k == Qt.Key_Space:
            self._toggle()
        elif k == Qt.Key_Home:
            self.engine.set_position(0)
        elif k in (Qt.Key_Left, Qt.Key_Right) and not sel:
            step = self.roll.snap or 0.25
            self.engine.set_position(max(0.0, self.engine.playhead_beats()
                                         + (-step if k == Qt.Key_Left else step)))
        elif mod & Qt.KeyboardModifier.ControlModifier and k == Qt.Key_Z:
            self._redo() if (mod & Qt.KeyboardModifier.ShiftModifier) else self._undo()
        elif mod & Qt.KeyboardModifier.ControlModifier and k == Qt.Key_Y:
            self._redo()
        elif mod & Qt.KeyboardModifier.ControlModifier and k == Qt.Key_D:
            self.duplicate_sel()
        elif mod & Qt.KeyboardModifier.ControlModifier and k == Qt.Key_Q:
            self.quantize_sel()
        elif mod & Qt.KeyboardModifier.ControlModifier and k == Qt.Key_C:
            self.copy_sel()
        elif mod & Qt.KeyboardModifier.ControlModifier and k == Qt.Key_V:
            self.paste_clip()
        elif mod & Qt.KeyboardModifier.ControlModifier and k == Qt.Key_A:
            tr = self.proj.sel()
            if tr:
                self.roll.selection = set(tr.notes)
                self.roll.update()
        elif mod & Qt.KeyboardModifier.ControlModifier and k == Qt.Key_T:
            self.edit_lyrics()
        elif k == Qt.Key_Delete and sel:
            tr = self.proj.sel()
            if tr:
                self.proj.push_undo()
                for n in list(sel):
                    if n in tr.notes:
                        tr.notes.remove(n)
                self.roll.selection.clear()
                self.roll.update()
        elif sel and k in (Qt.Key_Up, Qt.Key_Down, Qt.Key_Left, Qt.Key_Right):
            step = self.roll.snap or 0.25
            self.proj.push_undo()
            for n in sel:
                if k == Qt.Key_Up:
                    n.pitch = min(PITCH_MAX, n.pitch + 1)
                elif k == Qt.Key_Down:
                    n.pitch = max(PITCH_MIN, n.pitch - 1)
                elif k == Qt.Key_Left:
                    n.start = max(0.0, n.start - step)
                else:
                    n.start = min(self.proj.total_beats - step, n.start + step)
            self.roll.update()
        else:
            super().keyPressEvent(e)


# ============================================================================
# theme & entry point
# ============================================================================
def apply_dark(app):
    app.setStyle("Fusion")
    pal = QPalette()
    c = QColor
    pal.setColor(QPalette.ColorRole.Window, c("#232529"))
    pal.setColor(QPalette.ColorRole.WindowText, c("#d6d9e0"))
    pal.setColor(QPalette.ColorRole.Base, c("#1b1c20"))
    pal.setColor(QPalette.ColorRole.AlternateBase, c("#26282e"))
    pal.setColor(QPalette.ColorRole.Text, c("#d6d9e0"))
    pal.setColor(QPalette.ColorRole.Button, c("#2d2f36"))
    pal.setColor(QPalette.ColorRole.ButtonText, c("#d6d9e0"))
    pal.setColor(QPalette.ColorRole.Highlight, c("#3d6db5"))
    pal.setColor(QPalette.ColorRole.HighlightedText, c("white"))
    pal.setColor(QPalette.ColorRole.PlaceholderText, c("#7a7f8a"))
    pal.setColor(QPalette.ColorRole.ToolTipBase, c("#2d2f36"))
    pal.setColor(QPalette.ColorRole.ToolTipText, c("#d6d9e0"))
    for role in (QPalette.ColorRole.Text, QPalette.ColorRole.ButtonText,
                 QPalette.ColorRole.WindowText):
        pal.setColor(QPalette.ColorGroup.Disabled, role, c("#666a74"))
    app.setPalette(pal)


def main():
    app = QApplication(sys.argv)
    app.setApplicationName("ScoreDAW")
    apply_dark(app)
    w = MainWindow()
    w.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()