#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Klutter – visionneuse et outil de tri rapide pour photos RAW (CR2 & co).

Principe : on n'ouvre jamais le RAW complet. On lit l'aperçu JPEG intégré par
l'appareil dans chaque fichier (CR2, NEF, ARW, DNG…). C'est quasi instantané,
même avec des milliers de photos. Les originaux ne sont jamais modifiés.
Les notes et drapeaux sont enregistrés dans un petit fichier
« trieur_photos.json » placé dans le dossier ouvert.
"""
from __future__ import annotations

import colorsys
import csv
import datetime
import hashlib
import json
import math
import os
import random
import re
import shutil
import struct
import sys
import time
from collections import Counter, OrderedDict
from pathlib import Path

from PySide6.QtCore import (QUrl, QAbstractListModel, QBuffer, QByteArray, QIODevice,
                            QEvent, QItemSelectionModel, QModelIndex, QObject, QPoint, QPointF, QPropertyAnimation,
                            QEasingCurve, QRect, QRectF, QRunnable, QSizeF, QVariantAnimation,
                            QSettings, QSize, Qt, QThreadPool, QTimer, Signal)
from PySide6.QtGui import (QAction, QColor, QFont, QFontMetrics, QImage,
                           QImageIOHandler, QImageReader, QKeySequence,
                           QDesktopServices, QIcon, QLinearGradient, QPainter, QPainterPath, QPen,
                           QPixmap, QPolygonF, QShortcut,
                           QTransform)
from PySide6.QtWidgets import (QApplication, QButtonGroup, QCheckBox, QColorDialog, QComboBox,
                               QFileDialog,
                               QGridLayout, QInputDialog, QListWidget, QMenu, QProgressBar, QScrollArea, QSizePolicy,
                               QFrame, QGraphicsOpacityEffect, QGraphicsPixmapItem, QGraphicsScene,
                               QGraphicsView, QHBoxLayout, QLabel, QListView,
                               QLineEdit, QMainWindow, QMessageBox, QProgressDialog,
                               QPushButton, QSlider, QSplitter, QStackedWidget, QStyle,
                               QStyledItemDelegate, QToolBar, QVBoxLayout,
                               QWidget, QAbstractItemView)

try:
    import numpy as np
except Exception:          # sans numpy, l'éditeur de photo est désactivé (le reste fonctionne)
    np = None

APP_NAME = "Klutter"
RAW_EXTS = {".cr2", ".cr3", ".crw", ".nef", ".nrw", ".arw", ".srf", ".sr2",
            ".dng", ".orf", ".rw2", ".raf", ".pef", ".srw", ".raw", ".3fr",
            ".erf", ".kdc", ".mrw", ".rwl", ".iiq"}
IMG_EXTS = {".jpg", ".jpeg", ".png", ".tif", ".tiff", ".webp", ".bmp"}
SIDECAR_NAME = "trieur_photos.json"
CACHE_DIR = Path.home() / ".trieur_photos"
THUMB_MAX = 360          # taille (grand côté) des vignettes en cache
THUMB_LRU = 900          # nombre de vignettes gardées en mémoire
VIEW_LRU = 4             # nombre de grandes images gardées en mémoire

NO_FLAG, PICK, REJECT = 0, 1, -1

DEST_COLORS = ["#6d8cff", "#3ecf8e", "#ffc857", "#ff8a5c", "#c77dff", "#4dd0e1", "#ff6b9a",
               "#9ccc65"]
DEST_AUTO_KEYS = "QWERTYASDG"   # touches proposées automatiquement aux destinations
RESERVED_KEYS = set("PXUCNFHZB")  # déjà utilisées par l'application
STAR_R, STAR_GAP = 6.0, 3.0      # étoiles des vignettes (rayon / espace)

# Couleurs dépendant du thème (remplies par apply_theme)
PAL = {"accent": "#6d8cff", "card": "#1c1e26", "card_hover": "#242734", "star_off": "#3a3d4a",
       "thumb_bg": "#101116", "stage": "#0d0e12", "muted": "#8b90a3", "muted2": "#7d8397",
       "text": "#d6d9e3", "text_dim": "#737888", "ph_text": "#6b7080", "key_bg": "#2d3140",
       "key_fg": "#c9cde0", "hist_label": "#9aa0b4", "text_strong": "#ffffff",
       "hist_bg": (12, 13, 18, 205), "gold": "#ffc857", "ok": "#3ecf8e", "bad": "#ff5d6c",
       "dark": True}
THEME = {"mode": "dark", "accent": "#6d8cff", "tint": False}
ANIM = {"on": True}          # animations (réglable dans les paramètres)

# ---------------------------------------------------------------------------
# Lecture de l'aperçu JPEG intégré dans les RAW
# ---------------------------------------------------------------------------
_TYPE_SIZE = {1: 1, 2: 1, 3: 2, 4: 4, 5: 8, 6: 1, 7: 1, 8: 2, 9: 4, 10: 8,
              11: 4, 12: 8, 13: 4}
_TYPE_FMT = {1: "B", 3: "H", 4: "I", 6: "b", 7: "B", 8: "h", 9: "i",
             11: "f", 12: "d", 13: "I"}


class _Tiff:
    """Lecteur TIFF minimal (CR2, NEF, ARW, DNG… sont des TIFF)."""

    def __init__(self, f):
        self.f = f
        f.seek(0)
        h = f.read(8)
        if len(h) < 8 or h[:2] not in (b"II", b"MM"):
            raise ValueError("pas un fichier TIFF")
        self.e = "<" if h[:2] == b"II" else ">"
        self.first = struct.unpack(self.e + "I", h[4:8])[0]

    def ifd(self, off):
        self.f.seek(off)
        b = self.f.read(2)
        if len(b) < 2:
            raise ValueError("IFD tronqué")
        n = struct.unpack(self.e + "H", b)[0]
        if n == 0 or n > 1000:
            raise ValueError("IFD invalide")
        raw = self.f.read(12 * n + 4)
        if len(raw) < 12 * n:
            raise ValueError("IFD tronqué")
        raw = raw.ljust(12 * n + 4, b"\0")
        ents = {}
        for i in range(n):
            tag, typ, cnt = struct.unpack(self.e + "HHI", raw[i * 12:i * 12 + 8])
            ents[tag] = (typ, cnt, raw[i * 12 + 8:i * 12 + 12])
        nxt = struct.unpack(self.e + "I", raw[12 * n:12 * n + 4])[0]
        return ents, nxt

    def vals(self, ent):
        typ, cnt, v = ent
        size = _TYPE_SIZE.get(typ, 1) * cnt
        if size <= 4:
            data = v[:size]
        else:
            if size > (1 << 16):
                return []
            off = struct.unpack(self.e + "I", v)[0]
            self.f.seek(off)
            data = self.f.read(size)
        if typ == 2:
            return data.split(b"\0")[0].decode("latin-1").strip()
        if typ in (5, 10):
            fmt = "II" if typ == 5 else "ii"
            return [struct.unpack(self.e + fmt, data[i:i + 8])
                    for i in range(0, len(data) - 7, 8)]
        fmt = _TYPE_FMT.get(typ, "B")
        n = len(data) // struct.calcsize(fmt)
        return list(struct.unpack(self.e + str(n) + fmt,
                                  data[:n * struct.calcsize(fmt)]))


def _first(v, default=None):
    return v[0] if isinstance(v, list) and v else default


def _ratio(r):
    try:
        n, d = r
        return n / d if d else None
    except Exception:
        return None


def _jpeg_info(b: bytes):
    """Retourne (largeur, hauteur) si b commence par un JPEG affichable
    (baseline/progressif). Les JPEG « lossless » des données RAW sont refusés."""
    if b[:2] != b"\xff\xd8":
        return None
    i = 2
    n = len(b)
    while i + 4 <= n:
        if b[i] != 0xFF:
            return None
        m = b[i + 1]
        if m == 0xFF:
            i += 1
            continue
        if m == 0x01 or 0xD0 <= m <= 0xD8:
            i += 2
            continue
        if m in (0xD9, 0xDA):
            return None
        length = struct.unpack(">H", b[i + 2:i + 4])[0]
        if m in (0xC0, 0xC1, 0xC2):
            if i + 9 > n:
                return None
            h, w = struct.unpack(">HH", b[i + 5:i + 9])
            return w, h
        if 0xC3 <= m <= 0xCF and m not in (0xC4, 0xC8, 0xCC):
            return None  # lossless / arithmétique : pas affichable
        i += 2 + length
    return None


def _read_tiff_raw(path):
    """-> (jpeg_bytes | None, orientation, meta)"""
    with open(path, "rb") as f:
        t = _Tiff(f)
        ifds, seen, off = [], set(), t.first
        while off and off not in seen and len(ifds) < 10:
            seen.add(off)
            try:
                ents, nxt = t.ifd(off)
            except Exception:
                break
            ifds.append(ents)
            off = nxt
        if not ifds:
            raise ValueError("aucun IFD")
        extra = []
        for ents in list(ifds):
            if 0x014A in ents:  # SubIFDs (NEF, ARW, DNG…)
                for so in t.vals(ents[0x014A]):
                    if so and so not in seen:
                        seen.add(so)
                        try:
                            e, _ = t.ifd(so)
                            extra.append(e)
                        except Exception:
                            pass
        ifd0 = ifds[0]
        meta = {}
        orient = 1
        if 0x0112 in ifd0:
            orient = _first(t.vals(ifd0[0x0112]), 1) or 1
        make = t.vals(ifd0[0x010F]) if 0x010F in ifd0 else ""
        model = t.vals(ifd0[0x0110]) if 0x0110 in ifd0 else ""
        if model:
            meta["camera"] = model if (not make or model.lower().startswith(
                make.split()[0].lower())) else f"{make} {model}"
        if 0x8769 in ifd0:
            try:
                ex, _ = t.ifd(_first(t.vals(ifd0[0x8769])))
                if 0x829A in ex:
                    meta["shutter"] = _ratio(_first(t.vals(ex[0x829A])))
                if 0x829D in ex:
                    meta["aperture"] = _ratio(_first(t.vals(ex[0x829D])))
                if 0x8827 in ex:
                    meta["iso"] = _first(t.vals(ex[0x8827]))
                if 0x920A in ex:
                    meta["focal"] = _ratio(_first(t.vals(ex[0x920A])))
                if 0x9003 in ex:
                    meta["date"] = t.vals(ex[0x9003])
                if 0xA434 in ex:
                    meta["lens"] = t.vals(ex[0xA434])
                if 0xA002 in ex and 0xA003 in ex:
                    meta["dims"] = (_first(t.vals(ex[0xA002])),
                                    _first(t.vals(ex[0xA003])))
            except Exception:
                pass
        cands = []
        for ents in ifds + extra:
            try:
                if 0x0111 in ents and 0x0117 in ents:
                    so, sl = t.vals(ents[0x0111]), t.vals(ents[0x0117])
                    if len(so) == 1 and len(sl) == 1:
                        cands.append((so[0], sl[0]))
                if 0x0201 in ents and 0x0202 in ents:
                    cands.append((_first(t.vals(ents[0x0201])),
                                  _first(t.vals(ents[0x0202]))))
            except Exception:
                continue
        best = None
        for off, ln in cands:
            if not off or not ln or ln < 4000:
                continue
            f.seek(off)
            head = f.read(min(ln, 70000))
            info = _jpeg_info(head)
            if not info:
                continue
            area = info[0] * info[1]
            if best is None or area > best[0]:
                best = (area, off, ln, info)
        jpeg = None
        if best:
            f.seek(best[1])
            jpeg = f.read(best[2])
            meta["preview"] = best[3]
        return jpeg, orient, meta


def _scan_jpeg(path, limit=24 << 20):
    """Dernier recours : cherche le plus grand JPEG affichable dans le fichier."""
    with open(path, "rb") as f:
        data = f.read(limit)
    best, pos = None, 0
    while True:
        i = data.find(b"\xff\xd8\xff", pos)
        if i < 0:
            break
        pos = i + 3
        info = _jpeg_info(data[i:i + 70000])
        if info:
            area = info[0] * info[1]
            if best is None or area > best[0]:
                best = (area, i, info)
    if not best:
        raise ValueError("aucun aperçu JPEG trouvé")
    area, i, info = best
    return data[i:i + area * 2 + 70000], {"preview": info}


def get_source(path):
    """-> (jpeg_bytes | None, orientation, meta). None = lire le fichier tel quel."""
    ext = os.path.splitext(path)[1].lower()
    if ext not in RAW_EXTS:
        return None, 1, {}
    try:
        jpeg, orient, meta = _read_tiff_raw(path)
        if jpeg:
            return jpeg, orient, meta
    except Exception:
        pass
    try:
        jpeg, meta = _scan_jpeg(path)
        return jpeg, 1, meta
    except Exception:
        pass
    try:  # facultatif : pip install rawpy
        import rawpy  # type: ignore
        with rawpy.imread(path) as raw:
            th = raw.extract_thumb()
            if th.format == rawpy.ThumbFormat.JPEG:
                return bytes(th.data), 1, {}
    except Exception:
        pass
    raise ValueError("aperçu introuvable")


def read_meta(path):
    ext = os.path.splitext(path)[1].lower()
    if ext in RAW_EXTS:
        try:
            _, _, meta = get_source(path)
            return meta
        except Exception:
            return {}
    r = QImageReader(path)
    s = r.size()
    return {"dims": (s.width(), s.height())} if s.isValid() else {}


def _apply_orient(img: QImage, o: int) -> QImage:
    t = QTransform()
    if o == 2:
        return img.mirrored(True, False)
    if o == 4:
        return img.mirrored(False, True)
    if o == 3:
        t.rotate(180)
    elif o == 6:
        t.rotate(90)
    elif o == 8:
        t.rotate(270)
    elif o == 5:
        img = img.mirrored(True, False)
        t.rotate(270)
    elif o == 7:
        img = img.mirrored(True, False)
        t.rotate(90)
    else:
        return img
    return img.transformed(t, Qt.TransformationMode.SmoothTransformation)


def decode_image(path, max_side=None):
    """Décode l'image (aperçu intégré pour les RAW). Thread-safe."""
    jpeg, orient, _ = get_source(path)
    ba = buf = None
    if jpeg is not None:
        ba = QByteArray(jpeg)
        buf = QBuffer(ba)
        buf.open(QIODevice.OpenModeFlag.ReadOnly)
        reader = QImageReader(buf)
    else:
        reader = QImageReader(path)
    reader.setAutoTransform(True)
    own = reader.transformation()
    has_own = bool(getattr(own, "value", own))
    size = reader.size()
    if max_side and size.isValid() and max(size.width(), size.height()) > max_side:
        reader.setScaledSize(size.scaled(max_side, max_side,
                                         Qt.AspectRatioMode.KeepAspectRatio))
    img = reader.read()
    if img.isNull():
        raise ValueError(reader.errorString() or "image illisible")
    if jpeg is not None and orient > 1 and not has_own:
        img = _apply_orient(img, orient)
    if max_side and max(img.width(), img.height()) > max_side:
        img = img.scaled(max_side, max_side, Qt.AspectRatioMode.KeepAspectRatio,
                         Qt.TransformationMode.SmoothTransformation)
    return img


def _thumb_cache_path(path):
    st = os.stat(path)
    key = hashlib.sha1(
        f"{path}|{st.st_mtime_ns}|{st.st_size}|{THUMB_MAX}".encode("utf-8", "replace")
    ).hexdigest()
    return CACHE_DIR / "thumbs" / key[:2] / f"{key}.jpg"


def load_thumb(path):
    cp = None
    try:
        cp = _thumb_cache_path(path)
        if cp.exists():
            img = QImage(str(cp))
            if not img.isNull():
                return img
    except Exception:
        cp = None
    img = decode_image(path, THUMB_MAX)
    if cp is not None:
        try:
            cp.parent.mkdir(parents=True, exist_ok=True)
            img.save(str(cp), "JPG", 85)
        except Exception:
            pass
    return img


# ---------------------------------------------------------------------------
# Retouche : réglages de tons, géométrie, rognage (numpy), noms de fichiers
# ---------------------------------------------------------------------------
# --- BEGIN IMGPROC
# Réglages « Développement » (approximations des curseurs de Lightroom, calculées avec numpy).
EDIT_DEFAULTS = {"temperature": 0, "tint": 0, "exposure": 0.0, "contrast": 0, "highlights": 0,
                 "shadows": 0, "whites": 0, "blacks": 0, "texture": 0, "clarity": 0, "dehaze": 0,
                 "vibrance": 0, "saturation": 0, "sharpness": 0, "noise": 0, "vignette": 0,
                 "bw": False}
CROP_FULL = [0.0, 0.0, 1.0, 1.0]


def edit_is_neutral(p):
    return all(p.get(k, v) == v for k, v in EDIT_DEFAULTS.items())


def dev_params(dev):
    """Tous les réglages (valeurs par défaut comprises) d'un dict « dev » (peut être None)."""
    p = dict(EDIT_DEFAULTS)
    if dev:
        for k, v in (dev.get("p") or {}).items():
            if k in p:
                p[k] = v
    return p


def dev_clean(p, ops=(), crop=None):
    """Dict « dev » minimal (seulement ce qui diffère du neutre), ou None si rien n'est modifié."""
    out = {}
    pp = {k: v for k, v in p.items() if k in EDIT_DEFAULTS and v != EDIT_DEFAULTS[k]}
    if pp:
        out["p"] = pp
    if ops:
        out["ops"] = list(ops)
    if crop and [round(float(x), 5) for x in crop] != CROP_FULL:
        out["crop"] = [round(float(x), 5) for x in crop]
    return out or None


def _bump(y, centre, width):
    return np.exp(-((y - centre) / width) ** 2)


def tone_luts(p):
    """Tableau (3, 256) uint8 : balance des blancs, exposition, noirs/blancs, ombres/hautes lumières,
    contraste et correction du voile (une table par canal R, V, B)."""
    x = np.arange(256, dtype=np.float32) / 255.0
    t = float(p.get("temperature", 0)) / 100.0
    ti = float(p.get("tint", 0)) / 100.0
    gains = (1.0 + 0.22 * t + 0.05 * ti, 1.0 - 0.10 * ti, 1.0 - 0.22 * t + 0.05 * ti)
    ev = float(p.get("exposure", 0.0))
    blacks = float(p.get("blacks", 0)) / 100.0
    whites = float(p.get("whites", 0)) / 100.0
    sh = float(p.get("shadows", 0)) / 100.0
    hl = float(p.get("highlights", 0)) / 100.0
    c = float(p.get("contrast", 0)) / 100.0
    dh = float(p.get("dehaze", 0)) / 100.0
    luts = []
    for g in gains:
        y = np.clip(x * g, 0.0, 1.0)
        if ev:
            y = np.clip(y ** 2.2 * (2.0 ** ev), 0.0, 1.0) ** (1.0 / 2.2)
        if blacks:
            lo = -blacks * 0.10
            y = np.clip((y - lo) / (1.0 - lo), 0.0, 1.0)
        if whites:
            y = np.clip(y / (1.0 - whites * 0.15), 0.0, 1.0)
        if sh:
            y = np.clip(y + sh * 0.32 * _bump(y, 0.25, 0.22), 0.0, 1.0)
        if hl:
            y = np.clip(y + hl * 0.32 * _bump(y, 0.78, 0.20), 0.0, 1.0)
        if c > 0:
            s = y * y * (3.0 - 2.0 * y)
            y = y + (s - y) * min(1.0, c * 1.3)
        elif c < 0:
            y = 0.5 + (y - 0.5) * (1.0 + 0.7 * c)
        if dh:
            lo = 0.10 * dh
            y = np.clip((y - lo) / (1.0 - lo), 0.0, 1.0)
        y = np.maximum.accumulate(np.clip(y, 0.0, 1.0))
        luts.append(np.round(y * 255.0).astype(np.uint8))
    return np.stack(luts)


def _rows(h, w, budget=2_000_000):
    return max(1, budget // max(1, w))


def _box_blur(a, r):
    """Flou moyen (carré de côté 2r+1) d'un tableau 2D float32, via sommes cumulées."""
    if r < 1:
        return a
    out = np.pad(a, ((r + 1, r), (r + 1, r)), mode="edge").astype(np.float64)
    out = np.cumsum(np.cumsum(out, axis=0), axis=1)
    k = 2 * r + 1
    h, w = a.shape
    s = out[k:k + h, k:k + w] - out[:h, k:k + w] - out[k:k + h, :w] + out[:h, :w]
    return (s / (k * k)).astype(np.float32)


def _blurred_luma(lum, radius):
    """Flou de la luminance à grand rayon, calculé sur une version réduite (rapide, peu de mémoire)."""
    h, w = lum.shape
    s = max(1, radius // 6)
    if s == 1:
        return _box_blur(_box_blur(lum, radius), max(1, radius // 2))
    h2, w2 = h // s, w // s
    if h2 < 2 or w2 < 2:
        return np.full_like(lum, float(lum.mean()))
    small = lum[:h2 * s, :w2 * s].reshape(h2, s, w2, s).mean(axis=(1, 3)).astype(np.float32)
    r = max(1, radius // s)
    small = _box_blur(_box_blur(small, r), max(1, r // 2))
    big = np.repeat(np.repeat(small, s, axis=0), s, axis=1)
    return np.pad(big, ((0, h - big.shape[0]), (0, w - big.shape[1])), mode="edge")


def local_contrast(arr, texture, clarity, dehaze=0.0):
    """Texture (détails fins) et clarté (contraste des tons moyens) : masque flou sur la luminance."""
    h, w, _ = arr.shape
    lum = (arr[..., 0] * 0.299 + arr[..., 1] * 0.587 + arr[..., 2] * 0.114).astype(np.float32)
    long_side = max(h, w)
    layers = []
    if texture:
        layers.append((float(texture) / 100.0, max(2, round(long_side * 0.0025)), False))
    if clarity or dehaze:
        layers.append(((float(clarity) + 0.5 * float(dehaze)) / 100.0, max(4, round(long_side * 0.015)), True))
    blurs = [(amt, _blurred_luma(lum, r), mid) for amt, r, mid in layers if amt]
    if not blurs:
        return arr
    out = np.empty_like(arr)
    step = _rows(h, w)
    for y0 in range(0, h, step):
        sl = slice(y0, min(h, y0 + step))
        l = lum[sl]
        delta = np.zeros_like(l)
        for amt, bl, mid in blurs:
            d = (l - bl[sl]) * amt * 1.4
            if mid:
                d = d * (1.0 - (2.0 * l / 255.0 - 1.0) ** 2 * 0.8)
            delta += d
        f = arr[sl].astype(np.float32) + delta[..., None]
        out[sl] = np.clip(f + 0.5, 0, 255).astype(np.uint8)
    return out


def _color_pass(arr, sat, vib):
    """Saturation (-1..1+) et vibrance (-1..1) : sat = -1 donne du noir et blanc."""
    h, w, _ = arr.shape
    out = np.empty_like(arr)
    step = _rows(h, w)
    for y0 in range(0, h, step):
        f = arr[y0:y0 + step].astype(np.float32)
        gray = (f[..., 0] * 0.299 + f[..., 1] * 0.587 + f[..., 2] * 0.114)[..., None]
        k = 1.0 + sat
        if vib:
            mx, mn = f.max(axis=-1), f.min(axis=-1)
            s = (mx - mn) / (mx + 1.0)
            k = k + vib * (1.0 - s)[..., None]
        out[y0:y0 + step] = np.clip(gray + (f - gray) * np.maximum(k, 0.0) + 0.5, 0, 255).astype(np.uint8)
    return out


def _neighbors(arr, fn, step_budget=1_000_000):
    """Applique fn(f, haut, bas, gauche, droite) -> uint8 par bandes (avec 1 ligne de recouvrement)."""
    h, w, _ = arr.shape
    if h < 3 or w < 3:
        return arr
    out = arr.copy()
    step = max(1, step_budget // max(1, w))
    for y0 in range(0, h, step):
        y1 = min(h, y0 + step)
        a, b = max(0, y0 - 1), min(h, y1 + 1)
        f = arr[a:b].astype(np.float32)
        pad = np.pad(f, ((1, 1), (1, 1), (0, 0)), mode="edge")
        res = fn(f, pad[:-2, 1:-1], pad[2:, 1:-1], pad[1:-1, :-2], pad[1:-1, 2:])
        out[y0:y1] = res[y0 - a:y0 - a + (y1 - y0)]
    return out


def sharpen(arr, amount):
    """Netteté (masque flou 3x3)."""
    if amount <= 0:
        return arr

    def fn(f, up, dn, lf, rt):
        blur = (4.0 * f + up + dn + lf + rt) / 8.0
        return np.clip(f + (f - blur) * (amount * 3.0) + 0.5, 0, 255).astype(np.uint8)
    return _neighbors(arr, fn)


def denoise(arr, amount):
    """Réduction du bruit de luminance (lissage léger, 0..1)."""
    if amount <= 0:
        return arr

    def fn(f, up, dn, lf, rt):
        mean = (f + up + dn + lf + rt) / 5.0
        return np.clip(f + (mean - f) * min(1.0, amount) * 0.85 + 0.5, 0, 255).astype(np.uint8)
    return _neighbors(arr, fn)


def vignette(arr, amount):
    """Vignetage (-1 assombrit les bords, +1 les éclaircit)."""
    if not amount:
        return arr
    h, w, _ = arr.shape
    out = np.empty_like(arr)
    xs = ((np.arange(w, dtype=np.float32) + 0.5) / w * 2.0 - 1.0) ** 2
    step = _rows(h, w)
    for y0 in range(0, h, step):
        y1 = min(h, y0 + step)
        ys = ((np.arange(y0, y1, dtype=np.float32) + 0.5) / h * 2.0 - 1.0) ** 2
        r = np.sqrt(ys[:, None] + xs[None, :]) / 1.4142
        t = np.clip((r - 0.35) / 0.65, 0.0, 1.0)
        fall = (t * t * (3.0 - 2.0 * t))[..., None]
        f = arr[y0:y1].astype(np.float32)
        if amount < 0:
            f = f * (1.0 + amount * 0.9 * fall)
        else:
            f = f + (255.0 - f) * (amount * 0.6 * fall)
        out[y0:y1] = np.clip(f + 0.5, 0, 255).astype(np.uint8)
    return out


def apply_tone(arr, p):
    """arr : uint8 (h, w, 3) -> tableau uint8 avec les réglages appliqués (arr n'est pas modifié)."""
    if edit_is_neutral(p):
        return arr
    h, w, _ = arr.shape
    cur = arr
    if any(p.get(k, 0) for k in ("exposure", "contrast", "temperature", "tint", "highlights",
                                  "shadows", "whites", "blacks", "dehaze")):
        luts = tone_luts(p)
        cur = np.empty_like(arr)
        step = _rows(h, w)
        for y0 in range(0, h, step):
            blk = arr[y0:y0 + step]
            cur[y0:y0 + step] = np.stack(
                [luts[0][blk[..., 0]], luts[1][blk[..., 1]], luts[2][blk[..., 2]]], axis=-1)
    if p.get("texture", 0) or p.get("clarity", 0) or p.get("dehaze", 0):
        cur = local_contrast(cur, p.get("texture", 0), p.get("clarity", 0), p.get("dehaze", 0))
    sat = -1.0 if p.get("bw") else (float(p.get("saturation", 0)) + 0.25 * float(p.get("dehaze", 0))) / 100.0
    vib = 0.0 if p.get("bw") else float(p.get("vibrance", 0)) / 100.0
    if sat or vib:
        cur = _color_pass(cur, sat, vib)
    if p.get("noise", 0):
        cur = denoise(cur, float(p["noise"]) / 100.0)
    if p.get("sharpness", 0):
        cur = sharpen(cur, float(p["sharpness"]) / 150.0)
    if p.get("vignette", 0):
        cur = vignette(cur, float(p["vignette"]) / 100.0)
    return cur


def apply_geometry(arr, ops):
    """ops : suite de 'r' (quart de tour horaire), 'l' (anti-horaire), 'h' / 'v' (miroirs)."""
    for op in ops:
        if op == "r":
            arr = np.rot90(arr, -1)
        elif op == "l":
            arr = np.rot90(arr, 1)
        elif op == "h":
            arr = arr[:, ::-1]
        elif op == "v":
            arr = arr[::-1]
    return np.ascontiguousarray(arr)


def rect_after(rect, op):
    """Rectangle normalisé (g, h, d, b) -> même zone de l'image après l'opération op."""
    l, t, r, b = rect
    if op == "r":
        return (1 - b, l, 1 - t, r)
    if op == "l":
        return (t, 1 - r, b, 1 - l)
    if op == "h":
        return (1 - r, t, 1 - l, b)
    if op == "v":
        return (l, 1 - b, r, 1 - t)
    return rect


def crop_array(arr, rect):
    h, w = arr.shape[:2]
    l = min(max(int(round(rect[0] * w)), 0), w - 1)
    t = min(max(int(round(rect[1] * h)), 0), h - 1)
    r = min(max(int(round(rect[2] * w)), l + 1), w)
    b = min(max(int(round(rect[3] * h)), t + 1), h)
    return np.ascontiguousarray(arr[t:b, l:r])


def render_dev(arr, dev, with_crop=True, with_tone=True):
    """Image développée : géométrie, recadrage puis réglages (arr = image d'origine, uint8 h x l x 3)."""
    dev = dev or {}
    out = apply_geometry(arr, dev.get("ops") or [])
    crop = dev.get("crop")
    if with_crop and crop and [round(x, 5) for x in crop] != CROP_FULL:
        out = crop_array(out, crop)
    if with_tone:
        out = apply_tone(out, dev_params(dev))
    return out


def auto_tone(arr):
    """Réglages automatiques (exposition, noirs, blancs) d'après les percentiles de la luminance."""
    sub = arr[::max(1, arr.shape[0] // 400), ::max(1, arr.shape[1] // 400)]
    lum = sub[..., 0] * 0.299 + sub[..., 1] * 0.587 + sub[..., 2] * 0.114
    lo, med, hi = (float(v) / 255.0 for v in np.percentile(lum, (0.5, 50, 99.5)))
    blacks = int(max(-60, min(30, -lo * 1000.0)))
    whites = int(max(-30, min(60, (1.0 - hi) / 0.15 * 100.0)))
    m = min(0.95, max(0.02, (med - (-blacks / 100.0 * 0.10)) / (1.0 + blacks / 100.0 * 0.10)))
    m = min(0.95, m / max(0.3, 1.0 - whites / 100.0 * 0.15))
    ev = max(-2.0, min(2.0, 2.2 * float(np.log2(0.45 / max(m, 0.02))) * 0.6))
    return {"exposure": round(ev, 2), "blacks": blacks, "whites": whites}
# --- END IMGPROC


# --- BEGIN NAMES
_WIN_RESERVED = {"CON", "PRN", "AUX", "NUL"} | {f"COM{i}" for i in range(1, 10)} \
    | {f"LPT{i}" for i in range(1, 10)}


def check_new_stem(stem):
    """Message d'erreur si `stem` n'est pas un nom de fichier valide, sinon None."""
    if not stem:
        return "Le nom ne peut pas être vide."
    bad = sorted({c for c in stem if c in '<>:"/\\|?*' or ord(c) < 32})
    if bad:
        return "Caractères interdits dans un nom de fichier : " + " ".join(bad)
    if stem != stem.rstrip(". "):
        return "Le nom ne peut pas se terminer par un point ou une espace."
    if stem.split(".")[0].upper() in _WIN_RESERVED:
        return "Ce nom est réservé par Windows."
    if len(stem) > 180:
        return "Ce nom est trop long."
    return None


def plan_rename(photo_files, old_stem, new_stem):
    """[(ancien chemin, nouveau chemin)] : renomme aussi les fichiers associés (xmp, jpg…)."""
    plan = []
    for fp in photo_files:
        d, n = os.path.split(fp)
        plan.append((fp, os.path.join(d, new_stem + n[len(old_stem):])))
    return plan
# --- END NAMES


def qimage_to_array(img):
    img = img.convertToFormat(QImage.Format.Format_RGB888)
    w, h, bpl = img.width(), img.height(), img.bytesPerLine()
    buf = np.frombuffer(img.constBits(), dtype=np.uint8, count=bpl * h)
    return buf.reshape(h, bpl)[:, :w * 3].reshape(h, w, 3).copy()


def array_to_qimage(arr):
    arr = np.ascontiguousarray(arr)
    h, w, _ = arr.shape
    return QImage(arr.data, w, h, w * 3, QImage.Format.Format_RGB888).copy()


# ---------------------------------------------------------------------------
# Données : photos, notes/drapeaux, dossier
# ---------------------------------------------------------------------------
LABELS = [None, ("Rouge", "#e5484d"), ("Jaune", "#f5c542"), ("Vert", "#3ecf8e"),
          ("Bleu", "#4f8cff"), ("Violet", "#a77bff")]


class Photo:
    __slots__ = ("path", "rel", "name", "mtime", "rating", "flag", "edited", "label")

    def __init__(self, path, rel, mtime):
        self.path = path
        self.rel = rel
        self.name = os.path.basename(path)
        self.mtime = mtime
        self.rating = 0
        self.flag = NO_FLAG
        self.edited = False
        self.label = 0


def scan_folder(root: str, recursive: bool):
    groups = {}
    stack = [root]
    while stack:
        d = stack.pop()
        try:
            it = os.scandir(d)
        except OSError:
            continue
        with it:
            for e in it:
                try:
                    if e.is_dir(follow_symlinks=False):
                        if recursive and not e.name.startswith("."):
                            stack.append(e.path)
                        continue
                    if not e.is_file():
                        continue
                    stem, ext = os.path.splitext(e.name)
                    ext = ext.lower()
                    is_raw = ext in RAW_EXTS
                    if not (is_raw or ext in IMG_EXTS):
                        continue
                    key = (d, stem.lower())
                    cur = groups.get(key)
                    # RAW + JPG du même nom : on n'affiche que le RAW
                    if cur is None or (is_raw and not cur[0]):
                        groups[key] = (is_raw, e.path, e.stat().st_mtime)
                except OSError:
                    continue
    photos = []
    for is_raw, p, mt in groups.values():
        rel = os.path.relpath(p, root).replace("\\", "/")
        photos.append(Photo(p, rel, mt))
    return photos


class Store:
    """Notes et drapeaux, sauvegardés à côté des photos (JSON)."""

    def __init__(self):
        self.root = None
        self.data = {}
        self.dirty = False
        self.timer = QTimer()
        self.timer.setSingleShot(True)
        self.timer.setInterval(600)
        self.timer.timeout.connect(self.flush)

    def _files(self):
        h = hashlib.sha1(str(self.root).encode("utf-8", "replace")).hexdigest()[:16]
        return [Path(self.root) / SIDECAR_NAME, CACHE_DIR / f"meta_{h}.json"]

    def load(self, root):
        self.flush()
        self.root = root
        self.data = {}
        for fp in self._files():
            try:
                with open(fp, "r", encoding="utf-8") as f:
                    self.data = json.load(f).get("photos", {})
                break
            except Exception:
                continue

    def get(self, rel):
        d = self.data.get(rel)
        if not d:
            return 0, NO_FLAG
        flag = {"pick": PICK, "reject": REJECT}.get(d.get("flag"), NO_FLAG)
        return int(d.get("rating", 0)), flag

    def set(self, rel, rating, flag):
        e = {}
        if rating:
            e["rating"] = rating
        if flag:
            e["flag"] = "pick" if flag == PICK else "reject"
        old = self.data.get(rel) or {}
        if old.get("dev"):
            e["dev"] = old["dev"]
        if old.get("label"):
            e["label"] = old["label"]
        if e:
            self.data[rel] = e
        else:
            self.data.pop(rel, None)
        self.dirty = True
        self.timer.start()

    def get_label(self, rel):
        v = (self.data.get(rel) or {}).get("label", 0)
        return v if isinstance(v, int) and 0 < v < len(LABELS) else 0

    def set_label(self, rel, label):
        e = dict(self.data.get(rel) or {})
        if label:
            e["label"] = int(label)
        else:
            e.pop("label", None)
        if e:
            self.data[rel] = e
        else:
            self.data.pop(rel, None)
        self.dirty = True
        self.timer.start()

    def get_dev(self, rel):
        d = (self.data.get(rel) or {}).get("dev")
        return d if isinstance(d, dict) and d else None

    def set_dev(self, rel, dev):
        """Réglages de développement de la photo (None = aucun). Les notes et drapeaux sont conservés."""
        e = dict(self.data.get(rel) or {})
        if dev:
            e["dev"] = dev
        else:
            e.pop("dev", None)
        if e:
            self.data[rel] = e
        else:
            self.data.pop(rel, None)
        self.dirty = True
        self.timer.start()

    def entry(self, rel):
        return dict(self.data.get(rel) or {})

    def rename(self, old, new):
        if old in self.data:
            self.data[new] = self.data.pop(old)
            self.dirty = True
            self.timer.start()

    def forget(self, rels):
        for r in rels:
            self.data.pop(r, None)
        self.dirty = True
        self.timer.start()

    def flush(self):
        if not self.dirty or not self.root:
            return
        payload = json.dumps({"version": 1, "photos": self.data},
                             ensure_ascii=False, indent=1)
        for fp in self._files():
            try:
                fp.parent.mkdir(parents=True, exist_ok=True)
                with open(fp, "w", encoding="utf-8") as f:
                    f.write(payload)
                self.dirty = False
                return
            except OSError:
                continue


def _natural(s):
    return [int(t) if t.isdigit() else t.lower() for t in re.split(r"(\d+)", s)]


# ---------------------------------------------------------------------------
# Modèle (liste filtrée/triée) + chargement asynchrone des vignettes
# ---------------------------------------------------------------------------
class _ThumbSignals(QObject):
    done = Signal(str, QImage)


class _ThumbJob(QRunnable):
    def __init__(self, path, signals):
        super().__init__()
        self.path = path
        self.signals = signals

    def run(self):
        try:
            img = load_thumb(self.path)
        except Exception:
            img = QImage()
        try:
            self.signals.done.emit(self.path, img)
        except RuntimeError:
            pass


class PhotoModel(QAbstractListModel):
    def __init__(self, pool):
        super().__init__()
        self.pool = pool
        self.all = []
        self.vis = []
        self.row_of = {}
        self.sort_key = "name"
        self.flag_filter = "all"
        self.min_rating = 0
        self.rating_eq = None
        self.label_filter = set()
        self.name_filter = ""
        self._thumbs = OrderedDict()
        self._pending = set()
        self._failed = set()
        self._counter = 0
        self._born = {}                       # chemin -> instant d'arrivée de la vignette (fondu)
        self._fade_timer = QTimer()
        self._fade_timer.setInterval(30)
        self._fade_timer.timeout.connect(self._fade_tick)
        self.sig = _ThumbSignals()
        self.sig.done.connect(self._on_done)

    # --- API Qt
    def rowCount(self, parent=QModelIndex()):
        return 0 if parent.isValid() else len(self.vis)

    def data(self, index, role=Qt.ItemDataRole.DisplayRole):
        if not index.isValid():
            return None
        ph = self.vis[index.row()]
        if role == Qt.ItemDataRole.DisplayRole:
            return ph.name
        if role == Qt.ItemDataRole.ToolTipRole:
            return ph.path
        return None

    # --- données
    def photo(self, row):
        return self.vis[row]

    def set_photos(self, photos):
        self.all = photos
        self._thumbs.clear()
        self._pending.clear()
        self._failed.clear()
        self.rebuild()

    def rebuild(self):
        def keep(p):
            if self.name_filter and self.name_filter not in p.name.lower():
                return False
            if self.flag_filter == "pick" and p.flag != PICK:
                return False
            if self.flag_filter == "reject" and p.flag != REJECT:
                return False
            if self.flag_filter == "none" and p.flag != NO_FLAG:
                return False
            if self.flag_filter == "notreject" and p.flag == REJECT:
                return False
            if self.rating_eq is not None and p.rating != self.rating_eq:
                return False
            if self.label_filter and p.label not in self.label_filter:
                return False
            return p.rating >= self.min_rating

        vis = [p for p in self.all if keep(p)]
        k = self.sort_key
        if k == "date_asc":
            vis.sort(key=lambda p: (p.mtime, _natural(p.name)))
        elif k == "date_desc":
            vis.sort(key=lambda p: (-p.mtime, _natural(p.name)))
        elif k == "rating":
            vis.sort(key=lambda p: (-p.rating, _natural(p.name)))
        elif k == "rating_asc":
            vis.sort(key=lambda p: (p.rating, _natural(p.name)))
        else:
            vis.sort(key=lambda p: _natural(p.name))
        self.beginResetModel()
        self.vis = vis
        self.row_of = {p.path: i for i, p in enumerate(vis)}
        self.endResetModel()

    def refresh_rows(self, rows):
        for r in rows:
            ix = self.index(r)
            self.dataChanged.emit(ix, ix)

    def remove_paths(self, paths):
        ps = set(paths)
        self.all = [p for p in self.all if p.path not in ps]
        for p in ps:
            self._thumbs.pop(p, None)
        self.rebuild()

    def counts(self):
        picks = sum(1 for p in self.all if p.flag == PICK)
        rejects = sum(1 for p in self.all if p.flag == REJECT)
        return len(self.all), picks, rejects

    # --- vignettes
    def thumb_for(self, ph):
        pm = self._thumbs.get(ph.path)
        if pm is not None:
            self._thumbs.move_to_end(ph.path)
            return pm
        if ph.path not in self._pending and ph.path not in self._failed:
            self._pending.add(ph.path)
            self._counter += 1
            # les demandes les plus récentes (= ce qu'on voit) passent en premier
            self.pool.start(_ThumbJob(ph.path, self.sig), self._counter)
        return None

    def has_failed(self, ph):
        return ph.path in self._failed

    FADE = 0.28   # durée du fondu d'une vignette (s)

    def thumb_alpha(self, path):
        t = self._born.get(path)
        if t is None:
            return 1.0
        a = (time.monotonic() - t) / self.FADE
        return 1.0 if a >= 1.0 else max(0.0, a)

    def _fade_tick(self):
        now = time.monotonic()
        for path in list(self._born):
            row = self.row_of.get(path)
            if row is not None:
                ix = self.index(row)
                self.dataChanged.emit(ix, ix)
            if now - self._born[path] >= self.FADE:
                self._born.pop(path, None)
        if not self._born:
            self._fade_timer.stop()

    def rekey(self, old, ph):
        """La photo a changé de nom : on garde sa vignette et sa place."""
        pm = self._thumbs.pop(old, None)
        if pm is not None:
            self._thumbs[ph.path] = pm
        self._pending.discard(old)
        self._failed.discard(old)
        r = self.row_of.pop(old, None)
        if r is not None:
            self.row_of[ph.path] = r
            ix = self.index(r)
            self.dataChanged.emit(ix, ix)

    def _on_done(self, path, img):
        self._pending.discard(path)
        if img.isNull():
            self._failed.add(path)
        else:
            self._thumbs[path] = QPixmap.fromImage(img)
            while len(self._thumbs) > THUMB_LRU:
                self._thumbs.popitem(last=False)
            if ANIM["on"]:
                self._born[path] = time.monotonic()
                if not self._fade_timer.isActive():
                    self._fade_timer.start()
        row = self.row_of.get(path)
        if row is not None:
            ix = self.index(row)
            self.dataChanged.emit(ix, ix)


# ---------------------------------------------------------------------------
# Dessin des vignettes
# ---------------------------------------------------------------------------
ACCENT = QColor("#6d8cff")
CARD = QColor("#1c1e26")
CARD_HOVER = QColor("#242734")
GOLD = QColor("#ffc857")
GREEN = QColor("#3ecf8e")
RED = QColor("#ff5d6c")


def star_polygon(cx, cy, r):
    pts = []
    for i in range(10):
        a = -math.pi / 2 + i * math.pi / 5
        rad = r if i % 2 == 0 else r * 0.45
        pts.append(QPointF(cx + rad * math.cos(a), cy + rad * math.sin(a)))
    return QPolygonF(pts)


def draw_stars(p: QPainter, x, cy, r, rating, gap=2):
    p.save()
    p.setPen(Qt.PenStyle.NoPen)
    for i in range(5):
        cx = x + r + i * (2 * r + gap)
        p.setBrush(GOLD if i < rating else QColor(PAL["star_off"]))
        p.drawPolygon(star_polygon(cx, cy, r))
    p.restore()


def draw_flag_badge(p: QPainter, cx, cy, flag, d=22):
    p.save()
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    col = GREEN if flag == PICK else RED
    p.setPen(Qt.PenStyle.NoPen)
    p.setBrush(col)
    p.drawEllipse(QPointF(cx, cy), d / 2, d / 2)
    pen = QPen(QColor("white"), max(1.6, d / 9))
    pen.setCapStyle(Qt.PenCapStyle.RoundCap)
    pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
    p.setPen(pen)
    s = d * 0.2
    if flag == PICK:
        p.drawPolyline(QPolygonF([QPointF(cx - s * 1.1, cy), QPointF(cx - s * 0.2, cy + s * 0.9),
                                  QPointF(cx + s * 1.2, cy - s * 0.9)]))
    else:
        p.drawLine(QPointF(cx - s, cy - s), QPointF(cx + s, cy + s))
        p.drawLine(QPointF(cx - s, cy + s), QPointF(cx + s, cy - s))
    p.restore()


def draw_edit_badge(p: QPainter, x, y):
    """Petit pictogramme « réglages » (photo retouchée) dont le coin haut-gauche est en (x, y)."""
    p.save()
    p.setPen(Qt.PenStyle.NoPen)
    p.setBrush(QColor(0, 0, 0, 150))
    p.drawRoundedRect(QRectF(x, y, 24, 20), 6, 6)
    p.setPen(QPen(QColor(255, 255, 255, 235), 1.4))
    for i, k in enumerate((0.7, 0.3, 0.6)):
        yy = y + 5 + i * 5
        p.drawLine(QPointF(x + 5, yy), QPointF(x + 19, yy))
        p.setBrush(QColor(255, 255, 255))
        p.drawEllipse(QPointF(x + 5 + 14 * k, yy), 1.9, 1.9)
    p.restore()


def draw_thumb(p: QPainter, pm, rect: QRect, radius, dim=False, alpha=1.0):
    """Dessine la vignette en « cover » (remplit le cadre), coins arrondis."""
    path = QPainterPath()
    path.addRoundedRect(float(rect.x()), float(rect.y()), float(rect.width()),
                        float(rect.height()), radius, radius)
    p.save()
    p.setClipPath(path)
    p.fillRect(rect, QColor(PAL["thumb_bg"]))
    if pm is not None and not pm.isNull():
        s = pm.size().scaled(rect.size(), Qt.AspectRatioMode.KeepAspectRatioByExpanding)
        target = QRect(0, 0, s.width(), s.height())
        target.moveCenter(rect.center())
        p.setOpacity((0.28 if dim else 1.0) * alpha)
        p.drawPixmap(target, pm)
        p.setOpacity(1.0)
    p.restore()


class PhotoDelegate(QStyledItemDelegate):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.cell = 220
        self.hover = None   # (ligne, nb d'étoiles) survolées

    def set_cell(self, v):
        self.cell = v

    def star_at(self, item_rect, pos):
        """Étoile (1 à 5) située sous la souris dans la carte, 0 si aucune."""
        r = item_rect.adjusted(6, 6, -6, -6)
        x0 = r.left() + 10
        cy = r.bottom() - 11
        if not (cy - 9 <= pos.y() <= cy + 10):
            return 0
        k = int((pos.x() - (x0 - STAR_GAP / 2)) // (2 * STAR_R + STAR_GAP))
        return k + 1 if 0 <= k < 5 else 0

    def item_size(self):
        return QSize(self.cell + 14, int(self.cell * 0.72) + 14 + 40)

    def sizeHint(self, option, index):
        return self.item_size()

    def paint(self, p, opt, index):
        model = index.model()
        ph = model.photo(index.row())
        r = opt.rect.adjusted(6, 6, -6, -6)
        sel = bool(opt.state & QStyle.StateFlag.State_Selected)
        hov = bool(opt.state & QStyle.StateFlag.State_MouseOver)
        p.save()
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        p.setBrush(CARD_HOVER if (sel or hov) else CARD)
        p.setPen(QPen(ACCENT, 2) if sel else Qt.PenStyle.NoPen)
        p.drawRoundedRect(r, 10, 10)

        img_rect = QRect(r.left() + 5, r.top() + 5, r.width() - 10, r.height() - 10 - 36)
        pm = model.thumb_for(ph)
        draw_thumb(p, pm, img_rect, 7, dim=(ph.flag == REJECT), alpha=model.thumb_alpha(ph.path))
        if pm is None:
            p.setPen(QColor(PAL["ph_text"]))
            txt = "illisible" if model.has_failed(ph) else "…"
            p.drawText(img_rect, Qt.AlignmentFlag.AlignCenter, txt)

        f = QFont(p.font())
        f.setPointSizeF(max(8.0, f.pointSizeF() * 0.92))
        p.setFont(f)
        p.setPen(QColor(PAL["text"]) if ph.flag != REJECT else QColor(PAL["text_dim"]))
        fm = QFontMetrics(f)
        name_rect = QRect(r.left() + 10, r.bottom() - 33, r.width() - 20, 15)
        p.drawText(name_rect, Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter,
                   fm.elidedText(ph.name, Qt.TextElideMode.ElideMiddle, name_rect.width()))
        shown = ph.rating
        if self.hover and self.hover[0] == index.row():
            shown = self.hover[1]
        draw_stars(p, r.left() + 10, r.bottom() - 11, STAR_R, shown, gap=STAR_GAP)
        if ph.label:
            p.setPen(QPen(QColor(0, 0, 0, 120), 1))
            p.setBrush(QColor(LABELS[ph.label][1]))
            p.drawEllipse(QPointF(r.right() - 16, r.bottom() - 11), 6, 6)
        if ph.flag != NO_FLAG:
            draw_flag_badge(p, img_rect.right() - 14, img_rect.top() + 16, ph.flag)
        if ph.edited:
            draw_edit_badge(p, img_rect.left() + 6, img_rect.top() + 6)
        p.restore()


class GridView(QListView):
    """Grille de vignettes : les étoiles de chaque carte sont cliquables."""
    star_clicked = Signal(int, int)   # ligne, nombre d'étoiles

    def _star_hit(self, e):
        pos = e.position().toPoint()
        ix = self.indexAt(pos)
        if not ix.isValid():
            return None
        n = self.itemDelegate().star_at(self.visualRect(ix), pos)
        return (ix.row(), n) if n else None

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            hit = self._star_hit(e)
            if hit:
                self.star_clicked.emit(hit[0], hit[1])
                e.accept()
                return
        super().mousePressEvent(e)

    def mouseDoubleClickEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            hit = self._star_hit(e)
            if hit:
                self.star_clicked.emit(hit[0], hit[1])
                e.accept()
                return
        super().mouseDoubleClickEvent(e)

    def _repaint_row(self, row):
        m = self.model()
        if m is not None and 0 <= row < m.rowCount():
            self.viewport().update(self.visualRect(m.index(row)))

    def mouseMoveEvent(self, e):
        d = self.itemDelegate()
        hit = self._star_hit(e)
        if hit != d.hover:
            old, d.hover = d.hover, hit
            for h in (old, hit):
                if h:
                    self._repaint_row(h[0])
            self.viewport().setCursor(Qt.CursorShape.PointingHandCursor if hit
                                      else Qt.CursorShape.ArrowCursor)
        super().mouseMoveEvent(e)

    def leaveEvent(self, e):
        d = self.itemDelegate()
        if d.hover:
            old, d.hover = d.hover, None
            self._repaint_row(old[0])
        self.viewport().setCursor(Qt.CursorShape.ArrowCursor)
        super().leaveEvent(e)


class FilmDelegate(QStyledItemDelegate):
    """Petites vignettes de la bande sous la visionneuse."""
    W, H = 104, 74

    def sizeHint(self, option, index):
        return QSize(self.W, self.H)

    def paint(self, p, opt, index):
        model = index.model()
        ph = model.photo(index.row())
        r = opt.rect.adjusted(3, 3, -3, -3)
        cur = bool(opt.state & QStyle.StateFlag.State_Selected)
        p.save()
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        draw_thumb(p, model.thumb_for(ph), r, 6, dim=(ph.flag == REJECT))
        if cur:
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.setPen(QPen(ACCENT, 3))
            p.drawRoundedRect(r.adjusted(1, 1, -1, -1), 6, 6)
        if ph.flag != NO_FLAG:
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(GREEN if ph.flag == PICK else RED)
            p.drawRoundedRect(QRect(r.left() + 6, r.bottom() - 7, r.width() - 12, 3), 1.5, 1.5)
        p.restore()


# ---------------------------------------------------------------------------
# Visionneuse (zoom / déplacement)
# ---------------------------------------------------------------------------
class ImageView(QGraphicsView):
    view_changed = Signal()

    def __init__(self):
        super().__init__()
        self.locked = False
        self._scene = QGraphicsScene(self)
        self.setScene(self._scene)
        self._item = QGraphicsPixmapItem()
        self._item.setTransformationMode(Qt.TransformationMode.SmoothTransformation)
        self._scene.addItem(self._item)
        self.setRenderHints(QPainter.RenderHint.SmoothPixmapTransform |
                            QPainter.RenderHint.Antialiasing)
        self.setDragMode(QGraphicsView.DragMode.ScrollHandDrag)
        self.setTransformationAnchor(QGraphicsView.ViewportAnchor.AnchorUnderMouse)
        self.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.setFrameShape(QFrame.Shape.NoFrame)
        self.setBackgroundBrush(QColor(PAL["stage"]))
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.fit = True
        self.guides = 0
        self._has = False
        self.horizontalScrollBar().valueChanged.connect(lambda *_: self.view_changed.emit())
        self.verticalScrollBar().valueChanged.connect(lambda *_: self.view_changed.emit())

    def clear(self):
        self._item.setPixmap(QPixmap())
        self._has = False
        self.view_changed.emit()

    def set_pixmap(self, pm: QPixmap, logical=None, keep_view=False):
        """logical = (l, h) : taille « réelle » représentée, pour que le zoom reste le même quand
        on remplace un aperçu réduit par l'image pleine définition."""
        self._item.setPixmap(pm)
        if logical and not pm.isNull() and pm.width():
            self._item.setScale(logical[0] / pm.width())
        else:
            self._item.setScale(1.0)
        self._scene.setSceneRect(self._item.sceneBoundingRect())
        self._has = not pm.isNull()
        if self.fit or not keep_view:
            self.fit_view()
        self.view_changed.emit()

    def set_image(self, img: QImage):
        self.set_pixmap(QPixmap.fromImage(img))

    def current_pixmap(self):
        return self._item.pixmap()

    def item_rect(self):
        return self._item.sceneBoundingRect()

    def drawForeground(self, p, rect):
        super().drawForeground(p, rect)
        if not self.guides or not self._has:
            return
        r = self.item_rect()
        pen = QPen(QColor(255, 255, 255, 150), 1)
        pen.setCosmetic(True)
        p.setPen(pen)
        x0, y0, w, h = r.x(), r.y(), r.width(), r.height()
        if self.guides == 1:
            for k in (1, 2):
                p.drawLine(QPointF(x0 + w * k / 3, y0), QPointF(x0 + w * k / 3, y0 + h))
                p.drawLine(QPointF(x0, y0 + h * k / 3), QPointF(x0 + w, y0 + h * k / 3))
        elif self.guides == 2:
            for k in range(1, 6):
                p.drawLine(QPointF(x0 + w * k / 6, y0), QPointF(x0 + w * k / 6, y0 + h))
                p.drawLine(QPointF(x0, y0 + h * k / 6), QPointF(x0 + w, y0 + h * k / 6))
        else:
            p.drawLine(QPointF(x0, y0), QPointF(x0 + w, y0 + h))
            p.drawLine(QPointF(x0 + w, y0), QPointF(x0, y0 + h))
            p.drawLine(QPointF(x0 + w / 2, y0), QPointF(x0 + w / 2, y0 + h))
            p.drawLine(QPointF(x0, y0 + h / 2), QPointF(x0 + w, y0 + h / 2))

    def fit_view(self):
        self.resetTransform()
        if self._has:
            self.fitInView(self._item, Qt.AspectRatioMode.KeepAspectRatio)
        self.fit = True
        self.view_changed.emit()

    def fill_view(self):
        """Zoom pour que l'image remplisse toute la zone (les bords dépassent)."""
        if not self._has:
            return
        self.resetTransform()
        r = self.item_rect()
        vp = self.viewport().size()
        s = max(vp.width() / max(1.0, r.width()), vp.height() / max(1.0, r.height()))
        self.scale(s, s)
        self.centerOn(r.center())
        self.fit = False
        self.view_changed.emit()

    def zoom_to(self, s):
        if not self._has:
            return
        self.resetTransform()
        self.scale(s, s)
        self.centerOn(self.item_rect().center())
        self.fit = False
        self.view_changed.emit()

    def actual_size(self, center=None):
        if not self._has:
            return
        self.resetTransform()
        self.fit = False
        self.centerOn(center if center is not None else self.item_rect().center())
        self.view_changed.emit()

    def toggle_zoom(self, pos=None):
        if self.fit:
            c = self.mapToScene(pos) if pos is not None else None
            self.actual_size(c)
        else:
            self.fit_view()

    def resizeEvent(self, e):
        super().resizeEvent(e)
        if self.fit:
            self.fit_view()
        self.view_changed.emit()

    def wheelEvent(self, e):
        if not self._has or self.locked:
            return
        steps = e.angleDelta().y() / 120.0
        if steps == 0:
            return
        factor = 1.25 ** steps
        cur = self.transform().m11()
        new = cur * factor
        if new < 0.02 or new > 16:
            return
        self.fit = False
        self.scale(factor, factor)
        self.view_changed.emit()

    def mouseDoubleClickEvent(self, e):
        if not self.locked:
            self.toggle_zoom(e.position().toPoint())


class _ViewSignals(QObject):
    ready = Signal(str, QImage)


class _ViewJob(QRunnable):
    def __init__(self, path, signals):
        super().__init__()
        self.path = path
        self.signals = signals

    def run(self):
        try:
            img = decode_image(self.path)
        except Exception:
            img = QImage()
        try:
            self.signals.ready.emit(self.path, img)
        except RuntimeError:
            pass


def _fmt_shutter(s):
    if not s:
        return None
    if s >= 1:
        return f"{s:g} s"
    return f"1/{round(1 / s)} s"


def meta_line(meta):
    parts = []
    if meta.get("camera"):
        parts.append(meta["camera"])
    if meta.get("lens"):
        parts.append(meta["lens"])
    if meta.get("focal"):
        parts.append(f"{meta['focal']:.0f} mm")
    if meta.get("aperture"):
        parts.append(f"f/{meta['aperture']:.1f}")
    sh = _fmt_shutter(meta.get("shutter"))
    if sh:
        parts.append(sh)
    if meta.get("iso"):
        parts.append(f"ISO {meta['iso']}")
    d = meta.get("dims")
    if d and d[0] and d[1]:
        parts.append(f"{d[0]}×{d[1]}")
    if meta.get("date"):
        parts.append(meta["date"].replace(":", "/", 2))
    return "  ·  ".join(parts)


class HistogramWidget(QWidget):
    """Histogramme RVB + alerte hautes lumières / ombres bouchées."""

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setFixedHeight(124)
        self.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents, True)
        self.bins = None
        self.hi = 0.0
        self.lo = 0.0

    def set_image(self, img):
        self.bins = None
        try:
            small = img.scaled(160, 160, Qt.AspectRatioMode.KeepAspectRatio,
                               Qt.TransformationMode.FastTransformation)
            small = small.convertToFormat(QImage.Format.Format_RGB32)
            n = small.width() * small.height()
            bits = small.constBits()
            try:
                data = bytes(bits)
            except TypeError:
                data = bits.asstring(small.sizeInBytes())
            data = data[:n * 4]
            chans = []
            for off in (2, 1, 0):  # R, G, B (mémoire : B G R A)
                ch = data[off::4]
                cnt = [0] * 64
                for v, c in Counter(ch).items():
                    cnt[v >> 2] += c
                chans.append(cnt)
            r, g, b = data[2::4], data[1::4], data[0::4]
            hi = sum(1 for x, y, z in zip(r, g, b) if x >= 250 or y >= 250 or z >= 250)
            lo = sum(1 for x, y, z in zip(r, g, b) if x <= 5 and y <= 5 and z <= 5)
            self.hi = 100.0 * hi / max(1, n)
            self.lo = 100.0 * lo / max(1, n)
            self.bins = chans
        except Exception:
            self.bins = None
        self.update()

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor(*PAL["hist_bg"]))
        p.drawRoundedRect(self.rect(), 12, 12)
        if not self.bins:
            return
        area = QRect(12, 10, self.width() - 24, self.height() - 38)
        peak = max(1, max(max(c[1:63]) if len(c) > 2 else max(c) for c in self.bins))
        colors = [QColor(255, 90, 100, 130), QColor(80, 220, 140, 130), QColor(100, 140, 255, 130)]
        for cnt, col in zip(self.bins, colors):
            pts = [QPointF(area.left(), area.bottom())]
            for i, c in enumerate(cnt):
                x = area.left() + area.width() * i / 63.0
                h = min(1.0, c / peak) * area.height()
                pts.append(QPointF(x, area.bottom() - h))
            pts.append(QPointF(area.right(), area.bottom()))
            p.setBrush(col)
            p.drawPolygon(QPolygonF(pts))
        f = QFont(p.font())
        f.setPointSizeF(8.0)
        p.setFont(f)
        y = self.height() - 22
        p.setPen(RED if self.hi > 1.0 else QColor(PAL["hist_label"]))
        p.drawText(QRect(12, y, 112, 16), Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter,
                   f"Hautes lumières {self.hi:.1f} %")
        p.setPen(QColor(PAL["accent"]) if self.lo > 5.0 else QColor(PAL["hist_label"]))
        p.drawText(QRect(self.width() - 124, y, 112, 16),
                   Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter,
                   f"Ombres {self.lo:.1f} %")


class StarRating(QWidget):
    """Étoiles cliquables (visionneuse). Re-cliquer sur la note actuelle la retire."""
    rated = Signal(int)
    R, GAP = 9.0, 4.0

    def __init__(self):
        super().__init__()
        self.rating = 0
        self.hover = 0
        self.setFixedSize(int((2 * self.R + self.GAP) * 5) + 4, 30)
        self.setMouseTracking(True)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setToolTip("Clique pour noter (touches 1 à 5) · re-clique sur la même étoile pour retirer la note")

    def set_rating(self, n):
        self.rating = n
        self.update()

    def _n_at(self, x):
        return max(1, min(5, int((x - 2) // (2 * self.R + self.GAP)) + 1))

    def mouseMoveEvent(self, e):
        n = self._n_at(e.position().x())
        if n != self.hover:
            self.hover = n
            self.update()

    def leaveEvent(self, e):
        self.hover = 0
        self.update()

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            n = self._n_at(e.position().x())
            self.rated.emit(0 if n == self.rating else n)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        draw_stars(p, 2, self.height() / 2, self.R, self.hover or self.rating, gap=self.GAP)


class CompareCell(QWidget):
    def __init__(self):
        super().__init__()
        self.setObjectName("cmpCell")
        self.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(3, 3, 3, 3)
        lay.setSpacing(0)
        self.view = ImageView()
        self.label = QLabel()
        self.label.setTextFormat(Qt.TextFormat.RichText)
        self.label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.label.setContentsMargins(0, 6, 0, 4)
        lay.addWidget(self.view, 1)
        lay.addWidget(self.label)
        self.set_active(False)

    def set_active(self, on):
        col = PAL["accent"] if on else "transparent"
        self.setStyleSheet("QWidget#cmpCell { border: 2px solid %s; border-radius: 10px; }" % col)


class ComparePage(QWidget):
    def __init__(self):
        super().__init__()
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(0)
        self.row = QHBoxLayout()
        self.row.setContentsMargins(4, 4, 4, 0)
        self.row.setSpacing(4)
        lay.addLayout(self.row, 1)
        hint = QLabel("← → : changer de photo active   ·   P / X / 1-5 : noter la photo active"
                      "   ·   molette : zoom   ·   Échap : retour")
        hint.setObjectName("viewFoot")
        hint.setAlignment(Qt.AlignmentFlag.AlignCenter)
        hint.setContentsMargins(0, 7, 0, 7)
        lay.addWidget(hint)
        self.cells = []

    def setup(self, n):
        for c in self.cells:
            self.row.removeWidget(c)
            c.setParent(None)
            c.deleteLater()
        self.cells = []
        for _ in range(n):
            c = CompareCell()
            self.row.addWidget(c, 1)
            self.cells.append(c)


STYLE = """
QMainWindow, QWidget { background: #14151b; color: #e6e8f0; }
QLabel { background: transparent; }
QToolTip { background: #232634; color: #e6e8f0; border: 1px solid #3a3f55; padding: 5px 9px; }

QWidget#sidebarInner { background: #181a22; }
QScrollArea { background: transparent; border: none; }
QPushButton::menu-indicator { image: none; width: 0px; }
QFrame#sidebar { background: #181a22; border-right: 1px solid #262936; }
QFrame#topbar { background: #14151b; border-bottom: 1px solid #262936; }
QFrame#viewHead { background: #181a22; border-bottom: 1px solid #262936; }
QLabel#viewTitle { font-size: 15px; font-weight: 600; }
QLabel#viewFoot { background: #181a22; color: #8b90a3; border-top: 1px solid #262936; }
QListView#film { background: #12131a; border-top: 1px solid #262936; }
QLabel#brand { font-size: 15px; font-weight: 700; }
QLabel#section { color: #7d8397; font-size: 10px; font-weight: 700; }
QLabel#muted { color: #8b90a3; }
QLabel#folderName { font-size: 13px; font-weight: 600; }
QLabel#welcomeTitle { font-size: 34px; font-weight: 700; }
QLabel#welcomeText { color: #8b90a3; font-size: 14px; }
QLabel#toast { background: #232634; border: 1px solid #3a3f55; border-radius: 14px;
               padding: 11px 20px; color: #f1f3fa; font-size: 13px; }

QPushButton { background: #232634; border: 1px solid #2d3140; border-radius: 9px;
              padding: 7px 14px; color: #e6e8f0; }
QPushButton:hover { background: #2b2f40; border-color: #3a3f55; }
QPushButton:pressed { background: #1f2230; }
QPushButton:disabled { color: #566077; background: #191b24; border-color: #22252f; }
QPushButton#primary { background: #6d8cff; border: none; color: #0d1022; font-weight: 700;
                      padding: 9px 14px; }
QPushButton#primary:hover { background: #8aa3ff; }
QPushButton#chip { padding: 4px 8px; border-radius: 13px; background: transparent;
                   border: 1px solid #2d3140; color: #a6abbd; }
QPushButton#chip:hover { border-color: #4a5170; color: #ffffff; }
QPushButton#chip:checked { background: #6d8cff; border-color: #6d8cff; color: #0d1022;
                           font-weight: 700; }
QPushButton#ghost { background: transparent; border: none; color: #a6abbd; padding: 6px 6px; }
QPushButton#ghost:hover { background: #232634; color: #ffffff; }
QPushButton#recent { background: #1c1e26; border: 1px solid #2d3140; text-align: left;
                     padding: 10px 16px; border-radius: 10px; }
QPushButton#recent:hover { background: #262a3a; border-color: #4a5170; }
QPushButton#dest { background: #1f222d; border: 1px solid #2d3140; border-radius: 11px;
                   padding: 0px; text-align: left; }
QPushButton#dest:hover { background: #282c3c; border-color: #4a5170; }
QPushButton#dest:pressed { background: #323852; }
QPushButton#dest:disabled { background: #191b24; }
QPushButton#seg { background: transparent; border: 1px solid #2d3140; color: #a6abbd;
                  padding: 6px 10px; border-radius: 8px; }
QPushButton#seg:checked { background: #2b3350; border-color: #6d8cff; color: #ffffff; }
QPushButton#add { background: transparent; border: 1px dashed #3a3f55; color: #8b90a3;
                  padding: 9px; border-radius: 11px; }
QPushButton#add:hover { border-color: #6d8cff; color: #ffffff; }

QComboBox { background: #1f222d; border: 1px solid #2d3140; border-radius: 9px;
            padding: 6px 10px; min-height: 20px; }
QComboBox:hover { border-color: #4a5170; }
QComboBox::drop-down { border: none; width: 22px; }
QComboBox QAbstractItemView { background: #1f222d; border: 1px solid #2d3140;
                              selection-background-color: #34406b; outline: none; }
QLineEdit { background: #1f222d; border: 1px solid #2d3140; border-radius: 10px;
            padding: 7px 12px; selection-background-color: #34406b; }
QLineEdit:focus { border-color: #6d8cff; }

QMenuBar { background: #14151b; border-bottom: 1px solid #262936; }
QMenuBar::item { padding: 6px 12px; background: transparent; }
QMenuBar::item:selected { background: #232634; border-radius: 6px; }
QMenu { background: #1f222d; border: 1px solid #2d3140; padding: 6px; }
QMenu::item { padding: 7px 26px 7px 14px; border-radius: 6px; }
QMenu::item:selected { background: #34406b; }
QMenu::separator { height: 1px; background: #2d3140; margin: 5px 8px; }

QListView { background: transparent; border: none; outline: none; }
QStatusBar { background: #14151b; color: #8b90a3; border-top: 1px solid #262936; }
QStatusBar::item { border: none; }
QProgressBar { background: #232634; border: none; border-radius: 3px; max-height: 6px;
               min-height: 6px; text-align: center; }
QProgressBar::chunk { background: #3ecf8e; border-radius: 3px; }

QSlider::groove:horizontal { height: 4px; background: #2d3140; border-radius: 2px; }
QSlider::sub-page:horizontal { background: #6d8cff; border-radius: 2px; }
QSlider::handle:horizontal { background: #ffffff; width: 14px; height: 14px; margin: -5px 0;
                             border-radius: 7px; }
QScrollBar:vertical { background: transparent; width: 12px; margin: 2px; }
QScrollBar::handle:vertical { background: #353949; border-radius: 4px; min-height: 36px; }
QScrollBar::handle:vertical:hover { background: #4a5170; }
QScrollBar:horizontal { background: transparent; height: 10px; margin: 2px; }
QScrollBar::handle:horizontal { background: #353949; border-radius: 4px; min-width: 36px; }
QScrollBar::add-line, QScrollBar::sub-line { width: 0; height: 0; }
QScrollBar::add-page, QScrollBar::sub-page { background: transparent; }
QLabel#homeBrand { font-size: 18px; font-weight: 700; }
QLabel#homeGreet { font-size: 36px; font-weight: 700; }
QLabel#homeSub { color: #8b90a3; font-size: 14px; }
QLabel#pageTitle { font-size: 26px; font-weight: 700; }
QLabel#cardTitle { font-size: 15px; font-weight: 700; }
QLabel#tipTitle { font-size: 13px; font-weight: 700; }
QLabel#dropZone { border: 2px dashed #3a3f55; border-radius: 16px; color: #8b90a3; font-size: 13px; }
QLabel#cardIcon { background: #2b3350; border-radius: 12px; font-size: 20px; font-weight: 700; }
QLabel#cardName { font-size: 14px; font-weight: 600; }
QFrame#card, QFrame#tipCard { background: #1c1e26; border: 1px solid #2d3140; border-radius: 14px; }
QPushButton#recentCard { background: #1c1e26; border: 1px solid #2d3140; border-radius: 14px;
                         text-align: left; padding: 0px; }
QPushButton#recentCard:hover { background: #262a3a; border-color: #4a5170; }
QPushButton#ghostBorder { background: transparent; border: 1px solid #2d3140; color: #e6e8f0; }
QPushButton#ghostBorder:hover { background: #232634; border-color: #4a5170; }
QPushButton#toggle { background: transparent; border: 1px solid #2d3140; color: #a6abbd;
                     border-radius: 9px; padding: 7px 14px; }
QPushButton#toggle:hover { border-color: #4a5170; color: #ffffff; }
QPushButton#toggle:checked { background: #6d8cff; border-color: #6d8cff; color: #0d1022;
                             font-weight: 700; }
QCheckBox { spacing: 10px; background: transparent; }
QCheckBox::indicator { width: 18px; height: 18px; border-radius: 5px; border: 1px solid #4a5170;
                       background: #1f222d; }
QCheckBox::indicator:hover { border-color: #6d8cff; }
QCheckBox::indicator:checked { background: #6d8cff; border-color: #6d8cff; }
QMessageBox, QInputDialog, QProgressDialog, QColorDialog { background: #181a22; }
QFrame#editPanel { background: #181a22; border-left: 1px solid #262936; }
QFrame#editFoot { background: #181a22; border-top: 1px solid #262936; }
QLabel#sliderName { font-weight: 600; }

QFrame#lrTop { background: #14151b; border-bottom: 1px solid #262936; }
QPushButton#lrBack { background: #1f222d; border: 1px solid #2d3140; border-radius: 8px; color: #e6e8f0;
    font-size: 16px; font-weight: 700; padding: 0; }
QPushButton#lrBack:hover { background: #2b3350; border-color: #6d8cff; }
QSplitter::handle { background: transparent; }
QSplitter::handle:hover { background: #6d8cff; }
QLabel#lrBrand { font-size: 14px; font-weight: 700; }
QLabel#lrSep { color: #4a5170; }
QPushButton#lrModule { background: transparent; border: none; color: #8b90a3; padding: 6px 8px;
                       font-size: 13px; font-weight: 600; border-radius: 0; }
QPushButton#lrModule:hover { color: #ffffff; }
QPushButton#lrModule:checked { color: #ffffff; border-bottom: 2px solid #6d8cff; }
QFrame#lrSide { background: #181a22; }
QFrame#lrToolbar { background: #181a22; border-top: 1px solid #262936; }
QFrame#lrStrip { background: #181a22; border-top: 1px solid #262936; border-bottom: 1px solid #262936; }
QFrame#lrFoot { background: #181a22; border-top: 1px solid #262936; }
QFrame#lrFilmWrap { background: #12131a; border-top: 1px solid #262936; }
QFrame#lrFilmHead { background: #181a22; border-bottom: 1px solid #262936; }
QFrame#lrPanel { background: transparent; border: none; border-bottom: 1px solid #262936; }
QWidget#lrBody { background: transparent; }
QPushButton#lrHeader { background: transparent; border: none; border-radius: 0; text-align: left;
                       padding: 0px; }
QPushButton#lrHeader:hover { background: #1f222d; }
QLabel#lrTitle { font-size: 12px; font-weight: 700; color: #e6e8f0; }
QLabel#lrArrow { color: #7d8397; font-size: 11px; }
QLabel#lrName { color: #a6abbd; font-size: 12px; }
QLabel#lrValue { color: #a6abbd; font-size: 12px; }
QLabel#lrGroup { color: #7d8397; font-size: 11px; font-weight: 700; padding-top: 6px; }
QLabel#lrInfo { color: #e6e8f0; font-size: 12px; font-weight: 600; }
QPushButton#lrMini { background: transparent; border: 1px solid #2d3140; color: #a6abbd; padding: 3px 4px;
                     border-radius: 6px; font-size: 11px; }
QPushButton#lrMini:hover { border-color: #4a5170; color: #ffffff; }
QPushButton#lrPreset { background: transparent; border: none; text-align: left; color: #a6abbd;
                       padding: 5px 8px; border-radius: 6px; }
QPushButton#lrPreset:hover { background: #232634; color: #ffffff; }
QPushButton#lrTool { background: #1f222d; border: 1px solid #2d3140; color: #a6abbd; padding: 5px 12px;
                     border-radius: 8px; }
QPushButton#lrTool:hover { border-color: #4a5170; color: #ffffff; }
QPushButton#lrTool:checked { background: #2b3350; border-color: #6d8cff; color: #ffffff; }
QListWidget#lrHistory { background: #14151b; border: 1px solid #262936; border-radius: 8px; outline: none; }
QListWidget#lrHistory::item { padding: 4px 8px; color: #a6abbd; }
QListWidget#lrHistory::item:selected { background: #34406b; color: #ffffff; }
QPushButton#flagOk, QPushButton#flagBad { background: transparent; border: 1px solid #2d3140; color: #a6abbd;
                                          padding: 5px 12px; border-radius: 8px; }
QPushButton#flagOk:checked { background: #1f3d31; border-color: #3ecf8e; color: #ffffff; }
QPushButton#flagBad:checked { background: #402329; border-color: #ff5d6c; color: #ffffff; }
QLabel#homeTagline { color: #8b90a3; font-size: 14px; }
QLabel#homeTitle { font-size: 46px; font-weight: 700; }
"""

# ---------------------------------------------------------------------------
# Thèmes : clair / sombre + couleur d'accent au choix
# ---------------------------------------------------------------------------
ACCENT_PRESETS = [("Bleu", "#6d8cff"), ("Violet", "#a678ff"), ("Rose", "#ff6b9a"),
                  ("Rouge", "#ff5d6c"), ("Orange", "#ff9f4a"), ("Jaune", "#ffc857"),
                  ("Vert", "#3ecf8e"), ("Turquoise", "#2fd0c0"), ("Cyan", "#4dd0e1"),
                  ("Gris", "#9aa3b8")]
THEME_DEFAULT = {"mode": "dark", "accent": "#6d8cff", "tint": False}

# Couleur d'origine (thème sombre) -> luminosité équivalente en thème clair.
_NEUTRALS = {
    "#12131a": 0.925, "#14151b": 0.955, "#181a22": 0.985, "#1c1e26": 0.995, "#1f222d": 0.995,
    "#242734": 0.940, "#232634": 0.925, "#2b2f40": 0.895, "#1f2230": 0.860, "#262936": 0.875,
    "#2d3140": 0.835, "#3a3f55": 0.775, "#4a5170": 0.600, "#282c3c": 0.930, "#323852": 0.885,
    "#262a3a": 0.940, "#191b24": 0.950, "#22252f": 0.900, "#566077": 0.620, "#353949": 0.775,
    "#101116": 0.900, "#3a3d4a": 0.800,
    "#e6e8f0": 0.130, "#f1f3fa": 0.100, "#ffffff": 0.070, "#d6d9e3": 0.160, "#c9cde0": 0.250,
    "#a6abbd": 0.330, "#8b90a3": 0.370, "#7d8397": 0.410, "#9aa0b4": 0.360, "#737888": 0.550,
    "#6b7080": 0.500,
}


def _hex_rgb(h):
    h = h.lstrip("#")
    return tuple(int(h[i:i + 2], 16) / 255.0 for i in (0, 2, 4))


def _rgb_hex(r, g, b):
    return "#%02x%02x%02x" % tuple(max(0, min(255, int(round(v * 255)))) for v in (r, g, b))


def _hex_hls(h):
    return colorsys.rgb_to_hls(*_hex_rgb(h))


def _from_hsl(h, s, l):
    r, g, b = colorsys.hls_to_rgb(h % 1.0, max(0.0, min(1.0, l)), max(0.0, min(1.0, s)))
    return _rgb_hex(r, g, b)


def _mix(a, b, t):
    return _rgb_hex(*[x + (y - x) * t for x, y in zip(_hex_rgb(a), _hex_rgb(b))])


def _lum(h):
    def f(c):
        return c / 12.92 if c <= 0.03928 else ((c + 0.055) / 1.055) ** 2.4
    r, g, b = (f(c) for c in _hex_rgb(h))
    return 0.2126 * r + 0.7152 * g + 0.0722 * b


def contrast(a, b):
    la, lb = _lum(a), _lum(b)
    if la < lb:
        la, lb = lb, la
    return (la + 0.05) / (lb + 0.05)


def _ensure_contrast(hx, bg, need, lighten):
    """Éclaircit (ou assombrit) hx jusqu'à atteindre le contraste voulu avec bg."""
    h, l, s_ = _hex_hls(hx)
    for _ in range(60):
        if contrast(_from_hsl(h, s_, l), bg) >= need:
            break
        if lighten:
            if l >= 0.98:
                break
            l = min(0.98, l + 0.02)
        else:
            if l <= 0.02:
                break
            l = max(0.02, l - 0.02)
    return _from_hsl(h, s_, l)


def compute_palette(mode, accent, tint):
    """-> (table couleur d'origine -> couleur du thème, dictionnaire PAL)."""
    dark = mode != "light"
    if not re.fullmatch(r"#[0-9a-fA-F]{6}", accent or ""):
        accent = "#6d8cff"
    ah, _al, a_s = _hex_hls(accent)
    hue = ah if a_s > 0.06 else 0.62            # accent gris : fond neutre légèrement bleuté

    m = {}
    for hx, light_l in _NEUTRALS.items():
        h0, l0, s0 = _hex_hls(hx)
        if dark:
            if hx == "#ffffff":
                m[hx] = hx
                continue
            lum_ = l0
            sat = min(0.42, s0 * 1.45) if tint else 0.035
            if lum_ > 0.7:
                sat = min(sat, 0.25)
        else:
            lum_ = light_l
            sat = 0.34 if tint else 0.04
        m[hx] = _from_hsl(hue, sat, lum_)

    bg = m["#14151b"]
    card = m["#1c1e26"]
    # les textes discrets restent lisibles sur le fond, le panneau et les cartes
    for key in ("#a6abbd", "#8b90a3", "#7d8397", "#9aa0b4"):
        for surface in (bg, m["#181a22"], card):
            m[key] = _ensure_contrast(m[key], surface, 4.6, lighten=dark)
    acc = _ensure_contrast(accent, bg, 3.2, lighten=dark)   # l'accent reste visible sur le fond
    _h, al, a_s2 = _hex_hls(acc)
    m["#6d8cff"] = acc
    m["#8aa3ff"] = _from_hsl(ah, a_s2, min(0.92, al + 0.08)) if dark else _from_hsl(ah, a_s2, max(0.15, al - 0.07))
    fg = max(["#10131f", "#ffffff"], key=lambda c: contrast(acc, c))
    if contrast(acc, fg) < 4.5:
        fg = max(["#000000", "#ffffff"], key=lambda c: contrast(acc, c))
    m["#0d1022"] = fg
    ratios = (0.38, 0.32, 0.26, 0.20, 0.14) if dark else (0.30, 0.24, 0.18, 0.12)
    for t in ratios:
        sel = _mix(bg, acc, t)
        if contrast(m["#e6e8f0"], sel) >= 4.8:
            break
    m["#34406b"] = sel
    m["#2b3350"] = _mix(bg, acc, t * 0.63)

    pal = {
        "accent": acc, "card": card, "card_hover": m["#242734"], "star_off": m["#3a3d4a"],
        "thumb_bg": m["#101116"], "stage": "#0d0e12" if dark else "#dcdde2",
        "muted": m["#8b90a3"], "muted2": m["#7d8397"], "text": m["#d6d9e3"],
        "text_dim": m["#737888"], "ph_text": m["#6b7080"], "key_bg": m["#2d3140"],
        "key_fg": m["#c9cde0"], "hist_label": m["#9aa0b4"], "text_strong": m["#ffffff"],
        "hist_bg": (12, 13, 18, 205) if dark else (255, 255, 255, 228),
        "gold": "#ffc857" if dark else _ensure_contrast("#e89f00", card, 3.0, False),
        "ok": "#3ecf8e" if dark else _ensure_contrast("#139a65", bg, 4.5, False),
        "bad": "#ff5d6c" if dark else _ensure_contrast("#d6293f", bg, 4.5, False),
        "dark": dark,
    }
    return m, pal


def build_style(table):
    return re.sub(r"#[0-9a-fA-F]{6}\b", lambda mo: table.get(mo.group(0).lower(), mo.group(0)), STYLE)


def apply_theme(app=None):
    """Applique THEME (mode, couleur, fond teinté) à toute l'application."""
    global ACCENT, CARD, CARD_HOVER, GOLD
    table, pal = compute_palette(THEME["mode"], THEME["accent"], THEME["tint"])
    PAL.clear()
    PAL.update(pal)
    ACCENT = QColor(pal["accent"])
    CARD = QColor(pal["card"])
    CARD_HOVER = QColor(pal["card_hover"])
    GOLD = QColor(pal["gold"])
    if app is not None:
        app.setStyleSheet(build_style(table))


def load_theme(settings):
    # nouveau thème par défaut (gris foncé + bleu) : appliqué une seule fois aux anciennes installations
    if str(settings.value("theme_version", "")) != "2":
        settings.setValue("theme_mode", THEME_DEFAULT["mode"])
        settings.setValue("theme_accent", THEME_DEFAULT["accent"])
        settings.setValue("theme_tint", "false")
        settings.setValue("theme_version", "2")
    THEME["mode"] = "light" if str(settings.value("theme_mode", "dark")) == "light" else "dark"
    acc = str(settings.value("theme_accent", "#6d8cff"))
    THEME["accent"] = acc.lower() if re.fullmatch(r"#[0-9a-fA-F]{6}", acc) else "#6d8cff"
    THEME["tint"] = str(settings.value("theme_tint", "false")).lower() == "true"


def _resource(name):
    """Chemin d'un fichier livré avec l'appli (script, ou dossier interne de l'.exe)."""
    base = getattr(sys, "_MEIPASS", None) or os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base, name)


def make_logo(size=64):
    """Logo de l'application : klutter.png s'il est présent, sinon une étoile aux couleurs du thème."""
    custom = _resource("klutter.png")
    if os.path.isfile(custom):
        img = QPixmap(custom)
        if not img.isNull():
            return img.scaled(size, size, Qt.AspectRatioMode.KeepAspectRatio,
                              Qt.TransformationMode.SmoothTransformation)
    pm = QPixmap(size, size)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    acc = QColor(PAL["accent"])
    g = QLinearGradient(0, 0, size, size)
    g.setColorAt(0.0, acc.lighter(125))
    g.setColorAt(1.0, acc.darker(140))
    p.setPen(Qt.PenStyle.NoPen)
    p.setBrush(g)
    p.drawRoundedRect(QRect(0, 0, size, size), size * 0.24, size * 0.24)
    p.setBrush(QColor(255, 255, 255, 240))
    p.drawPolygon(star_polygon(size / 2, size / 2 + size * 0.02, size * 0.30))
    p.end()
    return pm


HELP_TEXT = """<h3>Trier en 1 clic</h3>
<p>Dans la barre latérale, ajoute des <b>destinations</b> (un dossier chacune).<br>
Clique sur une destination (ou appuie sur sa touche) : la photo affichée ou les photos
sélectionnées partent aussitôt dans ce dossier. <b>Ctrl+Z</b> annule.<br>
Clic droit sur une destination : renommer, changer la touche ou le dossier, retirer.</p>
<h3>Grille</h3>
<p>Flèches : naviguer · <b>Entrée</b> ou double-clic : ouvrir en grand<br>
Ctrl+clic / Maj+clic : sélection multiple · Ctrl+A : tout sélectionner</p>
<h3>Notation (grille, visionneuse, comparaison)</h3>
<p><b>1</b> à <b>5</b> : étoiles · <b>0</b> : aucune étoile<br>
ou <b>clic direct sur les étoiles</b> d'une photo (re-clic sur la même étoile = retirer la note)<br>
Trie ensuite par note avec le bouton « ★ Trier par note » ou le menu « Tri »<br>
Après avoir changé des notes, <b>↻</b> (ou <b>F6</b>) replace les photos selon leur nouvelle note<br>
<b>P</b> : gardée · <b>X</b> : rejetée · <b>U</b> : retirer le drapeau<br>
<b>Ctrl+Z</b> ou bouton « Annuler » : annule la dernière action<br>
<b>N</b> : prochaine photo sans drapeau<br>
<b>C</b> : comparer 2 à 4 photos sélectionnées</p>
<h3>Étiquettes couleur et notes rapides</h3>
<p><b>6 7 8 9</b> : étiquette rouge / jaune / verte / bleue (re-appuyer = retirer) ; la violette se pose au menu « Photo »<br>
Les pastilles de la barre latérale filtrent la grille par couleur<br>
<b>]</b> / <b>[</b> (ou Ctrl+↑ / Ctrl+↓) : augmenter / diminuer la note</p>
<h3>Visionneuse (module Développement)</h3>
<p><b>←</b> en haut à gauche, <b>Échap</b>, <b>Alt+Gauche</b> ou le bouton « précédent » de la souris : retour à la grille<br>
← / → ou Espace : photo précédente / suivante · bande de vignettes en bas<br>
Molette : zoom · double-clic ou <b>Z</b> : 100 % ↔ ajusté · <b>F</b> : ajuster<br>
<b>H</b> : histogramme · <b>G</b> : grille de composition (tiers, quadrillage, diagonales)<br>
<b>L</b> : lumières éteintes · <b>S</b> : diaporama · <b>Tab</b> : masquer les panneaux · <b>\\</b> ou <b>B</b> : avant / après</p>
<h3>Développer (non destructif)</h3>
<p>Panneaux Basique, Détail, Effets, Recadrer, Préréglages, Historique à la manière de Lightroom.
Double-clic sur un curseur : remise à zéro. Les réglages sont enregistrés à côté des photos, l'original n'est jamais touché.<br>
<b>Ctrl+Maj+C / V</b> : copier / coller les réglages (sur toute la sélection depuis la grille)<br>
<b>Ctrl+Maj+E</b> : exporter en JPEG, PNG ou TIFF · <b>F2</b> : renommer</p>
<h3>Barre latérale</h3>
<p>Glisse le bord droit de la barre latérale pour l'élargir ou la réduire ; <b>Ctrl+B</b> la masque.</p>
<h3>Accueil et paramètres</h3>
<p>« Accueil » (Ctrl+H) : page d'accueil, dossiers récents<br>
« Paramètres » (Ctrl+,) : thème clair / sombre, couleur de l'application au choix, options</p>
<p style='color:#8b90a3'>Les photos d'origine ne sont jamais modifiées sans action de ta part.
Les notes sont enregistrées dans « trieur_photos.json » dans le dossier ouvert.</p>"""


# ---------------------------------------------------------------------------
# Animations
# ---------------------------------------------------------------------------
def fade_in(widget, ms=220, delay=0, start=0.0):
    """Fondu d'apparition (l'effet est retiré à la fin pour ne pas ralentir l'affichage)."""
    if not ANIM["on"]:
        return
    old = getattr(widget, "_fade", None)
    if old is not None:
        try:
            old.stop()
        except RuntimeError:
            pass
    eff = QGraphicsOpacityEffect(widget)
    eff.setOpacity(start)
    widget.setGraphicsEffect(eff)
    anim = QPropertyAnimation(eff, b"opacity", widget)
    anim.setDuration(ms)
    anim.setStartValue(start)
    anim.setEndValue(1.0)
    anim.setEasingCurve(QEasingCurve.Type.OutCubic)
    widget._fade = anim

    def done():
        if getattr(widget, "_fade", None) is anim:
            try:
                widget.setGraphicsEffect(None)
            except RuntimeError:
                pass

    def go():
        try:
            anim.start()
        except RuntimeError:
            pass

    anim.finished.connect(done)
    if delay:
        QTimer.singleShot(delay, go)
    else:
        go()


class FadingLabel(QLabel):
    """Texte qui change en fondu (phrase d'accroche de l'accueil)."""

    def __init__(self, text=""):
        super().__init__(text)
        self.eff = QGraphicsOpacityEffect(self)
        self.setGraphicsEffect(self.eff)
        self.anim = QPropertyAnimation(self.eff, b"opacity", self)
        self.anim.setEasingCurve(QEasingCurve.Type.InOutQuad)
        self.anim.finished.connect(self._done)
        self._phase = 0
        self._pending = ""

    def swap(self, text):
        if text == self.text():
            return
        if not ANIM["on"]:
            self.setText(text)
            return
        self._phase = 0
        self.anim.stop()
        self._pending = text
        self._phase = 1
        self.anim.setDuration(380)
        self.anim.setStartValue(self.eff.opacity())
        self.anim.setEndValue(0.0)
        self.anim.start()

    def _done(self):
        if self._phase == 1:
            self.setText(self._pending)
            self._phase = 2
            self.anim.setDuration(520)
            self.anim.setStartValue(0.0)
            self.anim.setEndValue(1.0)
            self.anim.start()
        else:
            self._phase = 0


class ZoomMorph(QWidget):
    """Animation « on entre dans la photo » : la vignette grandit jusqu'à sa place dans la
    visionneuse (et inversement à la sortie). Dessinée par-dessus le contenu, sans toucher aux pages."""

    def __init__(self, parent):
        super().__init__(parent)
        self.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents, True)
        self.pm = None
        self.a = QRectF()
        self.b = QRectF()
        self.mode = "in"
        self.t = 0.0
        self.anim = QVariantAnimation(self)
        self.anim.setStartValue(0.0)
        self.anim.setEndValue(1.0)
        self.anim.valueChanged.connect(self._tick)
        self.anim.finished.connect(self._end)
        self.hide()

    def play(self, pm, a, b, mode):
        if pm is None or pm.isNull() or a.isEmpty() or b.isEmpty():
            return
        self.anim.stop()
        self.pm, self.a, self.b, self.mode, self.t = pm, QRectF(a), QRectF(b), mode, 0.0
        self.setGeometry(self.parentWidget().rect())
        self.anim.setDuration(380 if mode == "in" else 320)
        self.anim.setEasingCurve(QEasingCurve.Type.OutCubic if mode == "in" else QEasingCurve.Type.InOutCubic)
        self.show()
        self.raise_()
        self.anim.start()

    def _tick(self, v):
        self.t = float(v)
        self.update()

    def _end(self):
        self.hide()
        self.pm = None

    def paintEvent(self, e):
        if self.pm is None:
            return
        t = self.t
        lerp = lambda x, y: x + (y - x) * t
        r = QRectF(lerp(self.a.x(), self.b.x()), lerp(self.a.y(), self.b.y()),
                   lerp(self.a.width(), self.b.width()), lerp(self.a.height(), self.b.height()))
        fade = 1.0 if t < 0.72 else max(0.0, 1.0 - (t - 0.72) / 0.28)
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        p.setOpacity(fade)
        path = QPainterPath()
        rad = lerp(7.0, 0.0) if self.mode == "in" else lerp(0.0, 7.0)
        path.addRoundedRect(r, rad, rad)
        p.setClipPath(path)
        s = QSizeF(self.pm.size()).scaled(r.size(), Qt.AspectRatioMode.KeepAspectRatioByExpanding)
        tgt = QRectF(0, 0, s.width(), s.height())
        tgt.moveCenter(r.center())
        p.drawPixmap(tgt, self.pm, QRectF(self.pm.rect()))


# ---------------------------------------------------------------------------
# Visionneuse « Développement » (même organisation que Lightroom)
# ---------------------------------------------------------------------------
class ResetSlider(QSlider):
    """Curseur : un double-clic le remet à sa valeur d'origine."""

    def __init__(self, default=0):
        super().__init__(Qt.Orientation.Horizontal)
        self.default = default
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)

    def mouseDoubleClickEvent(self, e):
        self.setValue(self.default)


class ClickLabel(QLabel):
    double_clicked = Signal()

    def mouseDoubleClickEvent(self, e):
        self.double_clicked.emit()


class LrSlider(QWidget):
    """Ligne de réglage : nom · curseur · valeur. Double-clic sur le nom ou le curseur = remise à zéro."""
    changed = Signal(str, float)

    def __init__(self, key, label, lo, hi, scale=1, decimals=0, signed=True, track=None):
        super().__init__()
        self.key, self.scale, self.decimals, self.signed = key, scale, decimals, signed
        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(8)
        self.name = ClickLabel(label)
        self.name.setObjectName("lrName")
        self.name.setFixedWidth(104)
        self.name.setToolTip("Double-clic : remettre à zéro")
        self.name.double_clicked.connect(self.reset)
        self.slider = ResetSlider(0)
        self.slider.setRange(lo, hi)
        self.slider.setToolTip("Double-clic : remettre à zéro")
        if track:
            self.slider.setStyleSheet(
                "QSlider::groove:horizontal { height: 4px; border-radius: 2px; "
                f"background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 {track[0]}, stop:1 {track[1]}); }} "
                "QSlider::sub-page:horizontal { background: transparent; } "
                "QSlider::add-page:horizontal { background: transparent; }")
        self.val = QLabel()
        self.val.setObjectName("lrValue")
        self.val.setFixedWidth(46)
        self.val.setAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
        lay.addWidget(self.name)
        lay.addWidget(self.slider, 1)
        lay.addWidget(self.val)
        self.slider.valueChanged.connect(self._on)
        self._show()

    def value(self):
        return self.slider.value() / self.scale

    def set_value(self, v):
        self.slider.blockSignals(True)
        self.slider.setValue(int(round(float(v) * self.scale)))
        self.slider.blockSignals(False)
        self._show()

    def reset(self):
        self.slider.setValue(0)

    def _show(self):
        v = self.value()
        if not v:
            txt = "0"
        elif self.decimals:
            txt = f"{v:+.{self.decimals}f}".replace(".", ",")
        else:
            txt = f"{int(v):+d}" if self.signed else str(int(v))
        self.val.setText(txt)

    def _on(self, _iv):
        self._show()
        self.changed.emit(self.key, self.value())


class CollapsiblePanel(QFrame):
    """Panneau repliable (titre + flèche), comme dans les colonnes de Lightroom."""

    def __init__(self, title, open_=True):
        super().__init__()
        self.setObjectName("lrPanel")
        v = QVBoxLayout(self)
        v.setContentsMargins(0, 0, 0, 0)
        v.setSpacing(0)
        self.head = QPushButton()
        self.head.setObjectName("lrHeader")
        self.head.setCheckable(True)
        self.head.setChecked(open_)
        self.head.setCursor(Qt.CursorShape.PointingHandCursor)
        self.head.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        hl = QHBoxLayout(self.head)
        hl.setContentsMargins(14, 0, 14, 0)
        self.title = QLabel(title)
        self.title.setObjectName("lrTitle")
        self.arrow = QLabel()
        self.arrow.setObjectName("lrArrow")
        for w in (self.title, self.arrow):
            w.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents, True)
        hl.addWidget(self.title)
        hl.addStretch(1)
        hl.addWidget(self.arrow)
        self.head.setFixedHeight(32)
        self.body = QWidget()
        self.body.setObjectName("lrBody")
        self.lay = QVBoxLayout(self.body)
        self.lay.setContentsMargins(14, 4, 14, 14)
        self.lay.setSpacing(7)
        v.addWidget(self.head)
        v.addWidget(self.body)
        self.body.setVisible(open_)
        self.head.toggled.connect(self._toggled)
        self._arrow()

    def _arrow(self):
        self.arrow.setText("▾" if self.head.isChecked() else "◂")

    def _toggled(self, on):
        self.body.setVisible(on)
        self._arrow()


class NavigatorWidget(QWidget):
    """Aperçu de la photo avec le cadre de la zone visible ; un clic recentre la vue."""
    center_requested = Signal(QPointF)

    def __init__(self, view):
        super().__init__()
        self.view = view
        self.setFixedHeight(150)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        view.view_changed.connect(self.update)

    def _rect(self, pm):
        s = pm.size().scaled(max(1, self.width() - 8), max(1, self.height() - 8),
                             Qt.AspectRatioMode.KeepAspectRatio)
        return QRectF((self.width() - s.width()) / 2, (self.height() - s.height()) / 2,
                      s.width(), s.height())

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        p.fillRect(self.rect(), QColor(PAL["stage"]))
        pm = self.view.current_pixmap()
        if pm.isNull():
            return
        r = self._rect(pm)
        p.drawPixmap(r, pm, QRectF(pm.rect()))
        item = self.view.item_rect()
        vis = self.view.mapToScene(self.view.viewport().rect()).boundingRect().intersected(item)
        if item.width() <= 0 or item.height() <= 0:
            return
        box = QRectF(r.left() + (vis.left() - item.left()) / item.width() * r.width(),
                     r.top() + (vis.top() - item.top()) / item.height() * r.height(),
                     vis.width() / item.width() * r.width(), vis.height() / item.height() * r.height())
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.setPen(QPen(QColor(255, 255, 255, 235), 1.4))
        p.drawRect(box)

    def mousePressEvent(self, e):
        self._pick(e)

    def mouseMoveEvent(self, e):
        if e.buttons() & Qt.MouseButton.LeftButton:
            self._pick(e)

    def _pick(self, e):
        pm = self.view.current_pixmap()
        if pm.isNull() or self.view.fit:
            return
        r, item = self._rect(pm), self.view.item_rect()
        x = item.left() + (e.position().x() - r.left()) / max(1.0, r.width()) * item.width()
        y = item.top() + (e.position().y() - r.top()) / max(1.0, r.height()) * item.height()
        self.center_requested.emit(QPointF(x, y))


class CropOverlay(QWidget):
    """Cadre de recadrage manipulable à la souris, posé sur l'image (outil Recadrer)."""
    crop_changed = Signal()
    MIN = 0.03

    def __init__(self, view):
        super().__init__(view.viewport())
        self.view = view
        self.setMouseTracking(True)
        self.crop = [0.0, 0.0, 1.0, 1.0]       # (g, h, d, b) normalisés
        self.ratio = None                        # largeur / hauteur en pixels, None = libre
        self.img_size = (1, 1)                   # taille réelle (l, h) de l'image après rotations
        self._drag = None
        self.hide()

    # --- géométrie
    def _frame(self):
        return QRectF(self.view.mapFromScene(self.view.item_rect()).boundingRect())

    def _to_widget(self, n):
        fr = self._frame()
        return QPointF(fr.left() + n[0] * fr.width(), fr.top() + n[1] * fr.height())

    def _to_norm(self, pos):
        fr = self._frame()
        return ((pos.x() - fr.left()) / max(1.0, fr.width()), (pos.y() - fr.top()) / max(1.0, fr.height()))

    def _crop_rect(self):
        return QRectF(self._to_widget((self.crop[0], self.crop[1])), self._to_widget((self.crop[2], self.crop[3])))

    def set_ratio(self, ratio):
        """Fixe le rapport largeur/hauteur et adapte le cadre actuel (centré)."""
        self.ratio = ratio
        if ratio:
            W, H = self.img_size
            ar = ratio * H / W
            l, t, r, b = self.crop
            cw, ch = r - l, b - t
            if cw / max(1e-6, ch) > ar:
                nh, nw = ch, ch * ar
            else:
                nw, nh = cw, cw / ar
            cx, cy = (l + r) / 2, (t + b) / 2
            self.crop = [cx - nw / 2, cy - nh / 2, cx + nw / 2, cy + nh / 2]
            self.crop_changed.emit()
        self.update()

    # --- dessin
    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        fr = self._frame()
        cr = self._crop_rect()
        outside = QPainterPath()
        outside.addRect(fr)
        inner = QPainterPath()
        inner.addRect(cr)
        p.fillPath(outside.subtracted(inner), QColor(0, 0, 0, 150))
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.setPen(QPen(QColor(255, 255, 255, 70), 1))
        for i in (1, 2):
            x = cr.left() + cr.width() * i / 3
            y = cr.top() + cr.height() * i / 3
            p.drawLine(QPointF(x, cr.top()), QPointF(x, cr.bottom()))
            p.drawLine(QPointF(cr.left(), y), QPointF(cr.right(), y))
        p.setPen(QPen(QColor(255, 255, 255, 230), 1.6))
        p.drawRect(cr)
        p.setBrush(QColor(255, 255, 255))
        p.setPen(QPen(QColor(40, 40, 40), 1))
        for pt in self._handle_points(cr).values():
            p.drawRect(QRectF(pt.x() - 4, pt.y() - 4, 8, 8))

    @staticmethod
    def _handle_points(cr):
        return {"tl": cr.topLeft(), "tr": cr.topRight(), "bl": cr.bottomLeft(), "br": cr.bottomRight(),
                "t": QPointF(cr.center().x(), cr.top()), "b": QPointF(cr.center().x(), cr.bottom()),
                "l": QPointF(cr.left(), cr.center().y()), "r": QPointF(cr.right(), cr.center().y())}

    # --- souris
    def _hit(self, pos):
        cr = self._crop_rect()
        for k, pt in self._handle_points(cr).items():
            if abs(pos.x() - pt.x()) <= 10 and abs(pos.y() - pt.y()) <= 10:
                return k
        return "move" if cr.contains(pos) else None

    _CURSORS = {"tl": Qt.CursorShape.SizeFDiagCursor, "br": Qt.CursorShape.SizeFDiagCursor,
                "tr": Qt.CursorShape.SizeBDiagCursor, "bl": Qt.CursorShape.SizeBDiagCursor,
                "t": Qt.CursorShape.SizeVerCursor, "b": Qt.CursorShape.SizeVerCursor,
                "l": Qt.CursorShape.SizeHorCursor, "r": Qt.CursorShape.SizeHorCursor,
                "move": Qt.CursorShape.SizeAllCursor}

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            h = self._hit(e.position())
            if h:
                self._drag = (h, self._to_norm(e.position()), list(self.crop))

    def mouseMoveEvent(self, e):
        if self._drag is None:
            self.setCursor(self._CURSORS.get(self._hit(e.position()), Qt.CursorShape.ArrowCursor))
            return
        h, n0, c0 = self._drag
        n = self._to_norm(e.position())
        if h == "move":
            w, hh = c0[2] - c0[0], c0[3] - c0[1]
            l = min(max(c0[0] + n[0] - n0[0], 0.0), 1.0 - w)
            t = min(max(c0[1] + n[1] - n0[1], 0.0), 1.0 - hh)
            self.crop = [l, t, l + w, t + hh]
        else:
            self.crop = self._resize(h, n, c0)
        self.crop_changed.emit()
        self.update()

    def mouseReleaseEvent(self, e):
        self._drag = None

    def _resize(self, h, n, c0):
        MIN = self.MIN
        l, t, r, b = c0
        x, y = min(max(n[0], 0.0), 1.0), min(max(n[1], 0.0), 1.0)
        if "l" in h:
            l = min(x, r - MIN)
        if "r" in h:
            r = max(x, l + MIN)
        if "t" in h:
            t = min(y, b - MIN)
        if "b" in h:
            b = max(y, t + MIN)
        if not self.ratio:
            return [l, t, r, b]
        W, H = self.img_size
        ar = self.ratio * H / W                  # largeur / hauteur en coordonnées normalisées
        if len(h) == 2:                           # coin : le coin opposé reste fixe
            ax = c0[2] if "l" in h else c0[0]
            ay = c0[3] if "t" in h else c0[1]
            maxw = ax if "l" in h else 1.0 - ax
            maxh = ay if "t" in h else 1.0 - ay
            nw = max(r - l, (b - t) * ar)
            nw = min(nw, maxw, maxh * ar)
            nh = nw / ar
            l, r = (ax - nw, ax) if "l" in h else (ax, ax + nw)
            t, b = (ay - nh, ay) if "t" in h else (ay, ay + nh)
        elif h in ("l", "r"):
            cy = (c0[1] + c0[3]) / 2
            maxw = min(c0[2] if h == "l" else 1.0 - c0[0], 2 * min(cy, 1 - cy) * ar)
            nw = min(r - l, maxw)
            nh = nw / ar
            if h == "l":
                r = c0[2]
                l = r - nw
            else:
                l = c0[0]
                r = l + nw
            t, b = cy - nh / 2, cy + nh / 2
        else:
            cx = (c0[0] + c0[2]) / 2
            maxh = min(c0[3] if h == "t" else 1.0 - c0[1], 2 * min(cx, 1 - cx) / ar)
            nh = min(b - t, maxh)
            nw = nh * ar
            if h == "t":
                b = c0[3]
                t = b - nh
            else:
                t = c0[1]
                b = t + nh
            l, r = cx - nw / 2, cx + nw / 2
        return [l, t, r, b]


class _RefineSignals(QObject):
    done = Signal(int, QImage)


class _RefineJob(QRunnable):
    """Rendu pleine définition de la photo retouchée, en arrière-plan."""

    def __init__(self, img, dev, version, with_tone, signals):
        super().__init__()
        self.img, self.dev, self.version, self.with_tone, self.signals = img, dev, version, with_tone, signals

    def run(self):
        try:
            arr = qimage_to_array(self.img)
            out = array_to_qimage(render_dev(arr, self.dev, with_crop=True, with_tone=self.with_tone))
        except Exception:
            out = QImage()
        try:
            self.signals.done.emit(self.version, out)
        except RuntimeError:
            pass


# (clé, libellé, min, max, échelle, décimales, signé, dégradé de la piste)
SLIDERS_WB = [("temperature", "Température", -100, 100, 1, 0, True, ("#3d6fd1", "#e3b53c")),
              ("tint", "Teinte", -100, 100, 1, 0, True, ("#3aa65a", "#cc4fb5"))]
SLIDERS_TONE = [("exposure", "Exposition", -500, 500, 100, 2, True, None),
                ("contrast", "Contraste", -100, 100, 1, 0, True, None),
                ("highlights", "Hautes lumières", -100, 100, 1, 0, True, None),
                ("shadows", "Ombres", -100, 100, 1, 0, True, None),
                ("whites", "Blancs", -100, 100, 1, 0, True, None),
                ("blacks", "Noirs", -100, 100, 1, 0, True, None)]
SLIDERS_PRESENCE = [("texture", "Texture", -100, 100, 1, 0, True, None),
                    ("clarity", "Clarté", -100, 100, 1, 0, True, None),
                    ("dehaze", "Correction du voile", -100, 100, 1, 0, True, None),
                    ("vibrance", "Vibrance", -100, 100, 1, 0, True, None),
                    ("saturation", "Saturation", -100, 100, 1, 0, True, None)]
SLIDERS_DETAIL = [("sharpness", "Netteté : gain", 0, 150, 1, 0, False, None),
                  ("noise", "Bruit : luminance", 0, 100, 1, 0, False, None)]
SLIDERS_EFFECTS = [("vignette", "Vignetage : gain", -100, 100, 1, 0, True, None)]

PRESETS = [
    ("Couleur", [
        ("Vif", {"contrast": 15, "vibrance": 35, "saturation": 10, "clarity": 15}),
        ("Chaud", {"temperature": 25, "tint": 5, "exposure": 0.1, "vibrance": 10}),
        ("Froid", {"temperature": -25, "tint": -3, "contrast": 8}),
        ("Doux", {"contrast": -15, "clarity": -20, "highlights": -20, "shadows": 15}),
        ("Mat", {"blacks": 45, "contrast": -12, "saturation": -15, "whites": -10}),
        ("Portrait", {"texture": -15, "clarity": -10, "vibrance": 12, "shadows": 10}),
        ("Paysage", {"clarity": 20, "dehaze": 15, "vibrance": 25, "highlights": -20, "shadows": 25,
                     "contrast": 10}),
        ("Dramatique", {"contrast": 30, "clarity": 30, "highlights": -30, "shadows": 20,
                        "vibrance": -10, "vignette": -25, "dehaze": 15}),
    ]),
    ("Noir et blanc", [
        ("Noir et blanc", {"bw": True, "contrast": 15}),
        ("N&B contrasté", {"bw": True, "contrast": 40, "clarity": 25, "blacks": -20, "whites": 15}),
        ("N&B doux", {"bw": True, "contrast": -10, "highlights": -15, "shadows": 15}),
    ]),
]


class ViewerPage(QWidget):
    """Visionneuse organisée comme le module « Développement » de Lightroom :
    barre de modules en haut, colonne de gauche (navigateur, préréglages, historique), image au centre
    avec sa barre d'outils, colonne de droite (histogramme, recadrage, réglages), bande de vignettes."""
    PREVIEW = 1500
    dev_changed = Signal(str, object)       # clé de la photo, réglages (dict ou None)
    back_requested = Signal()
    copy_requested = Signal()
    paste_requested = Signal()
    previous_requested = Signal()
    export_requested = Signal()
    flag_requested = Signal(int)
    label_requested = Signal(int)
    RATIOS = [("Libre", None), ("Original", "orig"), ("1 × 1", 1.0), ("4 × 3", 4 / 3), ("3 × 2", 3 / 2),
              ("16 × 9", 16 / 9), ("5 × 4", 5 / 4), ("4 × 5", 4 / 5), ("2 × 3", 2 / 3)]

    def __init__(self):
        super().__init__()
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self.hist_on = True
        self.last_img = None
        self.small = None
        self._orig_pm = None
        self.cur_key = None
        self.dev_p = dict(EDIT_DEFAULTS)
        self.ops = []
        self.crop = list(CROP_FULL)
        self.before = False
        self.crop_mode = False
        self.history = []
        self.hist_idx = -1
        self._label = "Réglage"
        self._loading = False
        self._version = 0
        self._dirty = False
        self.sliders = {}
        self.render_timer = QTimer(self)
        self.render_timer.setSingleShot(True)
        self.render_timer.setInterval(30)
        self.render_timer.timeout.connect(self._render)
        self.refine_timer = QTimer(self)
        self.refine_timer.setSingleShot(True)
        self.refine_timer.setInterval(450)
        self.refine_timer.timeout.connect(self._refine)
        self.commit_timer = QTimer(self)
        self.commit_timer.setSingleShot(True)
        self.commit_timer.setInterval(650)
        self.commit_timer.timeout.connect(self._commit)
        self._rsig = _RefineSignals()
        self._rsig.done.connect(self._on_refined)

        root = QVBoxLayout(self)
        root.setContentsMargins(0, 0, 0, 0)
        root.setSpacing(0)
        self.top_bar = self._build_top()
        root.addWidget(self.top_bar)
        self.lights = False
        self._saved_vis = None
        mid = QHBoxLayout()
        mid.setContentsMargins(0, 0, 0, 0)
        mid.setSpacing(0)
        center = self._build_center()          # crée self.view (utilisé par le navigateur)
        self.left_panel = self._build_left()
        self.right_panel = self._build_right()
        mid.addWidget(self.left_panel)
        mid.addLayout(center, 1)
        mid.addWidget(self.right_panel)
        root.addLayout(mid, 1)
        root.addWidget(self._build_film())
        self.view.view_changed.connect(self._sync_overlay)
        self.navigator.center_requested.connect(lambda pt: self.view.centerOn(pt))
        self._load_sliders({})

    # ------------------------------------------------------------------ construction
    def _build_top(self):
        bar = QFrame()
        bar.setObjectName("lrTop")
        bar.setFixedHeight(42)
        hl = QHBoxLayout(bar)
        hl.setContentsMargins(14, 0, 14, 0)
        hl.setSpacing(10)
        self.btn_back = QPushButton("\u2190")
        self.btn_back.setObjectName("lrBack")
        self.btn_back.setFixedSize(34, 28)
        self.btn_back.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_back.setToolTip("Retour à la grille  (Échap · Alt+Gauche · bouton « précédent » de la souris)")
        self.btn_back.clicked.connect(lambda _=False: self.back_requested.emit())
        hl.addWidget(self.btn_back)
        self.top_logo = QLabel()
        self.top_logo.setFixedSize(24, 24)
        self.top_logo.setPixmap(make_logo(24))
        name = QLabel(APP_NAME)
        name.setObjectName("lrBrand")
        hl.addWidget(self.top_logo)
        hl.addWidget(name)
        hl.addStretch(1)
        mods = [("Bibliothèque", False), ("Développement", True)]
        for i, (txt, cur) in enumerate(mods):
            if i:
                sep = QLabel("|")
                sep.setObjectName("lrSep")
                hl.addWidget(sep)
            b = QPushButton(txt)
            b.setObjectName("lrModule")
            b.setCheckable(True)
            b.setChecked(cur)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.setToolTip("Retour à la grille de photos (Échap)" if not cur else "Module actuel")
            if not cur:
                b.clicked.connect(lambda _=False: self.back_requested.emit())
            else:
                b.clicked.connect(lambda _=False, bb=b: bb.setChecked(True))
            hl.addWidget(b)
        return bar

    def _build_center(self):
        col = QVBoxLayout()
        col.setContentsMargins(0, 0, 0, 0)
        col.setSpacing(0)
        self.view = ImageView()
        self.overlay = CropOverlay(self.view)
        self.overlay.crop_changed.connect(self._on_crop_drag)
        col.addWidget(self.view, 1)
        tb = QFrame()
        tb.setObjectName("lrToolbar")
        tb.setFixedHeight(40)
        self.tool_bar = tb
        tl = QHBoxLayout(tb)
        tl.setContentsMargins(12, 0, 12, 0)
        tl.setSpacing(8)
        self.btn_before = QPushButton("Avant / Après")
        self.btn_before.setObjectName("toggle")
        self.btn_before.setCheckable(True)
        self.btn_before.setToolTip("Affiche la photo sans les réglages (touche \\)")
        self.btn_before.toggled.connect(self._on_before)
        tl.addWidget(self.btn_before)
        tl.addStretch(1)
        self.btn_pick = QPushButton("Gardée")
        self.btn_pick.setObjectName("flagOk")
        self.btn_pick.setCheckable(True)
        self.btn_pick.setToolTip("Garder (P)")
        self.btn_pick.clicked.connect(lambda: self.flag_requested.emit(PICK))
        self.btn_reject = QPushButton("Rejetée")
        self.btn_reject.setObjectName("flagBad")
        self.btn_reject.setCheckable(True)
        self.btn_reject.setToolTip("Rejeter (X)")
        self.btn_reject.clicked.connect(lambda: self.flag_requested.emit(REJECT))
        self.stars = StarRating()
        tl.addWidget(self.btn_pick)
        tl.addWidget(self.btn_reject)
        tl.addSpacing(10)
        tl.addWidget(self.stars)
        tl.addSpacing(10)
        self.label_dots = {}
        for i in range(1, len(LABELS)):
            b = QPushButton()
            b.setCheckable(True)
            b.setFixedSize(18, 18)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.setToolTip("Étiquette " + LABELS[i][0].lower() + (f"  ({i + 5})" if i < 5 else ""))
            b.setStyleSheet(f"QPushButton {{ background: {LABELS[i][1]}; border: 2px solid transparent; "
                            f"border-radius: 9px; }} QPushButton:checked {{ border-color: #ffffff; }}")
            b.clicked.connect(lambda _=False, i=i: self.label_requested.emit(i))
            tl.addWidget(b)
            self.label_dots[i] = b
        tl.addStretch(1)
        self.lbl_pos = QLabel()
        self.lbl_pos.setObjectName("muted")
        tl.addWidget(self.lbl_pos)
        col.addWidget(tb)
        return col

    def _side_scroll(self, panel_width):
        side = QFrame()
        side.setObjectName("lrSide")
        side.setFixedWidth(panel_width)
        outer = QVBoxLayout(side)
        outer.setContentsMargins(0, 0, 0, 0)
        outer.setSpacing(0)
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        inner = QWidget()
        inner.setObjectName("sidebarInner")
        scroll.setWidget(inner)
        col = QVBoxLayout(inner)
        col.setContentsMargins(0, 0, 0, 0)
        col.setSpacing(0)
        outer.addWidget(scroll, 1)
        return side, col, outer

    def _build_left(self):
        side, col, outer = self._side_scroll(252)
        # Navigateur
        nav = CollapsiblePanel("Navigateur")
        self.navigator = NavigatorWidget(self.view)
        nav.lay.addWidget(self.navigator)
        zr = QHBoxLayout()
        zr.setSpacing(4)
        for txt, fn in (("Ajuster", lambda: self.view.fit_view()), ("Remplir", lambda: self.view.fill_view()),
                        ("100 %", lambda: self.view.zoom_to(1.0)), ("200 %", lambda: self.view.zoom_to(2.0))):
            b = QPushButton(txt)
            b.setObjectName("lrMini")
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.clicked.connect(lambda _=False, f=fn: self._zoom(f))
            zr.addWidget(b)
        nav.lay.addLayout(zr)
        col.addWidget(nav)
        # Préréglages
        pre = CollapsiblePanel("Préréglages", open_=False)
        for group, items in PRESETS:
            g = QLabel(group)
            g.setObjectName("lrGroup")
            pre.lay.addWidget(g)
            for name, vals in items:
                b = QPushButton(name)
                b.setObjectName("lrPreset")
                b.setCursor(Qt.CursorShape.PointingHandCursor)
                b.clicked.connect(lambda _=False, n=name, v=vals: self.apply_preset(n, v))
                pre.lay.addWidget(b)
        col.addWidget(pre)
        # Historique
        his = CollapsiblePanel("Historique")
        self.hist_list = QListWidget()
        self.hist_list.setObjectName("lrHistory")
        self.hist_list.setMinimumHeight(110)
        self.hist_list.setMaximumHeight(190)
        self.hist_list.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.hist_list.currentRowChanged.connect(self._on_history_row)
        his.lay.addWidget(self.hist_list)
        col.addWidget(his)
        # Destinations (tri en 1 clic)
        self.dest_panel = CollapsiblePanel("Destinations")
        self.dest_box = QVBoxLayout()
        self.dest_box.setSpacing(6)
        self.dest_panel.lay.addLayout(self.dest_box)
        self.dest_empty = QLabel("Ajoute des destinations depuis la grille.")
        self.dest_empty.setObjectName("muted")
        self.dest_empty.setWordWrap(True)
        self.dest_panel.lay.addWidget(self.dest_empty)
        col.addWidget(self.dest_panel)
        col.addStretch(1)
        # boutons du bas : Copier / Coller / Exporter
        foot = QFrame()
        foot.setObjectName("lrFoot")
        fl = QHBoxLayout(foot)
        fl.setContentsMargins(12, 10, 12, 10)
        fl.setSpacing(6)
        b_copy = QPushButton("Copier…")
        b_copy.setToolTip("Copie les réglages de cette photo (Ctrl+Maj+C)")
        b_copy.clicked.connect(lambda: self.copy_requested.emit())
        b_paste = QPushButton("Coller")
        b_paste.setToolTip("Colle les réglages copiés sur cette photo (Ctrl+Maj+V)")
        b_paste.clicked.connect(lambda: self.paste_requested.emit())
        b_export = QPushButton("Exporter…")
        b_export.setToolTip("Enregistre la photo développée en JPEG / PNG / TIFF (Ctrl+Maj+E)")
        b_export.clicked.connect(lambda: self.export_requested.emit())
        for b in (b_copy, b_paste, b_export):
            fl.addWidget(b)
        outer.addWidget(foot)
        return side

    def _slider_group(self, panel, specs):
        for key, label, lo, hi, scale, dec, signed, track in specs:
            s = LrSlider(key, label, lo, hi, scale, dec, signed, track)
            s.changed.connect(self._on_slider)
            self.sliders[key] = (s, label)
            panel.lay.addWidget(s)

    def _build_right(self):
        side, col, outer = self._side_scroll(292)
        # Histogramme + infos de prise de vue
        self.hist_box = QFrame()
        self.hist_box.setObjectName("lrPanel")
        hb = QVBoxLayout(self.hist_box)
        hb.setContentsMargins(14, 12, 14, 12)
        hb.setSpacing(8)
        title = QLabel("Histogramme")
        title.setObjectName("lrTitle")
        self.hist = HistogramWidget()
        self.info_line = QLabel()
        self.info_line.setObjectName("lrInfo")
        self.info_line.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.info_line2 = QLabel()
        self.info_line2.setObjectName("muted")
        self.info_line2.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.info_line2.setWordWrap(True)
        hb.addWidget(title)
        hb.addWidget(self.hist)
        hb.addWidget(self.info_line)
        hb.addWidget(self.info_line2)
        col.addWidget(self.hist_box)
        # Bande d'outils
        strip = QFrame()
        strip.setObjectName("lrStrip")
        sl = QHBoxLayout(strip)
        sl.setContentsMargins(14, 6, 14, 6)
        sl.setSpacing(8)
        self.btn_crop = QPushButton("Recadrer")
        self.btn_crop.setObjectName("lrTool")
        self.btn_crop.setCheckable(True)
        self.btn_crop.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_crop.setToolTip("Recadrage, rotation et miroir")
        self.btn_crop.toggled.connect(self.set_crop_mode)
        sl.addWidget(self.btn_crop)
        sl.addStretch(1)
        col.addWidget(strip)
        # Recadrage (visible quand l'outil est actif)
        self.crop_panel = CollapsiblePanel("Recadrage")
        self.crop_panel.setVisible(False)
        row = QHBoxLayout()
        row.setSpacing(6)
        lab = QLabel("Format")
        lab.setObjectName("lrName")
        self.cb_ratio = QComboBox()
        for name, val in self.RATIOS:
            self.cb_ratio.addItem(name, val)
        self.cb_ratio.currentIndexChanged.connect(self._on_ratio)
        b_flip = QPushButton("↔ ↕")
        b_flip.setToolTip("Inverser portrait / paysage")
        b_flip.clicked.connect(self._flip_ratio)
        row.addWidget(lab)
        row.addWidget(self.cb_ratio, 1)
        row.addWidget(b_flip)
        self.crop_panel.lay.addLayout(row)
        grid = QGridLayout()
        grid.setSpacing(6)
        for i, (txt, op, tip) in enumerate([("↺  Gauche", "l", "Pivoter de 90° vers la gauche"),
                                            ("↻  Droite", "r", "Pivoter de 90° vers la droite"),
                                            ("Miroir ↔", "h", "Retourner de gauche à droite"),
                                            ("Miroir ↕", "v", "Retourner de haut en bas")]):
            b = QPushButton(txt)
            b.setToolTip(tip)
            b.clicked.connect(lambda _=False, o=op: self._geo_op(o))
            grid.addWidget(b, i // 2, i % 2)
        self.crop_panel.lay.addLayout(grid)
        b_rc = QPushButton("Réinitialiser le recadrage")
        b_rc.setObjectName("ghost")
        b_rc.clicked.connect(self._reset_crop)
        b_done = QPushButton("Terminé")
        b_done.setObjectName("primary")
        b_done.clicked.connect(lambda: self.btn_crop.setChecked(False))
        self.crop_panel.lay.addWidget(b_rc)
        self.crop_panel.lay.addWidget(b_done)
        col.addWidget(self.crop_panel)
        # Basique
        basic = CollapsiblePanel("Basique")
        trow = QHBoxLayout()
        trow.setSpacing(6)
        tl = QLabel("Traitement")
        tl.setObjectName("lrName")
        self.btn_color = QPushButton("Couleur")
        self.btn_bw = QPushButton("Noir et blanc")
        for b in (self.btn_color, self.btn_bw):
            b.setObjectName("seg")
            b.setCheckable(True)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_color.setChecked(True)
        self.btn_color.clicked.connect(lambda: self._set_bw(False))
        self.btn_bw.clicked.connect(lambda: self._set_bw(True))
        trow.addWidget(tl)
        trow.addWidget(self.btn_color)
        trow.addWidget(self.btn_bw)
        basic.lay.addLayout(trow)
        basic.lay.addWidget(self._group_label("Balance des blancs"))
        self._slider_group(basic, SLIDERS_WB)
        hr = QHBoxLayout()
        hr.addWidget(self._group_label("Tonalité"))
        hr.addStretch(1)
        b_auto = QPushButton("Auto")
        b_auto.setObjectName("lrMini")
        b_auto.setCursor(Qt.CursorShape.PointingHandCursor)
        b_auto.setToolTip("Règle automatiquement l'exposition, les noirs et les blancs")
        b_auto.clicked.connect(self.apply_auto)
        hr.addWidget(b_auto)
        basic.lay.addLayout(hr)
        self._slider_group(basic, SLIDERS_TONE)
        basic.lay.addWidget(self._group_label("Présence"))
        self._slider_group(basic, SLIDERS_PRESENCE)
        col.addWidget(basic)
        detail = CollapsiblePanel("Détail", open_=False)
        self._slider_group(detail, SLIDERS_DETAIL)
        col.addWidget(detail)
        fx = CollapsiblePanel("Effets", open_=False)
        self._slider_group(fx, SLIDERS_EFFECTS)
        col.addWidget(fx)
        col.addStretch(1)
        # boutons du bas : Précédent / Réinitialiser
        foot = QFrame()
        foot.setObjectName("lrFoot")
        fl = QHBoxLayout(foot)
        fl.setContentsMargins(12, 10, 12, 10)
        fl.setSpacing(6)
        b_prev = QPushButton("Précédent")
        b_prev.setToolTip("Applique les réglages de la photo regardée juste avant")
        b_prev.clicked.connect(lambda: self.previous_requested.emit())
        b_reset = QPushButton("Réinitialiser")
        b_reset.setToolTip("Remet tous les réglages de cette photo à zéro")
        b_reset.clicked.connect(self.reset_all)
        fl.addWidget(b_prev, 1)
        fl.addWidget(b_reset, 1)
        outer.addWidget(foot)
        return side

    def _group_label(self, text):
        lab = QLabel(text)
        lab.setObjectName("lrGroup")
        return lab

    def _build_film(self):
        wrap = QFrame()
        wrap.setObjectName("lrFilmWrap")
        v = QVBoxLayout(wrap)
        v.setContentsMargins(0, 0, 0, 0)
        v.setSpacing(0)
        head = QFrame()
        head.setObjectName("lrFilmHead")
        head.setFixedHeight(26)
        hl = QHBoxLayout(head)
        hl.setContentsMargins(14, 0, 14, 0)
        self.film_head = QLabel()
        self.film_head.setObjectName("muted")
        hl.addWidget(self.film_head)
        hl.addStretch(1)
        self.film = QListView()
        self.film.setObjectName("film")
        self.film.setFlow(QListView.Flow.LeftToRight)
        self.film.setWrapping(False)
        self.film.setUniformItemSizes(True)
        self.film.setItemDelegate(FilmDelegate(self.film))
        self.film.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.film.setHorizontalScrollMode(QAbstractItemView.ScrollMode.ScrollPerPixel)
        self.film.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.film.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.film.setFixedHeight(FilmDelegate.H + 16)
        v.addWidget(head)
        v.addWidget(self.film)
        self.film_wrap = wrap
        return wrap

    # ------------------------------------------------------------------ API utilisée par la fenêtre
    def set_model(self, model):
        self.film.setModel(model)

    def select_film(self, row):
        m = self.film.model()
        if m is not None and 0 <= row < m.rowCount():
            ix = m.index(row)
            self.film.setCurrentIndex(ix)
            self.film.scrollTo(ix, QAbstractItemView.ScrollHint.PositionAtCenter)

    def toggle_hist(self):
        self.hist_on = not self.hist_on
        self.hist_box.setVisible(self.hist_on)
        if self.hist_on and self.last_img is not None:
            self.hist.set_image(self.last_img)

    def clear_hist(self):
        self.last_img = None
        self.hist.bins = None
        self.hist.update()

    def cycle_guides(self):
        self.view.guides = (self.view.guides + 1) % 4
        self.view.viewport().update()
        names = ["Grille : aucune", "Grille : tiers", "Grille : quadrillage", "Grille : diagonales"]
        self.guide_msg = names[self.view.guides]
        w = self.window()
        if hasattr(w, "toast"):
            w.toast.show_message(self.guide_msg, 1200)

    def toggle_lights(self):
        """Lumières éteintes : masque tout sauf la photo (L ou Échap pour revenir)."""
        parts = [self.top_bar, self.tool_bar, self.left_panel, self.right_panel, self.film_wrap]
        if not self.lights:
            self._saved_vis = [w.isVisible() for w in parts]
            for w in parts:
                w.setVisible(False)
            self.view.setBackgroundBrush(QColor(0, 0, 0))
            self.lights = True
        else:
            for w, v in zip(parts, self._saved_vis or [True] * len(parts)):
                w.setVisible(v)
            self.view.setBackgroundBrush(QColor(PAL["stage"]))
            self.lights = False

    def toggle_side_panels(self, both=False):
        """Tab : masque / affiche les colonnes ; Maj+Tab : masque aussi la bande de vignettes."""
        show = not self.left_panel.isVisible()
        self.left_panel.setVisible(show)
        self.right_panel.setVisible(show)
        if both:
            self.film_wrap.setVisible(show)

    def set_info(self, ph, pos, total, meta):
        self.lbl_pos.setText(f"{pos} / {total}")
        self.stars.set_rating(ph.rating)
        self.btn_pick.setChecked(ph.flag == PICK)
        self.btn_reject.setChecked(ph.flag == REJECT)
        for i, b in self.label_dots.items():
            b.setChecked(ph.label == i)
        folder = os.path.basename(os.path.dirname(ph.path)) or os.path.dirname(ph.path)
        self.film_head.setText(f"Dossier : {folder}      {total} photos      {ph.name}")
        parts = []
        if meta.get("iso"):
            parts.append(f"ISO {meta['iso']}")
        if meta.get("focal"):
            parts.append(f"{meta['focal']:.0f} mm")
        if meta.get("aperture"):
            parts.append(f"f / {meta['aperture']:.1f}")
        sh = _fmt_shutter(meta.get("shutter"))
        if sh:
            parts.append(sh)
        self.info_line.setText("     ".join(parts) or " ")
        second = [x for x in (meta.get("camera"), meta.get("lens")) if x]
        d = meta.get("dims")
        if d and d[0] and d[1]:
            second.append(f"{d[0]} × {d[1]}")
        self.info_line2.setText("  ·  ".join(second))

    # ------------------------------------------------------------------ photo courante
    def begin_photo(self, key, dev):
        """Une autre photo devient la photo courante : on enregistre l'ancienne, on charge la nouvelle."""
        self.flush()
        self.cur_key = key
        self.last_img = None
        self.small = None
        self._orig_pm = None
        self._loading = True
        try:
            self.before = False
            self.btn_before.setChecked(False)
            self.dev_p = dev_params(dev)
            self.ops = list((dev or {}).get("ops") or [])
            self.crop = list((dev or {}).get("crop") or CROP_FULL)
            self._load_sliders(self.dev_p)
            if self.crop_mode:
                self.btn_crop.setChecked(False)
        finally:
            self._loading = False
        self.history = [("Ouverture", self._snapshot())]
        self.hist_idx = 0
        self._refresh_history()
        self._dirty = False

    def show_image(self, img):
        self.last_img = img
        self.small = None
        self._orig_pm = None
        self._render()

    def current_dev(self):
        return dev_clean(self.dev_p, self.ops, self.crop)

    def flush(self):
        """Envoie tout de suite les réglages en attente (changement de photo, fermeture…)."""
        if self.commit_timer.isActive():
            self.commit_timer.stop()
            self._commit()

    def _snapshot(self):
        return (dict(self.dev_p), list(self.ops), list(self.crop))

    def _load_sliders(self, p):
        for key, (s, _label) in self.sliders.items():
            s.set_value(p.get(key, 0))
        self.btn_bw.setChecked(bool(p.get("bw")))
        self.btn_color.setChecked(not p.get("bw"))

    def _restore(self, snap):
        p, ops, crop = snap
        self._loading = True
        try:
            self.dev_p, self.ops, self.crop = dict(p), list(ops), list(crop)
            self._load_sliders(self.dev_p)
            self.overlay.crop = list(self.crop)
        finally:
            self._loading = False
        self._render()
        self.dev_changed.emit(self.cur_key or "", self.current_dev())

    # ------------------------------------------------------------------ réglages
    def _touch(self, label, render=True):
        if self._loading:
            return
        self._label = label
        self._dirty = True
        if render:
            self.render_timer.start()
        self.commit_timer.start()

    def _on_slider(self, key, value):
        self.dev_p[key] = value
        label = self.sliders[key][1]
        txt = f"{value:+.2f}".replace(".", ",") if key == "exposure" else f"{int(value):+d}"
        self._touch(f"{label} {txt}")

    def _set_bw(self, on):
        self.dev_p["bw"] = bool(on)
        self.btn_bw.setChecked(bool(on))
        self.btn_color.setChecked(not on)
        self._touch("Noir et blanc" if on else "Couleur")

    def _commit(self):
        if not self._dirty:
            return
        self._dirty = False
        snap = self._snapshot()
        if self.history and self.history[self.hist_idx][1] == snap:
            return
        del self.history[self.hist_idx + 1:]
        self.history.append((self._label, snap))
        del self.history[:-60]
        self.hist_idx = len(self.history) - 1
        self._refresh_history()
        self.dev_changed.emit(self.cur_key or "", self.current_dev())

    def _refresh_history(self):
        self.hist_list.blockSignals(True)
        self.hist_list.clear()
        for label, _snap in reversed(self.history):
            self.hist_list.addItem(label)
        self.hist_list.setCurrentRow(len(self.history) - 1 - self.hist_idx)
        self.hist_list.blockSignals(False)

    def _on_history_row(self, row):
        if row < 0 or not self.history:
            return
        idx = len(self.history) - 1 - row
        if idx == self.hist_idx:
            return
        self.flush()
        self.hist_idx = idx
        self._restore(self.history[idx][1])

    def undo_step(self):
        """Ctrl+Z : revient à l'étape précédente de l'historique. Faux s'il n'y en a plus."""
        self.flush()
        if self.hist_idx <= 0:
            return False
        self.hist_idx -= 1
        self._refresh_history()
        self._restore(self.history[self.hist_idx][1])
        return True

    def reset_all(self):
        self.apply_dev(None, "Réinitialisation")

    def apply_dev(self, dev, label, keep_geometry=False):
        """Remplace les réglages (collage, préréglage « Précédent »…)."""
        self.flush()
        p = dev_params(dev)
        self.dev_p = p
        if not keep_geometry:
            self.ops = list((dev or {}).get("ops") or [])
            self.crop = list((dev or {}).get("crop") or CROP_FULL)
        self._load_sliders(self.dev_p)
        self.overlay.crop = list(self.crop)
        self._dirty = True
        self._label = label
        self._render()
        self._commit()

    def apply_preset(self, name, values):
        self.flush()
        for k in EDIT_DEFAULTS:
            if k not in ("bw",):
                self.dev_p[k] = EDIT_DEFAULTS[k]
        self.dev_p["bw"] = False
        self.dev_p.update(values)
        self._load_sliders(self.dev_p)
        self._dirty = True
        self._label = f"Préréglage : {name}"
        self._render()
        self._commit()

    def apply_auto(self):
        if self.last_img is None or np is None:
            return
        self._ensure_small()
        vals = auto_tone(self.small)
        self.dev_p.update(vals)
        self._load_sliders(self.dev_p)
        self._dirty = True
        self._label = "Tonalité automatique"
        self._render()
        self._commit()

    # ------------------------------------------------------------------ zoom / avant-après
    def _zoom(self, fn):
        if self.crop_mode:
            return
        fn()

    def _on_before(self, on):
        self.before = bool(on)
        self._render()

    # ------------------------------------------------------------------ recadrage
    def set_crop_mode(self, on):
        on = bool(on)
        if self.btn_crop.isChecked() != on:
            self.btn_crop.setChecked(on)
            return
        self.crop_mode = on
        self.crop_panel.setVisible(on)
        self.view.locked = on
        self.overlay.setVisible(False)
        if on:
            self.btn_before.setChecked(False)
            self.view.fit_view()
        self._render()
        if on:
            self.overlay.crop = list(self.crop)
            self.overlay.img_size = self.full_size()
            self._sync_overlay()
            self.overlay.setVisible(True)
            self.overlay.raise_()
            self.overlay.update()
        else:
            self._commit()

    def _sync_overlay(self):
        self.overlay.setGeometry(self.view.viewport().rect())
        self.overlay.update()

    def _on_crop_drag(self):
        self.crop = list(self.overlay.crop)
        self._touch("Recadrage", render=False)

    def _on_ratio(self, _i):
        if self._loading:
            return
        val = self.cb_ratio.currentData()
        if val == "orig":
            w, h = self.full_size()
            val = w / h
        if not self.btn_crop.isChecked():
            self.btn_crop.setChecked(True)
        self.overlay.set_ratio(val)

    def _flip_ratio(self):
        if self.overlay.ratio:
            self.overlay.set_ratio(1.0 / self.overlay.ratio)

    def _reset_crop(self):
        self.crop = list(CROP_FULL)
        self.overlay.crop = list(CROP_FULL)
        self.overlay.ratio = None
        self.cb_ratio.blockSignals(True)
        self.cb_ratio.setCurrentIndex(0)
        self.cb_ratio.blockSignals(False)
        self.overlay.update()
        self._touch("Recadrage", render=False)

    def _geo_op(self, op):
        self.ops.append(op)
        self.crop = list(rect_after(self.crop, op))
        self.overlay.crop = list(self.crop)
        if op in ("l", "r") and self.overlay.ratio:
            self.overlay.ratio = 1.0 / self.overlay.ratio
        label = {"l": "Rotation à gauche", "r": "Rotation à droite",
                 "h": "Miroir horizontal", "v": "Miroir vertical"}[op]
        self._touch(label)
        self.overlay.img_size = self.full_size()
        if self.crop_mode:
            self.view.fit_view()

    def full_size(self):
        """Taille réelle (l, h) de la photo après rotations, avant recadrage."""
        img = self.last_img
        if img is None:
            return (1, 1)
        w, h = img.width(), img.height()
        turns = sum(1 for o in self.ops if o in ("l", "r"))
        return (h, w) if turns % 2 else (w, h)

    # ------------------------------------------------------------------ rendu
    def _ensure_small(self):
        if self.small is None and self.last_img is not None:
            im = self.last_img
            if max(im.width(), im.height()) > self.PREVIEW:
                im = im.scaled(self.PREVIEW, self.PREVIEW, Qt.AspectRatioMode.KeepAspectRatio,
                               Qt.TransformationMode.SmoothTransformation)
            self.small = qimage_to_array(im)

    def _render(self):
        img = self.last_img
        if img is None:
            return
        self._version += 1
        cropped = (not self.crop_mode) and self.crop != CROP_FULL
        tone_on = (not edit_is_neutral(self.dev_p)) and not self.before
        if np is None or not (tone_on or self.ops or cropped):
            if self._orig_pm is None:
                self._orig_pm = QPixmap.fromImage(img)
            self.view.set_pixmap(self._orig_pm, None, keep_view=True)
            if self.hist_on:
                self.hist.set_image(img)
            return
        self._ensure_small()
        arr = apply_geometry(self.small, self.ops)
        if cropped:
            arr = crop_array(arr, self.crop)
        if tone_on:
            arr = apply_tone(arr, self.dev_p)
        qi = array_to_qimage(arr)
        fw, fh = self.full_size()
        if cropped:
            fw, fh = (max(1, round((self.crop[2] - self.crop[0]) * fw)),
                      max(1, round((self.crop[3] - self.crop[1]) * fh)))
        self.view.set_pixmap(QPixmap.fromImage(qi), (fw, fh), keep_view=True)
        if self.hist_on:
            self.hist.set_image(qi)
        if max(img.width(), img.height()) > self.PREVIEW and not self.crop_mode:
            self.refine_timer.start()

    def _refine(self):
        img = self.last_img
        if img is None or np is None or self.crop_mode:
            return
        tone_on = (not edit_is_neutral(self.dev_p)) and not self.before
        if not (tone_on or self.ops or self.crop != CROP_FULL):
            return
        dev = {"p": dict(self.dev_p), "ops": list(self.ops), "crop": list(self.crop)}
        QThreadPool.globalInstance().start(_RefineJob(img, dev, self._version, tone_on, self._rsig))

    def _on_refined(self, version, qi):
        if version != self._version or self.last_img is None or qi.isNull() or self.crop_mode:
            return
        fw, fh = self.full_size()
        if self.crop != CROP_FULL:
            fw, fh = (max(1, round((self.crop[2] - self.crop[0]) * fw)),
                      max(1, round((self.crop[3] - self.crop[1]) * fh)))
        self.view.set_pixmap(QPixmap.fromImage(qi), (fw, fh), keep_view=True)

    def render_for_export(self):
        """Photo développée à pleine définition (QImage), ou None."""
        if self.last_img is None or np is None:
            return None
        arr = qimage_to_array(self.last_img)
        return array_to_qimage(render_dev(arr, self.current_dev()))


class RecentCard(QPushButton):
    """Carte d'un dossier récent sur la page d'accueil."""
    remove_clicked = Signal()

    def __init__(self):
        super().__init__()
        self.setObjectName("recentCard")
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.setMinimumHeight(96)
        lay = QHBoxLayout(self)
        lay.setContentsMargins(16, 12, 10, 12)
        lay.setSpacing(14)
        self.icon = QLabel("")
        self.icon.setObjectName("cardIcon")
        self.icon.setFixedSize(46, 46)
        self.icon.setAlignment(Qt.AlignmentFlag.AlignCenter)
        col = QVBoxLayout()
        col.setSpacing(3)
        self.name = QLabel()
        self.name.setObjectName("cardName")
        self.path = QLabel()
        self.path.setObjectName("muted")
        self.stats = QLabel()
        self.stats.setObjectName("muted")
        self.bar = QProgressBar()
        self.bar.setRange(0, 100)
        self.bar.setTextVisible(False)
        for w in (self.icon, self.name, self.path, self.stats, self.bar):
            w.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents, True)
        for w in (self.name, self.path, self.stats, self.bar):
            col.addWidget(w)
        lay.addWidget(self.icon)
        lay.addLayout(col, 1)
        self.btn_x = QPushButton("✕")
        self.btn_x.setObjectName("ghost")
        self.btn_x.setFixedSize(28, 28)
        self.btn_x.setToolTip("Retirer de la liste")
        self.btn_x.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.btn_x.clicked.connect(lambda: self.remove_clicked.emit())
        lay.addWidget(self.btn_x, 0, Qt.AlignmentFlag.AlignTop)

    def set_info(self, name, path, stats, pct):
        fm = QFontMetrics(self.font())
        self.name.setText(fm.elidedText(name, Qt.TextElideMode.ElideRight, 280))
        self.path.setText(fm.elidedText(path, Qt.TextElideMode.ElideMiddle, 300))
        self.stats.setText(stats)
        if ANIM["on"] and pct:
            self.bar.setValue(0)
            self._bar_anim = QPropertyAnimation(self.bar, b"value", self)
            self._bar_anim.setDuration(700)
            self._bar_anim.setStartValue(0)
            self._bar_anim.setEndValue(pct)
            self._bar_anim.setEasingCurve(QEasingCurve.Type.OutCubic)
            self._bar_anim.start()
        else:
            self.bar.setValue(pct)
        self.icon.setText((name.strip()[:1] or "?").upper())
        self.setToolTip(path)


class DestButton(QPushButton):
    """Bouton de destination : pastille de couleur, nom, compteur, touche."""

    def __init__(self):
        super().__init__()
        self.setObjectName("dest")
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setMinimumHeight(36)
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        lay = QHBoxLayout(self)
        lay.setContentsMargins(10, 0, 8, 0)
        lay.setSpacing(8)
        self.dot = QLabel()
        self.dot.setFixedSize(12, 12)
        self.name = QLabel()
        self.count = QLabel()
        self.count.setObjectName("muted")
        self.key = QLabel()
        self.key.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.key.setFixedSize(20, 20)
        for w in (self.dot, self.name, self.count, self.key):
            w.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents, True)
        lay.addWidget(self.dot)
        lay.addWidget(self.name, 1)
        lay.addWidget(self.count)
        lay.addWidget(self.key)

    def set_dest(self, dest, sent):
        c = dest.get("color", "#6d8cff")
        self.dot.setStyleSheet(f"background: {c}; border-radius: 6px;")
        self.name.setText(dest["name"])
        self.setToolTip(dest["path"])
        self.count.setText(str(sent) if sent else "")
        key = dest.get("key", "")
        self.key.setText(key)
        self.key.setVisible(bool(key))
        self.key.setStyleSheet(f"background: {PAL['key_bg']}; border-radius: 6px; "
                               f"color: {PAL['key_fg']}; font-weight: 700; font-size: 11px;")


class Toast(QLabel):
    """Petite notification en bas de la zone centrale."""

    def __init__(self, parent):
        super().__init__(parent)
        self.setObjectName("toast")
        self.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents, True)
        self.timer = QTimer(self)
        self.timer.setSingleShot(True)
        self.timer.timeout.connect(self._close)
        self.eff = QGraphicsOpacityEffect(self)
        self.setGraphicsEffect(self.eff)
        self.anim = QPropertyAnimation(self.eff, b"opacity", self)
        self.anim.setEasingCurve(QEasingCurve.Type.OutCubic)
        self.anim.finished.connect(self._anim_done)
        self._closing = False
        self.hide()

    def show_message(self, text, ms=3500):
        self._closing = False
        self.anim.stop()
        self.setText(text)
        self.adjustSize()
        self.reposition()
        self.show()
        self.raise_()
        if ANIM["on"]:
            self.anim.setDuration(200)
            self.anim.setStartValue(0.0)
            self.anim.setEndValue(1.0)
            self.anim.start()
        else:
            self.eff.setOpacity(1.0)
        self.timer.start(ms)

    def _close(self):
        if ANIM["on"] and self.isVisible():
            self.anim.stop()
            self._closing = True
            self.anim.setDuration(280)
            self.anim.setStartValue(1.0)
            self.anim.setEndValue(0.0)
            self.anim.start()
        else:
            self.hide()

    def _anim_done(self):
        if self._closing:
            self._closing = False
            self.hide()

    def reposition(self):
        p = self.parentWidget()
        if p is not None:
            self.move(max(0, (p.width() - self.width()) // 2), max(0, p.height() - self.height() - 30))


class Content(QWidget):
    def __init__(self):
        super().__init__()
        self.toast = None

    def resizeEvent(self, e):
        super().resizeEvent(e)
        if self.toast is not None:
            self.toast.reposition()


class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle(APP_NAME)
        self.resize(1400, 900)
        self.setAcceptDrops(True)
        self.settings = QSettings("TrieurPhotos", "TrieurPhotos")
        self.pool = QThreadPool.globalInstance()
        self.pool.setMaxThreadCount(max(2, min(8, os.cpu_count() or 4)))
        self.store = Store()
        self.model = PhotoModel(self.pool)
        self.root = None
        self.view_row = -1
        self.view_cache = OrderedDict()
        self.view_pending = set()
        self.view_counter = 0
        self.meta_cache = {}
        self.view_sig = _ViewSignals()
        self.view_sig.ready.connect(self._on_view_ready)
        self.undo_stack = []
        self.compare_paths = []
        self.compare_active = 0
        self.recent = []
        self.destinations = []
        self.dest_mode = "move"
        self.dest_shortcuts = []
        self.dest_buttons = []
        self.sent_counts = {}
        self.flag_value = "all"
        self.filter_widgets = []
        self.folder_stats = {}
        self._before_settings = None
        self._prev_dev = None
        self._dev_clip = None
        self.side_hidden = False
        self.side_w = 228
        self.slide_timer = QTimer(self)
        self.slide_timer.setInterval(4000)
        self.slide_timer.timeout.connect(self._slide_tick)
        self._syncing = False
        self._prev_sort = "name"
        self.swatches = []

        self._build_ui()
        self._build_menus()
        self._build_shortcuts()
        self._restore_settings()
        self.update_status()

    # ---------------- construction
    def _build_ui(self):
        central = QWidget()
        self.setCentralWidget(central)
        outer_l = QHBoxLayout(central)
        outer_l.setContentsMargins(0, 0, 0, 0)
        outer_l.setSpacing(0)
        self.split = QSplitter(Qt.Orientation.Horizontal)
        self.split.setHandleWidth(5)
        self.split.setChildrenCollapsible(False)
        outer_l.addWidget(self.split)
        root = self.split
        self.sidebar = self._build_sidebar()
        root.addWidget(self.sidebar)

        self.content = Content()
        cl = QVBoxLayout(self.content)
        cl.setContentsMargins(0, 0, 0, 0)
        cl.setSpacing(0)
        self.topbar = self._build_topbar()
        cl.addWidget(self.topbar)
        self.stack = QStackedWidget()
        cl.addWidget(self.stack, 1)
        root.addWidget(self.content)
        self.split.setStretchFactor(0, 0)
        self.split.setStretchFactor(1, 1)
        self.split.splitterMoved.connect(self._on_split_moved)

        # page 0 : accueil
        self.home_page = self._build_home()
        self.stack.addWidget(self.home_page)

        # page 1 : grille
        self.delegate = PhotoDelegate()
        self.grid = GridView()
        self.grid.setModel(self.model)
        self.grid.setItemDelegate(self.delegate)
        self.grid.setViewMode(QListView.ViewMode.IconMode)
        self.grid.setResizeMode(QListView.ResizeMode.Adjust)
        self.grid.setMovement(QListView.Movement.Static)
        self.grid.setUniformItemSizes(True)
        self.grid.setSpacing(0)
        self.grid.setMouseTracking(True)
        self.grid.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        self.grid.setVerticalScrollMode(QAbstractItemView.ScrollMode.ScrollPerPixel)
        self.grid.verticalScrollBar().setSingleStep(40)
        self.grid.doubleClicked.connect(lambda ix: self.open_viewer(ix.row()))
        self.grid.star_clicked.connect(self.rate_row)
        self.grid.selectionModel().selectionChanged.connect(lambda *_: self.update_status())
        self.stack.addWidget(self.grid)

        # page 2 : visionneuse
        self.viewer = ViewerPage()
        self.viewer.set_model(self.model)
        self.viewer.film.clicked.connect(lambda ix: self.show_row(ix.row()))
        self.viewer.stars.rated.connect(lambda n: self.apply(rating=n, advance=False))
        self.viewer.flag_requested.connect(lambda f: self.apply(flag=f, advance=False))
        self.viewer.label_requested.connect(lambda n: self.set_label(n, [self.view_row]))
        self.viewer.dev_changed.connect(self._on_dev_changed)
        self.viewer.back_requested.connect(self.close_viewer)
        self.viewer.copy_requested.connect(self.copy_settings)
        self.viewer.paste_requested.connect(self.paste_settings)
        self.viewer.previous_requested.connect(self.paste_previous)
        self.viewer.export_requested.connect(self.export_photo)
        self.stack.addWidget(self.viewer)

        # page 3 : comparaison
        self.compare = ComparePage()
        self.stack.addWidget(self.compare)

        # page 4 : paramètres
        self.settings_page = self._build_settings()
        self.settings_page.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self.stack.addWidget(self.settings_page)

        self.grid.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.grid.customContextMenuRequested.connect(self._grid_menu)

        self.toast = Toast(self.content)
        self.content.toast = self.toast
        self.morph = ZoomMorph(self.content)
        for b in central.findChildren(QPushButton):
            b.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.sort_cb.activated.connect(lambda *_: self.grid.setFocus())
        self.rating_cb.activated.connect(lambda *_: self.grid.setFocus())

        self.on_size_changed(220)
        self.status_label = QLabel()
        self.statusBar().addWidget(self.status_label, 1)
        self.progress = QProgressBar()
        self.progress.setRange(0, 100)
        self.progress.setTextVisible(False)
        self.progress.setFixedWidth(150)
        self.progress_label = QLabel()
        self.statusBar().addPermanentWidget(self.progress_label)
        self.statusBar().addPermanentWidget(self.progress)
        self.stack.currentChanged.connect(self._on_page_changed)
        self._on_page_changed()

    def _section(self, text):
        lab = QLabel(text)
        lab.setObjectName("section")
        return lab

    def _chip(self, text, value, checked=False):
        b = QPushButton(text)
        b.setObjectName("chip")
        b.setCheckable(True)
        b.setChecked(checked)
        b.setCursor(Qt.CursorShape.PointingHandCursor)
        b.clicked.connect(lambda _=False, v=value: self._set_flag_filter(v))
        self.chip_group.addButton(b)
        self.filter_widgets.append(b)
        return b

    def _build_sidebar(self):
        side = QFrame()
        side.setObjectName("sidebar")
        side.setMinimumWidth(170)
        side.setMaximumWidth(560)
        side.setMinimumHeight(0)
        outer = QVBoxLayout(side)
        outer.setContentsMargins(0, 0, 0, 0)
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        outer.addWidget(scroll)
        inner = QWidget()
        inner.setObjectName("sidebarInner")
        scroll.setWidget(inner)
        lay = QVBoxLayout(inner)
        lay.setContentsMargins(12, 12, 12, 12)
        lay.setSpacing(6)

        brand_row = QHBoxLayout()
        brand_row.setSpacing(8)
        self.side_logo = QLabel()
        self.side_logo.setFixedSize(22, 22)
        self.side_logo.setPixmap(make_logo(22))
        brand = QLabel("Klutter")
        brand.setObjectName("brand")
        brand_row.addWidget(self.side_logo)
        brand_row.addWidget(brand)
        brand_row.addStretch(1)
        lay.addLayout(brand_row)
        nav = QHBoxLayout()
        nav.setSpacing(6)
        self.nav_home = QPushButton("Accueil")
        self.nav_home.setObjectName("ghost")
        self.nav_home.setToolTip("Page d'accueil (Ctrl+H)")
        self.nav_home.clicked.connect(self.go_home)
        self.nav_settings = QPushButton("Paramètres")
        self.nav_settings.setObjectName("ghost")
        self.nav_settings.setToolTip("Thème, couleur, options (Ctrl+,)")
        self.nav_settings.clicked.connect(self.open_settings)
        nav.addWidget(self.nav_home)
        nav.addWidget(self.nav_settings)
        lay.addLayout(nav)
        lay.addSpacing(4)

        btn_open = QPushButton("Ouvrir un dossier")
        btn_open.setObjectName("primary")
        btn_open.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_open.setToolTip("Choisir un dossier de photos (Ctrl+O)")
        btn_open.clicked.connect(self.choose_folder)
        lay.addWidget(btn_open)
        row = QHBoxLayout()
        row.setSpacing(6)
        self.btn_prev_folder = QPushButton("◀ Précédent")
        self.btn_prev_folder.setObjectName("ghost")
        self.btn_prev_folder.setToolTip("Revenir au dossier ouvert juste avant")
        self.btn_prev_folder.clicked.connect(self.go_previous_folder)
        btn_reload = QPushButton("↻ Actualiser")
        btn_reload.setObjectName("ghost")
        btn_reload.setToolTip("Relire le dossier (F5)")
        btn_reload.clicked.connect(self.reload_folder)
        row.addWidget(self.btn_prev_folder)
        row.addWidget(btn_reload)
        lay.addLayout(row)

        self.folder_label = QLabel("Aucun dossier ouvert")
        self.folder_label.setObjectName("folderName")
        self.folder_count = QLabel("")
        self.folder_count.setObjectName("muted")
        lay.addWidget(self.folder_label)
        lay.addWidget(self.folder_count)
        lay.addSpacing(2)

        lay.addWidget(self._section("AFFICHER"))
        self.chip_group = QButtonGroup(self)
        self.chip_group.setExclusive(True)
        grid = QGridLayout()
        grid.setSpacing(6)
        grid.addWidget(self._chip("Toutes", "all", True), 0, 0)
        grid.addWidget(self._chip("Gardées", "pick"), 0, 1)
        grid.addWidget(self._chip("Rejetées", "reject"), 1, 0)
        grid.addWidget(self._chip("Non triées", "none"), 1, 1)
        lay.addLayout(grid)
        lay.addSpacing(4)

        lay.addWidget(self._section("ÉTIQUETTES COULEUR"))
        lrow = QHBoxLayout()
        lrow.setSpacing(8)
        self.label_btns = {}
        for i in range(1, len(LABELS)):
            b = QPushButton()
            b.setCheckable(True)
            b.setFixedSize(24, 24)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.setToolTip(f"Afficher seulement les photos « {LABELS[i][0]} »")
            b.setStyleSheet(f"QPushButton {{ background: {LABELS[i][1]}; border: 2px solid transparent; "
                            f"border-radius: 12px; }} QPushButton:checked {{ border-color: #ffffff; }}")
            b.clicked.connect(lambda _=False, i=i: self._toggle_label_filter(i))
            lrow.addWidget(b)
            self.label_btns[i] = b
            self.filter_widgets.append(b)
        lrow.addStretch(1)
        lay.addLayout(lrow)
        lay.addSpacing(4)

        lay.addWidget(self._section("TRI ET NOTE"))
        self.sort_cb = QComboBox()
        for text, data in [("Nom", "name"), ("Date (anciennes d'abord)", "date_asc"),
                           ("Date (récentes d'abord)", "date_desc"),
                           ("★  Note : meilleures d'abord", "rating"),
                           ("☆  Note : moins bonnes d'abord", "rating_asc")]:
            self.sort_cb.addItem(text, data)
        self.rating_cb = QComboBox()
        self.rating_cb.addItem("Toutes les notes", 0)
        self.rating_cb.addItem("Sans étoile", -1)
        for i in range(1, 6):
            self.rating_cb.addItem(f"{'★' * i} et plus", i)
        self.sort_cb.currentIndexChanged.connect(self.on_filter_changed)
        self.rating_cb.currentIndexChanged.connect(self.on_filter_changed)
        lay.addWidget(self.sort_cb)
        lay.addWidget(self.rating_cb)
        self.filter_widgets += [self.sort_cb, self.rating_cb]
        lay.addSpacing(8)

        head = QHBoxLayout()
        head.addWidget(self._section("DESTINATIONS  ·  1 CLIC"), 1)
        lay.addLayout(head)
        modes = QHBoxLayout()
        modes.setSpacing(6)
        self.mode_group = QButtonGroup(self)
        self.mode_group.setExclusive(True)
        self.btn_move = QPushButton("Déplacer")
        self.btn_copy = QPushButton("Copier")
        for b in (self.btn_move, self.btn_copy):
            b.setObjectName("seg")
            b.setCheckable(True)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            self.mode_group.addButton(b)
            modes.addWidget(b)
        self.btn_move.setChecked(True)
        self.btn_move.clicked.connect(lambda: self._set_mode("move"))
        self.btn_copy.clicked.connect(lambda: self._set_mode("copy"))
        lay.addLayout(modes)
        self.dest_hint = QLabel("Ajoute un dossier : un clic y envoie la photo affichée "
                                "ou la sélection.")
        self.dest_hint.setObjectName("muted")
        self.dest_hint.setWordWrap(True)
        lay.addWidget(self.dest_hint)
        self.dest_box = QVBoxLayout()
        self.dest_box.setSpacing(8)
        lay.addLayout(self.dest_box)
        self.btn_add_dest = QPushButton("＋   Ajouter une destination")
        self.btn_add_dest.setObjectName("add")
        self.btn_add_dest.setCursor(Qt.CursorShape.PointingHandCursor)
        menu = QMenu(self.btn_add_dest)
        self._act(menu, "Choisir un dossier existant…", self.add_dest_existing)
        self._act(menu, "Créer un sous-dossier dans le dossier ouvert…", self.add_dest_subfolder)
        self.btn_add_dest.setMenu(menu)
        lay.addWidget(self.btn_add_dest)
        lay.addStretch(1)
        return side

    def _build_topbar(self):
        bar = QFrame()
        bar.setObjectName("topbar")
        bar.setFixedHeight(58)
        lay = QHBoxLayout(bar)
        lay.setContentsMargins(16, 9, 16, 9)
        lay.setSpacing(10)
        self.btn_side = QPushButton("☰")
        self.btn_side.setObjectName("ghostBorder")
        self.btn_side.setFixedWidth(40)
        self.btn_side.setToolTip("Afficher / masquer le panneau de gauche (Ctrl+B)")
        self.btn_side.clicked.connect(self.toggle_sidebar)
        lay.addWidget(self.btn_side)
        self.act_back = QPushButton("←  Grille")
        self.act_back.setToolTip("Retour à la grille (Échap)")
        self.act_back.clicked.connect(self.back_to_grid)
        self.act_back.setVisible(False)
        lay.addWidget(self.act_back)
        self.search = QLineEdit()
        self.search.setPlaceholderText("🔍  Rechercher un nom de fichier…")
        self.search.setClearButtonEnabled(True)
        self.search.setFixedWidth(240)
        self.search.textChanged.connect(self.on_filter_changed)
        self.search.returnPressed.connect(lambda: self.grid.setFocus())
        lay.addWidget(self.search)
        self.btn_cmp = QPushButton("⇆  Comparer")
        self.btn_cmp.setToolTip("Comparer 2 à 4 photos sélectionnées (C)")
        self.btn_cmp.clicked.connect(self.open_compare)
        lay.addWidget(self.btn_cmp)
        self.btn_sort_stars = QPushButton("★  Trier par note")
        self.btn_sort_stars.setObjectName("toggle")
        self.btn_sort_stars.setCheckable(True)
        self.btn_sort_stars.setToolTip("Classer les photos de la mieux notée à la moins bien notée")
        self.btn_sort_stars.clicked.connect(self._toggle_sort_stars)
        lay.addWidget(self.btn_sort_stars)
        self.btn_resort = QPushButton("↻")
        self.btn_resort.setObjectName("ghost")
        self.btn_resort.setToolTip("Réappliquer le tri : replace les photos dont tu viens de "
                                   "changer la note (F6)")
        self.btn_resort.clicked.connect(lambda: self.resort())
        lay.addWidget(self.btn_resort)
        lay.addStretch(1)
        self.btn_undo = QPushButton("↶  Annuler")
        self.btn_undo.setToolTip("Annuler la dernière action (Ctrl+Z)")
        self.btn_undo.clicked.connect(self.undo)
        lay.addWidget(self.btn_undo)
        self.size_label = QLabel("Taille")
        self.size_label.setObjectName("muted")
        self.size_slider = QSlider(Qt.Orientation.Horizontal)
        self.size_slider.setRange(130, 360)
        self.size_slider.setValue(220)
        self.size_slider.setFixedWidth(130)
        self.size_slider.setFocusPolicy(Qt.FocusPolicy.NoFocus)  # les flèches restent pour la grille
        self.size_slider.valueChanged.connect(self.on_size_changed)
        lay.addWidget(self.size_label)
        lay.addWidget(self.size_slider)
        self.filter_widgets += [self.search, self.btn_cmp, self.btn_sort_stars, self.btn_resort,
                                self.size_slider, self.size_label]
        return bar

    TAGLINES = [
        "Trier, c'est choisir : garde l'essentiel, laisse le reste.",
        "Une bonne série commence par un bon tri.",
        "Ton œil fait la différence, Klutter s'occupe du reste.",
        "Les meilleures photos méritent d'être retrouvées en quelques secondes.",
        "Chaque photo gardée est une histoire que tu choisis de raconter.",
        "Moins de photos, plus d'impact.",
        "Dix minutes de tri aujourd'hui, des heures gagnées demain.",
        "Ta prochaine photo préférée est peut-être déjà dans ce dossier.",
        "Un dossier trié, c'est l'esprit libre pour la prochaine séance.",
        "Prends ton temps, ou va droit au but : au clavier, tout va vite.",
        "La lumière, le cadrage, l'instant : à toi de décider ce qui reste.",
        "Un peu d'ordre aujourd'hui, un grand plaisir de retoucher demain.",
        "Ne laisse plus tes meilleures images dormir dans un dossier.",
        "Le plus dur, c'est de commencer. Ouvre un dossier.",
    ]
    TIPS = [
        ("Notes en étoiles", "Touches 1 à 5, ou clique sur les étoiles d'une photo. "
                             "Classe ensuite tout par note."),
        ("Garder ou rejeter", "P pour garder, X pour rejeter, N pour passer à la prochaine photo non triée."),
        ("Destinations en 1 clic", "Ajoute des dossiers dans la barre latérale : un clic y envoie tes photos "
                                   "(Ctrl+Z pour annuler)."),
        ("Développement", "Ouvre une photo : exposition, couleurs, recadrage… Tes réglages sont "
                          "enregistrés sans jamais toucher à l'original."),
        ("Copier les réglages", "Ctrl+Maj+C sur une photo retouchée, puis Ctrl+Maj+V sur les autres : "
                                "toute une série prend le même look."),
        ("Avant / après", "Appuie sur la touche \\ dans la photo pour comparer avec l'original."),
        ("Remise à zéro rapide", "Double-clic sur le nom d'un curseur pour le remettre à zéro."),
        ("Plus de place", "Tab masque les panneaux de la visionneuse, Ctrl+B replie la barre latérale "
                          "de la grille."),
        ("Renommer", "F2 renomme la photo (et ses fichiers .xmp ou .jpg associés)."),
        ("Comparer", "Sélectionne 2 à 4 photos puis appuie sur C pour choisir la meilleure."),
        ("Zoom", "Molette pour zoomer, Z ou double-clic pour passer de 100 % à ajusté."),
        ("À ton goût", "Thème clair ou sombre et couleur de l'application dans les paramètres."),
    ]

    def _build_home(self):
        page = QScrollArea()
        page.setWidgetResizable(True)
        page.setFrameShape(QFrame.Shape.NoFrame)
        page.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        inner = QWidget()
        page.setWidget(inner)
        outer = QVBoxLayout(inner)
        outer.setContentsMargins(40, 22, 40, 40)
        wrap = QWidget()
        wrap.setMaximumWidth(900)
        col = QVBoxLayout(wrap)
        col.setContentsMargins(0, 0, 0, 0)
        col.setSpacing(0)
        outer.addWidget(wrap, 0, Qt.AlignmentFlag.AlignHCenter)
        outer.addStretch(1)

        top = QHBoxLayout()
        top.addStretch(1)
        btn_set = QPushButton("Paramètres")
        btn_set.setObjectName("ghostBorder")
        btn_set.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_set.setToolTip("Thème, couleur, options (Ctrl+,)")
        btn_set.clicked.connect(self.open_settings)
        top.addWidget(btn_set)
        col.addLayout(top)
        col.addSpacing(10)

        # logo + nom de l'application au premier plan, phrase qui change en dessous
        self.home_logo = QLabel()
        self.home_logo.setFixedSize(112, 112)
        self.home_logo.setPixmap(make_logo(112))
        self.home_logo.setAlignment(Qt.AlignmentFlag.AlignCenter)
        title = QLabel(APP_NAME)
        title.setObjectName("homeTitle")
        title.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.home_tagline = FadingLabel(random.choice(self.TAGLINES))
        self.home_tagline.setObjectName("homeTagline")
        self.home_tagline.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.home_tagline.setWordWrap(True)
        self.home_tagline.setMinimumHeight(40)
        self.home_sub = QLabel()
        self.home_sub.setObjectName("homeSub")
        self.home_sub.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.home_sub.setWordWrap(True)
        col.addWidget(self.home_logo, 0, Qt.AlignmentFlag.AlignHCenter)
        col.addSpacing(8)
        col.addWidget(title)
        col.addSpacing(2)
        col.addWidget(self.home_tagline)
        col.addSpacing(18)
        col.addWidget(self.home_sub)
        col.addSpacing(16)

        row = QHBoxLayout()
        row.setSpacing(12)
        row.addStretch(1)
        b = QPushButton("Ouvrir un dossier")
        b.setObjectName("primary")
        b.setMinimumHeight(48)
        b.setMinimumWidth(240)
        b.setCursor(Qt.CursorShape.PointingHandCursor)
        b.clicked.connect(self.choose_folder)
        self.btn_resume = QPushButton("Reprendre le tri")
        self.btn_resume.setMinimumHeight(48)
        self.btn_resume.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_resume.clicked.connect(self.resume_folder)
        self.btn_resume.setVisible(False)
        row.addWidget(b)
        row.addWidget(self.btn_resume)
        row.addStretch(1)
        col.addLayout(row)
        col.addSpacing(16)

        drop = QLabel("Glisse un dossier de photos ici pour l'ouvrir")
        drop.setObjectName("dropZone")
        drop.setAlignment(Qt.AlignmentFlag.AlignCenter)
        drop.setMinimumHeight(80)
        col.addWidget(drop)
        col.addSpacing(28)

        self.home_recent_title = self._section("DOSSIERS RÉCENTS")
        col.addWidget(self.home_recent_title)
        col.addSpacing(8)
        self.home_recent_grid = QGridLayout()
        self.home_recent_grid.setSpacing(12)
        col.addLayout(self.home_recent_grid)
        self.home_empty = QLabel("Aucun dossier récent pour l'instant.")
        self.home_empty.setObjectName("muted")
        col.addWidget(self.home_empty)
        col.addSpacing(28)

        col.addWidget(self._section("ASTUCES"))
        col.addSpacing(8)
        self.home_tips = QGridLayout()
        self.home_tips.setSpacing(12)
        col.addLayout(self.home_tips)
        self.home_tips.setColumnStretch(0, 1)
        self.home_tips.setColumnStretch(1, 1)
        self._tip_order = random.sample(range(len(self.TIPS)), len(self.TIPS))
        self._fill_tips()
        self.tag_timer = QTimer(self)
        self.tag_timer.setInterval(7000)
        self.tag_timer.timeout.connect(self._next_tagline)
        self.tag_timer.start()
        return page

    def _fill_tips(self):
        """Quatre astuces tirées au sort parmi toutes celles de la liste."""
        grid = self.home_tips
        while grid.count():
            it = grid.takeAt(0)
            w = it.widget()
            if w is not None:
                w.setParent(None)
                w.deleteLater()
        self._tip_order = self._tip_order[4:] + self._tip_order[:4]
        for i, idx in enumerate(self._tip_order[:4]):
            title, text = self.TIPS[idx]
            f = QFrame()
            f.setObjectName("tipCard")
            fl = QVBoxLayout(f)
            fl.setContentsMargins(16, 14, 16, 16)
            fl.setSpacing(6)
            t = QLabel(title)
            t.setObjectName("tipTitle")
            d = QLabel(text)
            d.setObjectName("muted")
            d.setWordWrap(True)
            fl.addWidget(t)
            fl.addWidget(d)
            fl.addStretch(1)
            grid.addWidget(f, i // 2, i % 2)

    def _next_tagline(self):
        if self.stack.currentWidget() is not self.home_page or not self.isVisible():
            return
        cur = self.home_tagline.text()
        choices = [t for t in self.TAGLINES if t != cur] or self.TAGLINES
        self.home_tagline.swap(random.choice(choices))

    @staticmethod
    def _ago(ts):
        try:
            days = (datetime.date.today() - datetime.date.fromtimestamp(ts)).days
        except Exception:
            return ""
        if days <= 0:
            return "aujourd'hui"
        if days == 1:
            return "hier"
        if days < 30:
            return f"il y a {days} jours"
        return datetime.date.fromtimestamp(ts).strftime("%d/%m/%Y")

    @staticmethod
    def _stats_key(path):
        return os.path.normcase(os.path.normpath(path))

    def _load_folder_stats(self):
        try:
            d = json.loads(self.settings.value("folder_stats", "{}"))
            self.folder_stats = d if isinstance(d, dict) else {}
        except Exception:
            self.folder_stats = {}

    def _remember_stats(self):
        """Mémorise la progression du dossier ouvert (affichée sur l'accueil)."""
        if self.root and self.model.all:
            total, picks, rejects = self.model.counts()
            self.folder_stats[self._stats_key(self.root)] = {
                "total": total, "done": picks + rejects, "picks": picks, "ts": time.time()}
        keep = {self._stats_key(r) for r in self.recent}
        if self.root:
            keep.add(self._stats_key(self.root))
        self.folder_stats = {k: v for k, v in self.folder_stats.items() if k in keep}
        self.settings.setValue("folder_stats", json.dumps(self.folder_stats))

    def _refresh_home(self):
        if not hasattr(self, "home_recent_grid"):
            return
        has = bool(self.root) and bool(self.model.all)
        self.btn_resume.setVisible(has)
        if has:
            total, picks, rejects = self.model.counts()
            name = os.path.basename(self.root.rstrip("/\\")) or self.root
            short = name if len(name) <= 26 else name[:25] + "…"
            self.btn_resume.setText(f"Reprendre « {short} »")
            self.home_sub.setText(f"« {name} » est ouvert : {picks + rejects} photo(s) triée(s) "
                                  f"sur {total}.")
        else:
            self.home_sub.setText("Ouvre un dossier de photos pour commencer à trier.")
        grid = self.home_recent_grid
        while grid.count():
            it = grid.takeAt(0)
            w = it.widget()
            if w is not None:
                w.setParent(None)
                w.deleteLater()
        for i, rp in enumerate(self.recent[:6]):
            card = RecentCard()
            if not os.path.isdir(rp):
                stats, pct = "Dossier introuvable", 0
            else:
                if has and self._stats_key(self.root) == self._stats_key(rp):
                    total, picks, rejects = self.model.counts()
                    st = {"total": total, "done": picks + rejects, "ts": time.time()}
                else:
                    st = self.folder_stats.get(self._stats_key(rp))
                if st and st.get("total"):
                    pct = int(100 * st["done"] / st["total"])
                    stats = (f"{st['total']} photos · {st['done']} triées ({pct} %) · "
                             f"{self._ago(st.get('ts'))}")
                else:
                    stats, pct = "Pas encore trié", 0
            card.set_info(os.path.basename(rp.rstrip("/\\")) or rp, rp, stats, pct)
            card.clicked.connect(lambda _=False, rp=rp: self._open_recent(rp))
            card.remove_clicked.connect(lambda rp=rp: self._forget_recent(rp))
            grid.addWidget(card, i // 2, i % 2)
            fade_in(card, 320, delay=120 + i * 70)
        grid.setColumnStretch(0, 1)
        grid.setColumnStretch(1, 1)
        self.home_empty.setVisible(not self.recent)
        if self.stack.currentWidget() is self.home_page:
            fade_in(self.home_logo, 450)
            fade_in(self.home_sub, 380, delay=90)

    def _forget_recent(self, rp):
        self.recent = [x for x in self.recent if x != rp]
        self.settings.setValue("recent", json.dumps(self.recent))
        self._refresh_recent_menu()

    def _build_menus(self):
        mb = self.menuBar()
        m = mb.addMenu("&Fichier")
        self._act(m, "Accueil", self.go_home, "Ctrl+H")
        self._act(m, "Paramètres…", self.open_settings, "Ctrl+,")
        m.addSeparator()
        self._act(m, "Ouvrir un dossier…", self.choose_folder, "Ctrl+O")
        self._act(m, "Actualiser", self.reload_folder, "F5")
        self.menu_recent = m.addMenu("Dossiers récents")
        self._act(m, "Dossier précédent", self.go_previous_folder)
        m.addSeparator()
        self._act(m, "Quitter", self.close, "Ctrl+Q")

        m = mb.addMenu("&Trier")
        self._act(m, "Annuler la dernière action (Ctrl+Z)", self.undo)
        m.addSeparator()
        self._act(m, "Ajouter une destination (dossier existant)…", self.add_dest_existing)
        self._act(m, "Ajouter une destination (sous-dossier du dossier ouvert)…",
                  self.add_dest_subfolder)
        m.addSeparator()
        self._act(m, "Déplacer les rejetées vers le dossier « Rejetées »",
                  self.move_rejects)
        self._act(m, "Déplacer les gardées vers un dossier…",
                  lambda: self.transfer_flagged(PICK, True))
        self._act(m, "Copier les gardées vers un dossier…",
                  lambda: self.transfer_flagged(PICK, False))
        m.addSeparator()
        self._act(m, "Copier la sélection vers un dossier…", self.copy_selection)
        m.addSeparator()
        self._act(m, "Copier les noms des gardées dans le presse-papiers", self.copy_pick_names)
        self._act(m, "Exporter la liste (CSV)…", self.export_csv)
        self._act(m, "Écrire notes et drapeaux dans des fichiers .xmp (Lightroom/Bridge)…",
                  self.write_xmp)

        m = mb.addMenu("&Photo")
        self._act(m, "Renommer la photo…", self.rename_photo, "F2")
        self._act(m, "Développer la photo…", self.develop_photo, "Ctrl+E")
        m.addSeparator()
        for i in range(1, len(LABELS)):
            self._act(m, f"Étiquette {LABELS[i][0].lower()}" + (f"  ({i + 5})" if i < 5 else ""),
                      lambda i=i: self.set_label(i))
        m.addSeparator()
        self._act(m, "Augmenter la note  ( ] )", lambda: self._step_rating(1))
        self._act(m, "Diminuer la note  ( [ )", lambda: self._step_rating(-1))
        m.addSeparator()
        self._act(m, "Copier les réglages", self.copy_settings, "Ctrl+Shift+C")
        self._act(m, "Coller les réglages", self.paste_settings, "Ctrl+Shift+V")
        self._act(m, "Réinitialiser les réglages", self.reset_settings)
        m.addSeparator()
        self._act(m, "Exporter la photo développée…", self.export_photo, "Ctrl+Shift+E")

        m = mb.addMenu("&Affichage")
        self.act_recursive = self._act(m, "Inclure les sous-dossiers", self.reload_folder,
                                       checkable=True)
        self.act_advance = self._act(m, "Passer à la photo suivante après une note / un envoi "
                                        "(visionneuse)", None, checkable=True)
        self.act_advance.setChecked(True)
        m.addSeparator()
        self._act(m, "Afficher / masquer l'histogramme (H)", self.toggle_hist)
        self._act(m, "Grille de composition (G)", lambda: self.viewer.cycle_guides()
                  if self.stack.currentWidget() is self.viewer else None)
        self._act(m, "Lumières éteintes (L)", lambda: self.viewer.toggle_lights()
                  if self.stack.currentWidget() is self.viewer else None)
        self._act(m, "Diaporama (S)", self.toggle_slideshow)
        self._act(m, "Plein écran", self.toggle_fullscreen, "F11")
        m.addSeparator()
        self._act(m, "Comparer la sélection (C)", self.open_compare)
        self._act(m, "Prochaine photo non triée (N)", self.next_unsorted)
        self._act(m, "Réappliquer le tri (F6)", self.resort, "F6")

        m = mb.addMenu("&Aide")
        self._act(m, "Raccourcis clavier", self.show_help, "F1")

    def _act(self, menu, text, slot, shortcut=None, checkable=False):
        a = QAction(text, self)
        a.setCheckable(checkable)
        if shortcut:
            a.setShortcut(QKeySequence(shortcut))
        if slot:
            if checkable:
                a.toggled.connect(lambda _=False, s=slot: s())
            else:
                a.triggered.connect(lambda _=False, s=slot: s())
        menu.addAction(a)
        return a

    def _bind(self, seq, fn, widget=None, ctx=Qt.ShortcutContext.WindowShortcut):
        sc = QShortcut(QKeySequence(seq), widget or self)
        sc.setContext(ctx)
        sc.activated.connect(fn)
        return sc

    def _build_shortcuts(self):
        for i in range(6):
            self._bind(str(i), lambda i=i: self.apply(rating=i))
        self._bind("P", lambda: self.apply(flag=PICK))
        self._bind("X", lambda: self.apply(flag=REJECT))
        self._bind("U", lambda: self.apply(flag=NO_FLAG))
        self._bind("Ctrl+Z", self.undo)
        ctx = Qt.ShortcutContext.WidgetWithChildrenShortcut
        for key in ("Return", "Enter"):
            self._bind(key, self._open_current, self.grid, ctx)
            self._bind(key, self.close_viewer, self.viewer, ctx)
        self._bind("Escape", self.close_viewer, self.viewer, ctx)
        self._bind("Alt+Left", self.close_viewer, self.viewer, ctx)
        QApplication.instance().installEventFilter(self)
        self._bind("Right", lambda: self.step(1), self.viewer, ctx)
        self._bind("Space", lambda: self.step(1), self.viewer, ctx)
        self._bind("Left", lambda: self.step(-1), self.viewer, ctx)
        self._bind("Backspace", lambda: self.step(-1), self.viewer, ctx)
        self._bind("F", self.viewer.view.fit_view, self.viewer, ctx)
        self._bind("C", self.open_compare)
        self._bind("H", lambda: self.viewer.toggle_hist() if self.stack.currentWidget() is self.viewer else None)
        self._bind("Z", self.viewer.view.toggle_zoom, self.viewer, ctx)
        self._bind("Escape", self._clear_search, self.search, Qt.ShortcutContext.WidgetShortcut)
        # claviers AZERTY : rangée du haut sans Maj (à & é " ' ( = 0 à 5)
        for i, ch in enumerate(["à", "&", "é", '"', "'", "("]):
            self._bind(ch, lambda i=i: self.apply(rating=i))
        self._bind("N", self.next_unsorted)
        for i, ch in enumerate(["6", "7", "8", "9"]):
            self._bind(ch, lambda i=i: self.set_label(i + 1))
        for i, ch in enumerate(["-", "è", "_", "ç"]):
            self._bind(ch, lambda i=i: self.set_label(i + 1))
        self._bind("]", lambda: self._step_rating(1))
        self._bind("[", lambda: self._step_rating(-1))
        self._bind("Ctrl+Up", lambda: self._step_rating(1))
        self._bind("Ctrl+Down", lambda: self._step_rating(-1))
        self._bind("S", self.toggle_slideshow, self.viewer, ctx)
        self._bind("G", self.viewer.cycle_guides, self.viewer, ctx)
        self._bind("L", self.viewer.toggle_lights, self.viewer, ctx)
        for key in ("Escape", "Return", "Enter"):
            self._bind(key, self.close_compare, self.compare, ctx)
        self._bind("Right", lambda: self.compare_step(1), self.compare, ctx)
        self._bind("Left", lambda: self.compare_step(-1), self.compare, ctx)
        self._bind("Escape", self.settings_back, self.settings_page, ctx)
        self._bind("B", lambda: self.viewer.btn_before.toggle(), self.viewer, ctx)
        self._bind("\\", lambda: self.viewer.btn_before.toggle(), self.viewer, ctx)
        self._bind("Tab", self.viewer.toggle_side_panels, self.viewer, ctx)
        self._bind("Shift+Tab", lambda: self.viewer.toggle_side_panels(True), self.viewer, ctx)
        self._bind("Ctrl+B", self.toggle_sidebar)

    def _restore_settings(self):
        g = self.settings.value("geometry")
        if g:
            self.restoreGeometry(g)
        self.size_slider.setValue(int(self.settings.value("thumb", 220)))
        self._load_folder_stats()
        ANIM["on"] = str(self.settings.value("animations", "true")) != "false"
        self.side_hidden = str(self.settings.value("side_hidden", "false")) == "true"
        try:
            self.side_w = max(170, min(560, int(self.settings.value("side_w", 228))))
        except Exception:
            self.side_w = 228
        self.act_advance.setChecked(self.settings.value("advance", "true") == "true")
        try:
            self.recent = [x for x in json.loads(self.settings.value("recent", "[]"))
                           if isinstance(x, str)]
        except Exception:
            self.recent = []
        self._refresh_recent_menu()
        self._load_destinations()
        i = self.sort_cb.findData(self.settings.value("sort", "name"))
        if i >= 0:
            self.sort_cb.setCurrentIndex(i)
        self.act_recursive.setChecked(str(self.settings.value("recursive", "false")) == "true")
        self.viewer.hist_on = str(self.settings.value("hist", "true")) != "false"

    # ---------------- ouverture
    def choose_folder(self):
        start = self.settings.value("lastdir", str(Path.home() / "Pictures"))
        d = QFileDialog.getExistingDirectory(self, "Choisir un dossier de photos", start)
        if d:
            self.open_folder(d)

    def reload_folder(self):
        if self.root:
            self.open_folder(self.root, keep_sel=True)

    def open_folder(self, path, keep_sel=False):
        self.store.flush()
        self._remember_stats()
        self.root = path
        self.settings.setValue("lastdir", path)
        self._push_recent(path)
        QApplication.setOverrideCursor(Qt.CursorShape.WaitCursor)
        try:
            photos = scan_folder(path, self.act_recursive.isChecked())
            self.store.load(path)
            for p in photos:
                p.rating, p.flag = self.store.get(p.rel)
                p.edited = bool(self.store.get_dev(p.rel))
                p.label = self.store.get_label(p.rel)
        finally:
            QApplication.restoreOverrideCursor()
        self.view_cache.clear()
        if not keep_sel:
            self.undo_stack.clear()
            self.sent_counts.clear()
            self._update_dest_counts()
        self.act_back.setVisible(False)
        self.search.blockSignals(True)
        self.search.clear()
        self.search.blockSignals(False)
        self.model.name_filter = ""
        self.model.set_photos(photos)
        self.setWindowTitle(f"{APP_NAME} – {path}")
        self.folder_label.setText(os.path.basename(path.rstrip("/\\")) or path)
        self.folder_label.setToolTip(path)
        if not photos:
            QMessageBox.information(self, APP_NAME, "Aucune photo trouvée dans ce dossier.")
            self.stack.setCurrentIndex(0)
        else:
            self.stack.setCurrentWidget(self.grid)
            self.set_filters_enabled(True)
            self.grid.setFocus()
            if self.model.rowCount():
                self.grid.setCurrentIndex(self.model.index(0))
        self.update_status()

    def dragEnterEvent(self, e):
        if e.mimeData().hasUrls() and any(os.path.isdir(u.toLocalFile())
                                          for u in e.mimeData().urls()):
            e.acceptProposedAction()

    def dropEvent(self, e):
        for u in e.mimeData().urls():
            if os.path.isdir(u.toLocalFile()):
                self.open_folder(u.toLocalFile())
                break

    # ---------------- filtres / tailles
    def set_filters_enabled(self, on):
        for w in self.filter_widgets:
            w.setEnabled(on)

    def _set_flag_filter(self, value):
        self.flag_value = value
        self.on_filter_changed()

    def _toggle_label_filter(self, i):
        f = self.model.label_filter
        f.symmetric_difference_update({i})
        self.label_btns[i].setChecked(i in f)
        self.on_filter_changed()

    def set_label(self, n, rows=None):
        """Étiquette couleur (1 à 5) ; la même touche une 2e fois la retire."""
        if rows is None:
            rows = self.target_rows()
        if not rows:
            return
        photos = [self.model.photo(r) for r in rows]
        if all(p.label == n for p in photos):
            n = 0
        undo = []
        for p in photos:
            undo.append((p.path, p.label))
            p.label = n
            self.store.set_label(p.rel, n)
        self.undo_stack.append(("label", undo))
        del self.undo_stack[:-200]
        self.model.refresh_rows(rows)
        if self.model.label_filter:
            self.on_filter_changed()
        if self.stack.currentWidget() is self.viewer:
            self.refresh_viewer_info()
        who = photos[0].name if len(photos) == 1 else f"{len(photos)} photos"
        self.toast.show_message((f"Étiquette « {LABELS[n][0]} »" if n else "Étiquette retirée") + f"      {who}", 1600)

    def _undo_label(self, data):
        by_path = {p.path: p for p in self.model.all}
        for path, old in data:
            p = by_path.get(path)
            if p:
                p.label = old
                self.store.set_label(p.rel, old)
        self.model.rebuild() if self.model.label_filter else self.model.refresh_rows(range(self.model.rowCount()))
        if self.stack.currentWidget() is self.viewer:
            self.refresh_viewer_info()
        self.toast.show_message("Étiquette annulée")

    def _step_rating(self, d):
        rows = self.target_rows() if self.stack.currentWidget() is not self.viewer else [self.view_row]
        if not rows:
            return
        cur = self.model.photo(rows[0]).rating
        self.apply(rating=max(0, min(5, cur + d)), rows=rows, advance=False)

    def _clear_search(self):
        self.search.clear()
        self.grid.setFocus()

    def toggle_hist(self):
        self.viewer.toggle_hist()

    def on_filter_changed(self, *_):
        m = self.model
        m.sort_key = self.sort_cb.currentData()
        m.flag_filter = self.flag_value
        rv = self.rating_cb.currentData()
        m.rating_eq = 0 if rv == -1 else None
        m.min_rating = max(0, rv)
        m.name_filter = self.search.text().strip().lower()
        m.rebuild()
        self.btn_sort_stars.setChecked(m.sort_key == "rating")
        self.update_status()

    def on_size_changed(self, v):
        self.delegate.set_cell(v)
        self.grid.setGridSize(self.delegate.item_size())
        self.grid.doItemsLayout()
        self.grid.viewport().update()

    # ---------------- statut
    def update_status(self):
        total, picks, rejects = self.model.counts()
        if not total:
            self.status_label.setText("Aucun dossier ouvert")
            self.progress.setValue(0)
            self.progress_label.setText("")
            self.folder_count.setText("")
            return
        sel = len(self.grid.selectionModel().selectedIndexes())
        done = picks + rejects
        if self.root:
            self.folder_stats[self._stats_key(self.root)] = {
                "total": total, "done": done, "picks": picks, "ts": time.time()}
        txt = (f"{self.model.rowCount()} affichées sur {total}   ·   "
               f"✔ {picks} gardées   ·   ✖ {rejects} rejetées")
        if sel > 1:
            txt += f"   ·   {sel} sélectionnées"
        self.status_label.setText(txt)
        self.progress.setValue(int(100 * done / total))
        self.progress_label.setText(f"{done} / {total} triées  ")
        self.folder_count.setText(f"{total} photos")

    # ---------------- notation
    def target_rows(self):
        if self.stack.currentWidget() is self.compare:
            if not self.compare_paths:
                return []
            r = self.model.row_of.get(self.compare_paths[self.compare_active])
            return [r] if r is not None else []
        if self.stack.currentWidget() is self.viewer:
            return [self.view_row] if 0 <= self.view_row < self.model.rowCount() else []
        if self.stack.currentWidget() is not self.grid:
            return []
        rows = sorted({ix.row() for ix in self.grid.selectionModel().selectedIndexes()})
        if not rows and self.grid.currentIndex().isValid():
            rows = [self.grid.currentIndex().row()]
        return rows

    def apply(self, rating=None, flag=None, rows=None, advance=True):
        if rows is None:
            rows = self.target_rows()
        if not rows:
            return
        photos = [self.model.photo(r) for r in rows]
        # P / X répétés = on retire le drapeau
        if flag in (PICK, REJECT) and all(p.flag == flag for p in photos):
            flag = NO_FLAG
        undo = []
        for p in photos:
            undo.append((p.path, p.rating, p.flag))
            if rating is not None:
                p.rating = rating
            if flag is not None:
                p.flag = flag
            self.store.set(p.rel, p.rating, p.flag)
        self.undo_stack.append(("rate", undo))
        del self.undo_stack[:-200]
        self.model.refresh_rows(rows)
        self.update_status()
        self._rate_toast(photos, rating, flag)
        if self.stack.currentWidget() is self.viewer:
            self.refresh_viewer_info()
            if (advance and self.act_advance.isChecked()
                    and self.view_row < self.model.rowCount() - 1):
                self.show_row(self.view_row + 1)
        elif self.stack.currentWidget() is self.compare:
            self.refresh_compare()

    def undo(self):
        if self.stack.currentWidget() is self.viewer and self.viewer.undo_step():
            return
        if not self.undo_stack:
            self.statusBar().showMessage("Rien à annuler.", 2500)
            return
        kind, data = self.undo_stack.pop()
        if kind == "move":
            self._undo_move(data)
            return
        if kind == "copy":
            self._undo_copy(data)
            return
        if kind == "rename":
            self._undo_rename(data)
            return
        if kind == "label":
            self._undo_label(data)
            return
        by_path = {p.path: p for p in self.model.all}
        rows = []
        for path, rating, flag in data:
            p = by_path.get(path)
            if not p:
                continue
            p.rating, p.flag = rating, flag
            self.store.set(p.rel, rating, flag)
            r = self.model.row_of.get(path)
            if r is not None:
                rows.append(r)
        self.model.refresh_rows(rows)
        self.update_status()
        if self.stack.currentWidget() is self.viewer:
            if rows:
                self.show_row(rows[0])
            self.refresh_viewer_info()
        elif self.stack.currentWidget() is self.compare:
            self.refresh_compare()

    # ---------------- destinations (tri en 1 clic)
    def _load_destinations(self):
        try:
            data = json.loads(self.settings.value("destinations", "[]"))
        except Exception:
            data = []
        self.destinations = [d for d in data if isinstance(d, dict)
                             and isinstance(d.get("path"), str) and isinstance(d.get("name"), str)]
        self.dest_mode = "copy" if self.settings.value("dest_mode", "move") == "copy" else "move"
        (self.btn_copy if self.dest_mode == "copy" else self.btn_move).setChecked(True)
        self._refresh_destinations()

    def _save_destinations(self):
        self.settings.setValue("destinations", json.dumps(self.destinations))
        self.settings.setValue("dest_mode", self.dest_mode)

    def _set_mode(self, mode):
        self.dest_mode = mode
        self._save_destinations()
        self.toast.show_message("Mode « " + ("Déplacer" if mode == "move" else "Copier")
                                + " » : un clic sur une destination "
                                + ("déplace" if mode == "move" else "copie") + " les photos.", 2800)

    def _refresh_destinations(self):
        for b in self.dest_buttons:
            self.dest_box.removeWidget(b)
            b.setParent(None)
            b.deleteLater()
        self.dest_buttons = []
        for i, d in enumerate(self.destinations):
            b = DestButton()
            b.set_dest(d, self.sent_counts.get(d["path"], 0))
            b.clicked.connect(lambda _=False, i=i: self.send_to(i))
            b.customContextMenuRequested.connect(
                lambda pos, i=i, b=b: self._dest_menu(i, b.mapToGlobal(pos)))
            self.dest_box.addWidget(b)
            self.dest_buttons.append(b)
        self.dest_hint.setVisible(not self.destinations)
        for sc in self.dest_shortcuts:
            sc.setEnabled(False)
            sc.setParent(None)
            sc.deleteLater()
        self.dest_shortcuts = []
        for i, d in enumerate(self.destinations):
            k = d.get("key", "")
            if k:
                self.dest_shortcuts.append(self._bind(k, lambda i=i: self.send_to(i)))

    def _update_dest_counts(self):
        for b, d in zip(self.dest_buttons, self.destinations):
            b.set_dest(d, self.sent_counts.get(d["path"], 0))

    def _free_key(self):
        used = {d.get("key") for d in self.destinations}
        for ch in DEST_AUTO_KEYS:
            if ch not in used:
                return ch
        return ""

    def _add_destination(self, path, name=None):
        path = os.path.normpath(path)
        for d in self.destinations:
            if os.path.normcase(d["path"]) == os.path.normcase(path):
                self.toast.show_message("Cette destination existe déjà.")
                return
        name = name or os.path.basename(path.rstrip("/\\")) or path
        self.destinations.append({"name": name, "path": path,
                                  "color": DEST_COLORS[len(self.destinations) % len(DEST_COLORS)],
                                  "key": self._free_key()})
        self._save_destinations()
        self._refresh_destinations()
        key = self.destinations[-1]["key"]
        self.toast.show_message(f"Destination « {name} » ajoutée"
                                + (f"  ·  touche {key}" if key else ""), 3000)

    def add_dest_existing(self):
        start = self.settings.value("lastdest", self.root or str(Path.home()))
        d = QFileDialog.getExistingDirectory(self, "Choisir le dossier de destination", start)
        if d:
            self.settings.setValue("lastdest", d)
            self._add_destination(d)

    def add_dest_subfolder(self):
        if not self._need_folder():
            return
        name, ok = QInputDialog.getText(self, APP_NAME,
                                        "Nom du nouveau dossier (créé dans le dossier ouvert) :")
        name = name.strip() if ok else ""
        if not name:
            return
        if any(c in '<>:"/\\|?*' for c in name):
            QMessageBox.information(self, APP_NAME,
                                    "Ce nom contient des caractères interdits pour un dossier.")
            return
        path = os.path.join(self.root, name)
        try:
            os.makedirs(path, exist_ok=True)
        except OSError as ex:
            QMessageBox.warning(self, APP_NAME, f"Impossible de créer le dossier :\n{ex}")
            return
        self._add_destination(path, name)

    def _dest_menu(self, i, global_pos):
        if not 0 <= i < len(self.destinations):
            return
        menu = QMenu(self)
        self._act(menu, "Renommer…", lambda: self._dest_rename(i))
        self._act(menu, "Changer la touche…", lambda: self._dest_key(i))
        self._act(menu, "Changer de dossier…", lambda: self._dest_folder(i))
        self._act(menu, "Ouvrir le dossier", lambda: self._dest_open(i))
        menu.addSeparator()
        self._act(menu, "Retirer cette destination", lambda: self._dest_remove(i))
        menu.exec(global_pos)

    def _dest_rename(self, i):
        d = self.destinations[i]
        t, ok = QInputDialog.getText(self, APP_NAME, "Nom de la destination :",
                                     QLineEdit.EchoMode.Normal, d["name"])
        if ok and t.strip():
            d["name"] = t.strip()
            self._save_destinations()
            self._refresh_destinations()

    def _dest_key(self, i):
        d = self.destinations[i]
        t, ok = QInputDialog.getText(
            self, APP_NAME, "Touche du clavier (une seule lettre, vide = aucune) :",
            QLineEdit.EchoMode.Normal, d.get("key", ""))
        if not ok:
            return
        k = t.strip().upper()
        if k and not (len(k) == 1 and k.isascii() and k.isalpha()):
            QMessageBox.information(self, APP_NAME, "Entre une seule lettre de A à Z.")
            return
        if k in RESERVED_KEYS:
            QMessageBox.information(
                self, APP_NAME, f"La touche {k} est déjà utilisée par l'application "
                                "(P, X, U, B, C, N, F, H, Z). Choisis-en une autre.")
            return
        if k and any(j != i and o.get("key") == k for j, o in enumerate(self.destinations)):
            QMessageBox.information(self, APP_NAME, f"La touche {k} est déjà prise par une "
                                                    "autre destination.")
            return
        d["key"] = k
        self._save_destinations()
        self._refresh_destinations()

    def _dest_folder(self, i):
        d = self.destinations[i]
        new = QFileDialog.getExistingDirectory(self, "Nouveau dossier de destination", d["path"])
        if new:
            d["path"] = os.path.normpath(new)
            self._save_destinations()
            self._refresh_destinations()

    def _dest_open(self, i):
        path = self.destinations[i]["path"]
        if os.path.isdir(path):
            QDesktopServices.openUrl(QUrl.fromLocalFile(path))
        else:
            self.toast.show_message("Ce dossier n'existe pas encore (il sera créé au premier envoi).")

    def _dest_remove(self, i):
        d = self.destinations.pop(i)
        self._save_destinations()
        self._refresh_destinations()
        self.toast.show_message(f"Destination « {d['name']} » retirée (le dossier n'est pas touché).")

    def _select_row(self, row):
        ix = self.model.index(row)
        sm = self.grid.selectionModel()
        sm.clearSelection()
        self.grid.setCurrentIndex(ix)
        sm.select(ix, QItemSelectionModel.SelectionFlag.Select)
        self.grid.scrollTo(ix, QAbstractItemView.ScrollHint.EnsureVisible)

    def send_to(self, i):
        """Envoie la photo affichée / la sélection vers la destination i, sans confirmation."""
        if not 0 <= i < len(self.destinations):
            return
        page = self.stack.currentWidget()
        if page not in (self.grid, self.viewer, self.compare):
            self.toast.show_message("Ouvre d'abord un dossier de photos.")
            return
        rows = self.target_rows()
        if not rows:
            self.toast.show_message("Sélectionne d'abord une photo.")
            return
        dest = self.destinations[i]
        path = dest["path"]
        move = self.dest_mode == "move"
        norm = os.path.normcase(os.path.normpath(path))
        photos = [self.model.photo(r) for r in rows]
        photos = [p for p in photos
                  if os.path.normcase(os.path.normpath(os.path.dirname(p.path))) != norm]
        if not photos:
            self.toast.show_message("Ces photos sont déjà dans ce dossier.")
            return
        try:
            os.makedirs(path, exist_ok=True)
        except OSError as ex:
            QMessageBox.warning(self, APP_NAME, f"Impossible d'accéder au dossier :\n{path}\n\n{ex}")
            return
        first_row = min(rows)
        done, errors, pairs, meta, created = self._transfer_files(photos, path, move)
        if done:
            self.sent_counts[path] = self.sent_counts.get(path, 0) + len(done)
            self._record_transfer(move, pairs, done, created, path)
            if move:
                self._after_move(done, first_row, page)
            self._update_dest_counts()
            verb = "déplacée(s)" if move else "copiée(s)"
            self.toast.show_message(f"✔  {len(done)} photo(s) {verb} → {dest['name']}"
                                    "      Ctrl+Z pour annuler")
        self.update_status()
        if errors:
            QMessageBox.warning(self, APP_NAME, f"{len(errors)} problème(s) :\n\n"
                                + "\n".join(errors[:8]))

    def _record_transfer(self, move, pairs, done, created, dest_path):
        entry = {"dest": dest_path, "n": len(done)}
        if move:
            entry["pairs"] = pairs
            entry["photos"] = [(p.path, p.rel, p.mtime, p.rating, p.flag) for p in done]
            self.undo_stack.append(("move", entry))
        else:
            entry["created"] = created
            self.undo_stack.append(("copy", entry))
        del self.undo_stack[:-200]

    def _after_move(self, done, first_row, page):
        paths = {p.path for p in done}
        self.store.forget([p.rel for p in done])
        self.view_cache.clear()
        view_row = self.view_row
        if page is self.compare:
            self.compare_paths = [p for p in self.compare_paths if p not in paths]
            self.compare_active = max(0, min(self.compare_active, len(self.compare_paths) - 1))
        self.model.remove_paths(list(paths))
        n = self.model.rowCount()
        if page is self.viewer:
            if n == 0:
                self.stack.setCurrentWidget(self.grid)
                self.set_filters_enabled(True)
                self.act_back.setVisible(False)
            else:
                self.show_row(max(0, min(view_row, n - 1)))
        elif page is self.compare:
            if len(self.compare_paths) < 2:
                self.close_compare()
            else:
                self._fill_compare()
        elif n:
            self._select_row(max(0, min(first_row, n - 1)))

    # ---------------- navigation : accueil / paramètres
    def _on_page_changed(self, *_):
        w = self.stack.currentWidget()
        self.topbar.setVisible(w in (self.grid, self.compare))
        self.act_back.setVisible(w is self.compare)
        self._apply_sidebar()
        self.set_filters_enabled(w is self.grid)
        if w is self.home_page:
            self._refresh_home()
        elif self.isVisible():
            fade_in(w, 240, start=0.0)

    def _apply_sidebar(self):
        w = self.stack.currentWidget()
        show = w in (self.grid, self.compare) and not self.side_hidden
        was = self.sidebar.isVisible()
        self.sidebar.setVisible(show)
        if show and not was:
            self._set_side_width(self.side_w)

    def _set_side_width(self, wpx):
        wpx = max(170, min(560, int(wpx)))
        total = max(self.split.width(), wpx + 400)
        self.split.setSizes([wpx, total - wpx])

    def _on_split_moved(self, pos, index):
        if self.sidebar.isVisible():
            self.side_w = max(170, min(560, self.sidebar.width()))
            self.settings.setValue("side_w", self.side_w)

    def toggle_sidebar(self):
        self.side_hidden = not self.side_hidden
        self.settings.setValue("side_hidden", "true" if self.side_hidden else "false")
        self._apply_sidebar()

    def go_home(self):
        self._remember_stats()
        self._fill_tips()
        self.stack.setCurrentWidget(self.home_page)
        self._refresh_home()

    def resume_folder(self):
        if self.root and self.model.all:
            self.stack.setCurrentWidget(self.grid)
            self.grid.setFocus()

    def open_settings(self):
        cur = self.stack.currentWidget()
        if cur is not self.settings_page:
            self._before_settings = cur
        self._sync_settings_ui()
        self.stack.setCurrentWidget(self.settings_page)
        self.settings_page.setFocus()      # pour que Échap ramène à la page précédente

    def settings_back(self):
        prev = self._before_settings
        if prev is None or prev is self.settings_page:
            prev = self.home_page
        self.stack.setCurrentWidget(prev)
        if prev is self.grid:
            self.grid.setFocus()
        elif prev is self.viewer:
            self.viewer.setFocus()
        elif prev is self.compare:
            self.compare.setFocus()

    # ---------------- page Paramètres
    def _settings_card(self, title, subtitle=None):
        f = QFrame()
        f.setObjectName("card")
        lay = QVBoxLayout(f)
        lay.setContentsMargins(22, 18, 22, 20)
        lay.setSpacing(12)
        t = QLabel(title)
        t.setObjectName("cardTitle")
        lay.addWidget(t)
        if subtitle:
            sub = QLabel(subtitle)
            sub.setObjectName("muted")
            sub.setWordWrap(True)
            lay.addWidget(sub)
        return f, lay

    def _seg_button(self, text):
        b = QPushButton(text)
        b.setObjectName("seg")
        b.setCheckable(True)
        b.setCursor(Qt.CursorShape.PointingHandCursor)
        return b

    def _build_settings(self):
        page = QScrollArea()
        page.setWidgetResizable(True)
        page.setFrameShape(QFrame.Shape.NoFrame)
        page.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        inner = QWidget()
        page.setWidget(inner)
        outer = QVBoxLayout(inner)
        outer.setContentsMargins(40, 26, 40, 40)
        wrap = QWidget()
        wrap.setMaximumWidth(780)
        col = QVBoxLayout(wrap)
        col.setContentsMargins(0, 0, 0, 0)
        col.setSpacing(16)
        outer.addWidget(wrap, 0, Qt.AlignmentFlag.AlignHCenter)
        outer.addStretch(1)

        head = QHBoxLayout()
        back = QPushButton("←  Retour")
        back.setObjectName("ghostBorder")
        back.setCursor(Qt.CursorShape.PointingHandCursor)
        back.clicked.connect(self.settings_back)
        title = QLabel("Paramètres")
        title.setObjectName("pageTitle")
        head.addWidget(back)
        head.addSpacing(14)
        head.addWidget(title)
        head.addStretch(1)
        col.addLayout(head)
        col.addSpacing(4)

        # --- Apparence
        card, lay = self._settings_card(
            "Apparence", "Choisis le thème et la couleur de toute l'application. "
                         "Le changement est immédiat et enregistré.")
        lay.addWidget(self._section("THÈME"))
        row = QHBoxLayout()
        row.setSpacing(8)
        self.theme_group = QButtonGroup(self)
        self.theme_group.setExclusive(True)
        self.btn_theme_dark = self._seg_button("☾   Sombre")
        self.btn_theme_light = self._seg_button("☀   Clair")
        for b, mode in ((self.btn_theme_dark, "dark"), (self.btn_theme_light, "light")):
            self.theme_group.addButton(b)
            b.clicked.connect(lambda _=False, m=mode: self.set_theme(mode=m))
            row.addWidget(b)
        row.addStretch(1)
        lay.addLayout(row)
        lay.addSpacing(4)
        lay.addWidget(self._section("COULEUR DE L'APPLICATION"))
        sw = QHBoxLayout()
        sw.setSpacing(10)
        for name, hexv in ACCENT_PRESETS:
            b = QPushButton()
            b.setFixedSize(34, 34)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.setToolTip(name)
            b.clicked.connect(lambda _=False, h=hexv: self.set_theme(accent=h))
            self.swatches.append((hexv, b))
            sw.addWidget(b)
        sw.addStretch(1)
        lay.addLayout(sw)
        custom = QHBoxLayout()
        custom.setSpacing(10)
        btn_custom = QPushButton("🎨   Choisir une autre couleur…")
        btn_custom.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_custom.clicked.connect(self.pick_custom_color)
        self.hex_edit = QLineEdit()
        self.hex_edit.setPlaceholderText("#6d8cff")
        self.hex_edit.setMaxLength(7)
        self.hex_edit.setFixedWidth(110)
        self.hex_edit.setToolTip("Code couleur (ex. #ff6b9a), puis Entrée")
        self.hex_edit.returnPressed.connect(self._hex_entered)
        lab = QLabel("ou saisis un code :")
        lab.setObjectName("muted")
        custom.addWidget(btn_custom)
        custom.addSpacing(6)
        custom.addWidget(lab)
        custom.addWidget(self.hex_edit)
        custom.addStretch(1)
        lay.addLayout(custom)
        self.chk_tint = QCheckBox("Teinter le fond de l'application avec la couleur choisie")
        self.chk_tint.clicked.connect(lambda v: self.set_theme(tint=v))
        lay.addWidget(self.chk_tint)
        self.chk_anim = QCheckBox("Animations (fondus, apparition des vignettes…)")
        self.chk_anim.clicked.connect(self._on_set_anim)
        lay.addWidget(self.chk_anim)
        reset = QPushButton("↺   Rétablir le thème par défaut")
        reset.setObjectName("ghost")
        reset.setCursor(Qt.CursorShape.PointingHandCursor)
        reset.clicked.connect(self.reset_theme)
        lay.addWidget(reset, 0, Qt.AlignmentFlag.AlignLeft)
        col.addWidget(card)

        # --- Photos et tri
        card, lay = self._settings_card("Photos et tri")
        self.chk_recursive = QCheckBox("Inclure les sous-dossiers à l'ouverture d'un dossier")
        self.chk_recursive.clicked.connect(lambda v: self.act_recursive.setChecked(v))
        self.chk_advance = QCheckBox("Passer à la photo suivante après une note ou un envoi "
                                     "(visionneuse)")
        self.chk_advance.clicked.connect(lambda v: self.act_advance.setChecked(v))
        self.chk_hist = QCheckBox("Afficher l'histogramme dans la visionneuse")
        self.chk_hist.clicked.connect(self._on_set_hist)
        for c in (self.chk_recursive, self.chk_advance, self.chk_hist):
            lay.addWidget(c)
        lay.addSpacing(4)
        lay.addWidget(self._section("UN CLIC SUR UNE DESTINATION"))
        row = QHBoxLayout()
        row.setSpacing(8)
        self.set_mode_group = QButtonGroup(self)
        self.set_mode_group.setExclusive(True)
        self.set_move = self._seg_button("Déplace les photos")
        self.set_copy = self._seg_button("Copie les photos")
        for b, mode in ((self.set_move, "move"), (self.set_copy, "copy")):
            self.set_mode_group.addButton(b)
            b.clicked.connect(lambda _=False, m=mode: self._on_set_mode(m))
            row.addWidget(b)
        row.addStretch(1)
        lay.addLayout(row)
        lay.addSpacing(4)
        lay.addWidget(self._section("TAILLE DES VIGNETTES"))
        self.set_thumb = QSlider(Qt.Orientation.Horizontal)
        self.set_thumb.setRange(130, 360)
        self.set_thumb.setFixedWidth(260)
        self.set_thumb.valueChanged.connect(self._on_set_thumb)
        lay.addWidget(self.set_thumb)
        col.addWidget(card)

        # --- Données
        card, lay = self._settings_card("Données")
        self.lbl_cache = QLabel()
        self.lbl_cache.setObjectName("muted")
        self.lbl_cache.setWordWrap(True)
        lay.addWidget(self.lbl_cache)
        row = QHBoxLayout()
        row.setSpacing(8)
        btn_cache = QPushButton("🗑   Vider le cache des vignettes")
        btn_cache.clicked.connect(self.clear_cache)
        btn_recent = QPushButton("Effacer les dossiers récents")
        btn_recent.clicked.connect(self.clear_recent)
        row.addWidget(btn_cache)
        row.addWidget(btn_recent)
        row.addStretch(1)
        lay.addLayout(row)
        col.addWidget(card)

        # --- Aide
        card, lay = self._settings_card("Aide")
        btn_help = QPushButton("⌨   Voir les raccourcis clavier")
        btn_help.clicked.connect(self.show_help)
        about = QLabel("Klutter · tes photos d'origine ne sont jamais modifiées sans action "
                       "de ta part. Les notes sont enregistrées dans « trieur_photos.json » "
                       "dans le dossier ouvert.")
        about.setObjectName("muted")
        about.setWordWrap(True)
        lay.addWidget(btn_help, 0, Qt.AlignmentFlag.AlignLeft)
        lay.addWidget(about)
        col.addWidget(card)
        return page

    def _sync_settings_ui(self):
        """Remet la page Paramètres en accord avec l'état actuel de l'application."""
        self._syncing = True
        try:
            self.btn_theme_dark.setChecked(THEME["mode"] != "light")
            self.btn_theme_light.setChecked(THEME["mode"] == "light")
            self.hex_edit.setText(THEME["accent"].upper())
            self.chk_tint.setChecked(THEME["tint"])
            self.chk_anim.setChecked(ANIM["on"])
            self._style_swatches()
            self.chk_recursive.setChecked(self.act_recursive.isChecked())
            self.chk_advance.setChecked(self.act_advance.isChecked())
            self.chk_hist.setChecked(self.viewer.hist_on)
            self.set_move.setChecked(self.dest_mode != "copy")
            self.set_copy.setChecked(self.dest_mode == "copy")
            self.set_thumb.setValue(self.size_slider.value())
            self.lbl_cache.setText(
                f"Cache des vignettes : {self._cache_size() / 1048576:.1f} Mo  ·  {CACHE_DIR}")
        finally:
            self._syncing = False

    def _style_swatches(self):
        ring = PAL["text_strong"]
        for hexv, b in self.swatches:
            sel = hexv.lower() == THEME["accent"].lower()
            border = f"3px solid {ring}" if sel else "2px solid transparent"
            b.setStyleSheet(
                f"QPushButton {{ background: {hexv}; border: {border}; border-radius: 17px; "
                f"padding: 0px; }} QPushButton:hover {{ border: 3px solid {ring}; }}")

    def _on_set_anim(self, v):
        if not self._syncing:
            ANIM["on"] = bool(v)
            self.settings.setValue("animations", "true" if v else "false")

    def _on_set_hist(self, v):
        if self.viewer.hist_on != v:
            self.viewer.toggle_hist()

    def _on_set_mode(self, mode):
        (self.btn_copy if mode == "copy" else self.btn_move).click()

    def _on_set_thumb(self, v):
        if not self._syncing:
            self.size_slider.setValue(v)

    # ---------------- thème
    def set_theme(self, mode=None, accent=None, tint=None):
        if mode in ("dark", "light"):
            THEME["mode"] = mode
        if accent and re.fullmatch(r"#[0-9a-fA-F]{6}", accent):
            THEME["accent"] = accent.lower()
        if tint is not None:
            THEME["tint"] = bool(tint)
        apply_theme(QApplication.instance())
        self.settings.setValue("theme_mode", THEME["mode"])
        self.settings.setValue("theme_accent", THEME["accent"])
        self.settings.setValue("theme_tint", "true" if THEME["tint"] else "false")
        self._after_theme()
        self._sync_settings_ui()

    def reset_theme(self):
        self.set_theme(mode=THEME_DEFAULT["mode"], accent=THEME_DEFAULT["accent"],
                       tint=THEME_DEFAULT["tint"])
        self.toast.show_message("Thème par défaut rétabli")

    def _after_theme(self):
        """Rafraîchit ce que la feuille de style ne met pas à jour toute seule."""
        self._update_dest_counts()
        bg = QColor(PAL["stage"])
        for v in self.findChildren(ImageView):
            v.setBackgroundBrush(bg)
        self.grid.viewport().update()
        self.viewer.film.viewport().update()
        self.viewer.hist.update()
        self.viewer.navigator.update()
        self.viewer.overlay.update()
        self.viewer.top_logo.setPixmap(make_logo(24))
        self.side_logo.setPixmap(make_logo(22))
        self.refresh_compare()
        if 0 <= self.view_row < self.model.rowCount():
            self.refresh_viewer_info()
        self.home_logo.setPixmap(make_logo(112))
        self.setWindowIcon(QIcon(make_logo(128)))

    def pick_custom_color(self):
        c = QColorDialog.getColor(QColor(THEME["accent"]), self, "Choisir la couleur de l'application")
        if c.isValid():
            self.set_theme(accent=c.name())

    def _hex_entered(self):
        t = self.hex_edit.text().strip()
        if t and not t.startswith("#"):
            t = "#" + t
        if re.fullmatch(r"#[0-9a-fA-F]{6}", t):
            self.set_theme(accent=t)
        else:
            self.toast.show_message("Code couleur invalide (exemple : #6d8cff)")

    # ---------------- cache / récents
    def _cache_size(self):
        total = 0
        for dp, _dn, fn in os.walk(CACHE_DIR / "thumbs"):
            for f in fn:
                try:
                    total += os.path.getsize(os.path.join(dp, f))
                except OSError:
                    pass
        return total

    def clear_cache(self):
        size = self._cache_size()
        if QMessageBox.question(
                self, APP_NAME,
                f"Vider le cache des vignettes ({size / 1048576:.1f} Mo) ?\n\n"
                "Elles seront recréées automatiquement à la prochaine ouverture d'un dossier.") \
                != QMessageBox.StandardButton.Yes:
            return
        shutil.rmtree(CACHE_DIR / "thumbs", ignore_errors=True)
        self._sync_settings_ui()
        self.toast.show_message("Cache des vignettes vidé")

    def clear_recent(self):
        self.recent = []
        self.settings.setValue("recent", json.dumps(self.recent))
        self._refresh_recent_menu()
        self.toast.show_message("Liste des dossiers récents effacée")

    # ---------------- étoiles : clic, tri, retour visuel
    def rate_row(self, row, n):
        """Clic sur une étoile d'une carte : note la photo (re-clic = retire la note)."""
        if not 0 <= row < self.model.rowCount():
            return
        if n == self.model.photo(row).rating:
            n = 0
        self.apply(rating=n, rows=[row], advance=False)
        if self.stack.currentWidget() is self.grid:
            self._select_row(row)

    def _toggle_sort_stars(self):
        if self.sort_cb.currentData() == "rating":
            i = self.sort_cb.findData(self._prev_sort or "name")
        else:
            self._prev_sort = self.sort_cb.currentData()
            i = self.sort_cb.findData("rating")
        if i >= 0:
            self.sort_cb.setCurrentIndex(i)
        self.btn_sort_stars.setChecked(self.sort_cb.currentData() == "rating")

    def _rate_toast(self, photos, rating, flag):
        if rating is not None:
            msg = "Note retirée" if rating == 0 else "★" * rating + "☆" * (5 - rating)
        elif flag == PICK:
            msg = "✔  Gardée"
        elif flag == REJECT:
            msg = "✖  Rejetée"
        else:
            msg = "Drapeau retiré"
        who = photos[0].name if len(photos) == 1 else f"{len(photos)} photos"
        self.toast.show_message(f"{msg}      {who}", 1600)

    # ---------------- dossiers récents / retour
    def _push_recent(self, path):
        path = os.path.normpath(path)
        self.recent = [x for x in self.recent if os.path.normcase(x) != os.path.normcase(path)]
        self.recent.insert(0, path)
        del self.recent[8:]
        self.settings.setValue("recent", json.dumps(self.recent))
        self._refresh_recent_menu()

    def _refresh_recent_menu(self):
        self.menu_recent.clear()
        for rp in self.recent:
            a = QAction(rp.replace("&", "&&"), self)
            a.triggered.connect(lambda _=False, rp=rp: self._open_recent(rp))
            self.menu_recent.addAction(a)
        self.menu_recent.setEnabled(bool(self.recent))
        self.btn_prev_folder.setEnabled(len(self.recent) >= 2)
        self._refresh_home()

    def _open_recent(self, rp):
        if not os.path.isdir(rp):
            QMessageBox.information(self, APP_NAME, f"Ce dossier n'existe plus :\n{rp}")
            self.recent = [x for x in self.recent if x != rp]
            self.settings.setValue("recent", json.dumps(self.recent))
            self._refresh_recent_menu()
            return
        self.open_folder(rp)

    def go_previous_folder(self):
        if len(self.recent) >= 2:
            self._open_recent(self.recent[1])
        else:
            self.statusBar().showMessage("Pas de dossier précédent.", 2500)

    def back_to_grid(self):
        page = self.stack.currentWidget()
        if page is self.viewer:
            self.close_viewer()
        elif page is self.compare:
            self.close_compare()

    def _dec_sent(self, entry):
        dest = entry.get("dest")
        if dest in self.sent_counts:
            self.sent_counts[dest] = max(0, self.sent_counts[dest] - entry.get("n", 0))
            self._update_dest_counts()

    def _undo_move(self, entry):
        problems = 0
        for src, dst in reversed(entry["pairs"]):
            try:
                if os.path.exists(dst) and not os.path.exists(src):
                    os.makedirs(os.path.dirname(src), exist_ok=True)
                    shutil.move(dst, src)
                else:
                    problems += 1
            except Exception:  # noqa: BLE001
                problems += 1
        known = {p.path for p in self.model.all}
        restored = []
        for path, rel, mtime, rating, flag in entry["photos"]:
            if path in known or not os.path.exists(path):
                continue
            ph = Photo(path, rel, mtime)
            ph.rating, ph.flag = rating, flag
            self.store.set(rel, rating, flag)
            restored.append(ph)
        self.model.all.extend(restored)
        self.model.rebuild()
        self._dec_sent(entry)
        page = self.stack.currentWidget()
        if restored:
            r = self.model.row_of.get(restored[0].path)
            if r is not None:
                if page is self.viewer:
                    self.show_row(r)
                elif page is self.grid:
                    self._select_row(r)
        self.update_status()
        if problems:
            QMessageBox.information(
                self, APP_NAME,
                f"{problems} fichier(s) n'ont pas pu être remis à leur place "
                "(déjà déplacés, renommés, ou un fichier existe déjà à l'emplacement d'origine).")
        else:
            self.toast.show_message(f"↶  {len(restored)} photo(s) remise(s) à leur place")

    def _undo_copy(self, entry):
        created = [f for f in entry.get("created", []) if os.path.isfile(f)]
        if created:
            if QMessageBox.question(
                    self, APP_NAME,
                    f"Annuler la copie : supprimer les {len(created)} fichier(s) copié(s) dans\n"
                    f"{entry.get('dest', '')}\n\n(Tes originaux ne sont pas touchés.)") \
                    != QMessageBox.StandardButton.Yes:
                self.undo_stack.append(("copy", entry))
                return
            for f in created:
                try:
                    os.remove(f)
                except OSError:
                    pass
        self._dec_sent(entry)
        self.toast.show_message("↶  Copie annulée")

    # ---------------- navigation rapide / comparaison
    def next_unsorted(self):
        n = self.model.rowCount()
        page = self.stack.currentWidget()
        if not n or page not in (self.grid, self.viewer):
            return
        if page is self.viewer:
            start = self.view_row
        else:
            ix = self.grid.currentIndex()
            start = ix.row() if ix.isValid() else -1
        for r in list(range(start + 1, n)) + list(range(0, start + 1)):
            if self.model.photo(r).flag == NO_FLAG:
                if page is self.viewer:
                    self.show_row(r)
                else:
                    ix = self.model.index(r)
                    sm = self.grid.selectionModel()
                    sm.clearSelection()
                    self.grid.setCurrentIndex(ix)
                    sm.select(ix, QItemSelectionModel.SelectionFlag.Select)
                    self.grid.scrollTo(ix, QAbstractItemView.ScrollHint.PositionAtCenter)
                return
        self.statusBar().showMessage("Toutes les photos affichées ont déjà un drapeau.", 3500)

    def open_compare(self):
        if self.stack.currentWidget() is not self.grid:
            return
        rows = self.target_rows()
        if len(rows) < 2:
            QMessageBox.information(
                self, APP_NAME,
                "Sélectionne 2 à 4 photos (Ctrl+clic ou Maj+clic), puis clique sur "
                "« Comparer » ou appuie sur C.")
            return
        rows = rows[:4]
        self.compare_paths = [self.model.photo(r).path for r in rows]
        self.compare_active = 0
        self.stack.setCurrentWidget(self.compare)
        self.set_filters_enabled(False)
        self.act_back.setVisible(True)
        self._fill_compare()
        self.compare.setFocus()

    def _fill_compare(self):
        self.compare.setup(len(self.compare_paths))
        for i, path in enumerate(self.compare_paths):
            view = self.compare.cells[i].view
            img = self.view_cache.get(path)
            if img is not None:
                view.set_image(img)
            else:
                thumb = self.model._thumbs.get(path)
                if thumb is not None:
                    view.set_pixmap(thumb)
                self._request_view(path, urgent=True)
        self.refresh_compare()

    def close_compare(self):
        if self.stack.currentWidget() is not self.compare:
            return
        if self._rating_dependent():
            self.model.rebuild()
        self.stack.setCurrentWidget(self.grid)
        self.set_filters_enabled(True)
        self.act_back.setVisible(False)
        sm = self.grid.selectionModel()
        sm.clearSelection()
        last = None
        for cp in self.compare_paths:
            r = self.model.row_of.get(cp)
            if r is not None:
                last = self.model.index(r)
                sm.select(last, QItemSelectionModel.SelectionFlag.Select)
        if last is not None:
            sm.setCurrentIndex(last, QItemSelectionModel.SelectionFlag.NoUpdate)
        self.grid.setFocus()
        self.update_status()

    def compare_step(self, d):
        if self.compare_paths:
            self.compare_active = (self.compare_active + d) % len(self.compare_paths)
            self.refresh_compare()

    def refresh_compare(self):
        by_path = {p.path: p for p in self.model.all}
        for i, cp in enumerate(self.compare_paths):
            if i >= len(self.compare.cells):
                break
            cell = self.compare.cells[i]
            ph = by_path.get(cp)
            if ph is None:
                continue
            stars = "".join("★" if k < ph.rating else "☆" for k in range(5))
            flag = ""
            if ph.flag == PICK:
                flag = f"  <span style='color:{PAL['ok']}'>✔ gardée</span>"
            elif ph.flag == REJECT:
                flag = f"  <span style='color:{PAL['bad']}'>✖ rejetée</span>"
            cell.label.setText(f"{ph.name}   <span style='color:{PAL['gold']}'>{stars}</span>{flag}")
            cell.set_active(i == self.compare_active)

    def copy_pick_names(self):
        names = [p.name for p in sorted(self.model.all, key=lambda p: _natural(p.name))
                 if p.flag == PICK]
        if not names:
            QMessageBox.information(self, APP_NAME, "Aucune photo gardée pour l'instant.")
            return
        QApplication.clipboard().setText("\n".join(names))
        QMessageBox.information(self, APP_NAME,
                                f"{len(names)} nom(s) de fichier copiés dans le presse-papiers.")

    # ---------------- renommer / retoucher
    def _current_photo_row(self):
        page = self.stack.currentWidget()
        if page is self.viewer:
            row = self.view_row
        elif page is self.grid:
            rows = self.target_rows()
            row = rows[0] if rows else -1
        else:
            return -1
        return row if 0 <= row < self.model.rowCount() else -1

    def _grid_menu(self, pos):
        ix = self.grid.indexAt(pos)
        if not ix.isValid():
            return
        sm = self.grid.selectionModel()
        if not sm.isSelected(ix):
            self._select_row(ix.row())
        menu = QMenu(self)
        self._act(menu, "Ouvrir", lambda: self.open_viewer(ix.row()))
        self._act(menu, "Renommer…  (F2)", self.rename_photo)
        self._act(menu, "Développer…  (Ctrl+E)", self.develop_photo)
        menu.exec(self.grid.viewport().mapToGlobal(pos))

    def _rename_plan(self, ph, new_stem):
        old_stem = os.path.splitext(ph.name)[0]
        return plan_rename(self._files_of(ph, {}), old_stem, new_stem)

    @staticmethod
    def _rename_conflict(plan):
        for a, b in plan:
            same = os.path.normcase(os.path.abspath(a)) == os.path.normcase(os.path.abspath(b))
            if os.path.exists(b) and not same:
                return f"« {os.path.basename(b)} » existe déjà dans ce dossier."
        return None

    @staticmethod
    def _perform_rename(plan):
        """Renomme tous les fichiers du plan ; en cas d'échec, remet tout comme avant."""
        done = []
        try:
            for a, b in plan:
                os.rename(a, b)
                done.append((a, b))
        except OSError as ex:
            for a, b in reversed(done):
                try:
                    os.rename(b, a)
                except OSError:
                    pass
            return f"Renommage impossible : {ex}"
        return None

    def rename_photo(self):
        self.viewer.flush()
        row = self._current_photo_row()
        if row < 0:
            if self.stack.currentWidget() in (self.grid, self.viewer):
                self.toast.show_message("Sélectionne d'abord une photo.")
            return
        ph = self.model.photo(row)
        stem, ext = os.path.splitext(ph.name)
        text = stem
        while True:
            text, ok = QInputDialog.getText(
                self, "Renommer la photo",
                f"Nouveau nom (l'extension « {ext} » et les fichiers associés suivent) :",
                QLineEdit.EchoMode.Normal, text)
            if not ok:
                return
            text = text.strip()
            if ext and text.lower().endswith(ext.lower()):
                text = text[:-len(ext)].rstrip()
            if text == stem:
                return
            err = check_new_stem(text)
            plan = None
            if err is None:
                plan = self._rename_plan(ph, text)
                err = self._rename_conflict(plan)
            if err:
                QMessageBox.warning(self, APP_NAME, err)
                continue
            break
        err = self._perform_rename(plan)
        if err:
            QMessageBox.warning(self, APP_NAME, err)
            return
        self._rekey_photo(ph, plan[0][1])
        self.undo_stack.append(("rename", {"plan": plan}))
        del self.undo_stack[:-200]
        self._after_rename(ph)
        self.toast.show_message(f"Renommée en « {ph.name} »      Ctrl+Z pour annuler")

    def _rekey_photo(self, ph, new_path):
        old_path, old_rel = ph.path, ph.rel
        ph.path = new_path
        ph.name = os.path.basename(new_path)
        head = old_rel.rsplit("/", 1)[0] + "/" if "/" in old_rel else ""
        ph.rel = head + ph.name
        self.store.rename(old_rel, ph.rel)
        if self.viewer.cur_key == old_rel:
            self.viewer.cur_key = ph.rel
        self.model.rekey(old_path, ph)
        img = self.view_cache.pop(old_path, None)
        if img is not None:
            self.view_cache[new_path] = img
        meta = self.meta_cache.pop(old_path, None)
        if meta is not None:
            self.meta_cache[new_path] = meta
        self.compare_paths = [new_path if x == old_path else x for x in self.compare_paths]

    def _after_rename(self, ph):
        page = self.stack.currentWidget()
        self.resort(quiet=True)
        row = self.model.row_of.get(ph.path)
        if page is self.viewer:
            if row is None:
                self.stack.setCurrentWidget(self.grid)
                self.grid.setFocus()
                self.toast.show_message("La photo renommée n'apparaît plus avec le filtre actuel.")
            else:
                self.show_row(row)
        elif row is not None:
            self._select_row(row)
        self.update_status()

    def _undo_rename(self, entry):
        plan = entry["plan"]
        back = [(b, a) for a, b in plan]
        problem = None
        if not all(os.path.exists(a) for a, _b in back):
            problem = "un des fichiers a été déplacé ou renommé en dehors de l'application"
        else:
            problem = self._rename_conflict(back)
        if problem:
            self.undo_stack.append(("rename", entry))
            self.toast.show_message("Annulation impossible : " + problem)
            return
        err = self._perform_rename(back)
        if err:
            self.undo_stack.append(("rename", entry))
            self.toast.show_message(err)
            return
        ph = next((p for p in self.model.all if p.path == plan[0][1]), None)
        if ph is not None:
            self._rekey_photo(ph, plan[0][0])
            self._after_rename(ph)
        self.toast.show_message("Renommage annulé")

    def develop_photo(self):
        row = self._current_photo_row()
        if row < 0:
            if self.stack.currentWidget() in (self.grid, self.viewer):
                self.toast.show_message("Sélectionne d'abord une photo.")
            return
        if self.stack.currentWidget() is not self.viewer:
            self.open_viewer(row)

    def _on_dev_changed(self, key, dev):
        """Les réglages d'une photo ont changé : on les garde dans le fichier de notes du dossier."""
        if not key:
            return
        self.store.set_dev(key, dev)
        ph = next((p for p in self.model.all if p.rel == key), None)
        if ph is not None:
            ph.edited = bool(dev)
            r = self.model.row_of.get(ph.path)
            if r is not None:
                self.model.refresh_rows([r])

    def copy_settings(self):
        self.viewer.flush()
        row = self._current_photo_row()
        dev = self.store.get_dev(self.model.photo(row).rel) if row >= 0 else None
        p = (dev or {}).get("p")
        if not p:
            self.toast.show_message("Cette photo n'a aucun réglage à copier.")
            return
        self._dev_clip = dict(p)
        self.toast.show_message(f"Réglages copiés ({len(p)})      Ctrl+Maj+V pour les coller")

    def _paste_rows(self):
        page = self.stack.currentWidget()
        if page is self.viewer:
            return [self.view_row] if 0 <= self.view_row < self.model.rowCount() else []
        if page is self.grid:
            return self.target_rows()
        return []

    def _apply_params_to_rows(self, params, rows, label):
        n = 0
        for r in rows:
            ph = self.model.photo(r)
            if self.stack.currentWidget() is self.viewer and r == self.view_row:
                self.viewer.apply_dev({"p": dict(params)}, label, keep_geometry=True)
            else:
                cur = self.store.get_dev(ph.rel) or {}
                new = dev_clean({**dict(EDIT_DEFAULTS), **params}, cur.get("ops") or [], cur.get("crop"))
                self.store.set_dev(ph.rel, new)
                ph.edited = bool(new)
                self.model.refresh_rows([r])
            n += 1
        return n

    def paste_settings(self):
        if not self._dev_clip:
            self.toast.show_message("Copie d'abord les réglages d'une photo (Ctrl+Maj+C).")
            return
        rows = self._paste_rows()
        if not rows:
            return
        n = self._apply_params_to_rows(self._dev_clip, rows, "Réglages collés")
        self.toast.show_message(f"Réglages collés sur {n} photo(s)")

    def paste_previous(self):
        prev = (self._prev_dev or {}).get("p")
        if not prev:
            self.toast.show_message("Pas de photo précédente retouchée.")
            return
        rows = self._paste_rows()
        if rows:
            self._apply_params_to_rows(prev, rows, "Réglages de la photo précédente")
            self.toast.show_message("Réglages de la photo précédente appliqués")

    def reset_settings(self):
        rows = self._paste_rows()
        for r in rows:
            if self.stack.currentWidget() is self.viewer and r == self.view_row:
                self.viewer.reset_all()
            else:
                ph = self.model.photo(r)
                self.store.set_dev(ph.rel, None)
                ph.edited = False
                self.model.refresh_rows([r])
        if rows:
            self.toast.show_message("Réglages remis à zéro")

    def export_photo(self):
        if np is None:
            QMessageBox.information(
                self, APP_NAME, "L'export demande le module « numpy ».\n\n"
                "Dans une invite de commandes : pip install numpy  (puis relance Klutter).")
            return
        self.viewer.flush()
        row = self._current_photo_row()
        if row < 0:
            self.toast.show_message("Sélectionne d'abord une photo.")
            return
        ph = self.model.photo(row)
        d = os.path.dirname(ph.path)
        stem = os.path.splitext(ph.name)[0]
        default = self._unique(d, f"{stem}_edit.jpg")
        target, _flt = QFileDialog.getSaveFileName(
            self, "Exporter la photo développée", default,
            "JPEG (*.jpg *.jpeg);;PNG (*.png);;TIFF (*.tif *.tiff)")
        if not target:
            return
        if not os.path.splitext(target)[1]:
            target += ".jpg"
        QApplication.setOverrideCursor(Qt.CursorShape.WaitCursor)
        try:
            arr = qimage_to_array(decode_image(ph.path))
            out = array_to_qimage(render_dev(arr, self.store.get_dev(ph.rel)))
            ext = os.path.splitext(target)[1].lower()
            fmt = {".png": "PNG", ".tif": "TIFF", ".tiff": "TIFF"}.get(ext, "JPG")
            ok = out.save(target, fmt, 95) if fmt == "JPG" else out.save(target, fmt)
        except Exception as ex:  # noqa: BLE001
            QApplication.restoreOverrideCursor()
            QMessageBox.warning(self, APP_NAME, f"Export impossible :\n{ex}")
            return
        QApplication.restoreOverrideCursor()
        if not ok:
            QMessageBox.warning(self, APP_NAME, f"Export impossible :\n{target}")
            return
        self._add_exported(target)

    def _add_exported(self, path):
        name = os.path.basename(path)
        root = os.path.normcase(os.path.abspath(self.root)) if self.root else None
        folder = os.path.normcase(os.path.abspath(os.path.dirname(path)))
        inside = root is not None and (folder == root or (
            self.act_recursive.isChecked() and folder.startswith(root + os.sep)))
        if inside and all(p.path != path for p in self.model.all):
            cur = None
            if 0 <= self.view_row < self.model.rowCount():
                cur = self.model.photo(self.view_row).path
            rel = os.path.relpath(path, self.root).replace("\\", "/")
            try:
                mt = os.path.getmtime(path)
            except OSError:
                mt = time.time()
            self.model.all.append(Photo(path, rel, mt))
            self.model.rebuild()
            if cur is not None:
                self.view_row = self.model.row_of.get(cur, min(self.view_row, self.model.rowCount() - 1))
            self.update_status()
        self.toast.show_message(f"Photo exportée : {name}")

    # ---------------- visionneuse
    def _open_current(self):
        ix = self.grid.currentIndex()
        if ix.isValid():
            self.open_viewer(ix.row())

    def open_viewer(self, row):
        if not 0 <= row < self.model.rowCount():
            return
        pm = start = None
        if ANIM["on"] and self.stack.currentWidget() is self.grid:
            pm = self.model._thumbs.get(self.model.photo(row).path)
            start = self._cell_img_rect(row)
        self.stack.setCurrentWidget(self.viewer)
        self.set_filters_enabled(False)
        self.show_row(row)
        self.viewer.setFocus()
        if pm is not None and start is not None:      # on « entre » dans la photo
            QTimer.singleShot(0, lambda: self.morph.play(pm, start, self._viewer_fit_rect(pm), "in"))

    # ---- animation d'entrée / sortie de la photo
    def _cell_img_rect(self, row):
        """Zone de l'image de la vignette `row` dans la grille, en coordonnées de la zone centrale."""
        vr = self.grid.visualRect(self.model.index(row))
        if vr.isEmpty() or not self.grid.viewport().rect().intersects(vr):
            return None
        r = vr.adjusted(6, 6, -6, -6)
        img = QRect(r.left() + 5, r.top() + 5, r.width() - 10, r.height() - 10 - 36)
        tl = self.grid.viewport().mapTo(self.content, img.topLeft())
        return QRectF(tl.x(), tl.y(), img.width(), img.height())

    def _viewer_fit_rect(self, pm):
        """Où l'image s'affiche (ajustée) dans la visionneuse, en coordonnées de la zone centrale."""
        vp = self.viewer.view.viewport()
        tl = vp.mapTo(self.content, QPoint(0, 0))
        area = QRectF(tl.x(), tl.y(), vp.width(), vp.height())
        s = QSizeF(pm.size()).scaled(area.size(), Qt.AspectRatioMode.KeepAspectRatio)
        r = QRectF(0, 0, s.width(), s.height())
        r.moveCenter(area.center())
        return r

    def _morph_out(self, pm, start, path):
        row = self.model.row_of.get(path)
        end = self._cell_img_rect(row) if row is not None else None
        if end is not None:
            self.morph.play(pm, start, end, "out")

    def _rating_dependent(self):
        """Vrai si l'ordre ou le filtre actuel dépend des notes en étoiles."""
        m = self.model
        return m.sort_key in ("rating", "rating_asc") or m.min_rating > 0 or m.rating_eq is not None

    def resort(self, quiet=False):
        """Réapplique le tri et les filtres (après avoir changé des notes), sélection conservée."""
        m = self.model
        if not m.all:
            return
        sm = self.grid.selectionModel()
        sel = [m.photo(r).path for r in sorted({ix.row() for ix in sm.selectedIndexes()})
               if 0 <= r < m.rowCount()]
        cur = self.grid.currentIndex()
        cur_path = m.photo(cur.row()).path if cur.isValid() and 0 <= cur.row() < m.rowCount() else None
        m.rebuild()
        sm.clearSelection()
        for path in sel:
            r = m.row_of.get(path)
            if r is not None:
                sm.select(m.index(r), QItemSelectionModel.SelectionFlag.Select)
        r = m.row_of.get(cur_path)
        if r is not None:
            sm.setCurrentIndex(m.index(r), QItemSelectionModel.SelectionFlag.NoUpdate)
            self.grid.scrollTo(m.index(r), QAbstractItemView.ScrollHint.EnsureVisible)
        self.update_status()
        if not quiet:
            self.toast.show_message("↻  Tri réappliqué", 1400)

    def close_viewer(self):
        if self.stack.currentWidget() is not self.viewer:
            return
        if self.viewer.lights:                    # Échap rallume d'abord les lumières
            self.viewer.toggle_lights()
            return
        if self.viewer.crop_mode:                 # Échap quitte d'abord l'outil de recadrage
            self.viewer.set_crop_mode(False)
            return
        self._stop_slideshow()
        self.viewer.flush()
        view_path = None
        if 0 <= self.view_row < self.model.rowCount():
            view_path = self.model.photo(self.view_row).path
        pm = start = None
        if ANIM["on"] and view_path:
            pm = self.model._thumbs.get(view_path)
            shown = self.viewer.view.current_pixmap()
            if pm is not None:
                start = self._viewer_fit_rect(shown if not shown.isNull() else pm)
        if self._rating_dependent():
            self.model.rebuild()      # les photos notées prennent leur nouvelle place
        self.stack.setCurrentWidget(self.grid)
        self.set_filters_enabled(True)
        self.act_back.setVisible(False)
        row = self.model.row_of.get(view_path) if view_path else None
        if row is not None:
            ix = self.model.index(row)
            self.grid.selectionModel().clearSelection()
            self.grid.setCurrentIndex(ix)
            self.grid.selectionModel().select(ix, QItemSelectionModel.SelectionFlag.Select)
            self.grid.scrollTo(ix, QAbstractItemView.ScrollHint.PositionAtCenter)
        self.grid.setFocus()
        self.update_status()
        if pm is not None and start is not None and view_path:
            QTimer.singleShot(0, lambda: self._morph_out(pm, start, view_path))

    def toggle_slideshow(self):
        if self.slide_timer.isActive():
            self._stop_slideshow(True)
            return
        if self.stack.currentWidget() is not self.viewer:
            if self.model.rowCount() == 0:
                return
            self._open_current()
            if self.stack.currentWidget() is not self.viewer:
                return
        self.slide_timer.start()
        self.toast.show_message("Diaporama lancé (4 s par photo)      S ou Échap pour arrêter", 2500)

    def _stop_slideshow(self, msg=False):
        if self.slide_timer.isActive():
            self.slide_timer.stop()
            if msg:
                self.toast.show_message("Diaporama arrêté", 1200)

    def _slide_tick(self):
        if self.stack.currentWidget() is not self.viewer or self.view_row >= self.model.rowCount() - 1:
            self._stop_slideshow(True)
            return
        self.show_row(self.view_row + 1)

    def step(self, d):
        r = self.view_row + d
        if 0 <= r < self.model.rowCount():
            self.show_row(r)

    def refresh_viewer_info(self):
        if not 0 <= self.view_row < self.model.rowCount():
            return
        ph = self.model.photo(self.view_row)
        meta = self.meta_cache.get(ph.path)
        if meta is None:
            meta = read_meta(ph.path)
            self.meta_cache[ph.path] = meta
            if len(self.meta_cache) > 500:
                self.meta_cache.pop(next(iter(self.meta_cache)))
        self.viewer.set_info(ph, self.view_row + 1, self.model.rowCount(), meta)

    def show_row(self, row):
        self.view_row = row
        ph = self.model.photo(row)
        self.refresh_viewer_info()
        if self.viewer.cur_key != ph.rel:
            before = self.viewer.current_dev()
            if self.viewer.cur_key and before:
                self._prev_dev = before          # pour le bouton « Précédent »
            self.viewer.begin_photo(ph.rel, self.store.get_dev(ph.rel))
        self.viewer.select_film(row)
        img = self.view_cache.get(ph.path)
        if img is not None:
            self.view_cache.move_to_end(ph.path)
            self.viewer.show_image(img)
        else:
            self.viewer.clear_hist()
            thumb = self.model._thumbs.get(ph.path)
            if thumb is not None:
                self.viewer.view.set_pixmap(thumb)
            else:
                self.viewer.view.clear()
            self._request_view(ph.path, urgent=True)
        for d in (1, -1, 2):
            r = row + d
            if 0 <= r < self.model.rowCount():
                p = self.model.photo(r)
                if p.path not in self.view_cache:
                    self._request_view(p.path, urgent=False)

    def _request_view(self, path, urgent):
        if not urgent and path in self.view_pending:
            return
        self.view_pending.add(path)
        self.view_counter += 1
        prio = (20_000_000 if urgent else 10_000_000) + self.view_counter
        self.pool.start(_ViewJob(path, self.view_sig), prio)

    def _on_view_ready(self, path, img):
        self.view_pending.discard(path)
        cur = None
        if 0 <= self.view_row < self.model.rowCount():
            cur = self.model.photo(self.view_row).path
        if img.isNull():
            return
        self.view_cache[path] = img
        while len(self.view_cache) > VIEW_LRU:
            oldest = next(iter(self.view_cache))
            if oldest == cur and len(self.view_cache) > 1:
                self.view_cache.move_to_end(oldest)
                continue
            self.view_cache.pop(oldest)
        if path == cur and self.stack.currentWidget() is self.viewer and path in self.view_cache:
            self.viewer.show_image(img)
        if self.stack.currentWidget() is self.compare:
            for i, cp in enumerate(self.compare_paths):
                if cp == path and i < len(self.compare.cells):
                    self.compare.cells[i].view.set_image(img)

    # ---------------- déplacer / copier / exporter
    def _files_of(self, photo, listing):
        d = os.path.dirname(photo.path)
        if d not in listing:
            try:
                listing[d] = os.listdir(d)
            except OSError:
                listing[d] = []
        base = os.path.basename(photo.path)
        stem = os.path.splitext(base)[0].lower()
        out = [photo.path]
        for n in listing[d]:
            fp = os.path.join(d, n)
            if fp == photo.path or n == SIDECAR_NAME or not os.path.isfile(fp):
                continue
            nl = n.lower()
            if os.path.splitext(n)[0].lower() == stem or nl.startswith(base.lower() + "."):
                out.append(fp)
        return out

    @staticmethod
    def _unique(dest_dir, name):
        target = os.path.join(dest_dir, name)
        if not os.path.exists(target):
            return target
        stem, ext = os.path.splitext(name)
        i = 1
        while True:
            target = os.path.join(dest_dir, f"{stem} ({i}){ext}")
            if not os.path.exists(target):
                return target
            i += 1

    def _transfer_files(self, photos, dest, move):
        """Déplace/copie les photos (et leurs fichiers associés). -> done, errors, pairs, meta, created"""
        listing = {}
        done, errors, pairs, meta, created = [], [], [], {}, []
        prog = None
        if len(photos) > 15:
            prog = QProgressDialog("Transfert en cours…", "Annuler", 0, len(photos), self)
            prog.setWindowModality(Qt.WindowModality.WindowModal)
            prog.setMinimumDuration(300)
        for i, ph in enumerate(photos):
            if prog is not None:
                prog.setValue(i)
                QApplication.processEvents()
                if prog.wasCanceled():
                    break
            try:
                for k, fp in enumerate(self._files_of(ph, listing)):
                    target = self._unique(dest, os.path.basename(fp))
                    try:
                        if move:
                            shutil.move(fp, target)
                            pairs.append((fp, target))
                        else:
                            shutil.copy2(fp, target)
                            created.append(target)
                    except Exception as ex:  # noqa: BLE001
                        if k == 0:
                            raise
                        errors.append(f"{os.path.basename(fp)} (fichier associé) : {ex}")
                done.append(ph)
                meta[ph.rel] = (ph.rating, ph.flag)
            except Exception as ex:  # noqa: BLE001
                errors.append(f"{ph.name} : {ex}")
        if prog is not None:
            prog.setValue(len(photos))
        return done, errors, pairs, meta, created

    def transfer(self, photos, dest, move):
        if not photos:
            QMessageBox.information(self, APP_NAME, "Aucune photo à traiter.")
            return
        verb = "Déplacer" if move else "Copier"
        if QMessageBox.question(
                self, APP_NAME,
                f"{verb} {len(photos)} photo(s) (avec leurs fichiers associés : JPG, XMP…) vers :\n\n{dest}") \
                != QMessageBox.StandardButton.Yes:
            return
        os.makedirs(dest, exist_ok=True)
        page = self.stack.currentWidget()
        done, errors, pairs, meta, created = self._transfer_files(photos, dest, move)
        if done:
            self._record_transfer(move, pairs, done, created, dest)
            if move:
                self._after_move(done, 0, page)
        self.update_status()
        msg = f"{len(done)} photo(s) {'déplacée(s)' if move else 'copiée(s)'}."
        if done:
            msg += "\n\nTu peux annuler avec le bouton « Annuler » (ou Ctrl+Z)."
        if errors:
            msg += f"\n\n{len(errors)} problème(s) :\n" + "\n".join(errors[:8])
        QMessageBox.information(self, APP_NAME, msg)

    def _need_folder(self):
        if not self.root:
            QMessageBox.information(self, APP_NAME, "Ouvrez d'abord un dossier.")
            return False
        return True

    def move_rejects(self):
        if not self._need_folder():
            return
        photos = [p for p in self.model.all if p.flag == REJECT]
        self.transfer(photos, os.path.join(self.root, "Rejetées"), True)

    def transfer_flagged(self, flag, move):
        if not self._need_folder():
            return
        photos = [p for p in self.model.all if p.flag == flag]
        if not photos:
            QMessageBox.information(self, APP_NAME, "Aucune photo avec ce drapeau.")
            return
        d = QFileDialog.getExistingDirectory(self, "Dossier de destination",
                                             self.settings.value("lastdest", self.root))
        if d:
            self.settings.setValue("lastdest", d)
            self.transfer(photos, d, move)

    def copy_selection(self):
        if not self._need_folder():
            return
        rows = self.target_rows()
        photos = [self.model.photo(r) for r in rows]
        d = QFileDialog.getExistingDirectory(self, "Dossier de destination",
                                             self.settings.value("lastdest", self.root))
        if d:
            self.settings.setValue("lastdest", d)
            self.transfer(photos, d, False)

    def export_csv(self):
        if not self._need_folder():
            return
        fn, _ = QFileDialog.getSaveFileName(self, "Exporter la liste",
                                            os.path.join(self.root, "liste_photos.csv"),
                                            "CSV (*.csv)")
        if not fn:
            return
        names = {PICK: "gardée", REJECT: "rejetée", NO_FLAG: ""}
        with open(fn, "w", newline="", encoding="utf-8-sig") as f:
            w = csv.writer(f, delimiter=";")
            w.writerow(["Fichier", "Note", "Drapeau", "Chemin"])
            for p in sorted(self.model.all, key=lambda p: _natural(p.name)):
                w.writerow([p.name, p.rating, names[p.flag], p.rel])
        QMessageBox.information(self, APP_NAME, f"Liste enregistrée :\n{fn}")

    def write_xmp(self):
        if not self._need_folder():
            return
        todo = [p for p in self.model.all if p.rating or p.flag]
        if not todo:
            QMessageBox.information(self, APP_NAME, "Aucune note ni drapeau à écrire.")
            return
        if QMessageBox.question(
                self, APP_NAME,
                f"Écrire un fichier .xmp à côté de {len(todo)} photo(s) ?\n\n"
                "• Note → étoiles (rejetée = -1)\n• Gardée → étiquette verte\n\n"
                "Les .xmp déjà existants (réglages Lightroom/Camera Raw) ne sont jamais écrasés.") \
                != QMessageBox.StandardButton.Yes:
            return
        written = skipped = 0
        for p in todo:
            xp = os.path.splitext(p.path)[0] + ".xmp"
            if os.path.exists(xp):
                skipped += 1
                continue
            rating = -1 if p.flag == REJECT else p.rating
            label = ' xmp:Label="Green"' if p.flag == PICK else ""
            xml = ('<?xpacket begin="﻿" id="W5M0MpCehiHzreSzNTczkc9d"?>\n'
                   '<x:xmpmeta xmlns:x="adobe:ns:meta/">\n'
                   ' <rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#">\n'
                   '  <rdf:Description rdf:about="" xmlns:xmp="http://ns.adobe.com/xap/1.0/"'
                   f' xmp:Rating="{rating}"{label}/>\n'
                   ' </rdf:RDF>\n</x:xmpmeta>\n<?xpacket end="w"?>\n')
            try:
                with open(xp, "w", encoding="utf-8") as f:
                    f.write(xml)
                written += 1
            except OSError:
                skipped += 1
        QMessageBox.information(self, APP_NAME,
                                f"{written} fichier(s) .xmp écrit(s), {skipped} ignoré(s) "
                                "(déjà existants ou erreur).")

    # ---------------- divers
    def toggle_fullscreen(self):
        self.showNormal() if self.isFullScreen() else self.showFullScreen()

    def show_help(self):
        QMessageBox.information(self, "Raccourcis clavier", HELP_TEXT)

    def eventFilter(self, obj, ev):
        if ev.type() == QEvent.Type.MouseButtonPress and ev.button() == Qt.MouseButton.BackButton \
                and self.isActiveWindow():
            page = self.stack.currentWidget()
            if page is self.viewer:
                self.close_viewer()
                return True
            if page is self.compare:
                self.back_to_grid()
                return True
        return super().eventFilter(obj, ev)

    def closeEvent(self, e):
        self.viewer.flush()
        self.store.flush()
        self.settings.setValue("geometry", self.saveGeometry())
        self.settings.setValue("thumb", self.size_slider.value())
        self.settings.setValue("advance", "true" if self.act_advance.isChecked() else "false")
        self.settings.setValue("sort", self.sort_cb.currentData())
        self.settings.setValue("recursive", "true" if self.act_recursive.isChecked() else "false")
        self.settings.setValue("hist", "true" if self.viewer.hist_on else "false")
        self._remember_stats()
        self.pool.clear()
        self.pool.waitForDone(3000)
        super().closeEvent(e)


def _install_excepthook():
    log = CACHE_DIR / "erreurs.log"
    shown = {"n": 0}

    def hook(et, ev, tb):
        import datetime
        import traceback
        txt = "".join(traceback.format_exception(et, ev, tb))
        try:
            CACHE_DIR.mkdir(parents=True, exist_ok=True)
            with open(log, "a", encoding="utf-8") as f:
                f.write(f"--- {datetime.datetime.now():%Y-%m-%d %H:%M:%S}\n{txt}\n")
        except Exception:
            pass
        try:
            sys.__excepthook__(et, ev, tb)
        except Exception:
            pass
        if shown["n"] < 3:
            shown["n"] += 1
            try:
                QMessageBox.critical(None, APP_NAME,
                                     f"Une erreur est survenue :\n\n{ev}\n\n"
                                     f"Détails enregistrés dans :\n{log}")
            except Exception:
                pass

    sys.excepthook = hook


def main():
    try:
        QImageReader.setAllocationLimit(0)  # autorise les très grandes images
    except Exception:
        pass
    if sys.platform == "win32":
        try:
            import ctypes
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("Klutter.App")
        except Exception:
            pass
    app = QApplication(sys.argv)
    app.setApplicationName(APP_NAME)
    app.setStyle("Fusion")
    if sys.platform == "win32":
        app.setFont(QFont("Segoe UI", 10))
    load_theme(QSettings("TrieurPhotos", "TrieurPhotos"))
    apply_theme(app)
    _install_excepthook()
    win = MainWindow()
    win.setWindowIcon(QIcon(make_logo(128)))
    win.show()
    if len(sys.argv) > 1 and os.path.isdir(sys.argv[1]):
        win.open_folder(sys.argv[1])
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
