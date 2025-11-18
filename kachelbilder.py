#!/usr/bin/env python3
import os
import sys
import math
import random
import argparse
import shutil
import colorsys
import itertools
import csv
import json
import queue
import threading
import subprocess
import tkinter as tk
from datetime import datetime
from tkinter import ttk, filedialog, messagebox, colorchooser
import hashlib

from PIL import Image, ImageTk, ImageDraw, ImageOps, ImageEnhance, ImageFilter, ImageStat, ImageChops

# Optional: Drag & Drop via tkinterdnd2 (falls installiert)
DND_AVAILABLE = False
try:
    from tkinterdnd2 import DND_FILES, TkinterDnD
    DND_AVAILABLE = True
except ImportError:
    DND_AVAILABLE = False

PALETTE_PRESETS = [
    ("4 Farben (2-bit)", 4),
    ("8 Farben", 8),
    ("16 Farben", 16),
    ("32 Farben", 32),
    ("64 Farben (Standard)", 64),
    ("128 Farben", 128),
    ("256 Farben (8-bit)", 256),
    ("Voll (RGB/sRGB)", 0),
]

APP_ROOT = os.getcwd()
SETTINGS_FILE = os.path.join(APP_ROOT, ".kachelbilder_settings.json")
DEFAULT_PALETTE_FOLDER = os.path.join(APP_ROOT, "kacheln")
DEFAULT_MOSAIC_PALETTE = os.path.join(APP_ROOT, "output", "palette_tiles")
DEFAULT_MOSAIC_IMAGE = ""
MAX_MOSAIC_DIMENSION = 8192  # px
TILE_BRIGHTNESS_FACTORS = [0.85, 1.0, 1.15]
DETAIL_THRESHOLD = 12.0
MAX_SUBDIVISION_DEPTH = 2
MIN_REGION_PIXELS = 24
APPLY_UNSHARP_MASK = True
ERROR_DIFFUSION_WEIGHTS = [
    (1, 0, 7 / 16),
    (-1, 1, 3 / 16),
    (0, 1, 5 / 16),
    (1, 1, 1 / 16),
]
PREVIEW_MAX_DIMENSION = 2048
GALLERY_PREVIEW_MAX_DIMENSION = 1024
GALLERY_TILE_SIZE_PRESETS = [
    ("Sehr klein", 56),
    ("Klein", 72),
    ("Mittel", 96),
    ("Groß", 128),
    ("Sehr groß", 168),
]
HARMONY_MODES = [
    ("Keine Anpassung", "none"),
    ("Komplementär", "complementary"),
    ("Analog", "analogous"),
    ("Triadisch", "triadic"),
    ("Split-Komplementär", "split_complementary"),
    ("Monochrom", "monochrome"),
]
HARMONY_TINT_OPTIONS = [
    ("Komplette Kachel tönen", "full"),
    ("Nur Hintergrund tönen", "background"),
]
HARMONY_INTENSITY_PRESETS = [
    ("Pastell", (0.75, 0.92)),
    ("Standard", (1.0, 1.0)),
    ("Lebhaft", (1.2, 1.06)),
    ("Kräftig", (1.35, 1.12)),
]
FOREGROUND_VARIANT_OPTIONS = [
    ("Neutral", {"brightness": 1.0}),
    ("Heller", {"brightness": 1.18}),
    ("Wärmer", {"brightness": 1.1, "overlay": (255, 184, 120), "alpha": 0.23}),
    ("Kühler", {"brightness": 1.1, "overlay": (130, 190, 255), "alpha": 0.23}),
]
DEFAULT_HARMONY_BASE = "#ff8c3f"
HARMONY_HUE_TOLERANCE = 30.0

TYPE_SYMBOLS = ["A", "B", "C", "D", "E"]
DEFAULT_TYPE_PATHS = {
    "A": os.path.join(APP_ROOT, "F"),
    "B": os.path.join(APP_ROOT, "E"),
    "C": os.path.join(APP_ROOT, "F1"),
    "D": os.path.join(APP_ROOT, "E1"),
    "E": os.path.join(APP_ROOT, "kacheln", "E"),
}
TILE_META_CACHE_PATH = os.path.join(APP_ROOT, ".cache", "tile_metadata.json")
_TILE_META_CACHE = None


def _pattern_chessboard(size=8):
    rows = []
    for y in range(size):
        row = "".join("AB"[(x + y) % 2] for x in range(size))
        rows.append(row)
    return "\n".join(rows)


def _pattern_diagonal(width=10, height=10, symbols="ABC"):
    rows = []
    length = len(symbols)
    for y in range(height):
        row = "".join(symbols[(x + y) % length] for x in range(width))
        rows.append(row)
    return "\n".join(rows)


def _pattern_cross(size=9, thickness=1):
    center = size // 2
    rows = []
    for y in range(size):
        row = []
        for x in range(size):
            if x == center and y == center:
                row.append("A")
            elif abs(x - center) <= thickness or abs(y - center) <= thickness:
                row.append("C")
            else:
                row.append("B")
        rows.append("".join(row))
    return "\n".join(rows)


def _pattern_circle(size=11):
    center = (size - 1) / 2
    radius = center
    symbols = ["E", "D", "C", "B", "A"]
    thresholds = [0.2, 0.45, 0.65, 0.85, 1.1]
    rows = []
    for y in range(size):
        row = []
        for x in range(size):
            dist = math.hypot(x - center, y - center) / radius
            for thresh, symbol in zip(thresholds, symbols):
                if dist <= thresh:
                    row.append(symbol)
                    break
        rows.append("".join(row))
    return "\n".join(rows)


def _pattern_tree(width=12, height=12):
    trunk_width = max(1, width // 6)
    foliage_height = height * 2 // 3
    rows = []
    for y in range(height):
        row = []
        for x in range(width):
            if y >= foliage_height:
                trunk_start = (width - trunk_width) // 2
                row.append("C" if trunk_start <= x < trunk_start + trunk_width else "A")
            else:
                center = width / 2
                spread = (foliage_height - y) / foliage_height * center
                row.append("B" if center - spread <= x <= center + spread else "A")
        rows.append("".join(row))
    return "\n".join(rows)


def _pattern_aztec(size=12):
    rows = []
    symbols = "ABCD"
    for y in range(size):
        row = []
        for x in range(size):
            zone = min(x, y, size - 1 - x, size - 1 - y)
            row.append(symbols[zone % len(symbols)])
        rows.append("".join(row))
    return "\n".join(rows)


def _pattern_vertical_stripes(width=15, height=10, symbols="ABCDE"):
    rows = []
    length = len(symbols)
    for y in range(height):
        row = []
        for x in range(width):
            row.append(symbols[(x // 2) % length])
        rows.append("".join(row))
    return "\n".join(rows)


RASTER_PATTERN_PRESETS = [
    ("Schachbrett 8x8 (2 Typen)", _pattern_chessboard(8)),
    ("Diagonal-Wellen 10x10 (3 Typen)", _pattern_diagonal(10, 10, "ABC")),
    ("Aztec 12x12 (4 Typen)", _pattern_aztec(12)),
    ("Kreuz 9x9 (3 Typen)", _pattern_cross(9, 1)),
    ("Kreis 11x11 (4 Typen)", _pattern_circle(11)),
    ("Baum 12x12 (3 Typen)", _pattern_tree(12, 12)),
    ("Streifen 15x10 (5 Typen)", _pattern_vertical_stripes(15, 10, "ABCDE")),
]


def palette_size_from_spec(spec: str) -> int:
    if not spec:
        return 64
    spec = spec.strip().lower()
    aliases = {
        "2bit": 4,
        "2-bit": 4,
        "4bit": 16,
        "4-bit": 16,
        "6bit": 64,
        "6-bit": 64,
        "8bit": 256,
        "8-bit": 256,
        "rgb": 0,
        "srgb": 0,
        "full": 0,
    }
    if spec in aliases:
        return aliases[spec]
    for label, size in PALETTE_PRESETS:
        if spec in label.lower():
            return size
    try:
        value = int(spec)
        if value < 0:
            value = 0
        return value
    except ValueError:
        return 64


# --------------------------------------------------------
# Utility-Funktionen
# --------------------------------------------------------

def ensure_folder(path: str) -> None:
    os.makedirs(path, exist_ok=True)


class ToolTip:
    def __init__(self, widget, text, delay=600, wraplength=340):
        self.widget = widget
        self.text = text
        self.delay = delay
        self.wraplength = wraplength
        self._after_id = None
        self.tip_window = None
        widget.bind("<Enter>", self._schedule)
        widget.bind("<Leave>", self._hide)
        widget.bind("<ButtonPress>", self._hide)

    def _schedule(self, _event=None):
        self._cancel()
        self._after_id = self.widget.after(self.delay, self._show)

    def _cancel(self):
        if self._after_id:
            self.widget.after_cancel(self._after_id)
            self._after_id = None

    def _show(self):
        if self.tip_window or not self.text:
            return
        x = self.widget.winfo_rootx() + 10
        y = self.widget.winfo_rooty() + self.widget.winfo_height() + 4
        self.tip_window = tw = tk.Toplevel(self.widget)
        tw.wm_overrideredirect(True)
        tw.wm_geometry(f"+{x}+{y}")
        label = ttk.Label(
            tw,
            text=self.text,
            justify="left",
            background="#ffffe0",
            relief="solid",
            borderwidth=1,
            wraplength=self.wraplength,
            padding=4,
        )
        label.pack()

    def _hide(self, _event=None):
        self._cancel()
        tw = self.tip_window
        if tw:
            tw.destroy()
            self.tip_window = None

def _load_tile_meta_cache():
    global _TILE_META_CACHE
    if _TILE_META_CACHE is not None:
        return _TILE_META_CACHE
    _TILE_META_CACHE = {}
    if os.path.isfile(TILE_META_CACHE_PATH):
        try:
            with open(TILE_META_CACHE_PATH, "r", encoding="utf-8") as fh:
                _TILE_META_CACHE = json.load(fh)
        except Exception:
            _TILE_META_CACHE = {}
    return _TILE_META_CACHE


def _save_tile_meta_cache():
    if _TILE_META_CACHE is None:
        return
    ensure_folder(os.path.dirname(TILE_META_CACHE_PATH))
    try:
        with open(TILE_META_CACHE_PATH, "w", encoding="utf-8") as fh:
            json.dump(_TILE_META_CACHE, fh)
    except Exception:
        pass


def _compute_tile_metadata(path, image=None):
    close_image = False
    if image is None:
        image = Image.open(path).convert("RGB")
        close_image = True
    stat = ImageStat.Stat(image)
    mean_rgb = tuple(int(round(val)) for val in stat.mean[:3])
    r, g, b = (val / 255.0 for val in mean_rgb)
    hue, sat, val = colorsys.rgb_to_hsv(r, g, b)
    meta = {
        "mtime": os.path.getmtime(path),
        "mean_rgb": mean_rgb,
        "hue": hue * 360.0,
        "saturation": sat,
        "value": val,
    }
    bg_color = _estimate_tile_background_color(image)
    if bg_color:
        meta["background"] = bg_color
    if close_image:
        image.close()
    return meta


def _get_tile_metadata(path, image=None):
    cache = _load_tile_meta_cache()
    try:
        mtime = os.path.getmtime(path)
    except OSError:
        return None
    entry = cache.get(path)
    if entry and abs(entry.get("mtime", 0) - mtime) < 0.0001:
        return entry
    meta = _compute_tile_metadata(path, image)
    cache[path] = meta
    _save_tile_meta_cache()
    return meta


def _quantize_color(rgb, step=32):
    return tuple((channel // step) * step for channel in rgb)


def _estimate_tile_background_color(img):
    if not img or img.width < 2 or img.height < 2:
        return None
    sample_size = max(4, min(48, min(img.width, img.height) // 2 or 4))
    sample = img.resize((sample_size, sample_size), Image.NEAREST)
    buckets = {}
    counts = {}
    for pixel in sample.getdata():
        q = _quantize_color(pixel)
        counts[q] = counts.get(q, 0) + 1
        bucket = buckets.setdefault(q, [0, 0, 0])
        bucket[0] += pixel[0]
        bucket[1] += pixel[1]
        bucket[2] += pixel[2]
    if not counts:
        return None
    best_key = max(counts.items(), key=lambda kv: kv[1])[0]
    total = counts[best_key]
    sums = buckets[best_key]
    if total <= 0:
        return None
    return tuple(int(s / total) for s in sums)


def _create_background_mask(img, bg_color, tolerance=35):
    if not img or bg_color is None:
        return None
    base = img.convert("RGB")
    bg_layer = Image.new("RGB", base.size, tuple(bg_color))
    diff = ImageChops.difference(base, bg_layer).convert("L")
    mask = diff.point(lambda v: 255 if v <= tolerance else 0)
    if mask.getextrema() == (0, 0):
        return None
    mask = mask.filter(ImageFilter.GaussianBlur(radius=1))
    return mask


def next_number_in_folder(folder: str, prefix: str) -> int:
    """Findet die nächste freie laufende Nummer für Dateien mit Prefix."""
    ensure_folder(folder)
    existing = []
    for f in os.listdir(folder):
        name, ext = os.path.splitext(f)
        if ext.lower() not in (".png", ".jpg", ".jpeg"):
            continue
        if not name.startswith(prefix):
            continue
        num_part = name[len(prefix):]
        if num_part.isdigit():
            existing.append(int(num_part))
    return max(existing) + 1 if existing else 1


def sort_and_rename(paths, category: str) -> None:
    """
    paths: Liste von Datei-Pfaden
    category: 'F' oder 'E'
    """
    if category not in ("F", "E"):
        raise ValueError("category must be 'F' or 'E'")

    folder = category
    prefix = category
    ensure_folder(folder)
    num = next_number_in_folder(folder, prefix)

    count = 0
    for p in paths:
        if not os.path.isfile(p):
            continue
        _, ext = os.path.splitext(p)
        ext = ext.lower()
        if ext not in (".png", ".jpg", ".jpeg"):
            continue
        new_name = f"{prefix}{num:03d}{ext}"
        dst = os.path.join(folder, new_name)
        shutil.copy2(p, dst)
        num += 1
        count += 1

    print(f"Sorted {count} files into {folder}/")


def unique_output_path(folder="output", prefix="raster_"):
    """Erzeugt einen eindeutigen Dateipfad für generierte Rasterbilder."""
    ensure_folder(folder)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    candidate = os.path.join(folder, f"{prefix}{timestamp}.png")
    idx = 1
    while os.path.exists(candidate):
        candidate = os.path.join(folder, f"{prefix}{timestamp}_{idx}.png")
        idx += 1
    return candidate


def count_pattern_slots(pattern_rows):
    counts = {"F": 0, "E": 0}
    for row in pattern_rows:
        for ch in row:
            if ch in counts:
                counts[ch] += 1
    return counts


def build_tile_batches(tiles, slots):
    """Teilt Tiles in Batches auf, sodass jede Kachel mindestens einmal genutzt wird."""
    if not tiles:
        return []
    if slots <= 0:
        return [tiles]
    num_batches = max(1, math.ceil(len(tiles) / slots))
    batches = []
    for i in range(num_batches):
        start = i * slots
        batch = tiles[start:start + slots]
        if not batch:
            batch = tiles[:slots]
        if len(batch) < slots:
            needed = slots - len(batch)
            batch = batch + tiles[:needed]
        batches.append(batch)
    return batches


def prepare_batches(pattern_rows, tiles_F, tiles_E):
    counts = count_pattern_slots(pattern_rows)
    num_f_slots = counts.get("F", 0)
    num_e_slots = counts.get("E", 0)
    batches_F = build_tile_batches(tiles_F, num_f_slots) or [tiles_F]
    batches_E = build_tile_batches(tiles_E, num_e_slots) or [tiles_E]
    return batches_F, batches_E


def generate_batch_rasters(
    pattern_rows,
    tiles_F,
    tiles_E,
    shuffle_tiles=False,
    prefix="raster_batch_",
    batches_F=None,
    batches_E=None,
    progress_cb=None,
    log_cb=None,
):
    """Erzeugt alle Batch-Kombinationen aus F/E Tiles und speichert die Ergebnisse."""
    if batches_F is None or batches_E is None:
        batches_F, batches_E = prepare_batches(pattern_rows, tiles_F, tiles_E)

    total = len(batches_F) * len(batches_E)
    if total == 0:
        return [], None, 0

    results = []
    last_img = None
    progress = 0

    for f_idx, batch_F in enumerate(batches_F, start=1):
        for e_idx, batch_E in enumerate(batches_E, start=1):
            img = build_raster(pattern_rows, batch_F, batch_E, shuffle_tiles=shuffle_tiles)
            out_prefix = f"{prefix}F{f_idx:02d}_E{e_idx:02d}_"
            out_path = unique_output_path(prefix=out_prefix)
            img.save(out_path)
            results.append(out_path)
            last_img = img
            progress += 1
            if progress_cb:
                progress_cb(progress, total)
            if log_cb:
                log_cb(f"Raster gespeichert als: {out_path}")

    return results, last_img, total


def tile_representative_color(img):
    """Ermittelt eine repräsentative Farbe (Downscale auf 1x1)."""
    return img.resize((1, 1), Image.LANCZOS).getpixel((0, 0))


def extract_tile_colors(tiles):
    return [tile_representative_color(t.convert("RGB")) for t in tiles]


def quantize_color_list(colors, palette_size):
    """Reduziert die Farbliste auf palette_size Einträge via Median Cut."""
    if palette_size <= 0 or palette_size >= len(colors):
        seen = set()
        deduped = []
        for c in colors:
            if c not in seen:
                deduped.append(c)
                seen.add(c)
        return deduped

    palette_img = Image.new("RGB", (len(colors), 1))
    palette_img.putdata(colors)
    pal = palette_img.quantize(colors=palette_size, method=Image.MEDIANCUT)
    palette = pal.getpalette()
    if not palette:
        return colors[:palette_size]
    quantized = []
    color_counts = pal.getcolors()
    if color_counts:
        for count, idx in sorted(color_counts, reverse=True):
            base = idx * 3
            rgb = tuple(palette[base:base + 3])
            quantized.append(rgb)
    return quantized[:palette_size]


def sort_colors_by_hsv(colors):
    def key(rgb):
        r, g, b = (val / 255.0 for val in rgb)
        h, s, v = colorsys.rgb_to_hsv(r, g, b)
        return (h, v, s)

    return sorted(colors, key=key)


def build_palette_image(colors, columns=None, cell_size=48):
    if not colors:
        raise ValueError("Keine Farben vorhanden.")
    n = len(colors)
    if columns is None:
        columns = math.ceil(math.sqrt(n))
    rows = math.ceil(n / columns)
    img = Image.new("RGB", (columns * cell_size, rows * cell_size), "white")
    draw = ImageDraw.Draw(img)
    for idx, color in enumerate(colors):
        row = idx // columns
        col = idx % columns
        x0 = col * cell_size
        y0 = row * cell_size
        x1 = x0 + cell_size
        y1 = y0 + cell_size
        draw.rectangle([x0, y0, x1, y1], fill=color, outline="black")
    return img


def _hex_color(rgb):
    return "#{:02X}{:02X}{:02X}".format(*rgb)


def tint_image_to_color(img, target_rgb, blend_factor=0.2):
    gray = img.convert("L")
    colorized = ImageOps.colorize(gray, black="black", white=tuple(target_rgb))
    if blend_factor > 0:
        colorized = Image.blend(colorized, img.convert("RGB"), blend_factor)
    return colorized


PALETTE_PRESET_SIZES = {
    "srgb": 4096,
    "rgb": 4096,
    "full": 4096,
}


def _build_target_palette(colors, desired_size):
    if desired_size <= len(colors):
        quantized = quantize_color_list(colors, desired_size)
        if not quantized:
            quantized = colors[:desired_size]
        return sort_colors_by_hsv(quantized) or quantized

    # We want more colors than inputs provide – generate evenly distributed RGB cube points
    levels = max(2, int(round(desired_size ** (1 / 3))))
    step = max(1, 255 // (levels - 1))
    generated = []
    for r in range(0, 256, step):
        for g in range(0, 256, step):
            for b in range(0, 256, step):
                generated.append((r, g, b))
                if len(generated) >= desired_size:
                    break
            if len(generated) >= desired_size:
                break
        if len(generated) >= desired_size:
            break
    return sort_colors_by_hsv(generated[:desired_size]) or generated[:desired_size]


def _resolve_palette_size(palette_size, label):
    if palette_size > 0:
        return palette_size
    key = (label or "").strip().lower()
    for token, size in PALETTE_PRESET_SIZES.items():
        if token in key:
            return size
    return palette_size


def generate_palette_tile_set(folder, palette_size, output_root=None, prefix="palette_tile_", label=None, progress_cb=None):
    if not os.path.isdir(folder):
        raise ValueError(f"Ordner nicht gefunden: {folder}")

    files = []
    for entry in sorted(os.listdir(folder)):
        if entry.lower().endswith((".png", ".jpg", ".jpeg")):
            files.append(os.path.join(folder, entry))

    if not files:
        raise ValueError("Keine Bilder im angegebenen Ordner gefunden.")

    tiles = []
    colors = []
    for path in files:
        with Image.open(path) as img:
            img_rgb = img.convert("RGB")
        tiles.append((path, img_rgb))
        colors.append(tile_representative_color(img_rgb))

    resolved_size = _resolve_palette_size(palette_size, label)
    if resolved_size <= 0:
        resolved_size = len(tiles)

    target_colors = _build_target_palette(colors, resolved_size)
    color_cycle = list(itertools.islice(itertools.cycle(target_colors), resolved_size))
    tile_cycle = list(itertools.islice(itertools.cycle(tiles), resolved_size))

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    base_dir = output_root or os.path.join("output", "palette_tiles")
    out_dir = os.path.join(base_dir, f"{prefix}{resolved_size}_{timestamp}")
    ensure_folder(out_dir)

    metadata_path = os.path.join(out_dir, "metadata.csv")
    saved_files = []

    with open(metadata_path, "w", newline="", encoding="utf-8") as meta_file:
        writer = csv.writer(meta_file)
        writer.writerow([
            "index",
            "palette_color",
            "hex",
            "source_file",
            "output_file",
            "lab_l",
            "lab_a",
            "lab_b",
            "histogram",
        ])

        for idx, (target_color, (src_path, img)) in enumerate(zip(color_cycle, tile_cycle), start=1):
            tinted = tint_image_to_color(img, target_color)
            filename = f"{prefix}{idx:04d}.png"
            out_path = os.path.join(out_dir, filename)
            tinted.save(out_path)
            saved_files.append(out_path)
            lab = _image_mean_lab(tinted)
            hist = _luminance_histogram(tinted)
            writer.writerow([
                idx,
                target_color,
                _hex_color(target_color),
                os.path.basename(src_path),
                filename,
                f"{lab[0]:.4f}",
                f"{lab[1]:.4f}",
                f"{lab[2]:.4f}",
                _hist_to_string(hist),
            ])
            if progress_cb:
                progress_cb(idx, resolved_size)

    preview_img = build_palette_image(color_cycle)
    preview_path = os.path.join(out_dir, "palette_preview.png")
    preview_img.save(preview_path)
    return {
        "directory": out_dir,
        "files": saved_files,
        "palette_image": preview_img,
        "preview_path": preview_path,
        "palette_colors": color_cycle,
        "metadata": metadata_path,
        "count": len(saved_files),
        "requested_size": palette_size,
    }


def _parse_color_string(value):
    if isinstance(value, (tuple, list)):
        return tuple(int(v) for v in value[:3])
    text = str(value).strip()
    if text.startswith("(") and text.endswith(")"):
        text = text[1:-1]
    parts = [p.strip() for p in text.split(",")]
    nums = []
    for part in parts[:3]:
        try:
            nums.append(int(float(part)))
        except ValueError:
            nums.append(0)
    while len(nums) < 3:
        nums.append(0)
    return tuple(nums[:3])


def read_palette_metadata(palette_dir):
    metadata_path = os.path.join(palette_dir, "metadata.csv")
    if not os.path.isfile(metadata_path):
        raise ValueError(f"metadata.csv nicht gefunden in {palette_dir}")
    entries = []
    with open(metadata_path, "r", encoding="utf-8") as meta_file:
        reader = csv.DictReader(meta_file)
        for row in reader:
            color = _parse_color_string(row.get("palette_color") or row.get("color"))
            filename = row.get("output_file") or row.get("file")
            if not filename:
                continue
            path = os.path.join(palette_dir, filename)
            if not os.path.isfile(path):
                continue
            hist = _parse_hist_string(row.get("histogram"))
            try:
                lab = (
                    float(row.get("lab_l")) if row.get("lab_l") else None,
                    float(row.get("lab_a")) if row.get("lab_a") else None,
                    float(row.get("lab_b")) if row.get("lab_b") else None,
                )
                if lab[0] is None:
                    lab = None
            except ValueError:
                lab = None
            entries.append({
                "color": color,
                "file": path,
                "index": row.get("index"),
                "hex": row.get("hex") or _hex_color(color),
                "lab": lab,
                "hist": hist,
            })
    if not entries:
        raise ValueError(f"Keine Palette-Kacheln in {metadata_path}")
    return entries


def load_palette_tile_images(palette_dir):
    metadata = read_palette_metadata(palette_dir)
    tiles = []
    for entry in metadata:
        base_img = Image.open(entry["file"]).convert("RGB")
        base_img.load()
        base_lab = entry.get("lab") or _image_mean_lab(base_img)
        base_hist = entry.get("hist") or _luminance_histogram(base_img)
        for factor in TILE_BRIGHTNESS_FACTORS:
            if abs(factor - 1.0) < 0.001:
                variant_img = base_img.copy()
                variant_color = base_img.resize((1, 1), Image.LANCZOS).getpixel((0, 0))
                variant_lab = base_lab
                variant_hist = base_hist
            else:
                enhancer = ImageEnhance.Brightness(base_img)
                variant_img = enhancer.enhance(factor)
                variant_color = variant_img.resize((1, 1), Image.LANCZOS).getpixel((0, 0))
                variant_lab = _image_mean_lab(variant_img)
                variant_hist = _luminance_histogram(variant_img)
            tiles.append({
                "color": variant_color,
                "hex": entry["hex"],
                "path": entry["file"],
                "image": variant_img,
                "lab": variant_lab,
                "hist": variant_hist,
                "brightness": factor,
            })
    return tiles


def get_palette_tile_size(palette_dir):
    metadata = read_palette_metadata(palette_dir)
    sample = metadata[0]
    with Image.open(sample["file"]) as img:
        return img.size


def _color_distance_sq(c1, c2):
    dr = c1[0] - c2[0]
    dg = c1[1] - c2[1]
    db = c1[2] - c2[2]
    return dr * dr + dg * dg + db * db


def _rgb_to_lab(r, g, b):
    """Konvertiert RGB (0-255) in CIE LAB (D65)"""
    def _pivot(c):
        return c / 12.92 if c <= 0.04045 else ((c + 0.055) / 1.055) ** 2.4

    r_lin = _pivot(r / 255.0)
    g_lin = _pivot(g / 255.0)
    b_lin = _pivot(b / 255.0)

    x = r_lin * 0.4124 + g_lin * 0.3576 + b_lin * 0.1805
    y = r_lin * 0.2126 + g_lin * 0.7152 + b_lin * 0.0722
    z = r_lin * 0.0193 + g_lin * 0.1192 + b_lin * 0.9505

    x /= 0.95047
    y /= 1.00000
    z /= 1.08883

    def _pivot_xyz(t):
        return t ** (1 / 3) if t > 0.008856 else (7.787 * t) + (16 / 116)

    fx = _pivot_xyz(x)
    fy = _pivot_xyz(y)
    fz = _pivot_xyz(z)

    l = max(0, 116 * fy - 16)
    a = 500 * (fx - fy)
    b = 200 * (fy - fz)
    return (l, a, b)


def _image_mean_lab(img, sample_size=32):
    if img.width > sample_size or img.height > sample_size:
        sample = img.resize((sample_size, sample_size), Image.LANCZOS)
    else:
        sample = img
    total = len(sample.getdata())
    if total == 0:
        return (0.0, 0.0, 0.0)
    sum_l = sum_a = sum_b = 0.0
    for pixel in sample.getdata():
        lab = _rgb_to_lab(*pixel)
        sum_l += lab[0]
        sum_a += lab[1]
        sum_b += lab[2]
    return (sum_l / total, sum_a / total, sum_b / total)


def _luminance_histogram(img, bins=8):
    gray = img.convert("L")
    hist = gray.histogram()
    bin_size = max(1, 256 // bins)
    values = []
    for i in range(bins):
        start = i * bin_size
        end = start + bin_size
        values.append(sum(hist[start:end]))
    total = sum(values) or 1
    return [v / total for v in values]


def _hist_to_string(hist):
    return "|".join(f"{v:.6f}" for v in hist)


def _parse_hist_string(text, bins=8):
    if not text:
        return None
    try:
        values = [float(v) for v in text.split("|") if v]
    except ValueError:
        return None
    if len(values) != bins:
        return None
    total = sum(values)
    if total <= 0:
        return None
    return values


def _lab_distance_sq(lab1, lab2):
    if not lab1 or not lab2:
        return 0
    return ((lab1[0] - lab2[0]) ** 2 +
            (lab1[1] - lab2[1]) ** 2 +
            (lab1[2] - lab2[2]) ** 2)


def _hist_distance(hist1, hist2):
    if not hist1 or not hist2 or len(hist1) != len(hist2):
        return 0
    return sum((a - b) ** 2 for a, b in zip(hist1, hist2))


def _tile_match_score(tile, rgb, lab, hist):
    weight_rgb = 0.5
    weight_lab = 0.35
    weight_hist = 0.15
    return (
        weight_rgb * _color_distance_sq(rgb, tile["color"]) +
        weight_lab * _lab_distance_sq(lab, tile.get("lab")) +
        weight_hist * _hist_distance(hist, tile.get("hist"))
    )


def _region_detail(region):
    gray = region.convert("L")
    stat = ImageStat.Stat(gray)
    return math.sqrt(max(stat.var[0], 0.0))


def _open_file_in_viewer(path):
    if not path or not os.path.isfile(path):
        return False
    try:
        if sys.platform.startswith("darwin"):
            subprocess.Popen(["open", path])
        elif os.name == "nt":
            os.startfile(path)  # type: ignore[attr-defined]
        else:
            subprocess.Popen(["xdg-open", path])
        return True
    except Exception:
        return False


def suggest_mosaic_resolutions(image_path, tile_size, max_options=6):
    if not os.path.isfile(image_path):
        raise ValueError("Bild nicht gefunden.")
    tile_w, tile_h = tile_size
    if tile_w <= 0 or tile_h <= 0:
        raise ValueError("Ungültige Tile-Größe.")
    with Image.open(image_path) as img:
        width, height = img.size
    scales = [0.05, 0.08, 0.12, 0.16, 0.2, 0.3, 0.4, 0.6, 0.8, 1, 1.5, 2]
    candidates = []
    for scale in scales:
        col = max(1, int(round(width * scale)))
        row = max(1, int(round(height * scale)))
        candidates.append((col, row))

    half_cols = max(1, width // 2)
    half_rows = max(1, height // 2)
    candidates.append((half_cols, half_rows))

    unique = []
    seen = set()
    for col, row in candidates:
        key = (col, row)
        if key in seen:
            continue
        seen.add(key)
        unique.append({"cols": col, "rows": row})
        if len(unique) >= max_options:
            break

    if not unique:
        unique = [{"cols": width, "rows": height}]

    for opt in unique:
        total_tiles = opt["cols"] * opt["rows"]
        opt["label"] = f"{opt['cols']} x {opt['rows']} Tiles (~{total_tiles} Kacheln)"
    return unique


def generate_mosaic_from_palette(image_path, palette_dir, cols=None, rows=None, prefix="mosaic_", progress_cb=None):
    entries = load_palette_tile_images(palette_dir)
    if not entries:
        raise ValueError("Keine Palette-Kacheln gefunden.")
    tile_w, tile_h = entries[0]["image"].size
    with Image.open(image_path) as img:
        target = img.convert("RGB")
    width, height = target.size
    if cols is None and rows is None:
        cols = width
    if cols is None:
        cols = max(1, int(round(rows * width / height)))
    if rows is None:
        rows = max(1, int(round(cols * height / width)))

    small = target.resize((cols, rows), Image.LANCZOS)
    desired_cell_w = max(1, int(math.ceil(width / cols)))
    desired_cell_h = max(1, int(math.ceil(height / rows)))
    cell_w = max(tile_w, desired_cell_w)
    cell_h = max(tile_h, desired_cell_h)

    out_w = cols * cell_w
    out_h = rows * cell_h
    max_dim = max(out_w, out_h)
    if max_dim > MAX_MOSAIC_DIMENSION:
        scale = MAX_MOSAIC_DIMENSION / max_dim
        scaled_w = max(1, int(cell_w * scale))
        scaled_h = max(1, int(cell_h * scale))
        cell_w = max(desired_cell_w, scaled_w)
        cell_h = max(desired_cell_h, scaled_h)
        out_w = cols * cell_w
        out_h = rows * cell_h

    mosaic = Image.new("RGB", (out_w, out_h))
    scale_x = out_w / width
    scale_y = out_h / height

    min_region_w = max(MIN_REGION_PIXELS, tile_w)
    min_region_h = max(MIN_REGION_PIXELS, tile_h)

    total = rows * cols
    processed = 0

    err_r = [[0.0] * cols for _ in range(rows)]
    err_g = [[0.0] * cols for _ in range(rows)]
    err_b = [[0.0] * cols for _ in range(rows)]

    def render_region(x0, y0, x1, y1, depth=0, color_bias=None):
        region_w = max(1.0, x1 - x0)
        region_h = max(1.0, y1 - y0)
        box = (int(math.floor(x0)), int(math.floor(y0)), int(math.ceil(x1)), int(math.ceil(y1)))
        if box[2] <= box[0]:
            box = (box[0], box[1], box[0] + 1, box[3])
        if box[3] <= box[1]:
            box = (box[0], box[1], box[2], box[1] + 1)
        region = target.crop(box)
        detail = _region_detail(region)
        if (
            detail > DETAIL_THRESHOLD
            and depth < MAX_SUBDIVISION_DEPTH
            and region_w >= min_region_w
            and region_h >= min_region_h
        ):
            xm = x0 + region_w / 2
            ym = y0 + region_h / 2
            quadrants = [
                (render_region(x0, y0, xm, ym, depth + 1, color_bias), (xm - x0) * (ym - y0)),
                (render_region(xm, y0, x1, ym, depth + 1, color_bias), (x1 - xm) * (ym - y0)),
                (render_region(x0, ym, xm, y1, depth + 1, color_bias), (xm - x0) * (y1 - ym)),
                (render_region(xm, ym, x1, y1, depth + 1, color_bias), (x1 - xm) * (y1 - ym)),
            ]
            total_area = sum(area for _, area in quadrants if area > 0)
            valid = [item for item in quadrants if item[0] and item[1] > 0]
            if not valid or total_area == 0:
                return None
            avg = []
            for i in range(3):
                avg.append(sum(color[i] * area for color, area in valid) / total_area)
            return tuple(avg)

        region_rgb = region.resize((1, 1), Image.LANCZOS).getpixel((0, 0))
        if color_bias:
            region_rgb = tuple(
                int(max(0, min(255, (region_rgb[i] + color_bias[i]) / 2)))
                for i in range(3)
            )
        region_lab = _rgb_to_lab(*region_rgb)
        region_hist = _luminance_histogram(region)

        best = min(entries, key=lambda e: _tile_match_score(e, region_rgb, region_lab, region_hist))
        tile_img = best["image"]
        dest_w = max(1, int(round(region_w * scale_x)))
        dest_h = max(1, int(round(region_h * scale_y)))
        if tile_img.size != (dest_w, dest_h):
            tile_img = tile_img.resize((dest_w, dest_h), Image.LANCZOS)
        dest_x = int(round(x0 * scale_x))
        dest_y = int(round(y0 * scale_y))
        mosaic.paste(tile_img, (dest_x, dest_y))
        return best["color"]

    for y in range(rows):
        for x in range(cols):
            x0 = x * width / cols
            x1 = (x + 1) * width / cols
            y0 = y * height / rows
            y1 = (y + 1) * height / rows
            base_rgb = small.getpixel((x, y))
            adj_rgb = (
                int(max(0, min(255, base_rgb[0] + err_r[y][x]))),
                int(max(0, min(255, base_rgb[1] + err_g[y][x]))),
                int(max(0, min(255, base_rgb[2] + err_b[y][x]))),
            )
            avg_color = render_region(x0, y0, x1, y1, 0, adj_rgb) or base_rgb
            diff = (
                adj_rgb[0] - avg_color[0],
                adj_rgb[1] - avg_color[1],
                adj_rgb[2] - avg_color[2],
            )
            for dx, dy, weight in ERROR_DIFFUSION_WEIGHTS:
                nx = x + dx
                ny = y + dy
                if 0 <= nx < cols and 0 <= ny < rows:
                    err_r[ny][nx] += diff[0] * weight
                    err_g[ny][nx] += diff[1] * weight
                    err_b[ny][nx] += diff[2] * weight
            processed += 1
            if progress_cb:
                progress_cb(processed, total)

    if APPLY_UNSHARP_MASK:
        mosaic = mosaic.filter(ImageFilter.UnsharpMask(radius=2, percent=130, threshold=2))

    out_path = unique_output_path(prefix=prefix)
    mosaic.save(out_path)
    return {
        "path": out_path,
        "cols": cols,
        "rows": rows,
        "tile_size": (cell_w, cell_h),
        "image": mosaic,
    }


def load_tiles(folder: str):
    """Lädt alle Tiles (PNG/JPG) aus einem Ordner."""
    if not os.path.isdir(folder):
        raise ValueError(f"Folder not found: {folder}")

    files = []
    for f in sorted(os.listdir(folder)):
        if f.lower().endswith((".png", ".jpg", ".jpeg")):
            files.append(os.path.join(folder, f))

    if not files:
        raise ValueError(f"No images in folder: {folder}")

    tiles = []
    for path in files:
        img = Image.open(path).convert("RGB")
        tiles.append(img)
    return tiles


def load_tile_infos(folder: str):
    """Lädt Tiles mit Metadaten (Farbe, Pfad)."""
    if not os.path.isdir(folder):
        raise ValueError(f"Folder not found: {folder}")
    infos = []
    for name in sorted(os.listdir(folder)):
        if not name.lower().endswith((".png", ".jpg", ".jpeg")):
            continue
        path = os.path.join(folder, name)
        try:
            img = Image.open(path).convert("RGB")
        except OSError:
            continue
        meta = _get_tile_metadata(path, img) or {}
        info = {
            "path": path,
            "image": img,
            "mean_rgb": tuple(meta.get("mean_rgb") or (128, 128, 128)),
            "hue": float(meta.get("hue", 0.0)),
            "saturation": float(meta.get("saturation", 0.0)),
            "value": float(meta.get("value", 0.0)),
            "background": tuple(meta.get("background")) if meta.get("background") else None,
        }
        infos.append(info)
    if not infos:
        raise ValueError(f"No images in folder: {folder}")
    return infos


def normalize_tiles(tiles, size=None):
    """Bringt alle Tiles auf die gleiche Größe."""
    if not tiles:
        raise ValueError("Tile list is empty")

    if size is None:
        w = min(t.width for t in tiles)
        h = min(t.height for t in tiles)
        size = (w, h)

    return [t.resize(size, Image.LANCZOS) for t in tiles]


def build_raster(pattern_rows, tiles_F, tiles_E, shuffle_tiles=False):
    """
    pattern_rows: Liste von Strings, z.B.
        ["EFEFE",
         "FEFEF",
         ...]
    tiles_F: Liste von PIL-Images (Frauen)
    tiles_E: Liste von PIL-Images (Ergometer)
    """
    if not pattern_rows:
        raise ValueError("Pattern is empty")

    cols = len(pattern_rows[0])
    for row in pattern_rows:
        if len(row) != cols:
            raise ValueError("All pattern rows must have same length")
        if any(ch not in ("F", "E") for ch in row):
            raise ValueError("Pattern may only contain 'F' and 'E' characters")

    if not tiles_F:
        raise ValueError("No F tiles loaded")
    if not tiles_E:
        raise ValueError("No E tiles loaded")

    # Tiles normalisieren
    tiles_F = normalize_tiles(tiles_F)
    tiles_E = normalize_tiles(tiles_E, size=tiles_F[0].size)

    if shuffle_tiles:
        random.shuffle(tiles_F)
        random.shuffle(tiles_E)

    tile_w, tile_h = tiles_F[0].size
    rows = len(pattern_rows)
    cols = len(pattern_rows[0])

    canvas = Image.new("RGB", (cols * tile_w, rows * tile_h), "white")

    f_i = 0
    e_i = 0
    for r, row in enumerate(pattern_rows):
        for c, ch in enumerate(row):
            if ch == "F":
                tile = tiles_F[f_i % len(tiles_F)]
                f_i += 1
            else:
                tile = tiles_E[e_i % len(tiles_E)]
                e_i += 1
            canvas.paste(tile, (c * tile_w, r * tile_h))

    return canvas


def build_raster_multi(pattern_rows, tile_sets, shuffle_tiles=False):
    if not pattern_rows:
        raise ValueError("Pattern is empty")
    if not tile_sets:
        raise ValueError("Kein Bildtyp angegeben")

    cols = len(pattern_rows[0])
    for row in pattern_rows:
        if len(row) != cols:
            raise ValueError("All pattern rows must have same length")

    pattern_symbols = {ch for row in pattern_rows for ch in row if ch}
    for symbol in pattern_symbols:
        if symbol not in tile_sets:
            raise ValueError(f"Symbol {symbol} besitzt keinen Bildtyp")

    symbols_order = list(tile_sets.keys())
    first_symbol = symbols_order[0]
    normalized_sets = {}
    normalized_sets[first_symbol] = normalize_tiles(tile_sets[first_symbol])
    tile_w, tile_h = normalized_sets[first_symbol][0].size

    for symbol in symbols_order[1:]:
        normalized_sets[symbol] = normalize_tiles(tile_sets[symbol], size=(tile_w, tile_h))

    if shuffle_tiles:
        for tiles in normalized_sets.values():
            random.shuffle(tiles)

    rows = len(pattern_rows)
    canvas = Image.new("RGB", (cols * tile_w, rows * tile_h), "white")
    counters = {symbol: 0 for symbol in normalized_sets}

    for y, row in enumerate(pattern_rows):
        for x, ch in enumerate(row):
            if ch not in normalized_sets:
                continue
            tiles = normalized_sets[ch]
            idx = counters[ch] % len(tiles)
            counters[ch] += 1
            canvas.paste(tiles[idx], (x * tile_w, y * tile_h))

    return canvas


# --------------------------------------------------------
# GUI-Basisklasse
# --------------------------------------------------------

class RasterAppBase:
    def __init__(self):
        self.drop_paths = []
        self.pattern_text_default = "ABAB\nBABA\nABAB\nBABA"
        self.shuffle_var = None
        self.category_var = None
        self.preview_image = None
        self.pattern_box = None
        self.preview_label = None
        self.log_text = None
        self.status_var = None
        self.palette_folder_var = None
        self.palette_type_var = None
        self.palette_preview_label = None
        self.palette_preview_image = None
        self.palette_columns_var = None
        self.mosaic_image_var = None
        self.mosaic_palette_var = None
        self.mosaic_resolution_var = None
        self.mosaic_resolution_box = None
        self.mosaic_resolution_options = []
        self.gallery_root = os.path.abspath(APP_ROOT)
        self.gallery_tree = None
        self.gallery_tree_root_id = None
        self.gallery_preview_label = None
        self.gallery_preview_image = None
        self.gallery_current_dir = self.gallery_root
        self.gallery_files = []
        self.gallery_tile_size_var = None
        self.gallery_tile_mode_var = None
        self.gallery_tile_scale = None
        self.gallery_tile_label = None
        self.gallery_tile_canvas = None
        self.gallery_tile_scroll = None
        self.gallery_tile_images = {}
        self.gallery_tile_tag_map = {}
        self.gallery_tile_rects = {}
        self.gallery_selected_file = None
        self.gallery_selected_files = []
        self.gallery_selection_anchor = None
        self.gallery_tile_render_pending = False
        self._gallery_tile_render_info = None
        self._gallery_render_token = 0
        self._gallery_columns = 1
        self._gallery_dir_scan_cache = {}
        self.thumbnail_placeholder_images = {}
        self.thumbnail_pending = set()
        self.thumbnail_stop = threading.Event()
        self.thumbnail_queue = queue.Queue()
        self.thumbnail_results = queue.Queue()
        self.thumbnail_worker = None
        self.gallery_loading_var = None
        self.settings_path = SETTINGS_FILE
        self.user_settings = self._load_user_settings()
        self.last_dir = self.user_settings.get("last_dir", os.getcwd())
        self.default_palette_folder = os.path.abspath(DEFAULT_PALETTE_FOLDER)
        self.default_mosaic_palette = os.path.abspath(DEFAULT_MOSAIC_PALETTE)
        self.default_mosaic_image = DEFAULT_MOSAIC_IMAGE
        self.tile_type_count_var = None
        self.tile_type_path_vars = {}
        self.tile_type_frames = {}
        self.pattern_preset_var = None
        self._preview_base_image = None
        self._preview_photo = None
        self._palette_preview_base = None
        self._palette_preview_photo = None
        self._gallery_preview_base = None
        self._gallery_preview_photo = None
        self.current_preview_path = None
        self.progress_label = None
        self.progress_bar = None
        self.progress_active = False
        self.main_paned = None
        self.left_paned = None
        self.right_paned = None
        self.gallery_paned = None
        self.gallery_lower_paned = None
        self.paned_meta = {}
        self.thumbnail_cache_dir = os.path.join(APP_ROOT, ".cache", "thumbnails")
        self._start_thumbnail_worker()
        self.harmony_mode_var = None
        self.harmony_base_color_var = None
        self.harmony_tint_mode_var = None
        self.harmony_intensity_var = None
        self.harmony_contrast_var = None
        self.harmony_texture_var = None
        self.harmony_preserve_fg_var = None
        self._tile_set_paths = {}
        self._tile_infos = {}

    def _load_user_settings(self):
        if os.path.isfile(self.settings_path):
            try:
                with open(self.settings_path, "r", encoding="utf-8") as fh:
                    return json.load(fh)
            except Exception:
                return {}
        return {}

    def _save_user_settings(self):
        try:
            with open(self.settings_path, "w", encoding="utf-8") as fh:
                json.dump(self.user_settings, fh, indent=2)
        except Exception:
            pass

    def _get_setting(self, key, default=None):
        return self.user_settings.get(key, default)

    def _set_setting(self, key, value):
        self.user_settings[key] = value
        self._save_user_settings()

    def _reset_setting(self, key):
        if key in self.user_settings:
            del self.user_settings[key]
            self._save_user_settings()

    def _remember_dir(self, path):
        if path:
            self.last_dir = path
            self._set_setting("last_dir", self.last_dir)

    def _attach_tooltip(self, widget, text):
        if not widget or not text:
            return
        ToolTip(widget, text)

    def _reset_palette_folder_default(self):
        if self.palette_folder_var:
            self.palette_folder_var.set(self.default_palette_folder)
            self._set_setting("palette_folder", self.default_palette_folder)
            self._remember_dir(self.default_palette_folder)

    def _reset_mosaic_image_default(self):
        if self.mosaic_image_var is not None:
            self.mosaic_image_var.set(self.default_mosaic_image)
            self._set_setting("mosaic_image", self.default_mosaic_image)
            self._update_mosaic_resolution_options()

    def _reset_mosaic_palette_default(self):
        if self.mosaic_palette_var:
            self.mosaic_palette_var.set(self.default_mosaic_palette)
            self._set_setting("mosaic_palette", self.default_mosaic_palette)
            self._remember_dir(self.default_mosaic_palette)
            self._update_mosaic_resolution_options()

    def _register_panedwindow(self, paned, key, orient="horizontal", default_ratio=0.5):
        if not paned:
            return
        self.paned_meta[key] = (paned, orient, default_ratio)
        paned.bind("<<PanedwindowMoved>>", lambda _e, k=key: self._store_paned_position(k))
        self.after(100, lambda k=key: self._restore_paned_position(k))

    def _store_paned_position(self, key):
        info = self.paned_meta.get(key)
        if not info:
            return
        paned, orient, _default = info
        try:
            pos = paned.sashpos(0)
        except tk.TclError:
            return
        total = paned.winfo_width() if orient == "horizontal" else paned.winfo_height()
        if total <= 0:
            return
        ratio = max(0.05, min(0.95, pos / total))
        self._set_setting(f"pane_{key}", ratio)

    def _restore_paned_position(self, key):
        info = self.paned_meta.get(key)
        if not info:
            return
        paned, orient, default_ratio = info
        ratio = self._get_setting(f"pane_{key}", default_ratio)
        try:
            ratio = float(ratio)
        except (TypeError, ValueError):
            ratio = default_ratio
        ratio = max(0.05, min(0.95, ratio))
        total = paned.winfo_width() if orient == "horizontal" else paned.winfo_height()
        if total <= 0:
            paned.after(100, lambda k=key: self._restore_paned_position(k))
            return
        pos = int(total * ratio)
        try:
            paned.sashpos(0, pos)
        except tk.TclError:
            pass

    def _start_thumbnail_worker(self):
        ensure_folder(self.thumbnail_cache_dir)
        if self.thumbnail_worker and self.thumbnail_worker.is_alive():
            return
        self.thumbnail_worker = threading.Thread(target=self._thumbnail_worker_loop, daemon=True)
        self.thumbnail_worker.start()
        self.after(200, self._process_thumbnail_results)

    def _thumbnail_cache_path(self, path, size):
        abs_path = os.path.abspath(path)
        digest = hashlib.md5(f"{abs_path}|{size}".encode("utf-8")).hexdigest()
        ensure_folder(self.thumbnail_cache_dir)
        return os.path.join(self.thumbnail_cache_dir, f"{digest}.png")

    def _generate_thumbnail_file(self, path, size):
        cache_path = self._thumbnail_cache_path(path, size)
        try:
            src_mtime = os.path.getmtime(path)
        except OSError:
            return
        try:
            cache_mtime = os.path.getmtime(cache_path)
            if cache_mtime >= src_mtime:
                return
        except OSError:
            pass
        try:
            with Image.open(path) as img:
                thumb = ImageOps.fit(img.convert("RGB"), (size, size), Image.LANCZOS)
                thumb.save(cache_path, format="PNG", optimize=True)
        except Exception:
            return

    def _purge_thumbnail_cache(self, path):
        sizes = {size for _, size in GALLERY_TILE_SIZE_PRESETS}
        for size in sizes:
            cache_path = self._thumbnail_cache_path(path, size)
            try:
                os.remove(cache_path)
            except OSError:
                pass

    def _thumbnail_worker_loop(self):
        while not self.thumbnail_stop.is_set():
            try:
                task = self.thumbnail_queue.get(timeout=0.5)
            except queue.Empty:
                continue
            if task is None:
                self.thumbnail_queue.task_done()
                break
            path, size = task
            self._generate_thumbnail_file(path, size)
            self.thumbnail_results.put((path, size))
            self.thumbnail_queue.task_done()

    def _queue_thumbnail_generation(self, path, size):
        abs_path = os.path.abspath(path)
        key = (abs_path, size)
        if key in self.thumbnail_pending:
            return
        self.thumbnail_pending.add(key)
        self._update_gallery_loading_status()
        self.thumbnail_queue.put(key)

    def _process_thumbnail_results(self):
        updated = False
        current_dir = os.path.abspath(self.gallery_current_dir) if self.gallery_current_dir else None
        try:
            while True:
                path, size = self.thumbnail_results.get_nowait()
                key = (os.path.abspath(path), size)
                self.thumbnail_pending.discard(key)
                if current_dir and os.path.abspath(os.path.dirname(path)) == current_dir:
                    updated = True
        except queue.Empty:
            pass
        if updated:
            self._request_gallery_tile_render()
        self._update_gallery_loading_status()
        if not self.thumbnail_stop.is_set():
            self.after(200, self._process_thumbnail_results)


    def _store_all_panes(self):
        for key in list(self.paned_meta.keys()):
            self._store_paned_position(key)

    def _on_close(self):
        self._store_all_panes()
        self._save_user_settings()
        self.thumbnail_stop.set()
        if self.thumbnail_queue:
            try:
                self.thumbnail_queue.put_nowait(None)
            except Exception:
                pass
        if self.thumbnail_worker:
            self.thumbnail_worker.join(timeout=1.5)
        try:
            self.destroy()
        except Exception:
            pass

    def _default_tile_path(self, symbol):
        return self._get_setting(f"type_{symbol}_path", DEFAULT_TYPE_PATHS.get(symbol, os.path.join(APP_ROOT, symbol)))

    def _browse_tile_type(self, symbol):
        var = self.tile_type_path_vars[symbol]
        initial = var.get() or self.last_dir
        folder = filedialog.askdirectory(title=f"Ordner für Typ {symbol}", initialdir=initial or os.getcwd())
        if folder:
            var.set(folder)
            self._set_setting(f"type_{symbol}_path", folder)
            self._remember_dir(folder)

    def _reset_tile_type_default(self, symbol):
        default = DEFAULT_TYPE_PATHS.get(symbol, os.path.join(APP_ROOT, symbol))
        self.tile_type_path_vars[symbol].set(default)
        self._set_setting(f"type_{symbol}_path", default)

    def _on_tile_type_count_change(self, *_args):
        if not self.tile_type_count_var:
            return
        try:
            count = int(self.tile_type_count_var.get())
        except (TypeError, ValueError):
            count = 1
        count = max(1, min(len(TYPE_SYMBOLS), count))
        self.tile_type_count_var.set(count)
        self._set_setting("tile_type_count", count)
        self._update_tile_type_visibility()

    def _update_tile_type_visibility(self):
        count = int(self.tile_type_count_var.get()) if self.tile_type_count_var else 1
        for idx, symbol in enumerate(TYPE_SYMBOLS):
            frame = self.tile_type_frames.get(symbol)
            if not frame:
                continue
            if idx < count:
                frame.pack(fill="x", pady=2)
            else:
                frame.pack_forget()

    def _symbols_in_pattern(self, pattern_text):
        return sorted({ch for ch in pattern_text if ch in TYPE_SYMBOLS})

    def _apply_pattern_preset(self):
        if not (self.pattern_preset_var and self.pattern_box):
            return
        name = self.pattern_preset_var.get()
        for preset_name, pattern_text in RASTER_PATTERN_PRESETS:
            if preset_name == name:
                text = pattern_text.strip("\n")
                self.pattern_box.delete("1.0", "end")
                self.pattern_box.insert("1.0", text + "\n")
                needed_symbols = self._symbols_in_pattern(text)
                if needed_symbols and self.tile_type_count_var:
                    required = max(TYPE_SYMBOLS.index(sym) + 1 for sym in needed_symbols)
                    if self.tile_type_count_var.get() < required:
                        self.tile_type_count_var.set(required)
                        self._on_tile_type_count_change()
                return

    def _build_raster_section(self, parent):
        info_frame = ttk.LabelFrame(parent, text="Bildtypen (max 5)")
        info_frame.pack(fill="x", pady=(0, 8))

        if not self.tile_type_path_vars:
            self.tile_type_path_vars = {}
        if not self.tile_type_frames:
            self.tile_type_frames = {}

        count_row = ttk.Frame(info_frame)
        count_row.pack(fill="x", pady=2)
        ttk.Label(count_row, text="Anzahl Typen:").pack(side="left")
        default_count = int(self._get_setting("tile_type_count", 2))
        self.tile_type_count_var = tk.IntVar(value=default_count)
        count_spin = tk.Spinbox(
            count_row,
            from_=1,
            to=len(TYPE_SYMBOLS),
            textvariable=self.tile_type_count_var,
            width=5,
            command=self._on_tile_type_count_change
        )
        count_spin.pack(side="left", padx=4)

        for symbol in TYPE_SYMBOLS:
            frame = ttk.Frame(info_frame)
            self.tile_type_frames[symbol] = frame
            path_var = tk.StringVar(value=self._default_tile_path(symbol))
            self.tile_type_path_vars[symbol] = path_var
            ttk.Label(frame, text=f"Typ {symbol}:").pack(side="left")
            ttk.Entry(frame, textvariable=path_var).pack(side="left", fill="x", expand=True, padx=4)
            ttk.Button(frame, text="…", width=3, command=lambda s=symbol: self._browse_tile_type(s)).pack(side="left")
            ttk.Button(frame, text="Standard", command=lambda s=symbol: self._reset_tile_type_default(s)).pack(side="left", padx=(4, 0))
            path_var.trace_add("write", lambda *_args, s=symbol, v=path_var: self._set_setting(f"type_{s}_path", v.get()))

        self._on_tile_type_count_change()

        preset_row = ttk.Frame(parent)
        preset_row.pack(fill="x", pady=(4, 2))
        ttk.Label(preset_row, text="Muster-Vorlage:").pack(side="left")
        self.pattern_preset_var = tk.StringVar()
        preset_values = [name for name, _ in RASTER_PATTERN_PRESETS]
        preset_combo = ttk.Combobox(preset_row, textvariable=self.pattern_preset_var, values=preset_values, state="readonly")
        preset_combo.pack(side="left", fill="x", expand=True, padx=4)
        ttk.Button(preset_row, text="Übernehmen", command=self._apply_pattern_preset).pack(side="left")
        if preset_values:
            self.pattern_preset_var.set(preset_values[0])

        ttk.Label(parent, text="Muster mit den Buchstaben A-E definieren. Leerzeichen werden ignoriert.").pack(anchor="w", pady=(4, 0))
        self.pattern_box = tk.Text(parent, height=10)
        self.pattern_box.insert("1.0", self.pattern_text_default)
        self.pattern_box.pack(fill="both", expand=True, pady=(0, 6))

        harmony_frame = ttk.LabelFrame(parent, text="Farbmodus & Harmonie")
        harmony_frame.pack(fill="x", pady=(4, 4))
        mode_labels = [label for label, _code in HARMONY_MODES]
        default_mode = self._get_setting("harmony_mode", mode_labels[0])
        if default_mode not in mode_labels:
            default_mode = mode_labels[0]
        self.harmony_mode_var = tk.StringVar(value=default_mode)
        harmony_combo = ttk.Combobox(
            harmony_frame,
            textvariable=self.harmony_mode_var,
            values=mode_labels,
            state="readonly"
        )
        harmony_combo.pack(fill="x", pady=(0, 4))
        self.harmony_mode_var.trace_add("write", self._on_harmony_mode_change)

        base_row = ttk.Frame(harmony_frame)
        base_row.pack(fill="x", pady=(0, 2))
        ttk.Label(base_row, text="Basisfarbe (#RRGGBB):").pack(side="left")
        default_color = self._get_setting("harmony_base_color", DEFAULT_HARMONY_BASE)
        normalized_color = self._normalize_hex_color(default_color)
        self.harmony_base_color_var = tk.StringVar(value=normalized_color)
        base_entry = ttk.Entry(base_row, textvariable=self.harmony_base_color_var, width=12)
        base_entry.pack(side="left", padx=(4, 4))
        ttk.Button(base_row, text="Wählen…", command=self._choose_harmony_base_color).pack(side="left")
        self.harmony_base_color_var.trace_add("write", self._on_harmony_base_color_change)
        info_label = tk.Label(base_row, text=" (?)", fg="#666666", cursor="question_arrow")
        info_label.pack(side="left")
        self._attach_tooltip(info_label, "Die Basisfarbe bestimmt den Ausgangston für die gewählte Harmonie. "
                                         "Komplementär-, Analog- usw. werden aus diesem Farbton berechnet; "
                                         "alle Hintergründe orientieren sich an diesen abgeleiteten Farben.")
        ttk.Label(harmony_frame, text="Intensität:").pack(anchor="w")
        intensity_labels = [label for label, _ in HARMONY_INTENSITY_PRESETS]
        default_intensity = self._get_setting("harmony_intensity", intensity_labels[1])
        if default_intensity not in intensity_labels:
            default_intensity = intensity_labels[1]
        self.harmony_intensity_var = tk.StringVar(value=default_intensity)
        ttk.Combobox(
            harmony_frame,
            textvariable=self.harmony_intensity_var,
            values=intensity_labels,
            state="readonly"
        ).pack(fill="x", pady=(0, 4))
        self.harmony_intensity_var.trace_add("write", self._on_harmony_intensity_change)
        ttk.Label(harmony_frame, text="Tönungsmodus:").pack(anchor="w", pady=(4, 0))
        tint_labels = [label for label, _code in HARMONY_TINT_OPTIONS]
        default_tint = self._get_setting("harmony_tint_mode", tint_labels[0])
        if default_tint not in tint_labels:
            default_tint = tint_labels[0]
        self.harmony_tint_mode_var = tk.StringVar(value=default_tint)
        tint_combo = ttk.Combobox(
            harmony_frame,
            textvariable=self.harmony_tint_mode_var,
            values=tint_labels,
            state="readonly"
        )
        tint_combo.pack(fill="x", pady=(0, 4))
        self.harmony_tint_mode_var.trace_add("write", self._on_harmony_tint_mode_change)
        ttk.Label(harmony_frame, text="Vordergrund-Ton:").pack(anchor="w")
        fg_labels = [label for label, _ in FOREGROUND_VARIANT_OPTIONS]
        default_fg = self._get_setting("harmony_fg_variant", fg_labels[0])
        if default_fg not in fg_labels:
            default_fg = fg_labels[0]
        self.harmony_fg_variant_var = tk.StringVar(value=default_fg)
        ttk.Combobox(
            harmony_frame,
            textvariable=self.harmony_fg_variant_var,
            values=fg_labels,
            state="readonly"
        ).pack(fill="x", pady=(0, 4))
        self.harmony_fg_variant_var.trace_add("write", self._on_harmony_fg_variant_change)
        self.harmony_preserve_fg_var = tk.BooleanVar(value=bool(int(self._get_setting("harmony_preserve_fg", 1))))
        ttk.Checkbutton(
            harmony_frame,
            text="Vordergrundfarben beibehalten",
            variable=self.harmony_preserve_fg_var,
            command=self._on_harmony_preserve_toggle
        ).pack(anchor="w")
        self.harmony_contrast_var = tk.BooleanVar(value=bool(int(self._get_setting("harmony_contrast", 1))))
        ttk.Checkbutton(
            harmony_frame,
            text="Kontrast verstärken",
            variable=self.harmony_contrast_var,
            command=self._on_harmony_contrast_toggle
        ).pack(anchor="w")
        self.harmony_texture_var = tk.BooleanVar(value=bool(int(self._get_setting("harmony_texture", 0))))
        ttk.Checkbutton(
            harmony_frame,
            text="Leichte Textur hinzufügen",
            variable=self.harmony_texture_var,
            command=self._on_harmony_texture_toggle
        ).pack(anchor="w")

    def _gather_tile_sets(self):
        if not self.tile_type_count_var:
            raise ValueError("Keine Bildtypen definiert")
        count = int(self.tile_type_count_var.get())
        symbols = TYPE_SYMBOLS[:count]
        tile_sets = {}
        self._tile_set_paths = {}
        self._tile_infos = {}
        use_harmony = self._get_harmony_mode_code() != "none"
        for symbol in symbols:
            var = self.tile_type_path_vars.get(symbol)
            path = var.get().strip() if var else ""
            if not path:
                raise ValueError(f"Kein Ordner für Typ {symbol}")
            self._tile_set_paths[symbol] = path
            if use_harmony:
                infos = load_tile_infos(path)
                tile_sets[symbol] = [info["image"] for info in infos]
                self._tile_infos[symbol] = infos
            else:
                tile_sets[symbol] = load_tiles(path)
        return self._apply_harmony_mode(tile_sets)

    def _apply_harmony_mode(self, tile_sets):
        if not tile_sets:
            return tile_sets
        mode = self._get_harmony_mode_code()
        if mode == "none":
            return tile_sets
        base_rgb = self._get_harmony_base_rgb()
        r, g, b = (val / 255.0 for val in base_rgb)
        base_hue, base_sat, base_val = colorsys.rgb_to_hsv(r, g, b)
        base_hue *= 360.0
        target_sat = base_sat if base_sat > 0.05 else 0.65
        target_val = base_val if base_val > 0.05 else 0.9
        sat_factor, val_factor = self._get_harmony_intensity_factors()
        target_sat = max(0.05, min(1.0, target_sat * sat_factor))
        target_val = max(0.05, min(1.0, target_val * val_factor))
        symbols = list(tile_sets.keys())
        hues = self._resolve_harmony_hues(mode, base_hue, len(symbols))
        for symbol, target_hue in zip(symbols, hues):
            infos = self._tile_infos.get(symbol)
            if not infos:
                path = self._tile_set_paths.get(symbol)
                if path:
                    try:
                        infos = load_tile_infos(path)
                    except Exception:
                        infos = None
            if not infos:
                continue
            adjusted = []
            target_rgb = self._hsv_to_rgb_tuple(target_hue / 360.0, target_sat, target_val)
            for info in infos:
                hue_val = info.get("hue", 0.0)
                hue_diff = self._hue_distance(hue_val, target_hue)
                if hue_diff <= HARMONY_HUE_TOLERANCE:
                    adjusted.append(info["image"])
                else:
                    tinted = self._tint_tile_harmony(info, target_rgb)
                    adjusted.append(tinted)
            if adjusted:
                tile_sets[symbol] = adjusted
        return tile_sets

    def _get_harmony_mode_code(self):
        if not self.harmony_mode_var:
            return "none"
        label = self.harmony_mode_var.get()
        for display, code in HARMONY_MODES:
            if label == display or label == code:
                return code
        return "none"

    def _get_harmony_tint_mode(self):
        if not self.harmony_tint_mode_var:
            return "full"
        label = self.harmony_tint_mode_var.get()
        for display, code in HARMONY_TINT_OPTIONS:
            if label == display or label == code:
                return code
        return "full"

    def _get_harmony_intensity_factors(self):
        label = self.harmony_intensity_var.get() if self.harmony_intensity_var else HARMONY_INTENSITY_PRESETS[1][0]
        for display, factors in HARMONY_INTENSITY_PRESETS:
            if display == label:
                return factors
        return HARMONY_INTENSITY_PRESETS[1][1]

    def _harmony_contrast_enabled(self):
        return bool(self.harmony_contrast_var.get()) if self.harmony_contrast_var else False

    def _harmony_texture_enabled(self):
        return bool(self.harmony_texture_var.get()) if self.harmony_texture_var else False

    def _preserve_fg_colors(self):
        if not self.harmony_preserve_fg_var:
            return True
        return bool(self.harmony_preserve_fg_var.get())

    def _get_foreground_variant_params(self):
        label = self.harmony_fg_variant_var.get() if self.harmony_fg_variant_var else FOREGROUND_VARIANT_OPTIONS[0][0]
        for display, params in FOREGROUND_VARIANT_OPTIONS:
            if display == label:
                return params
        return FOREGROUND_VARIANT_OPTIONS[0][1]

    def _get_harmony_base_rgb(self):
        hex_color = self._normalize_hex_color(
            self.harmony_base_color_var.get() if self.harmony_base_color_var else DEFAULT_HARMONY_BASE
        )
        return tuple(int(hex_color[i:i + 2], 16) for i in (1, 3, 5))

    def _normalize_hex_color(self, value):
        raw = (value or "").strip()
        if not raw:
            return DEFAULT_HARMONY_BASE
        if not raw.startswith("#"):
            raw = f"#{raw}"
        if len(raw) != 7:
            return DEFAULT_HARMONY_BASE
        try:
            int(raw[1:], 16)
        except ValueError:
            return DEFAULT_HARMONY_BASE
        return raw.upper()

    def _choose_harmony_base_color(self):
        current = self._normalize_hex_color(
            self.harmony_base_color_var.get() if self.harmony_base_color_var else DEFAULT_HARMONY_BASE
        )
        color = colorchooser.askcolor(color=current, title="Basisfarbe wählen")
        if color and color[1] and self.harmony_base_color_var:
            self.harmony_base_color_var.set(color[1])

    def _on_harmony_base_color_change(self, *_args):
        if not self.harmony_base_color_var:
            return
        normalized = self._normalize_hex_color(self.harmony_base_color_var.get())
        if self.harmony_base_color_var.get() != normalized:
            self.harmony_base_color_var.set(normalized)
            return
        self._set_setting("harmony_base_color", normalized)

    def _on_harmony_mode_change(self, *_args):
        if not self.harmony_mode_var:
            return
        self._set_setting("harmony_mode", self.harmony_mode_var.get())
        self._request_gallery_tile_render(force=True)

    def _on_harmony_tint_mode_change(self, *_args):
        if not self.harmony_tint_mode_var:
            return
        self._set_setting("harmony_tint_mode", self.harmony_tint_mode_var.get())
        self._request_gallery_tile_render(force=True)

    def _on_harmony_fg_variant_change(self, *_args):
        if not self.harmony_fg_variant_var:
            return
        self._set_setting("harmony_fg_variant", self.harmony_fg_variant_var.get())
        self._request_gallery_tile_render(force=True)

    def _on_harmony_intensity_change(self, *_args):
        if not self.harmony_intensity_var:
            return
        self._set_setting("harmony_intensity", self.harmony_intensity_var.get())
        self._request_gallery_tile_render(force=True)

    def _on_harmony_preserve_toggle(self, *_args):
        if not self.harmony_preserve_fg_var:
            return
        self._set_setting("harmony_preserve_fg", 1 if self.harmony_preserve_fg_var.get() else 0)
        self._request_gallery_tile_render(force=True)

    def _on_harmony_contrast_toggle(self, *_args):
        if not self.harmony_contrast_var:
            return
        self._set_setting("harmony_contrast", 1 if self.harmony_contrast_var.get() else 0)
        self._request_gallery_tile_render(force=True)

    def _on_harmony_texture_toggle(self, *_args):
        if not self.harmony_texture_var:
            return
        self._set_setting("harmony_texture", 1 if self.harmony_texture_var.get() else 0)
        self._request_gallery_tile_render(force=True)

    def _resolve_harmony_hues(self, mode, base_hue, count):
        if count <= 0:
            return []
        if mode == "analogous":
            step = 30.0
            start = -((count - 1) / 2.0) * step
            offsets = [start + i * step for i in range(count)]
        elif mode == "monochrome":
            offsets = [0.0] * count
        elif mode == "triadic":
            base_offsets = [0.0, 120.0, 240.0]
            offsets = [base_offsets[i % 3] + 30.0 * (i // 3) for i in range(count)]
        elif mode == "split_complementary":
            base_offsets = [0.0, 150.0, -150.0]
            offsets = [base_offsets[i % 3] + 30.0 * (i // 3) for i in range(count)]
        elif mode == "complementary":
            base_offsets = [0.0, 180.0]
            offsets = [base_offsets[i % 2] + 45.0 * (i // 2) for i in range(count)]
        else:
            step = 360.0 / max(1, count)
            offsets = [i * step for i in range(count)]
        return [((base_hue + offset) % 360.0) for offset in offsets[:count]]

    def _hue_distance(self, h1, h2):
        diff = abs((h1 - h2) % 360.0)
        return diff if diff <= 180.0 else 360.0 - diff

    def _hsv_to_rgb_tuple(self, h, s, v):
        r, g, b = colorsys.hsv_to_rgb(h % 1.0, max(0.0, min(1.0, s)), max(0.0, min(1.0, v)))
        return (int(round(r * 255)), int(round(g * 255)), int(round(b * 255)))

    def _tint_tile_harmony(self, info, target_rgb):
        base = info["image"].convert("RGB")
        mode = self._get_harmony_tint_mode()
        bg_color = info.get("background") or _estimate_tile_background_color(base)
        bg_mask = None
        if mode == "background":
            bg_mask = _create_background_mask(base, bg_color, tolerance=40)
            tinted_bg = tint_image_to_color(base, target_rgb, blend_factor=0.25)
            result = Image.composite(tinted_bg, base, bg_mask) if bg_mask else tinted_bg
        else:
            result = tint_image_to_color(base, target_rgb, blend_factor=0.45)
            if self._preserve_fg_colors():
                bg_mask = _create_background_mask(base, bg_color, tolerance=45)
                if bg_mask:
                    fg_mask = ImageChops.invert(bg_mask)
                    result = Image.composite(result, base, fg_mask)
        result, fg_mask = self._apply_harmony_contrast_layers(result, base, bg_mask)
        result = self._apply_foreground_variant(result, fg_mask)
        if self._harmony_texture_enabled():
            result = self._apply_texture_overlay(result)
        return result

    def _apply_harmony_contrast_layers(self, tinted, original, bg_mask):
        fg_mask = None
        if bg_mask:
            fg_mask = ImageChops.invert(bg_mask.convert("L"))
        if not self._harmony_contrast_enabled():
            return tinted, fg_mask
        if bg_mask is None:
            enhanced = ImageEnhance.Contrast(tinted).enhance(1.05)
            enhanced = ImageEnhance.Brightness(enhanced).enhance(1.05)
            return enhanced, fg_mask
        if bg_mask.mode != "L":
            bg_mask = bg_mask.convert("L")
        fg_mask = ImageChops.invert(bg_mask)
        background_layer = ImageEnhance.Brightness(tinted).enhance(1.08)
        foreground_layer = ImageEnhance.Brightness(tinted).enhance(1.02)
        foreground_layer = ImageEnhance.Contrast(foreground_layer).enhance(1.03)
        combined = Image.composite(background_layer, tinted, bg_mask)
        combined = Image.composite(foreground_layer, combined, fg_mask)
        combined = ImageEnhance.Color(combined).enhance(1.08)
        return combined, fg_mask

    def _apply_texture_overlay(self, image):
        if image.mode != "RGB":
            base = image.convert("RGB")
        else:
            base = image
        noise = Image.effect_noise(base.size, 32).convert("L")
        noise = ImageOps.autocontrast(noise)
        noise = noise.point(lambda v: int(128 + (v - 128) * 0.35))
        grain = Image.merge("RGB", (noise, noise, noise))
        overlay = ImageChops.multiply(base, grain)
        return Image.blend(base, overlay, 0.12)

    def _apply_foreground_variant(self, image, fg_mask):
        params = self._get_foreground_variant_params()
        if not params:
            return image
        img = image
        mask = fg_mask
        if "brightness" in params and params["brightness"] != 1.0:
            brightened = ImageEnhance.Brightness(img).enhance(params["brightness"])
            img = Image.composite(brightened, img, mask) if mask else brightened
        if "overlay" in params:
            overlay = Image.new("RGB", img.size, params["overlay"])
            alpha = params.get("alpha", 0.2)
            blended = Image.blend(img, overlay, alpha)
            img = Image.composite(blended, img, mask) if mask else blended
        return img

    def _render_image_to_label(self, pil_image, label, photo_attr):
        if pil_image is None or label is None:
            return
        width = label.winfo_width()
        height = label.winfo_height()
        if width <= 1 or height <= 1:
            label.after(50, lambda: self._render_image_to_label(pil_image, label, photo_attr))
            return
        scale = min(width / pil_image.width, height / pil_image.height)
        if scale <= 0:
            scale = 1
        new_size = (max(1, int(pil_image.width * scale)), max(1, int(pil_image.height * scale)))
        show_img = pil_image.resize(new_size, Image.LANCZOS)
        photo = ImageTk.PhotoImage(show_img)
        setattr(self, photo_attr, photo)
        label.config(image=photo)

    def _render_preview_label(self, _event=None):
        self._render_image_to_label(self._preview_base_image, self.preview_label, "_preview_photo")

    def _render_palette_preview_label(self, _event=None):
        self._render_image_to_label(self._palette_preview_base, self.palette_preview_label, "_palette_preview_photo")

    def _render_gallery_preview_label(self, _event=None):
        self._render_image_to_label(self._gallery_preview_base, self.gallery_preview_label, "_gallery_preview_photo")

    def _is_hidden_name(self, name):
        return name.startswith(".")

    def _dir_contains_images(self, path):
        path = os.path.abspath(path)
        cached = self._gallery_dir_scan_cache.get(path)
        if cached is not None:
            return cached
        if not os.path.isdir(path):
            self._gallery_dir_scan_cache[path] = False
            return False
        result = False
        try:
            entries = os.listdir(path)
        except OSError:
            entries = []
        for entry in entries:
            if self._is_hidden_name(entry):
                continue
            full = os.path.join(path, entry)
            if os.path.islink(full):
                continue
            if os.path.isfile(full) and entry.lower().endswith((".png", ".jpg", ".jpeg")):
                result = True
                break
            if os.path.isdir(full) and self._dir_contains_images(full):
                result = True
                break
        self._gallery_dir_scan_cache[path] = result
        return result

    def _has_visible_subdirs(self, path):
        try:
            entries = os.listdir(path)
        except OSError:
            return False
        for entry in entries:
            if self._is_hidden_name(entry):
                continue
            full = os.path.join(path, entry)
            if not os.path.isdir(full) or os.path.islink(full):
                continue
            if self._dir_contains_images(full):
                return True
        return False

    def _gallery_size_description(self, idx):
        idx = max(0, min(len(GALLERY_TILE_SIZE_PRESETS) - 1, idx))
        name, size = GALLERY_TILE_SIZE_PRESETS[idx]
        return f"{name} ({size} px)"

    def _resolve_gallery_tile_mode(self, saved_mode, saved_size):
        if 0 <= saved_mode < len(GALLERY_TILE_SIZE_PRESETS):
            return saved_mode
        if saved_size <= 0:
            return 2
        best_idx = 0
        best_diff = float("inf")
        for idx, (_label, size) in enumerate(GALLERY_TILE_SIZE_PRESETS):
            diff = abs(size - saved_size)
            if diff < best_diff:
                best_diff = diff
                best_idx = idx
        return best_idx

    def _on_gallery_tile_size_change(self, value):
        if not (self.gallery_tile_size_var and self.gallery_tile_mode_var):
            return
        try:
            idx = int(round(float(value)))
        except (TypeError, ValueError):
            return
        idx = max(0, min(len(GALLERY_TILE_SIZE_PRESETS) - 1, idx))
        if self.gallery_tile_mode_var.get() == idx:
            if self.gallery_tile_label:
                self.gallery_tile_label.config(text=self._gallery_size_description(idx))
        else:
            self.gallery_tile_mode_var.set(idx)
        size = GALLERY_TILE_SIZE_PRESETS[idx][1]
        if self.gallery_tile_size_var.get() != size:
            self.gallery_tile_size_var.set(size)
        self._set_setting("gallery_tile_size_mode", idx)
        self._set_setting("gallery_tile_size", size)
        if self.gallery_tile_label:
            self.gallery_tile_label.config(text=self._gallery_size_description(idx))
        self._request_gallery_tile_render(force=True)

    def _on_gallery_tile_canvas_configure(self, _event=None):
        self._request_gallery_tile_render()

    def _shorten_filename(self, name, max_len=18):
        if len(name) <= max_len:
            return name
        return name[: max_len - 1] + "…"

    def _get_placeholder_thumbnail(self, size):
        key = ("placeholder", size)
        if key in self.thumbnail_placeholder_images:
            return self.thumbnail_placeholder_images[key]
        img = Image.new("RGB", (size, size), color="#444444")
        photo = ImageTk.PhotoImage(img)
        self.thumbnail_placeholder_images[key] = photo
        return photo

    def _get_gallery_thumbnail(self, path, size):
        abs_path = os.path.abspath(path)
        key = (abs_path, size)
        cached = self.gallery_tile_images.get(key)
        if cached:
            return cached
        if not os.path.isfile(abs_path):
            self.gallery_tile_images.pop(key, None)
            return self._get_placeholder_thumbnail(size)
        cache_file = self._thumbnail_cache_path(abs_path, size)
        if os.path.isfile(cache_file):
            try:
                with Image.open(cache_file) as img:
                    photo = ImageTk.PhotoImage(img.copy())
                    self.gallery_tile_images[key] = photo
                    return photo
            except Exception:
                pass
        self._queue_thumbnail_generation(abs_path, size)
        photo = self._get_placeholder_thumbnail(size)
        self.gallery_tile_images[key] = photo
        return photo

    def _request_gallery_tile_render(self, force=False):
        if not self.gallery_tile_canvas:
            return
        if self.gallery_tile_render_pending and not force:
            return
        self.gallery_tile_render_pending = True
        delay = 0 if force else 100
        self.after(delay, self._render_gallery_tiles)

    def _update_gallery_loading_status(self):
        if not self.gallery_loading_var:
            return
        pending = len(self.thumbnail_pending)
        if pending <= 0:
            self.gallery_loading_var.set("")
        else:
            self.gallery_loading_var.set(f"Lädt {pending}…")

    def _render_gallery_tiles(self):
        if not self.gallery_tile_canvas:
            self.gallery_tile_render_pending = False
            return
        self.gallery_tile_render_pending = False
        canvas = self.gallery_tile_canvas
        width = canvas.winfo_width()
        if width <= 1:
            self.after(100, self._render_gallery_tiles)
            return
        token = self._gallery_render_token + 1
        self._gallery_render_token = token
        padding = 10
        label_space = 24
        size = self.gallery_tile_size_var.get() if self.gallery_tile_size_var else 128
        columns = max(1, (width - padding) // (size + padding))
        self._gallery_columns = columns
        canvas.delete("tile_item")
        self.gallery_tile_tag_map = {}
        self.gallery_tile_rects = {}
        self._gallery_tile_render_info = {
            "files": list(self.gallery_files),
            "columns": columns,
            "padding": padding,
            "label_space": label_space,
            "size": size,
            "width": width,
            "canvas": canvas,
        }
        self._render_gallery_tiles_batch(0, token)

    def _render_gallery_tiles_batch(self, start_idx, token, batch_size=60):
        if token != self._gallery_render_token:
            return
        info = self._gallery_tile_render_info
        if not info:
            return
        files = info["files"]
        total = len(files)
        if start_idx >= total:
            return
        columns = info["columns"]
        padding = info["padding"]
        label_space = info["label_space"]
        size = info["size"]
        canvas = info["canvas"]
        for offset, filename in enumerate(files[start_idx:start_idx + batch_size]):
            idx = start_idx + offset
            col = idx % columns
            row = idx // columns
            x = padding + col * (size + padding) + size / 2
            y = padding + row * (size + label_space + padding) + size / 2
            path = os.path.join(self.gallery_current_dir, filename)
            photo = self._get_gallery_thumbnail(path, size)
            tag = f"tile_{idx}"
            rect = canvas.create_rectangle(
                x - size / 2 - 4,
                y - size / 2 - 4,
                x + size / 2 + 4,
                y + size / 2 + 4,
                outline="#666666",
                width=1,
                tags=("tile_item", tag),
            )
            canvas.create_image(x, y, image=photo, tags=("tile_item", tag))
            canvas.create_text(
                x,
                y + size / 2 + (label_space / 2),
                text=self._shorten_filename(filename),
                tags=("tile_item", tag),
            )
            self.gallery_tile_tag_map[tag] = filename
            self.gallery_tile_rects[filename] = rect

        next_idx = start_idx + batch_size
        if next_idx < total:
            self.after(10, lambda idx=next_idx, tok=token: self._render_gallery_tiles_batch(idx, tok, batch_size))
        else:
            rows = math.ceil(total / columns) if columns else 0
            height = padding + rows * (size + label_space + padding)
            canvas.configure(scrollregion=(0, 0, info["width"], height))
            self._select_in_tiles(self.gallery_selected_files, self.gallery_selected_file)

    def _on_gallery_mousewheel(self, event):
        if not self.gallery_tile_canvas:
            return "break"
        if hasattr(event, "num") and event.num in (4, 5):
            delta = -3 if event.num == 4 else 3
        else:
            delta = -int(event.delta / 120) if event.delta else 0
        if delta != 0:
            self.gallery_tile_canvas.yview_scroll(delta, "units")
        return "break"

    def _selection_mode_from_event(self, event):
        state = getattr(event, "state", 0)
        shift = bool(state & 0x0001)
        ctrl = bool(state & (0x0004 | 0x0008))
        if shift and self.gallery_selection_anchor:
            return "range"
        if ctrl:
            return "toggle"
        return "replace"

    def _handle_gallery_navigation(self, event=None, rows=0, cols=0, absolute=None):
        mode = self._selection_mode_from_event(event) if event else "replace"
        self._move_gallery_selection(rows, cols, absolute, mode)
        return "break"

    def _handle_gallery_open(self, _event=None):
        if self.gallery_selected_file:
            self._open_gallery_image(self.gallery_selected_file)
        return "break"

    def _delete_selected_tiles(self, _event=None):
        selection = list(self.gallery_selected_files) or ([self.gallery_selected_file] if self.gallery_selected_file else [])
        if not selection:
            messagebox.showinfo("Löschen", "Keine Dateien ausgewählt.")
            return "break"
        if not self.gallery_current_dir or not os.path.isdir(self.gallery_current_dir):
            return "break"
        plural = len(selection) > 1
        names = "\n".join(selection[:10])
        if len(selection) > 10:
            names += "\n…"
        if not messagebox.askyesno(
            "Löschen bestätigen",
            f"Sollen {len(selection)} Datei(en) gelöscht werden?\n{names}"
        ):
            return "break"
        deleted = []
        errors = []
        for name in selection:
            path = os.path.join(self.gallery_current_dir, name)
            try:
                os.remove(path)
                self._purge_thumbnail_cache(path)
                deleted.append(name)
            except Exception as exc:
                errors.append(f"{name}: {exc}")
        if deleted:
            self.gallery_files = [name for name in self.gallery_files if name not in deleted]
            self.gallery_selected_files = []
            self.gallery_selected_file = None
            self.gallery_selection_anchor = None
            self._request_gallery_tile_render(force=True)
        if errors:
            messagebox.showerror("Fehler beim Löschen", "\n".join(errors))
        elif deleted:
            messagebox.showinfo("Gelöscht", f"{len(deleted)} Datei(en) gelöscht.")
            self._refresh_gallery(self.gallery_current_dir)
        return "break"

    def _move_gallery_selection(self, delta_rows=0, delta_cols=0, absolute=None, mode="replace"):
        if not self.gallery_files:
            return
        columns = max(1, self._gallery_columns or 1)
        total = len(self.gallery_files)
        if absolute == "start":
            target_idx = 0
        elif absolute == "end":
            target_idx = total - 1
        else:
            try:
                current_idx = self.gallery_files.index(self.gallery_selected_file)
            except ValueError:
                current_idx = 0
            max_rows = max(0, (total - 1) // columns)
            row = current_idx // columns
            col = current_idx % columns
            row = max(0, min(row + delta_rows, max_rows))
            col = max(0, min(col + delta_cols, columns - 1))
            target_idx = row * columns + col
            if target_idx >= total:
                target_idx = total - 1
        filename = self.gallery_files[target_idx]
        self._set_gallery_selection(filename, mode=mode if absolute is None else ("range" if mode == "range" else "replace"))
        if self.gallery_tile_canvas:
            self.gallery_tile_canvas.focus_set()

    def _filename_from_tile_event(self, event):
        if not self.gallery_tile_canvas:
            return None
        current = self.gallery_tile_canvas.find_withtag("current")
        if not current:
            return None
        tags = self.gallery_tile_canvas.gettags(current[0])
        for tag in tags:
            if tag in self.gallery_tile_tag_map:
                return self.gallery_tile_tag_map[tag]
        return None

    def _on_gallery_tile_click(self, event):
        filename = self._filename_from_tile_event(event)
        if filename:
            mode = self._selection_mode_from_event(event)
            self._set_gallery_selection(filename, source="tiles", mode=mode)
            if self.gallery_tile_canvas:
                self.gallery_tile_canvas.focus_set()

    def _on_gallery_tile_double(self, event):
        filename = self._filename_from_tile_event(event)
        if filename:
            self._set_gallery_selection(filename, source="tiles", mode="replace")
            self._open_gallery_image(filename)
            if self.gallery_tile_canvas:
                self.gallery_tile_canvas.focus_set()

    def _clear_gallery_preview(self):
        self.gallery_selected_file = None
        self.gallery_selected_files = []
        self.gallery_selection_anchor = None
        self._gallery_preview_base = None
        self._select_in_tiles(None)
        if self.gallery_preview_label:
            self.gallery_preview_label.config(image="", text="Keine Auswahl")

    def _update_gallery_preview_display(self, filename):
        path = os.path.join(self.gallery_current_dir, filename)
        display = self._load_image_for_preview(path, GALLERY_PREVIEW_MAX_DIMENSION)
        if display is None:
            messagebox.showerror("Galerie", "Bild konnte nicht geladen werden.")
            return None
        self._gallery_preview_base = display
        self._render_gallery_preview_label()
        if self.gallery_preview_label:
            self.gallery_preview_label.config(text=filename)
        self._set_last_gallery_image_path(path)
        return display
        return display

    def _open_gallery_image(self, filename):
        image = self._update_gallery_preview_display(filename)
        if image is not None:
            self._update_preview(image)
            path = os.path.join(self.gallery_current_dir, filename)
            self._set_last_preview_path(path)

    def _set_gallery_selection(self, filename, source=None, update_preview=True, mode="replace"):
        if not filename or filename not in self.gallery_files:
            return
        files = self.gallery_files
        selection = list(self.gallery_selected_files) if self.gallery_selected_files else []
        anchor = self.gallery_selection_anchor

        if mode == "toggle":
            if filename in selection and len(selection) > 1:
                selection = [name for name in selection if name != filename]
            elif filename in selection:
                selection = [filename]
            else:
                selection.append(filename)
                anchor = anchor or filename
        elif mode == "range" and anchor in files:
            start = files.index(anchor)
            end = files.index(filename)
            if start <= end:
                selection = files[start:end + 1]
            else:
                selection = files[end:start + 1]
        else:
            selection = [filename]
            anchor = filename

        ordered = []
        seen = set()
        for name in files:
            if name in selection and name not in seen:
                ordered.append(name)
                seen.add(name)
        if not ordered:
            ordered = [filename]

        self.gallery_selected_files = ordered
        self.gallery_selected_file = ordered[-1]
        self.gallery_selection_anchor = anchor or self.gallery_selected_file
        self._select_in_tiles(self.gallery_selected_files, self.gallery_selected_file)
        self._scroll_tile_into_view(self.gallery_selected_file)
        if update_preview:
            self._open_gallery_image(self.gallery_selected_file)

    def _select_in_tiles(self, filenames, primary=None):
        if not self.gallery_tile_rects:
            return
        selected = set(filenames or [])
        primary = primary or (filenames[-1] if filenames else None)
        for name, rect in self.gallery_tile_rects.items():
            if not self.gallery_tile_canvas:
                break
            if name == primary:
                self.gallery_tile_canvas.itemconfigure(rect, outline="#2b6cb0", width=3)
            elif name in selected:
                self.gallery_tile_canvas.itemconfigure(rect, outline="#4a90e2", width=2)
            else:
                self.gallery_tile_canvas.itemconfigure(rect, outline="#666666", width=1)

    def _scroll_tile_into_view(self, filename):
        if not self.gallery_tile_canvas or not filename:
            return
        rect = self.gallery_tile_rects.get(filename)
        if not rect:
            return
        bbox = self.gallery_tile_canvas.bbox(rect)
        if not bbox:
            return
        canvas = self.gallery_tile_canvas
        view_top = canvas.canvasy(0)
        view_bottom = view_top + canvas.winfo_height()
        tile_top, tile_bottom = bbox[1], bbox[3]
        if tile_top < view_top:
            total = canvas.bbox("all")
            total_height = total[3] if total else 1
            canvas.yview_moveto(max(0, (tile_top - 10) / max(1, total_height)))
        elif tile_bottom > view_bottom:
            total = canvas.bbox("all")
            total_height = total[3] if total else 1
            canvas.yview_moveto(max(0, min(1, (tile_bottom - canvas.winfo_height() + 10) / max(1, total_height))))

    def _start_progress(self, total, text=""):
        if not self.progress_bar:
            return
        self.progress_active = True
        self.progress_bar.configure(maximum=max(1, total), value=0)
        self.progress_label.config(text=text or "0/{}".format(max(1, total)))
        self.update_idletasks()

    def _update_progress(self, current, total):
        if not self.progress_bar:
            return
        self.progress_bar.configure(maximum=max(1, total))
        self.progress_bar["value"] = min(max(0, current), total)
        self.progress_label.config(text=f"{current}/{total}")
        self.update_idletasks()

    def _finish_progress(self):
        if not self.progress_bar:
            return
        self.progress_active = False
        self.progress_bar.configure(value=0, maximum=1)
        self.progress_label.config(text="Bereit")
        self.update_idletasks()

    def _normalize_paths(self, paths):
        """Normiert Rückgaben aus Datei-Dialogen (String oder Sequenz)."""
        if not paths:
            return []
        if isinstance(paths, str):
            tk_app = getattr(self, "tk", None)
            if tk_app is not None:
                paths = tk_app.splitlist(paths)
            else:
                paths = [paths]
        return [p for p in paths if p]

    def _add_import_paths(self, paths):
        """Fügt neue Pfade hinzu und liefert Anzahl neuer Einträge."""
        normalized = self._normalize_paths(paths)
        if not normalized:
            return 0
        self.drop_paths.extend(normalized)
        return len(normalized)

    def _open_file_picker(self):
        """Öffnet den benutzerdefinierten Datei-Picker und liefert Pfade."""
        files = pick_multiple_files(self, initialdir=self.last_dir)
        if files:
            self._remember_dir(os.path.dirname(files[0]))
        return files

    def _load_tiles(self):
        tiles_F = load_tiles("F")
        tiles_E = load_tiles("E")
        return tiles_F, tiles_E

    def _get_pattern_rows(self):
        if not self.pattern_box:
            return []
        pattern_text = self.pattern_box.get("1.0", "end").strip()
        if not pattern_text:
            return []
        rows = []
        for line in pattern_text.splitlines():
            cleaned = line.replace(" ", "").upper()
            if cleaned:
                rows.append(cleaned)
        return rows

    def _generate_images(self, pattern_rows, batch=False):
        shuffle = self.shuffle_var.get() if self.shuffle_var else False
        if batch:
            tiles_F, tiles_E, batches_F, batches_E, _total, converted_rows = self._prepare_batch(pattern_rows)
            paths, last_img, _ = generate_batch_rasters(
                converted_rows,
                tiles_F,
                tiles_E,
                shuffle_tiles=shuffle,
                log_cb=self.log_message
            )
            return paths, last_img
        tile_sets = self._gather_tile_sets()
        total = len(pattern_rows) * len(pattern_rows[0])
        self._start_progress(total, "Raster wird erstellt…")
        try:
            img = build_raster_multi(pattern_rows, tile_sets, shuffle_tiles=shuffle)
        finally:
            self._finish_progress()
        out_path = unique_output_path()
        img.save(out_path)
        return [out_path], img

    def _prepare_batch(self, pattern_rows):
        tile_sets = self._gather_tile_sets()
        if len(tile_sets) < 2:
            raise ValueError("Batch-Export benötigt mindestens zwei Typen (A und B).")
        active_symbols = [symbol for symbol in TYPE_SYMBOLS if symbol in tile_sets][:2]
        if len(active_symbols) < 2:
            raise ValueError("Bitte konfigurieren Sie die Typen A und B für den Batch-Export.")
        mapping = {active_symbols[0]: "F", active_symbols[1]: "E"}
        converted_rows = []
        for row in pattern_rows:
            converted_row = ""
            for ch in row:
                if ch not in mapping:
                    raise ValueError("Batch-Export unterstützt nur Muster mit Typ A/B.")
                converted_row += mapping[ch]
            converted_rows.append(converted_row)
        tiles_F = tile_sets[active_symbols[0]]
        tiles_E = tile_sets[active_symbols[1]]
        batches_F, batches_E = prepare_batches(converted_rows, tiles_F, tiles_E)
        total = len(batches_F) * len(batches_E)
        return tiles_F, tiles_E, batches_F, batches_E, total, converted_rows

    def _prepare_preview_image(self, img, limit=PREVIEW_MAX_DIMENSION):
        if img is None:
            return None
        try:
            img = ImageOps.exif_transpose(img)
        except Exception:
            pass
        limit = max(1, int(limit))
        width, height = img.size
        if max(width, height) <= limit:
            return img.copy()
        return ImageOps.contain(img, (limit, limit), Image.LANCZOS)

    def _load_image_for_preview(self, path, limit=PREVIEW_MAX_DIMENSION):
        try:
            limit = max(1, int(limit))
        except Exception:
            limit = PREVIEW_MAX_DIMENSION
        try:
            with Image.open(path) as img:
                img.draft("RGB", (limit, limit))
                img = ImageOps.exif_transpose(img)
                img.thumbnail((limit, limit), Image.LANCZOS)
                return img.convert("RGB")
        except Exception:
            return None

    def _update_preview_from_path(self, path, limit=PREVIEW_MAX_DIMENSION):
        if not path or not os.path.isfile(path):
            return False
        img = self._load_image_for_preview(path, limit)
        if img is None:
            return False
        self._update_preview(img)
        self._set_last_preview_path(path)
        return True

    def _update_preview(self, img):
        if img is None:
            return
        prepared = self._prepare_preview_image(img, PREVIEW_MAX_DIMENSION)
        if prepared is None:
            return
        self._preview_base_image = prepared
        self._render_preview_label()

    def _set_last_preview_path(self, path):
        if path and os.path.isfile(path):
            self._set_setting("last_preview_image", path)
            self.current_preview_path = path

    def _set_last_gallery_image_path(self, path):
        if path and os.path.isfile(path):
            self._set_setting("last_gallery_image", path)

    def set_status(self, text):
        if self.status_var:
            self.status_var.set(text)

    def _on_preview_double_click(self, _event=None):
        path = self.current_preview_path or self._get_setting("last_preview_image")
        if not path or not os.path.isfile(path):
            messagebox.showwarning("Vorschau", "Kein Bild zum Öffnen verfügbar.")
            return
        if not _open_file_in_viewer(path):
            messagebox.showwarning("Vorschau", "Bild konnte nicht geöffnet werden.")

    def log_message(self, message):
        print(message)
        if self.log_text:
            widget = self.log_text
            if isinstance(widget, tk.Text):
                widget.configure(state="normal")
                widget.delete("1.0", "end")
                widget.insert("end", message + "\n")
                widget.see("end")
                widget.configure(state="disabled")
            else:
                widget.configure(state="normal")
                widget.delete(0, "end")
                widget.insert(0, message)
                widget.configure(state="readonly")
        self.set_status(message)

    def _get_palette_size_value(self):
        if not self.palette_type_var:
            return 64
        label = self.palette_type_var.get()
        for name, size in PALETTE_PRESETS:
            if name == label:
                return size
        try:
            return int(label)
        except Exception:
            return 64

    def _select_palette_folder(self):
        initial = self.palette_folder_var.get() if self.palette_folder_var else self.last_dir
        folder = filedialog.askdirectory(title="Ordner mit Kacheln auswählen", initialdir=initial or os.getcwd())
        if folder and self.palette_folder_var:
            self.palette_folder_var.set(folder)
            self._set_setting("palette_folder", folder)
            self._remember_dir(folder)

    def _generate_palette(self):
        if not self.palette_folder_var:
            messagebox.showerror("Kein Ordner", "Bitte zuerst einen Ordner auswählen.")
            return
        folder = self.palette_folder_var.get().strip()
        if not folder:
            messagebox.showwarning("Kein Ordner", "Bitte zuerst einen Ordner auswählen.")
            return
        palette_size = self._get_palette_size_value()
        target_total = _resolve_palette_size(palette_size, self.palette_type_var.get())
        if target_total <= 0:
            try:
                target_total = max(1, len(os.listdir(folder)))
            except OSError:
                target_total = 1
        self._start_progress(max(1, target_total), "Palette wird erzeugt…")
        try:
            result = generate_palette_tile_set(
                folder,
                palette_size,
                label=self.palette_type_var.get(),
                progress_cb=lambda done, total: self._update_progress(done, total)
            )
        except Exception as e:
            self._finish_progress()
            messagebox.showerror("Fehler beim Spektrum", str(e))
            return
        self._finish_progress()

        self._update_palette_preview(result["palette_image"])
        summary = (
            f"Palette mit {result['count']} Kacheln gespeichert in: {result['directory']}\n"
            f"Metadata: {result['metadata']}\n"
            f"Preview: {result.get('preview_path')}"
        )
        self.log_message(summary)
        messagebox.showinfo("Palette erzeugt", summary)
        self._refresh_gallery(result.get("preview_path"))
        self._set_last_preview_path(result.get("preview_path"))

    def _update_palette_preview(self, img):
        if img is None:
            return
        self._palette_preview_base = img.copy()
        self._render_palette_preview_label()

    def _restore_last_preview_images(self):
        main_path = self._get_setting("last_preview_image")
        if main_path:
            self._update_preview_from_path(main_path)
        gallery_path = self._get_setting("last_gallery_image")
        if gallery_path and os.path.isfile(gallery_path):
            self._focus_gallery_file(gallery_path, open_image=True)

    def _build_gallery_controls(self, parent):
        gallery_group = ttk.LabelFrame(parent, text="Galerie (output)")
        gallery_group.pack(fill="both", expand=True, pady=(10, 0))

        self.gallery_paned = ttk.Panedwindow(gallery_group, orient="horizontal")
        self.gallery_paned.pack(fill="both", expand=True)

        tree_frame = ttk.Frame(self.gallery_paned, padding=(0, 0))
        self.gallery_paned.add(tree_frame, weight=1)

        right_container = ttk.Frame(self.gallery_paned, padding=(6, 0))
        self.gallery_paned.add(right_container, weight=3)
        self._register_panedwindow(self.gallery_paned, "gallery_main", "horizontal", 0.25)

        self.gallery_tree = ttk.Treeview(tree_frame, show="tree")
        self.gallery_tree.pack(side="left", fill="both", expand=True)
        tree_scroll = ttk.Scrollbar(tree_frame, orient="vertical", command=self.gallery_tree.yview)
        tree_scroll.pack(side="right", fill="y")
        self.gallery_tree.configure(yscrollcommand=tree_scroll.set)
        self.gallery_tree.bind("<<TreeviewSelect>>", self._on_gallery_dir_select)
        self.gallery_tree.bind("<<TreeviewOpen>>", self._on_gallery_tree_open)

        self.gallery_lower_paned = None
        file_frame = ttk.Frame(right_container)
        file_frame.pack(fill="both", expand=True)

        controls = ttk.Frame(file_frame)
        controls.pack(fill="x", pady=(0, 4))
        ttk.Button(controls, text="Galerie aktualisieren", command=self._refresh_gallery).pack(side="left")
        ttk.Label(controls, text="Kachelgröße:").pack(side="left", padx=(8, 2))
        saved_mode = int(self._get_setting("gallery_tile_size_mode", -1))
        saved_size = int(self._get_setting("gallery_tile_size", 96))
        initial_mode = self._resolve_gallery_tile_mode(saved_mode, saved_size)
        initial_size = GALLERY_TILE_SIZE_PRESETS[initial_mode][1]
        self.gallery_tile_size_var = tk.IntVar(value=initial_size)
        self.gallery_tile_mode_var = tk.IntVar(value=initial_mode)
        self.gallery_tile_scale = tk.Scale(
            controls,
            from_=0,
            to=len(GALLERY_TILE_SIZE_PRESETS) - 1,
            orient="horizontal",
            resolution=1,
            showvalue=False,
            command=self._on_gallery_tile_size_change,
        )
        self.gallery_tile_scale.pack(side="left", fill="x", expand=True, padx=4)
        self.gallery_tile_scale.set(initial_mode)
        self.gallery_tile_label = ttk.Label(controls, text=self._gallery_size_description(initial_mode))
        self.gallery_tile_label.pack(side="left", padx=(4, 0))
        ttk.Button(controls, text="Auswahl löschen", command=self._delete_selected_tiles).pack(side="left", padx=(6, 0))
        self.gallery_loading_var = tk.StringVar(value="")
        ttk.Label(controls, textvariable=self.gallery_loading_var, width=14, anchor="e").pack(side="right", padx=(6, 0))
        self._update_gallery_loading_status()

        grid_frame = ttk.LabelFrame(file_frame, text="Kachelübersicht")
        grid_frame.pack(fill="both", expand=True)
        canvas_frame = ttk.Frame(grid_frame)
        canvas_frame.pack(fill="both", expand=True, padx=2, pady=(0, 4))
        self.gallery_tile_canvas = tk.Canvas(canvas_frame, highlightthickness=0)
        self.gallery_tile_canvas.pack(side="left", fill="both", expand=True)
        self.gallery_tile_scroll = ttk.Scrollbar(canvas_frame, orient="vertical", command=self.gallery_tile_canvas.yview)
        self.gallery_tile_scroll.pack(side="right", fill="y")
        self.gallery_tile_canvas.configure(yscrollcommand=self.gallery_tile_scroll.set, takefocus=1)
        self.gallery_tile_canvas.bind("<Configure>", self._on_gallery_tile_canvas_configure)
        self.gallery_tile_canvas.bind("<Button-1>", lambda _e: self.gallery_tile_canvas.focus_set())
        self.gallery_tile_canvas.tag_bind("tile_item", "<Button-1>", self._on_gallery_tile_click)
        self.gallery_tile_canvas.tag_bind("tile_item", "<Double-Button-1>", self._on_gallery_tile_double)
        self.gallery_tile_canvas.bind("<MouseWheel>", self._on_gallery_mousewheel)
        self.gallery_tile_canvas.bind("<Button-4>", self._on_gallery_mousewheel)
        self.gallery_tile_canvas.bind("<Button-5>", self._on_gallery_mousewheel)
        nav_bindings = {
            "<Left>": (0, -1),
            "<Right>": (0, 1),
            "<Up>": (-1, 0),
            "<Down>": (1, 0),
        }
        for seq, (dr, dc) in nav_bindings.items():
            self.gallery_tile_canvas.bind(seq, lambda e, r=dr, c=dc: self._handle_gallery_navigation(e, r, c))
        self.gallery_tile_canvas.bind("<Home>", lambda e: self._handle_gallery_navigation(e, absolute="start"))
        self.gallery_tile_canvas.bind("<End>", lambda e: self._handle_gallery_navigation(e, absolute="end"))
        self.gallery_tile_canvas.bind("<Prior>", lambda e: self._handle_gallery_navigation(e, rows=-5))
        self.gallery_tile_canvas.bind("<Next>", lambda e: self._handle_gallery_navigation(e, rows=5))
        self.gallery_tile_canvas.bind("<Return>", self._handle_gallery_open)
        self.gallery_tile_canvas.bind("<Delete>", self._delete_selected_tiles)
        self.gallery_tile_canvas.bind("<BackSpace>", self._delete_selected_tiles)

        self.gallery_preview_label = None

    def _refresh_gallery(self, highlight_path=None):
        if not self.gallery_tree:
            return
        self._gallery_dir_scan_cache = {}
        ensure_folder(self.gallery_root)
        self.gallery_tree.delete(*self.gallery_tree.get_children())
        self.gallery_tile_images.clear()
        self.gallery_tile_tag_map.clear()
        self.gallery_tile_rects.clear()
        self.gallery_tile_render_pending = False
        self.gallery_tree_root_id = self._add_tree_dir("", self.gallery_root)
        self.gallery_tree.item(self.gallery_tree_root_id, open=True)
        self._populate_tree_children(self.gallery_tree_root_id)
        default_dir = self._get_setting("gallery_last_dir", os.path.join(self.gallery_root, "output"))
        target_dir = default_dir
        highlight_file = None
        if highlight_path:
            if os.path.isdir(highlight_path):
                target_dir = highlight_path
            elif os.path.isfile(highlight_path):
                target_dir = os.path.dirname(highlight_path)
                highlight_file = os.path.basename(highlight_path)
        if not target_dir or not os.path.isdir(target_dir):
            target_dir = self.gallery_root
        self._select_gallery_dir(target_dir)
        if highlight_file and highlight_file in self.gallery_files:
            self._set_gallery_selection(highlight_file)
            self._open_gallery_image(highlight_file)

    def _add_tree_dir(self, parent_id, path):
        text = os.path.basename(path) or path
        node_id = self.gallery_tree.insert(parent_id, "end", text=text, values=(path, "dir"))
        if self._has_visible_subdirs(path):
            self.gallery_tree.insert(node_id, "end", text="…", values=(path, "placeholder"))
        return node_id

    def _populate_tree_children(self, node_id):
        values = self.gallery_tree.item(node_id, "values")
        if not values or values[1] != "dir":
            return
        children = self.gallery_tree.get_children(node_id)
        if children:
            first_values = self.gallery_tree.item(children[0], "values")
            if first_values and len(first_values) > 1 and first_values[1] != "placeholder":
                return
        for child in children:
            self.gallery_tree.delete(child)
        path = values[0]
        try:
            entries = sorted(os.listdir(path))
        except OSError:
            entries = []
        for entry in entries:
            if self._is_hidden_name(entry):
                continue
            full = os.path.join(path, entry)
            if not os.path.isdir(full) or os.path.islink(full):
                continue
            if not self._dir_contains_images(full):
                continue
            self._add_tree_dir(node_id, full)

    def _ensure_tree_path(self, target_path):
        if not self.gallery_tree_root_id:
            return None
        path = os.path.abspath(target_path)
        root_path = os.path.abspath(self.gallery_root)
        try:
            common = os.path.commonpath([path, root_path])
        except ValueError:
            return self.gallery_tree_root_id
        if common != root_path:
            return self.gallery_tree_root_id
        node = self.gallery_tree_root_id
        rel = os.path.relpath(path, root_path)
        if rel == ".":
            return node
        parts = rel.split(os.sep)
        for i, part in enumerate(parts):
            self._populate_tree_children(node)
            match = None
            for child in self.gallery_tree.get_children(node):
                values = self.gallery_tree.item(child, "values")
                if not values:
                    continue
                current_name = os.path.basename(values[0])
                if current_name == part:
                    match = child
                    break
            if not match:
                return node
            if self.gallery_tree.item(match, "values")[1] == "dir":
                self.gallery_tree.item(match, open=True)
            node = match
        return node

    def _select_gallery_dir(self, path):
        if not self.gallery_tree or not path:
            return
        item = self._ensure_tree_path(path)
        if not item:
            return
        self.gallery_tree.selection_set(item)
        self.gallery_tree.see(item)
        self.gallery_tree.item(item, open=True)
        values = self.gallery_tree.item(item, "values")
        directory = values[0] if values else path
        if directory and os.path.isdir(directory):
            self.gallery_current_dir = directory
            self._populate_gallery_files(directory)

    def _focus_gallery_file(self, filepath, open_image=True):
        if not filepath or not os.path.isfile(filepath):
            return
        directory = os.path.dirname(filepath)
        if directory:
            self._select_gallery_dir(directory)
        filename = os.path.basename(filepath)
        if filename in self.gallery_files:
            self._set_gallery_selection(filename, update_preview=open_image)

    def _populate_gallery_files(self, directory):
        self.gallery_current_dir = directory
        self._set_setting("gallery_last_dir", directory)
        files = []
        try:
            for name in sorted(os.listdir(directory)):
                if self._is_hidden_name(name):
                    continue
                full = os.path.join(directory, name)
                if os.path.isfile(full) and name.lower().endswith((".png", ".jpg", ".jpeg")):
                    files.append(name)
        except OSError:
            files = []
        self.gallery_files = files

        restore_file = self.gallery_selected_file if self.gallery_selected_file in files else None
        if self.gallery_tile_canvas:
            self.gallery_tile_canvas.yview_moveto(0)
        self._request_gallery_tile_render(force=True)

        if restore_file:
            self._set_gallery_selection(restore_file, update_preview=False)
        else:
            self._clear_gallery_preview()

    def _on_gallery_tree_open(self, event):
        tree = event.widget
        if not isinstance(tree, ttk.Treeview):
            return
        item = tree.focus()
        if item:
            self._populate_tree_children(item)

    def _on_gallery_dir_select(self, _event=None):
        selection = self.gallery_tree.selection()
        if not selection:
            return
        item = selection[0]
        values = self.gallery_tree.item(item, "values")
        if not values:
            return
        directory = values[0]
        if directory and os.path.isdir(directory):
            self.gallery_current_dir = directory
            self._populate_gallery_files(directory)

    def _select_mosaic_image(self):
        path = filedialog.askopenfilename(
            title="Mosaik-Quellbild auswählen",
            filetypes=[("Bilder", "*.png *.jpg *.jpeg"), ("Alle Dateien", "*.*")],
            initialdir=self.last_dir
        )
        if path and self.mosaic_image_var:
            self.mosaic_image_var.set(path)
            self._set_setting("mosaic_image", path)
            self._remember_dir(os.path.dirname(path))
            self._update_mosaic_resolution_options()

    def _select_mosaic_palette(self):
        initial = self.mosaic_palette_var.get() or self.last_dir
        folder = filedialog.askdirectory(title="Palette-Ordner auswählen", initialdir=initial or os.getcwd())
        if folder and self.mosaic_palette_var:
            self.mosaic_palette_var.set(folder)
            self._set_setting("mosaic_palette", folder)
            self._remember_dir(folder)
            self._update_mosaic_resolution_options()

    def _update_mosaic_resolution_options(self):
        if not (self.mosaic_image_var and self.mosaic_palette_var and self.mosaic_resolution_box):
            return
        image_path = self.mosaic_image_var.get().strip()
        palette_dir = self.mosaic_palette_var.get().strip()
        if not image_path or not palette_dir:
            return
        try:
            tile_size = get_palette_tile_size(palette_dir)
            options = suggest_mosaic_resolutions(image_path, tile_size)
        except Exception as e:
            messagebox.showerror("Auflösungen", str(e))
            return
        if not options:
            return
        self.mosaic_resolution_options = options
        labels = [opt["label"] for opt in options]
        self.mosaic_resolution_box["values"] = labels
        self.mosaic_resolution_var.set(labels[0])

    def _get_selected_mosaic_grid(self):
        if not self.mosaic_resolution_options:
            return None
        label = self.mosaic_resolution_var.get() if self.mosaic_resolution_var else ""
        for opt in self.mosaic_resolution_options:
            if opt["label"] == label:
                return opt
        return self.mosaic_resolution_options[0]

    def _generate_mosaic_image(self):
        if not (self.mosaic_image_var and self.mosaic_palette_var):
            messagebox.showwarning("Mosaik", "Bitte Bild und Palette auswählen.")
            return
        image_path = self.mosaic_image_var.get().strip()
        palette_dir = self.mosaic_palette_var.get().strip()
        if not image_path or not palette_dir:
            messagebox.showwarning("Mosaik", "Bitte Bild und Palette auswählen.")
            return
        if not self.mosaic_resolution_options:
            self._update_mosaic_resolution_options()
        grid = self._get_selected_mosaic_grid()
        if not grid:
            messagebox.showwarning("Mosaik", "Keine Auflösung ausgewählt.")
            return
        total_tiles = grid["cols"] * grid["rows"]
        if total_tiles > 16384:
            if not messagebox.askokcancel(
                "Große Auflösung",
                f"Es werden {total_tiles} Kacheln erzeugt. Dieser Vorgang kann länger dauern.\nFortfahren?"
            ):
                self.set_status("Mosaik abgebrochen.")
                return

        self.set_status("Mosaik wird generiert…")
        self._start_progress(total_tiles, "Mosaik wird generiert…")

        try:
            def _progress_cb(done, total):
                self._update_progress(done, total)
                self.set_status(f"Mosaik: {done}/{total} Kacheln")

            result = generate_mosaic_from_palette(
                image_path,
                palette_dir,
                cols=grid["cols"],
                rows=grid["rows"],
                progress_cb=_progress_cb
            )
        except Exception as e:
            self._finish_progress()
            messagebox.showerror("Mosaik", str(e))
            self.set_status("Fehler beim Mosaik.")
            return

        self._finish_progress()

        preview_loaded = self._update_preview_from_path(result["path"])
        if not preview_loaded:
            self._update_preview(result["image"])
            self._set_last_preview_path(result["path"])
        summary = (
            f"Mosaik gespeichert als: {result['path']} "
            f"({result['cols']} x {result['rows']} Tiles)"
        )
        self.log_message(summary)
        self._refresh_gallery(result["path"])
        messagebox.showinfo("Mosaik erstellt", summary)
        self.set_status("Mosaik fertig.")


class MultiFilePicker(tk.Toplevel):
    """Einfacher Datei-Picker mit Mehrfachauswahl (plattformunabhängig)."""

    def __init__(self, parent, initialdir=None):
        super().__init__(parent)
        self._parent = parent
        self.title("Mehrere Dateien auswählen")
        self.resizable(True, True)
        self.selected_files = []
        self.extensions = (".png", ".jpg", ".jpeg")
        self.current_dir = tk.StringVar(value=initialdir or os.getcwd())
        self.index_map = []

        self._build_ui()
        self._load_directory(self.current_dir.get())

        self.transient(parent)
        self.grab_set()
        self.protocol("WM_DELETE_WINDOW", self._on_cancel)

    def _build_ui(self):
        frm = ttk.Frame(self, padding=10)
        frm.pack(fill="both", expand=True)

        dir_frame = ttk.Frame(frm)
        dir_frame.pack(fill="x", pady=(0, 6))
        ttk.Label(dir_frame, text="Ordner:").pack(side="left")
        entry = ttk.Entry(dir_frame, textvariable=self.current_dir)
        entry.pack(side="left", fill="x", expand=True, padx=4)
        ttk.Button(dir_frame, text="Ordner wählen…", command=self._choose_directory).pack(side="left")

        list_frame = ttk.Frame(frm)
        list_frame.pack(fill="both", expand=True)
        self.listbox = tk.Listbox(list_frame, selectmode=tk.EXTENDED)
        self.listbox.pack(side="left", fill="both", expand=True)
        scrollbar = ttk.Scrollbar(list_frame, orient="vertical", command=self.listbox.yview)
        scrollbar.pack(side="right", fill="y")
        self.listbox.config(yscrollcommand=scrollbar.set)
        self.listbox.bind("<Double-Button-1>", self._on_double_click)

        ttk.Label(frm, text="Strg/Cmd oder Shift für Mehrfachauswahl verwenden.").pack(anchor="w", pady=4)

        btn_frame = ttk.Frame(frm)
        btn_frame.pack(fill="x", pady=(6, 0))
        ttk.Button(btn_frame, text="Alle auswählen", command=self._select_all).pack(side="left")
        ttk.Button(btn_frame, text="Hinzufügen", command=self._on_confirm).pack(side="right")
        ttk.Button(btn_frame, text="Abbrechen", command=self._on_cancel).pack(side="right", padx=(0, 6))

    def _choose_directory(self):
        new_dir = filedialog.askdirectory(parent=self, mustexist=True, initialdir=self.current_dir.get())
        if new_dir:
            self.current_dir.set(new_dir)
            self._load_directory(new_dir)

    def _load_directory(self, path):
        if not os.path.isdir(path):
            messagebox.showerror("Ungültiger Ordner", f"Ordner nicht gefunden:\n{path}", parent=self)
            return

        path = os.path.abspath(path)
        self.current_dir.set(path)
        dirs = []
        files = []
        for entry in sorted(os.listdir(path)):
            full = os.path.join(path, entry)
            if os.path.isdir(full):
                dirs.append((entry, full))
            elif os.path.isfile(full) and entry.lower().endswith(self.extensions):
                files.append((entry, full))

        self.listbox.delete(0, "end")
        self.index_map = []

        parent_dir = os.path.abspath(os.path.join(path, os.pardir))
        if parent_dir != path:
            self.listbox.insert("end", ".." + os.sep)
            self.index_map.append(("dir", parent_dir))

        for name, full in dirs:
            self.listbox.insert("end", name + os.sep)
            self.index_map.append(("dir", full))

        for name, full in files:
            self.listbox.insert("end", name)
            self.index_map.append(("file", full))

        if not self.index_map:
            self.listbox.insert("end", "(Keine passenden Dateien)")
            self.index_map.append(("info", None))

    def _select_all(self):
        if not self.index_map:
            return
        self.listbox.selection_clear(0, "end")
        for idx, entry in enumerate(self.index_map):
            if entry[0] == "file":
                self.listbox.selection_set(idx)

    def _on_double_click(self, event):
        index = self.listbox.nearest(event.y)
        if index < 0 or index >= len(self.index_map):
            return
        kind, target = self.index_map[index]
        if kind == "file":
            self.listbox.selection_clear(0, "end")
            self.listbox.selection_set(index)
            self._on_confirm()
        elif kind == "dir" and target:
            self._load_directory(target)

    def _on_confirm(self):
        selection = self.listbox.curselection()
        files = []
        for idx in selection:
            if idx >= len(self.index_map):
                continue
            kind, target = self.index_map[idx]
            if kind == "file" and target:
                files.append(target)
        if not files:
            messagebox.showwarning("Keine Auswahl", "Bitte mindestens eine Datei auswählen.", parent=self)
            return
        self.selected_files = files
        self.destroy()

    def _on_cancel(self):
        self.selected_files = []
        self.destroy()


def pick_multiple_files(parent, initialdir=None):
    """Zeigt den MultiFilePicker modal an und gibt die Auswahl zurück."""
    dialog = MultiFilePicker(parent, initialdir=initialdir)
    parent.wait_window(dialog)
    return dialog.selected_files


# --------------------------------------------------------
# GUI mit / ohne Drag & Drop
# --------------------------------------------------------

if DND_AVAILABLE:
    # Variante mit tkinterdnd2 (echtes Drag & Drop)
    class RasterApp(TkinterDnD.Tk, RasterAppBase):
        def __init__(self):
            TkinterDnD.Tk.__init__(self)
            RasterAppBase.__init__(self)
            self.title("Kachelbilder Tool (Drag & Drop)")
            self._build_ui()
            self._enable_drag_and_drop()
            self.protocol("WM_DELETE_WINDOW", self._on_close)

        def _build_ui(self):
            root = ttk.Frame(self, padding=10)
            root.pack(fill="both", expand=True)

            paned = ttk.Panedwindow(root, orient="horizontal")
            paned.pack(fill="both", expand=True)
            self.main_paned = paned

            control_area = ttk.Frame(paned)
            preview_area = ttk.Frame(paned, width=360)
            preview_area.pack_propagate(False)
            paned.add(control_area, weight=3)
            paned.add(preview_area, weight=2)
            self._register_panedwindow(paned, "main", "horizontal", 0.65)

            self.left_paned = ttk.Panedwindow(control_area, orient="vertical")
            self.left_paned.pack(fill="both", expand=True)
            notebook_container = ttk.Frame(self.left_paned)
            lower_container = ttk.Frame(self.left_paned, padding=(0, 4))
            self.left_paned.add(notebook_container, weight=5)
            self.left_paned.add(lower_container, weight=1)
            self._register_panedwindow(self.left_paned, "left", "vertical", 0.85)

            notebook = ttk.Notebook(notebook_container)
            notebook.pack(fill="both", expand=True)

            import_tab = ttk.Frame(notebook, padding=10)
            raster_tab = ttk.Frame(notebook, padding=10)
            palette_tab = ttk.Frame(notebook, padding=10)

            notebook.add(import_tab, text="Kacheln")
            notebook.add(raster_tab, text="Raster")
            notebook.add(palette_tab, text="Paletten & Mosaik")

            # --- Import Tab ---
            self.category_var = tk.StringVar(value="F")
            ttk.Label(import_tab, text="Kategorie für Sortierung (F/E):").pack(anchor="w")
            ttk.Combobox(import_tab, textvariable=self.category_var, values=["F", "E"], state="readonly").pack(fill="x", pady=(0, 4))

            ttk.Label(import_tab, text="Dateien hierher ziehen:").pack(anchor="w")
            self.drop_frame = ttk.Label(import_tab, text="⬇️ Dateien hier ablegen ⬇️", relief="solid", padding=20)
            self.drop_frame.pack(fill="both", expand=True, pady=6)

            ttk.Button(import_tab, text="Dateien auswählen…", command=self._select_files_dialog).pack(fill="x", pady=2)
            ttk.Button(import_tab, text="Sortieren & umbenennen", command=self._on_sort).pack(fill="x", pady=2)

            # --- Raster Tab ---
            self._build_raster_section(raster_tab)
            self.shuffle_var = tk.BooleanVar(value=False)
            ttk.Checkbutton(
                raster_tab,
                text="Shuffle Tiles (zufällige Reihenfolge)",
                variable=self.shuffle_var
            ).pack(anchor="w", pady=(0, 6))

            ttk.Button(raster_tab, text="Raster generieren", command=self._on_generate).pack(fill="x", pady=2)
            ttk.Button(raster_tab, text="Batch-Export aller Kombinationen", command=self._on_generate_all).pack(fill="x", pady=2)

            # --- Palette & Mosaik Tab ---
            palette_frame = ttk.LabelFrame(palette_tab, text="Farbspektrum aus Kacheln")
            palette_frame.pack(fill="x", expand=False, pady=(0, 10))

            self.palette_folder_var = tk.StringVar(value=self._get_setting("palette_folder", self.default_palette_folder))
            folder_row = ttk.Frame(palette_frame)
            folder_row.pack(fill="x", pady=2)
            ttk.Label(folder_row, text="Ordner:").pack(side="left")
            ttk.Entry(folder_row, textvariable=self.palette_folder_var).pack(side="left", fill="x", expand=True, padx=4)
            ttk.Button(folder_row, text="…", width=3, command=self._select_palette_folder).pack(side="left")
            ttk.Button(folder_row, text="Standard", command=self._reset_palette_folder_default).pack(side="left", padx=(4, 0))

            self.palette_type_var = tk.StringVar(value=PALETTE_PRESETS[4][0])
            ttk.Label(palette_frame, text="Palette:").pack(anchor="w")
            ttk.Combobox(
                palette_frame,
                textvariable=self.palette_type_var,
                values=[label for label, _ in PALETTE_PRESETS],
                state="readonly"
            ).pack(fill="x", pady=2)

            ttk.Button(palette_frame, text="Farbspektrum erzeugen", command=self._generate_palette).pack(fill="x", pady=4)
            self.palette_preview_label = ttk.Label(palette_frame)
            self.palette_preview_label.pack(fill="both", expand=True, pady=(4, 0))
            self.palette_preview_label.bind("<Configure>", self._render_palette_preview_label)

            mosaic_frame = ttk.LabelFrame(palette_tab, text="Bild → Kachelmosaik")
            mosaic_frame.pack(fill="both", expand=True)

            self.mosaic_image_var = tk.StringVar(value=self._get_setting("mosaic_image", self.default_mosaic_image))
            img_row = ttk.Frame(mosaic_frame)
            img_row.pack(fill="x", pady=2)
            ttk.Label(img_row, text="Bild:").pack(side="left")
            ttk.Entry(img_row, textvariable=self.mosaic_image_var).pack(side="left", fill="x", expand=True, padx=4)
            ttk.Button(img_row, text="…", width=3, command=self._select_mosaic_image).pack(side="left")
            ttk.Button(img_row, text="Standard", command=self._reset_mosaic_image_default).pack(side="left", padx=(4, 0))

            self.mosaic_palette_var = tk.StringVar(value=self._get_setting("mosaic_palette", self.default_mosaic_palette))
            pal_row = ttk.Frame(mosaic_frame)
            pal_row.pack(fill="x", pady=2)
            ttk.Label(pal_row, text="Palette:").pack(side="left")
            ttk.Entry(pal_row, textvariable=self.mosaic_palette_var).pack(side="left", fill="x", expand=True, padx=4)
            ttk.Button(pal_row, text="…", width=3, command=self._select_mosaic_palette).pack(side="left")
            ttk.Button(pal_row, text="Standard", command=self._reset_mosaic_palette_default).pack(side="left", padx=(4, 0))

            self.mosaic_resolution_var = tk.StringVar()
            ttk.Label(mosaic_frame, text="Auflösung:").pack(anchor="w")
            self.mosaic_resolution_box = ttk.Combobox(mosaic_frame, textvariable=self.mosaic_resolution_var, state="readonly")
            self.mosaic_resolution_box.pack(fill="x", pady=2)
            ttk.Button(mosaic_frame, text="Auflösungen aktualisieren", command=self._update_mosaic_resolution_options).pack(fill="x", pady=2)
            ttk.Button(mosaic_frame, text="Mosaik generieren", command=self._generate_mosaic_image).pack(fill="x", pady=4)

            # --- Log & Fortschritt im linken Bereich ---
            ttk.Label(lower_container, text="Log:").pack(anchor="w")
            self.log_text = ttk.Entry(lower_container, state="readonly")
            self.log_text.pack(fill="x", pady=(0, 2))

            self.progress_label = ttk.Label(lower_container, text="Bereit")
            self.progress_label.pack(anchor="w")
            self.progress_bar = ttk.Progressbar(lower_container, maximum=1, value=0)
            self.progress_bar.pack(fill="x")
            self._finish_progress()

            # --- Vorschau & Galerie rechts ---
            self.right_paned = ttk.Panedwindow(preview_area, orient="vertical")
            self.right_paned.pack(fill="both", expand=True)
            preview_group = ttk.LabelFrame(self.right_paned, text="Aktuelle Vorschau")
            gallery_container = ttk.Frame(self.right_paned)
            self.right_paned.add(preview_group, weight=2)
            self.right_paned.add(gallery_container, weight=3)
            try:
                self.right_paned.paneconfigure(preview_group, minsize=180)
                self.right_paned.paneconfigure(gallery_container, minsize=260)
            except tk.TclError:
                pass
            self._register_panedwindow(self.right_paned, "right", "vertical", 0.5)

            self.preview_label = ttk.Label(preview_group)
            self.preview_label.pack(fill="both", expand=True, padx=6, pady=6)
            self.preview_label.bind("<Configure>", self._render_preview_label)
            self.preview_label.bind("<Double-Button-1>", self._on_preview_double_click)

            self._build_gallery_controls(gallery_container)

            self.status_var = tk.StringVar(value="Bereit")
            ttk.Label(preview_area, textvariable=self.status_var, relief="sunken").pack(fill="x", pady=(8, 0))
            self._refresh_gallery()
            self.after(400, self._restore_last_preview_images)
            self.after(400, self._restore_last_preview_images)

        def _enable_drag_and_drop(self):
            self.drop_frame.drop_target_register(DND_FILES)
            self.drop_frame.dnd_bind("<<Drop>>", self._on_drop)

        def _on_drop(self, event):
            added = self._add_import_paths(event.data)
            if added:
                self.drop_frame.config(text=f"{len(self.drop_paths)} Datei(en) geladen")

        def _select_files_dialog(self):
            paths = self._open_file_picker()
            added = self._add_import_paths(paths)
            if added:
                self.drop_frame.config(text=f"{len(self.drop_paths)} Datei(en) geladen")

        def _on_sort(self):
            if not self.drop_paths:
                messagebox.showwarning("Keine Dateien", "Bitte zuerst Dateien ziehen oder auswählen.")
                return

            cat = self.category_var.get().strip().upper()
            if cat not in ("F", "E"):
                messagebox.showerror("Fehler", "Kategorie muss F oder E sein.")
                return

            try:
                sort_and_rename(self.drop_paths, cat)
            except Exception as e:
                messagebox.showerror("Fehler", str(e))
                return

            messagebox.showinfo("Fertig", f"{len(self.drop_paths)} Datei(en) sortiert.")
            self.drop_paths = []
            self.drop_frame.config(text="⬇️ Dateien hier ablegen ⬇️")

        def _on_generate(self):
            pattern_rows = self._get_pattern_rows()
            if not pattern_rows:
                messagebox.showwarning("Kein Muster", "Bitte ein Muster eingeben.")
                return

            self.set_status("Generiere Einzel-Raster…")
            try:
                paths, last_img = self._generate_images(pattern_rows, batch=False)
            except Exception as e:
                messagebox.showerror("Fehler beim Generieren", str(e))
                self.set_status("Fehler beim Generieren.")
                return

            preview_loaded = False
            if paths:
                preview_loaded = self._update_preview_from_path(paths[-1])
            if not preview_loaded and last_img is not None:
                self._update_preview(last_img)
                if paths:
                    self._set_last_preview_path(paths[-1])
            for path in paths:
                self.log_message(f"Raster gespeichert als: {path}")
            if paths:
                self._refresh_gallery(paths[-1])
            self.set_status("Fertig.")

        def _on_generate_all(self):
            pattern_rows = self._get_pattern_rows()
            if not pattern_rows:
                messagebox.showwarning("Kein Muster", "Bitte ein Muster eingeben.")
                return

            try:
                tiles_F, tiles_E, batches_F, batches_E, total, converted_rows = self._prepare_batch(pattern_rows)
            except Exception as e:
                messagebox.showerror("Fehler beim Laden", str(e))
                return

            if total == 0:
                messagebox.showinfo("Keine Raster", "Es wurden keine Raster erzeugt.")
                return

            if not messagebox.askokcancel("Batch starten", f"Es werden {total} Raster erzeugt. Fortfahren?"):
                return

            self.set_status("Batch wird erstellt…")
            self._start_progress(total, "Batch wird erstellt…")

            def _progress_cb(current, _total):
                self._update_progress(current, _total)

            try:
                paths, last_img, _ = generate_batch_rasters(
                    converted_rows,
                    tiles_F,
                    tiles_E,
                    shuffle_tiles=self.shuffle_var.get(),
                    batches_F=batches_F,
                    batches_E=batches_E,
                    progress_cb=_progress_cb,
                    log_cb=self.log_message
                )
            except Exception as e:
                self._finish_progress()
                messagebox.showerror("Fehler beim Batch", str(e))
                self.set_status("Fehler beim Batch.")
                return

            self._finish_progress()

            if not paths:
                messagebox.showinfo("Keine Raster", "Es wurden keine Raster erzeugt.")
                self.set_status("Keine Raster erzeugt.")
                return

            preview_loaded = False
            if paths:
                preview_loaded = self._update_preview_from_path(paths[-1])
            if not preview_loaded and last_img is not None:
                self._update_preview(last_img)
                if paths:
                    self._set_last_preview_path(paths[-1])
            if paths:
                self._refresh_gallery(paths[-1])
            self.set_status("Batch abgeschlossen.")
            messagebox.showinfo("Batch abgeschlossen", f"{len(paths)} Raster gespeichert.")

else:
    # Fallback ohne echtes Drag & Drop (nur Datei-Dialog)
    class RasterApp(tk.Tk, RasterAppBase):
        def __init__(self):
            tk.Tk.__init__(self)
            RasterAppBase.__init__(self)
            self.title("Kachelbilder Tool (ohne Drag & Drop)")
            self._build_ui()
            self.protocol("WM_DELETE_WINDOW", self._on_close)

        def _build_ui(self):
            root = ttk.Frame(self, padding=10)
            root.pack(fill="both", expand=True)

            self.main_paned = ttk.Panedwindow(root, orient="horizontal")
            self.main_paned.pack(fill="both", expand=True)

            control_area = ttk.Frame(self.main_paned)
            preview_area = ttk.Frame(self.main_paned, width=360)
            preview_area.pack_propagate(False)
            self.main_paned.add(control_area, weight=3)
            self.main_paned.add(preview_area, weight=2)
            self._register_panedwindow(self.main_paned, "main", "horizontal", 0.65)

            self.left_paned = ttk.Panedwindow(control_area, orient="vertical")
            self.left_paned.pack(fill="both", expand=True)
            notebook_container = ttk.Frame(self.left_paned)
            lower_container = ttk.Frame(self.left_paned, padding=(0, 4))
            self.left_paned.add(notebook_container, weight=5)
            self.left_paned.add(lower_container, weight=1)
            self._register_panedwindow(self.left_paned, "left", "vertical", 0.85)

            notebook = ttk.Notebook(notebook_container)
            notebook.pack(fill="both", expand=True)

            import_tab = ttk.Frame(notebook, padding=10)
            raster_tab = ttk.Frame(notebook, padding=10)
            palette_tab = ttk.Frame(notebook, padding=10)

            notebook.add(import_tab, text="Kacheln")
            notebook.add(raster_tab, text="Raster")
            notebook.add(palette_tab, text="Paletten & Mosaik")

            self.category_var = tk.StringVar(value="F")
            ttk.Label(import_tab, text="Kategorie für Sortierung (F/E):").pack(anchor="w")
            ttk.Combobox(import_tab, textvariable=self.category_var, values=["F", "E"], state="readonly").pack(fill="x", pady=(0, 4))
            ttk.Button(import_tab, text="Dateien auswählen…", command=self._select_files_dialog).pack(fill="x", pady=2)
            ttk.Button(import_tab, text="Sortieren & umbenennen", command=self._on_sort).pack(fill="x", pady=2)

            self._build_raster_section(raster_tab)
            self.shuffle_var = tk.BooleanVar(value=False)
            ttk.Checkbutton(
                raster_tab,
                text="Shuffle Tiles (zufällige Reihenfolge)",
                variable=self.shuffle_var
            ).pack(anchor="w", pady=(0, 6))

            ttk.Button(raster_tab, text="Raster generieren", command=self._on_generate).pack(fill="x", pady=2)
            ttk.Button(raster_tab, text="Batch-Export aller Kombinationen", command=self._on_generate_all).pack(fill="x", pady=2)

            palette_frame = ttk.LabelFrame(palette_tab, text="Farbspektrum aus Kacheln")
            palette_frame.pack(fill="x", expand=False, pady=(0, 10))

            self.palette_folder_var = tk.StringVar(value=self._get_setting("palette_folder", self.default_palette_folder))
            folder_row = ttk.Frame(palette_frame)
            folder_row.pack(fill="x", pady=2)
            ttk.Label(folder_row, text="Ordner:").pack(side="left")
            ttk.Entry(folder_row, textvariable=self.palette_folder_var).pack(side="left", fill="x", expand=True, padx=4)
            ttk.Button(folder_row, text="…", width=3, command=self._select_palette_folder).pack(side="left")
            ttk.Button(folder_row, text="Standard", command=self._reset_palette_folder_default).pack(side="left", padx=(4, 0))

            self.palette_type_var = tk.StringVar(value=PALETTE_PRESETS[4][0])
            ttk.Label(palette_frame, text="Palette:").pack(anchor="w")
            ttk.Combobox(
                palette_frame,
                textvariable=self.palette_type_var,
                values=[label for label, _ in PALETTE_PRESETS],
                state="readonly"
            ).pack(fill="x", pady=2)

            ttk.Button(palette_frame, text="Farbspektrum erzeugen", command=self._generate_palette).pack(fill="x", pady=4)
            self.palette_preview_label = ttk.Label(palette_frame)
            self.palette_preview_label.pack(fill="both", expand=True, pady=(4, 0))
            self.palette_preview_label.bind("<Configure>", self._render_palette_preview_label)

            mosaic_frame = ttk.LabelFrame(palette_tab, text="Bild → Kachelmosaik")
            mosaic_frame.pack(fill="both", expand=True)

            self.mosaic_image_var = tk.StringVar(value=self._get_setting("mosaic_image", self.default_mosaic_image))
            img_row = ttk.Frame(mosaic_frame)
            img_row.pack(fill="x", pady=2)
            ttk.Label(img_row, text="Bild:").pack(side="left")
            ttk.Entry(img_row, textvariable=self.mosaic_image_var).pack(side="left", fill="x", expand=True, padx=4)
            ttk.Button(img_row, text="…", width=3, command=self._select_mosaic_image).pack(side="left")
            ttk.Button(img_row, text="Standard", command=self._reset_mosaic_image_default).pack(side="left", padx=(4, 0))

            self.mosaic_palette_var = tk.StringVar(value=self._get_setting("mosaic_palette", self.default_mosaic_palette))
            pal_row = ttk.Frame(mosaic_frame)
            pal_row.pack(fill="x", pady=2)
            ttk.Label(pal_row, text="Palette:").pack(side="left")
            ttk.Entry(pal_row, textvariable=self.mosaic_palette_var).pack(side="left", fill="x", expand=True, padx=4)
            ttk.Button(pal_row, text="…", width=3, command=self._select_mosaic_palette).pack(side="left")
            ttk.Button(pal_row, text="Standard", command=self._reset_mosaic_palette_default).pack(side="left", padx=(4, 0))

            self.mosaic_resolution_var = tk.StringVar()
            ttk.Label(mosaic_frame, text="Auflösung:").pack(anchor="w")
            self.mosaic_resolution_box = ttk.Combobox(mosaic_frame, textvariable=self.mosaic_resolution_var, state="readonly")
            self.mosaic_resolution_box.pack(fill="x", pady=2)
            ttk.Button(mosaic_frame, text="Auflösungen aktualisieren", command=self._update_mosaic_resolution_options).pack(fill="x", pady=2)
            ttk.Button(mosaic_frame, text="Mosaik generieren", command=self._generate_mosaic_image).pack(fill="x", pady=4)

            ttk.Label(lower_container, text="Log:").pack(anchor="w")
            self.log_text = ttk.Entry(lower_container, state="readonly")
            self.log_text.pack(fill="x", pady=(0, 2))
            self.progress_label = ttk.Label(lower_container, text="Bereit")
            self.progress_label.pack(anchor="w")
            self.progress_bar = ttk.Progressbar(lower_container, maximum=1, value=0)
            self.progress_bar.pack(fill="x")
            self._finish_progress()

            self.right_paned = ttk.Panedwindow(preview_area, orient="vertical")
            self.right_paned.pack(fill="both", expand=True)
            preview_group = ttk.LabelFrame(self.right_paned, text="Aktuelle Vorschau")
            gallery_container = ttk.Frame(self.right_paned)
            self.right_paned.add(preview_group, weight=2)
            self.right_paned.add(gallery_container, weight=3)
            try:
                self.right_paned.paneconfigure(preview_group, minsize=180)
                self.right_paned.paneconfigure(gallery_container, minsize=260)
            except tk.TclError:
                pass
            self._register_panedwindow(self.right_paned, "right", "vertical", 0.5)

            self.preview_label = ttk.Label(preview_group)
            self.preview_label.pack(fill="both", expand=True, padx=6, pady=6)
            self.preview_label.bind("<Configure>", self._render_preview_label)
            self.preview_label.bind("<Double-Button-1>", self._on_preview_double_click)

            self._build_gallery_controls(gallery_container)

            self.status_var = tk.StringVar(value="Bereit")
            ttk.Label(preview_area, textvariable=self.status_var, relief="sunken").pack(fill="x", pady=(8, 0))
            self._refresh_gallery()
            self.after(400, self._restore_last_preview_images)

        def _select_files_dialog(self):
            paths = self._open_file_picker()
            self._add_import_paths(paths)

        def _on_sort(self):
            if not self.drop_paths:
                messagebox.showwarning("Keine Dateien", "Bitte zuerst Dateien auswählen.")
                return

            cat = self.category_var.get().strip().upper()
            if cat not in ("F", "E"):
                messagebox.showerror("Fehler", "Kategorie muss F oder E sein.")
                return

            try:
                sort_and_rename(self.drop_paths, cat)
            except Exception as e:
                messagebox.showerror("Fehler", str(e))
                return

            messagebox.showinfo("Fertig", f"{len(self.drop_paths)} Datei(en) sortiert.")
            self.drop_paths = []

        def _on_generate(self):
            pattern_rows = self._get_pattern_rows()
            if not pattern_rows:
                messagebox.showwarning("Kein Muster", "Bitte ein Muster eingeben.")
                return

            self.set_status("Generiere Einzel-Raster…")
            try:
                paths, last_img = self._generate_images(pattern_rows, batch=False)
            except Exception as e:
                messagebox.showerror("Fehler beim Generieren", str(e))
                self.set_status("Fehler beim Generieren.")
                return

            preview_loaded = False
            if paths:
                preview_loaded = self._update_preview_from_path(paths[-1])
            if not preview_loaded and last_img is not None:
                self._update_preview(last_img)
                if paths:
                    self._set_last_preview_path(paths[-1])
            for path in paths:
                self.log_message(f"Raster gespeichert als: {path}")
            if paths:
                self._refresh_gallery(paths[-1])
            self.set_status("Fertig.")

        def _on_generate_all(self):
            pattern_rows = self._get_pattern_rows()
            if not pattern_rows:
                messagebox.showwarning("Kein Muster", "Bitte ein Muster eingeben.")
                return

            try:
                tiles_F, tiles_E, batches_F, batches_E, total, converted_rows = self._prepare_batch(pattern_rows)
            except Exception as e:
                messagebox.showerror("Fehler beim Laden", str(e))
                return

            if total == 0:
                messagebox.showinfo("Keine Raster", "Es wurden keine Raster erzeugt.")
                return

            if not messagebox.askokcancel("Batch starten", f"Es werden {total} Raster erzeugt. Fortfahren?"):
                return

            self.set_status("Batch wird erstellt…")
            self._start_progress(total, "Batch wird erstellt…")

            def _progress_cb(current, _total):
                self._update_progress(current, _total)

            try:
                paths, last_img, _ = generate_batch_rasters(
                    converted_rows,
                    tiles_F,
                    tiles_E,
                    shuffle_tiles=self.shuffle_var.get(),
                    batches_F=batches_F,
                    batches_E=batches_E,
                    progress_cb=_progress_cb,
                    log_cb=self.log_message
                )
            except Exception as e:
                self._finish_progress()
                messagebox.showerror("Fehler beim Batch", str(e))
                self.set_status("Fehler beim Batch.")
                return

            self._finish_progress()

            if not paths:
                messagebox.showinfo("Keine Raster", "Es wurden keine Raster erzeugt.")
                self.set_status("Keine Raster erzeugt.")
                return

            preview_loaded = False
            if paths:
                preview_loaded = self._update_preview_from_path(paths[-1])
            if not preview_loaded and last_img is not None:
                self._update_preview(last_img)
                if paths:
                    self._set_last_preview_path(paths[-1])
            if paths:
                self._refresh_gallery(paths[-1])
            self.set_status("Batch abgeschlossen.")
            messagebox.showinfo("Batch abgeschlossen", f"{len(paths)} Raster gespeichert.")


# --------------------------------------------------------
# CLI-Modus
# --------------------------------------------------------

def run_cli_if_requested():
    parser = argparse.ArgumentParser(description="Kachelbilder Raster-Tool (CLI/GUI)")
    parser.add_argument("--pattern", type=str, help="Pfad zu einer Textdatei mit Muster (E/F pro Zeile)")
    parser.add_argument("--shuffle", action="store_true", help="Tiles zufällig mischen")
    parser.add_argument("--amount", type=int, default=1, help="Anzahl Raster im CLI-Modus")
    parser.add_argument("--batch-all", action="store_true", help="Alle möglichen Rasterversionen generieren")
    parser.add_argument("--palette-folder", type=str, help="Ordner mit Kacheln für Farbspektrum")
    parser.add_argument("--palette-type", type=str, default="64", help="Palette (z.B. 64, 256, 2bit, rgb)")
    parser.add_argument("--mosaic-image", type=str, help="Bild für Mosaik-Erstellung")
    parser.add_argument("--mosaic-palette", type=str, help="Palette-Ordner für das Mosaik")
    parser.add_argument("--mosaic-cols", type=int, help="Spaltenzahl für das Mosaik")
    parser.add_argument("--mosaic-rows", type=int, help="Zeilenzahl für das Mosaik")
    args, _ = parser.parse_known_args()

    mosaic_requested = bool(args.mosaic_image and args.mosaic_palette)

    if args.palette_folder:
        palette_size = palette_size_from_spec(args.palette_type)
        try:
            result = generate_palette_tile_set(
                args.palette_folder,
                palette_size,
                prefix="cli_palette_tile_",
                label=args.palette_type
            )
        except Exception as e:
            print("Fehler beim Erzeugen der Palette:", e, file=sys.stderr)
            sys.exit(1)
        print(f"Palette ({result['count']} Kacheln) gespeichert in: {result['directory']}")
        print("Metadata:", result["metadata"])
        if not args.pattern and not mosaic_requested:
            sys.exit(0)

    if mosaic_requested:
        try:
            result = generate_mosaic_from_palette(
                args.mosaic_image,
                args.mosaic_palette,
                cols=args.mosaic_cols,
                rows=args.mosaic_rows
            )
        except Exception as e:
            print("Fehler beim Erzeugen des Mosaiks:", e, file=sys.stderr)
            sys.exit(1)
        print(f"Mosaik gespeichert als: {result['path']} ({result['cols']} x {result['rows']} Tiles)")
        if not args.pattern:
            sys.exit(0)

    if args.pattern:
        with open(args.pattern, "r", encoding="utf-8") as f:
            pattern_rows = [line.strip() for line in f if line.strip()]

        try:
            tiles_F = load_tiles("F")
            tiles_E = load_tiles("E")
        except Exception as e:
            print("Fehler beim Laden der Tiles:", e, file=sys.stderr)
            sys.exit(1)

        if args.batch_all:
            batches_F, batches_E = prepare_batches(pattern_rows, tiles_F, tiles_E)
            total = len(batches_F) * len(batches_E)
            print(f"Starte Batch mit {total} Raster-Dateien…")
            paths, _, _ = generate_batch_rasters(
                pattern_rows,
                tiles_F,
                tiles_E,
                shuffle_tiles=args.shuffle,
                prefix="cli_batch_",
                batches_F=batches_F,
                batches_E=batches_E
            )
            for path in paths:
                print("Gespeichert:", path)
            print(f"Batch abgeschlossen: {len(paths)} Dateien.")
            sys.exit(0)

        for i in range(args.amount):
            img = build_raster(pattern_rows, tiles_F, tiles_E, shuffle_tiles=args.shuffle)
            out_path = unique_output_path(prefix="cli_raster_")
            img.save(out_path)
            print("Gespeichert:", out_path)

        sys.exit(0)


# --------------------------------------------------------
# Main
# --------------------------------------------------------

if __name__ == "__main__":
    run_cli_if_requested()
    app = RasterApp()
    app.mainloop()
