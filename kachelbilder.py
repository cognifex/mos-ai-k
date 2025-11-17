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
import tkinter as tk
from datetime import datetime
from tkinter import ttk, filedialog, messagebox

from PIL import Image, ImageTk, ImageDraw, ImageOps

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

TYPE_SYMBOLS = ["A", "B", "C", "D", "E"]
DEFAULT_TYPE_PATHS = {
    "A": os.path.join(APP_ROOT, "F"),
    "B": os.path.join(APP_ROOT, "E"),
    "C": os.path.join(APP_ROOT, "F1"),
    "D": os.path.join(APP_ROOT, "E1"),
    "E": os.path.join(APP_ROOT, "kacheln", "E"),
}


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


def generate_palette_tile_set(folder, palette_size, output_root=None, prefix="palette_tile_"):
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

    if palette_size <= 0:
        palette_size = len(tiles)

    quantized = quantize_color_list(colors, palette_size)
    if not quantized:
        quantized = colors

    ordered_colors = sort_colors_by_hsv(quantized)
    if not ordered_colors:
        ordered_colors = colors

    color_cycle = list(itertools.islice(itertools.cycle(ordered_colors), palette_size))
    tile_cycle = list(itertools.islice(itertools.cycle(tiles), palette_size))

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    base_dir = output_root or os.path.join("output", "palette_tiles")
    out_dir = os.path.join(base_dir, f"{prefix}{palette_size}_{timestamp}")
    ensure_folder(out_dir)

    metadata_path = os.path.join(out_dir, "metadata.csv")
    saved_files = []

    with open(metadata_path, "w", newline="", encoding="utf-8") as meta_file:
        writer = csv.writer(meta_file)
        writer.writerow(["index", "palette_color", "hex", "source_file", "output_file"])

        for idx, (target_color, (src_path, img)) in enumerate(zip(color_cycle, tile_cycle), start=1):
            tinted = tint_image_to_color(img, target_color)
            filename = f"{prefix}{idx:04d}.png"
            out_path = os.path.join(out_dir, filename)
            tinted.save(out_path)
            saved_files.append(out_path)
            writer.writerow([idx, target_color, _hex_color(target_color), os.path.basename(src_path), filename])

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
            entries.append({
                "color": color,
                "file": path,
                "index": row.get("index"),
                "hex": row.get("hex") or _hex_color(color),
            })
    if not entries:
        raise ValueError(f"Keine Palette-Kacheln in {metadata_path}")
    return entries


def load_palette_tile_images(palette_dir):
    metadata = read_palette_metadata(palette_dir)
    tiles = []
    for entry in metadata:
        img = Image.open(entry["file"]).convert("RGB")
        img.load()
        tiles.append({
            "color": entry["color"],
            "hex": entry["hex"],
            "path": entry["file"],
            "image": img,
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


def suggest_mosaic_resolutions(image_path, tile_size, max_options=6):
    if not os.path.isfile(image_path):
        raise ValueError("Bild nicht gefunden.")
    tile_w, tile_h = tile_size
    if tile_w <= 0 or tile_h <= 0:
        raise ValueError("Ungültige Tile-Größe.")
    with Image.open(image_path) as img:
        width, height = img.size
    scales = [0.2, 0.4, 0.6, 0.8, 1, 1.2, 1.4, 1.6, 2, 3, 4]
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
    cell_w = max(1, int(round(width / cols)))
    cell_h = max(1, int(round(height / rows)))
    mosaic = Image.new("RGB", (cols * cell_w, rows * cell_h))

    total = rows * cols
    processed = 0
    for y in range(rows):
        for x in range(cols):
            color = small.getpixel((x, y))
            best = min(entries, key=lambda e: _color_distance_sq(color, e["color"]))
            tile_img = best["image"]
            if tile_img.size != (cell_w, cell_h):
                tile_img = tile_img.resize((cell_w, cell_h), Image.LANCZOS)
            mosaic.paste(tile_img, (x * cell_w, y * cell_h))
            processed += 1
            if progress_cb:
                progress_cb(processed, total)

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
        self.gallery_root = os.path.abspath("output")
        self.gallery_tree = None
        self.gallery_file_list = None
        self.gallery_preview_label = None
        self.gallery_preview_image = None
        self.gallery_current_dir = self.gallery_root
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
        self._preview_base_image = None
        self._preview_photo = None
        self._palette_preview_base = None
        self._palette_preview_photo = None
        self._gallery_preview_base = None
        self._gallery_preview_photo = None

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

    def _gather_tile_sets(self):
        if not self.tile_type_count_var:
            raise ValueError("Keine Bildtypen definiert")
        count = int(self.tile_type_count_var.get())
        symbols = TYPE_SYMBOLS[:count]
        tile_sets = {}
        for symbol in symbols:
            var = self.tile_type_path_vars.get(symbol)
            path = var.get().strip() if var else ""
            if not path:
                raise ValueError(f"Kein Ordner für Typ {symbol}")
            tile_sets[symbol] = load_tiles(path)
        return tile_sets

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
        img = build_raster_multi(pattern_rows, tile_sets, shuffle_tiles=shuffle)
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

    def _update_preview(self, img):
        if img is None:
            return
        self._preview_base_image = img.copy()
        self._render_preview_label()

    def set_status(self, text):
        if self.status_var:
            self.status_var.set(text)

    def log_message(self, message):
        print(message)
        if self.log_text:
            self.log_text.configure(state="normal")
            self.log_text.insert("end", message + "\n")
            self.log_text.see("end")
            self.log_text.configure(state="disabled")
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
        try:
            result = generate_palette_tile_set(folder, palette_size)
        except Exception as e:
            messagebox.showerror("Fehler beim Spektrum", str(e))
            return

        self._update_palette_preview(result["palette_image"])
        summary = (
            f"Palette mit {result['count']} Kacheln gespeichert in: {result['directory']}\n"
            f"Metadata: {result['metadata']}\n"
            f"Preview: {result.get('preview_path')}"
        )
        self.log_message(summary)
        messagebox.showinfo("Palette erzeugt", summary)
        self._refresh_gallery(result.get("preview_path"))

    def _update_palette_preview(self, img):
        if img is None:
            return
        self._palette_preview_base = img.copy()
        self._render_palette_preview_label()

    def _build_gallery_controls(self, parent):
        gallery_group = ttk.LabelFrame(parent, text="Galerie (output)")
        gallery_group.pack(fill="both", expand=True, pady=(10, 0))

        tree_frame = ttk.Frame(gallery_group)
        tree_frame.pack(fill="both", expand=True)
        self.gallery_tree = ttk.Treeview(tree_frame, show="tree", height=6)
        self.gallery_tree.pack(side="left", fill="both", expand=True)
        tree_scroll = ttk.Scrollbar(tree_frame, orient="vertical", command=self.gallery_tree.yview)
        tree_scroll.pack(side="right", fill="y")
        self.gallery_tree.configure(yscrollcommand=tree_scroll.set)
        self.gallery_tree.bind("<<TreeviewSelect>>", self._on_gallery_dir_select)

        file_frame = ttk.Frame(gallery_group)
        file_frame.pack(fill="both", expand=True, pady=(6, 0))
        self.gallery_file_list = tk.Listbox(file_frame, height=6)
        self.gallery_file_list.pack(side="left", fill="both", expand=True)
        file_scroll = ttk.Scrollbar(file_frame, orient="vertical", command=self.gallery_file_list.yview)
        file_scroll.pack(side="right", fill="y")
        self.gallery_file_list.config(yscrollcommand=file_scroll.set)
        self.gallery_file_list.bind("<Double-Button-1>", self._on_gallery_file_double)

        ttk.Button(gallery_group, text="Galerie aktualisieren", command=self._refresh_gallery).pack(fill="x", pady=(6, 4))
        self.gallery_preview_label = ttk.Label(gallery_group, text="Keine Auswahl")
        self.gallery_preview_label.pack(fill="both", expand=True, padx=6, pady=(0, 6))
        self.gallery_preview_label.bind("<Configure>", self._render_gallery_preview_label)

    def _refresh_gallery(self, highlight_path=None):
        if not self.gallery_tree:
            return
        ensure_folder(self.gallery_root)
        self.gallery_tree.delete(*self.gallery_tree.get_children())
        root_id = self._insert_gallery_node("", self.gallery_root)
        self.gallery_tree.item(root_id, open=True)
        target_dir = os.path.dirname(highlight_path) if highlight_path else self.gallery_root
        self._select_gallery_dir(target_dir)
        if highlight_path:
            self._select_gallery_file(os.path.basename(highlight_path))

    def _insert_gallery_node(self, parent_id, path):
        tree = self.gallery_tree
        text = os.path.basename(path) or path
        node_id = tree.insert(parent_id, "end", text=text, values=(path,))
        try:
            entries = sorted(
                d for d in os.listdir(path)
                if os.path.isdir(os.path.join(path, d))
            )
        except OSError:
            entries = []
        for entry in entries:
            self._insert_gallery_node(node_id, os.path.join(path, entry))
        return node_id

    def _find_gallery_item(self, path):
        if not self.gallery_tree:
            return None
        target = os.path.abspath(path)

        def _search(items):
            for item in items:
                values = self.gallery_tree.item(item, "values")
                if values:
                    current = os.path.abspath(values[0])
                    if current == target:
                        return item
                result = _search(self.gallery_tree.get_children(item))
                if result:
                    return result
            return None

        return _search(self.gallery_tree.get_children(""))

    def _select_gallery_dir(self, path):
        if not self.gallery_tree:
            return
        item = self._find_gallery_item(path)
        if not item:
            return
        self.gallery_tree.selection_set(item)
        self.gallery_tree.see(item)
        values = self.gallery_tree.item(item, "values")
        if values:
            self.gallery_current_dir = values[0]
            self._populate_gallery_files(values[0])

    def _populate_gallery_files(self, directory):
        if not self.gallery_file_list:
            return
        self.gallery_current_dir = directory
        files = []
        try:
            for name in sorted(os.listdir(directory)):
                full = os.path.join(directory, name)
                if os.path.isfile(full) and name.lower().endswith((".png", ".jpg", ".jpeg")):
                    files.append(name)
        except OSError:
            files = []
        self.gallery_file_list.delete(0, "end")
        for name in files:
            self.gallery_file_list.insert("end", name)

    def _on_gallery_dir_select(self, _event=None):
        selection = self.gallery_tree.selection()
        if not selection:
            return
        item = selection[0]
        values = self.gallery_tree.item(item, "values")
        if values:
            self._populate_gallery_files(values[0])

    def _select_gallery_file(self, filename):
        if not self.gallery_file_list:
            return
        for idx in range(self.gallery_file_list.size()):
            if self.gallery_file_list.get(idx) == filename:
                self.gallery_file_list.selection_clear(0, "end")
                self.gallery_file_list.selection_set(idx)
                self.gallery_file_list.see(idx)
                break

    def _on_gallery_file_double(self, _event=None):
        if not self.gallery_file_list:
            return
        selection = self.gallery_file_list.curselection()
        if not selection:
            return
        filename = self.gallery_file_list.get(selection[0])
        path = os.path.join(self.gallery_current_dir, filename)
        self._show_gallery_image_path(path)

    def _show_gallery_image_path(self, path):
        try:
            with Image.open(path) as img:
                display = img.convert("RGB")
                preview = display.copy()
        except Exception as e:
            messagebox.showerror("Galerie", f"Bild konnte nicht geladen werden:\n{e}")
            return

        self._update_preview(preview)
        self._gallery_preview_base = display
        self._render_gallery_preview_label()
        if self.gallery_preview_label:
            self.gallery_preview_label.config(text=os.path.basename(path))

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
        progress = BatchProgress(self, max(1, total_tiles))

        try:
            def _progress_cb(done, total):
                progress.update_progress(done, total)
                self.set_status(f"Mosaik: {done}/{total} Kacheln")

            result = generate_mosaic_from_palette(
                image_path,
                palette_dir,
                cols=grid["cols"],
                rows=grid["rows"],
                progress_cb=_progress_cb
            )
        except Exception as e:
            progress.close()
            messagebox.showerror("Mosaik", str(e))
            self.set_status("Fehler beim Mosaik.")
            return
        finally:
            try:
                progress.close()
            except Exception:
                pass

        self._update_preview(result["image"])
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


class BatchProgress(tk.Toplevel):
    """Einfache Fortschrittsanzeige für Batch-Generierung."""

    def __init__(self, parent, total):
        super().__init__(parent)
        self.total = max(1, total)
        self.title("Batch wird erstellt…")
        self.resizable(False, False)
        self.status_var = tk.StringVar(value="0 / 0")

        frm = ttk.Frame(self, padding=10)
        frm.pack(fill="both", expand=True)

        ttk.Label(frm, text="Fortschritt:").pack(anchor="w")
        self.progress = ttk.Progressbar(frm, maximum=self.total, length=250)
        self.progress.pack(fill="x", pady=4)
        ttk.Label(frm, textvariable=self.status_var).pack(anchor="center")

        self.protocol("WM_DELETE_WINDOW", lambda: None)
        self.transient(parent)
        self.grab_set()

    def update_progress(self, current, total=None):
        if total:
            self.total = total
            self.progress.config(maximum=total)
        self.progress.config(value=current)
        self.status_var.set(f"{current} / {self.total}")
        self.update_idletasks()

    def close(self):
        self.grab_release()
        self.destroy()


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

        def _build_ui(self):
            root = ttk.Frame(self, padding=10)
            root.pack(fill="both", expand=True)

            paned = ttk.Panedwindow(root, orient="horizontal")
            paned.pack(fill="both", expand=True)

            control_area = ttk.Frame(paned)
            preview_area = ttk.Frame(paned, width=360)
            preview_area.pack_propagate(False)
            paned.add(control_area, weight=3)
            paned.add(preview_area, weight=2)

            notebook = ttk.Notebook(control_area)
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

            # --- Preview / Gallery / Log ---
            preview_group = ttk.LabelFrame(preview_area, text="Aktuelle Vorschau")
            preview_group.pack(fill="both", expand=False)
            self.preview_label = ttk.Label(preview_group)
            self.preview_label.pack(fill="both", expand=True, padx=6, pady=6)
            self.preview_label.bind("<Configure>", self._render_preview_label)
            self.preview_label.bind("<Configure>", self._render_preview_label)

            self._build_gallery_controls(preview_area)

            log_group = ttk.LabelFrame(preview_area, text="Log")
            log_group.pack(fill="both", expand=True, pady=(10, 0))
            self.log_text = tk.Text(log_group, height=6, state="disabled")
            self.log_text.pack(fill="both", expand=True)

            self.status_var = tk.StringVar(value="Bereit")
            ttk.Label(preview_area, textvariable=self.status_var, relief="sunken").pack(fill="x", pady=(8, 0))
            self._refresh_gallery()

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

            self._update_preview(last_img)
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

            progress = BatchProgress(self, total)
            self.set_status("Batch wird erstellt…")

            def _progress_cb(current, _total):
                progress.update_progress(current, _total)
                self.set_status(f"Batch: {current}/{_total}")

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
                progress.close()
                messagebox.showerror("Fehler beim Batch", str(e))
                self.set_status("Fehler beim Batch.")
                return

            progress.close()

            if not paths:
                messagebox.showinfo("Keine Raster", "Es wurden keine Raster erzeugt.")
                self.set_status("Keine Raster erzeugt.")
                return

            self._update_preview(last_img)
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

        def _build_ui(self):
            root = ttk.Frame(self, padding=10)
            root.pack(fill="both", expand=True)

            paned = ttk.Panedwindow(root, orient="horizontal")
            paned.pack(fill="both", expand=True)

            control_area = ttk.Frame(paned)
            preview_area = ttk.Frame(paned, width=360)
            preview_area.pack_propagate(False)
            paned.add(control_area, weight=3)
            paned.add(preview_area, weight=2)

            notebook = ttk.Notebook(control_area)
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

            preview_group = ttk.LabelFrame(preview_area, text="Aktuelle Vorschau")
            preview_group.pack(fill="both", expand=False)
            self.preview_label = ttk.Label(preview_group)
            self.preview_label.pack(fill="both", expand=True, padx=6, pady=6)

            self._build_gallery_controls(preview_area)

            log_group = ttk.LabelFrame(preview_area, text="Log")
            log_group.pack(fill="both", expand=True, pady=(10, 0))
            self.log_text = tk.Text(log_group, height=6, state="disabled")
            self.log_text.pack(fill="both", expand=True)

            self.status_var = tk.StringVar(value="Bereit")
            ttk.Label(preview_area, textvariable=self.status_var, relief="sunken").pack(fill="x", pady=(8, 0))
            self._refresh_gallery()

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

            self._update_preview(last_img)
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
                tiles_F, tiles_E, batches_F, batches_E, total = self._prepare_batch(pattern_rows)
            except Exception as e:
                messagebox.showerror("Fehler beim Laden", str(e))
                return

            if total == 0:
                messagebox.showinfo("Keine Raster", "Es wurden keine Raster erzeugt.")
                return

            if not messagebox.askokcancel("Batch starten", f"Es werden {total} Raster erzeugt. Fortfahren?"):
                return

            progress = BatchProgress(self, total)
            self.set_status("Batch wird erstellt…")

            def _progress_cb(current, _total):
                progress.update_progress(current, _total)
                self.set_status(f"Batch: {current}/{_total}")

            try:
                paths, last_img, _ = generate_batch_rasters(
                    pattern_rows,
                    tiles_F,
                    tiles_E,
                    shuffle_tiles=self.shuffle_var.get(),
                    batches_F=batches_F,
                    batches_E=batches_E,
                    progress_cb=_progress_cb,
                    log_cb=self.log_message
                )
            except Exception as e:
                progress.close()
                messagebox.showerror("Fehler beim Batch", str(e))
                self.set_status("Fehler beim Batch.")
                return

            progress.close()

            if not paths:
                messagebox.showinfo("Keine Raster", "Es wurden keine Raster erzeugt.")
                self.set_status("Keine Raster erzeugt.")
                return

            self._update_preview(last_img)
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
            result = generate_palette_tile_set(args.palette_folder, palette_size, prefix="cli_palette_tile_")
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
