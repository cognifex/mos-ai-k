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
    max_cols = max(1, width // tile_w)
    max_rows = max(1, height // tile_h)
    aspect = height / width if width else 1

    candidates = []
    preset_cols = [32, 48, 64, 80, 96, 128, 160, 192, 224, 256, 320, 384, 448, 512, 640]
    for col in preset_cols:
        if col <= max_cols:
            candidates.append(col)
    if max_cols not in candidates:
        candidates.append(max_cols)
    if not candidates:
        candidates = [max_cols]

    unique = []
    seen = set()
    for col in sorted(candidates):
        if col <= 0:
            continue
        if col in seen:
            continue
        seen.add(col)
        row = max(1, int(round(col * aspect)))
        if row > max_rows:
            row = max_rows
        unique.append({"cols": col, "rows": row})
        if len(unique) >= max_options:
            break

    if not unique:
        unique = [{"cols": 1, "rows": max(1, int(round(aspect)))}]

    for opt in unique:
        total_tiles = opt["cols"] * opt["rows"]
        opt["label"] = f"{opt['cols']} x {opt['rows']} Tiles (~{total_tiles} Kacheln)"
    return unique


def generate_mosaic_from_palette(image_path, palette_dir, cols=None, rows=None, prefix="mosaic_"):
    entries = load_palette_tile_images(palette_dir)
    if not entries:
        raise ValueError("Keine Palette-Kacheln gefunden.")
    tile_w, tile_h = entries[0]["image"].size
    with Image.open(image_path) as img:
        target = img.convert("RGB")
    width, height = target.size
    if cols is None and rows is None:
        cols = max(1, width // tile_w)
    if cols is None:
        cols = max(1, int(round(rows * width / height)))
    if rows is None:
        rows = max(1, int(round(cols * height / width)))

    small = target.resize((cols, rows), Image.LANCZOS)
    mosaic = Image.new("RGB", (cols * tile_w, rows * tile_h))

    for y in range(rows):
        for x in range(cols):
            color = small.getpixel((x, y))
            best = min(entries, key=lambda e: _color_distance_sq(color, e["color"]))
            mosaic.paste(best["image"], (x * tile_w, y * tile_h))

    out_path = unique_output_path(prefix=prefix)
    mosaic.save(out_path)
    return {
        "path": out_path,
        "cols": cols,
        "rows": rows,
        "tile_size": (tile_w, tile_h),
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


# --------------------------------------------------------
# GUI-Basisklasse
# --------------------------------------------------------

class RasterAppBase:
    def __init__(self):
        self.drop_paths = []
        self.pattern_text_default = "EFEFE\nFEFEF\nEFEFE\nFEFEF\nEFEFE\nFEFEF"
        self.shuffle_var = None
        self.category_var = None
        self.preview_image = None
        self.last_dir = os.getcwd()
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
        self.gallery_listbox = None
        self.gallery_items = []
        self.gallery_preview_label = None
        self.gallery_preview_image = None

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
            self.last_dir = os.path.dirname(files[0])
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
        rows = [line.strip() for line in pattern_text.splitlines() if line.strip()]
        return rows

    def _generate_images(self, pattern_rows, batch=False):
        tiles_F, tiles_E = self._load_tiles()
        shuffle = self.shuffle_var.get() if self.shuffle_var else False
        if batch:
            paths, last_img, _ = generate_batch_rasters(
                pattern_rows,
                tiles_F,
                tiles_E,
                shuffle_tiles=shuffle,
                log_cb=self.log_message
            )
            return paths, last_img
        img = build_raster(pattern_rows, tiles_F, tiles_E, shuffle_tiles=shuffle)
        out_path = unique_output_path()
        img.save(out_path)
        return [out_path], img

    def _prepare_batch(self, pattern_rows):
        tiles_F, tiles_E = self._load_tiles()
        batches_F, batches_E = prepare_batches(pattern_rows, tiles_F, tiles_E)
        total = len(batches_F) * len(batches_E)
        return tiles_F, tiles_E, batches_F, batches_E, total

    def _update_preview(self, img):
        if img is None or not self.preview_label:
            return
        max_w, max_h = 600, 600
        scale = min(max_w / img.width, max_h / img.height, 1.0)
        new_size = (int(img.width * scale), int(img.height * scale))
        show_img = img.resize(new_size, Image.LANCZOS)
        self.preview_image = ImageTk.PhotoImage(show_img)
        self.preview_label.config(image=self.preview_image)

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
            self.last_dir = folder

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
            f"Metadata: {result['metadata']}"
        )
        self.log_message(summary)
        messagebox.showinfo("Palette erzeugt", summary)
        self._add_to_gallery(result.get("preview_path"), f"Palette {result['count']} Farben", result["palette_image"])

    def _update_palette_preview(self, img):
        if img is None or not self.palette_preview_label:
            return
        max_w, max_h = 400, 200
        scale = min(max_w / img.width, max_h / img.height, 1.0)
        new_size = (int(img.width * scale), int(img.height * scale))
        show_img = img.resize(new_size, Image.LANCZOS)
        self.palette_preview_image = ImageTk.PhotoImage(show_img)
        self.palette_preview_label.config(image=self.palette_preview_image)

    def _add_to_gallery(self, path, label, pil_image):
        if not self.gallery_listbox or pil_image is None:
            return
        entry = {
            "path": path,
            "label": label or os.path.basename(path or ""),
            "image": pil_image.copy(),
        }
        self.gallery_items.append(entry)
        self.gallery_listbox.insert("end", entry["label"])
        self.gallery_listbox.selection_clear(0, "end")
        last = self.gallery_listbox.size() - 1
        if last >= 0:
            self.gallery_listbox.selection_set(last)
            self.gallery_listbox.see(last)
            self._show_gallery_item(entry)

    def _on_gallery_select(self, _event=None):
        if not self.gallery_listbox:
            return
        selection = self.gallery_listbox.curselection()
        if not selection:
            return
        idx = selection[0]
        if 0 <= idx < len(self.gallery_items):
            self._show_gallery_item(self.gallery_items[idx])

    def _show_gallery_item(self, entry):
        if not self.gallery_preview_label:
            return
        img = entry.get("image")
        if img is None and entry.get("path") and os.path.isfile(entry["path"]):
            img = Image.open(entry["path"]).convert("RGB")
            entry["image"] = img
        if img is None:
            return
        max_w, max_h = 300, 200
        scale = min(max_w / img.width, max_h / img.height, 1.0)
        new_size = (int(img.width * scale), int(img.height * scale))
        show_img = img.resize(new_size, Image.LANCZOS)
        self.gallery_preview_image = ImageTk.PhotoImage(show_img)
        self.gallery_preview_label.config(image=self.gallery_preview_image, text=entry.get("label", ""))

    def _select_mosaic_image(self):
        path = filedialog.askopenfilename(
            title="Mosaik-Quellbild auswählen",
            filetypes=[("Bilder", "*.png *.jpg *.jpeg"), ("Alle Dateien", "*.*")]
        )
        if path and self.mosaic_image_var:
            self.mosaic_image_var.set(path)
            self._update_mosaic_resolution_options()

    def _select_mosaic_palette(self):
        folder = filedialog.askdirectory(title="Palette-Ordner auswählen")
        if folder and self.mosaic_palette_var:
            self.mosaic_palette_var.set(folder)
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
        self.set_status("Mosaik wird generiert…")
        try:
            result = generate_mosaic_from_palette(
                image_path,
                palette_dir,
                cols=grid["cols"],
                rows=grid["rows"]
            )
        except Exception as e:
            messagebox.showerror("Mosaik", str(e))
            self.set_status("Fehler beim Mosaik.")
            return

        self._update_preview(result["image"])
        summary = (
            f"Mosaik gespeichert als: {result['path']} "
            f"({result['cols']} x {result['rows']} Tiles)"
        )
        self.log_message(summary)
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

            main = ttk.Frame(root)
            main.pack(fill="both", expand=True)

            control_area = ttk.Frame(main)
            control_area.pack(side="left", fill="both", expand=True, padx=(0, 10))

            preview_area = ttk.Frame(main, width=320)
            preview_area.pack(side="right", fill="y")
            preview_area.pack_propagate(False)

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
            ttk.Label(raster_tab, text="Muster (E/F pro Zeile):").pack(anchor="w")
            self.pattern_box = tk.Text(raster_tab, height=8)
            self.pattern_box.insert("1.0", self.pattern_text_default)
            self.pattern_box.pack(fill="both", expand=True, pady=(0, 6))

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

            self.palette_folder_var = tk.StringVar()
            folder_row = ttk.Frame(palette_frame)
            folder_row.pack(fill="x", pady=2)
            ttk.Label(folder_row, text="Ordner:").pack(side="left")
            ttk.Entry(folder_row, textvariable=self.palette_folder_var).pack(side="left", fill="x", expand=True, padx=4)
            ttk.Button(folder_row, text="…", width=3, command=self._select_palette_folder).pack(side="left")

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

            mosaic_frame = ttk.LabelFrame(palette_tab, text="Bild → Kachelmosaik")
            mosaic_frame.pack(fill="both", expand=True)

            self.mosaic_image_var = tk.StringVar()
            img_row = ttk.Frame(mosaic_frame)
            img_row.pack(fill="x", pady=2)
            ttk.Label(img_row, text="Bild:").pack(side="left")
            ttk.Entry(img_row, textvariable=self.mosaic_image_var).pack(side="left", fill="x", expand=True, padx=4)
            ttk.Button(img_row, text="…", width=3, command=self._select_mosaic_image).pack(side="left")

            self.mosaic_palette_var = tk.StringVar()
            pal_row = ttk.Frame(mosaic_frame)
            pal_row.pack(fill="x", pady=2)
            ttk.Label(pal_row, text="Palette:").pack(side="left")
            ttk.Entry(pal_row, textvariable=self.mosaic_palette_var).pack(side="left", fill="x", expand=True, padx=4)
            ttk.Button(pal_row, text="…", width=3, command=self._select_mosaic_palette).pack(side="left")

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

            gallery_group = ttk.LabelFrame(preview_area, text="Galerie")
            gallery_group.pack(fill="both", expand=True, pady=(10, 0))
            gallery_inner = ttk.Frame(gallery_group)
            gallery_inner.pack(fill="both", expand=True)
            self.gallery_listbox = tk.Listbox(gallery_inner, height=6)
            self.gallery_listbox.pack(side="left", fill="both", expand=True)
            gallery_scroll = ttk.Scrollbar(gallery_inner, orient="vertical", command=self.gallery_listbox.yview)
            gallery_scroll.pack(side="right", fill="y")
            self.gallery_listbox.config(yscrollcommand=gallery_scroll.set)
            self.gallery_listbox.bind("<<ListboxSelect>>", self._on_gallery_select)
            self.gallery_preview_label = ttk.Label(gallery_group)
            self.gallery_preview_label.pack(fill="both", expand=True, padx=6, pady=(6, 0))

            log_group = ttk.LabelFrame(preview_area, text="Log")
            log_group.pack(fill="both", expand=True, pady=(10, 0))
            self.log_text = tk.Text(log_group, height=6, state="disabled")
            self.log_text.pack(fill="both", expand=True)

            self.status_var = tk.StringVar(value="Bereit")
            ttk.Label(preview_area, textvariable=self.status_var, relief="sunken").pack(fill="x", pady=(8, 0))

            mosaic_frame = ttk.LabelFrame(frm, text="Mosaik aus Palette")
            mosaic_frame.pack(fill="both", expand=True, pady=(10, 0))

            self.mosaic_image_var = tk.StringVar()
            img_row = ttk.Frame(mosaic_frame)
            img_row.pack(fill="x", pady=2)
            ttk.Label(img_row, text="Bild:").pack(side="left")
            ttk.Entry(img_row, textvariable=self.mosaic_image_var).pack(side="left", fill="x", expand=True, padx=4)
            ttk.Button(img_row, text="…", width=3, command=self._select_mosaic_image).pack(side="left")

            self.mosaic_palette_var = tk.StringVar()
            pal_row = ttk.Frame(mosaic_frame)
            pal_row.pack(fill="x", pady=2)
            ttk.Label(pal_row, text="Palette:").pack(side="left")
            ttk.Entry(pal_row, textvariable=self.mosaic_palette_var).pack(side="left", fill="x", expand=True, padx=4)
            ttk.Button(pal_row, text="…", width=3, command=self._select_mosaic_palette).pack(side="left")

            self.mosaic_resolution_var = tk.StringVar()
            ttk.Label(mosaic_frame, text="Auflösung:").pack(anchor="w")
            self.mosaic_resolution_box = ttk.Combobox(
                mosaic_frame,
                textvariable=self.mosaic_resolution_var,
                state="readonly"
            )
            self.mosaic_resolution_box.pack(fill="x", pady=2)
            ttk.Button(mosaic_frame, text="Auflösungen aktualisieren", command=self._update_mosaic_resolution_options).pack(fill="x", pady=2)
            ttk.Button(mosaic_frame, text="Mosaik generieren", command=self._generate_mosaic_image).pack(fill="x", pady=4)

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
                self._add_to_gallery(paths[-1], "Raster", last_img)
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
                self._add_to_gallery(paths[-1], f"Batch ({len(paths)})", last_img)
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
            frm = ttk.Frame(self, padding=10)
            frm.pack(fill="both", expand=True)

            self.category_var = tk.StringVar(value="F")
            ttk.Label(frm, text="Kategorie für Sortierung (F oder E):").pack(anchor="w")
            ttk.Combobox(frm, textvariable=self.category_var, values=["F", "E"]).pack(fill="x")

            ttk.Label(frm, text="Dateien auswählen (Drag & Drop nicht verfügbar):").pack(anchor="w")
            ttk.Button(frm, text="Dateien auswählen", command=self._select_files_dialog).pack(fill="x", pady=5)
            ttk.Button(frm, text="Sortieren & umbenennen", command=self._on_sort).pack(fill="x", pady=5)

            ttk.Label(frm, text="Muster (E/F, eine Zeile pro Zeile):").pack(anchor="w", pady=(10, 0))
            self.pattern_box = tk.Text(frm, height=6)
            self.pattern_box.insert("1.0", self.pattern_text_default)
            self.pattern_box.pack(fill="both")

            self.shuffle_var = tk.BooleanVar(value=False)
            ttk.Checkbutton(
                frm,
                text="Shuffle Tiles (zufällige Reihenfolge)",
                variable=self.shuffle_var
            ).pack(anchor="w", pady=4)

            ttk.Button(frm, text="Raster generieren", command=self._on_generate).pack(fill="x", pady=5)
            ttk.Button(frm, text="Alle Raster exportieren (Batch)", command=self._on_generate_all).pack(fill="x")

            self.preview_label = ttk.Label(frm)
            self.preview_label.pack(fill="both", expand=True, pady=10)

            ttk.Label(frm, text="Log:").pack(anchor="w")
            self.log_text = tk.Text(frm, height=6, state="disabled")
            self.log_text.pack(fill="both", expand=True, pady=(0, 6))

            self.status_var = tk.StringVar(value="Bereit")
            ttk.Label(frm, textvariable=self.status_var, relief="sunken").pack(fill="x")

            palette_frame = ttk.LabelFrame(frm, text="Farbspektrum")
            palette_frame.pack(fill="both", expand=True, pady=(10, 0))

            self.palette_folder_var = tk.StringVar()
            folder_row = ttk.Frame(palette_frame)
            folder_row.pack(fill="x", pady=4)
            ttk.Label(folder_row, text="Ordner:").pack(side="left")
            ttk.Entry(folder_row, textvariable=self.palette_folder_var).pack(side="left", fill="x", expand=True, padx=4)
            ttk.Button(folder_row, text="…", width=3, command=self._select_palette_folder).pack(side="left")

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
                self._add_to_gallery(paths[-1], "Raster", last_img)
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
                self._add_to_gallery(paths[-1], f"Batch ({len(paths)})", last_img)
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
