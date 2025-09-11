#!/usr/bin/env python3
"""
Generate log-scaled heatmaps (square figure, bigger text, no legend)
from the three count tables:

  provenance-size-depth → heatmap_size_depth.pdf
  provenance-depth-leaf → heatmap_depth_leafcnt.pdf
  provenance-size-leaf  → heatmap_size_leafcnt.pdf
"""

import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns
import matplotlib as mpl
from pathlib import Path

# Publication-friendly font & proper PDF embedding
mpl.rcParams["font.family"] = "Helvetica"     # fallback to Arial if missing
mpl.rcParams["pdf.fonttype"] = 42             # embed TrueType glyphs

def make_heatmap(csv_path: Path, x_name: str, y_name: str, pdf_path: Path) -> None:
    """Read three-column CSV (x, y, count) and save a log-scaled heatmap."""
    df = pd.read_csv(csv_path, header=None, names=[x_name, y_name, "cnt"])

    # Ensure numeric; drop rows without valid x/y; counts default to 0 if bad
    df[x_name] = pd.to_numeric(df[x_name], errors="coerce")
    df[y_name] = pd.to_numeric(df[y_name], errors="coerce")
    df["cnt"]  = pd.to_numeric(df["cnt"],  errors="coerce").fillna(0)
    df = df.dropna(subset=[x_name, y_name])

    # Define full integer ranges so no "middle" labels are skipped
    x_min, x_max = int(df[x_name].min()), int(df[x_name].max())
    y_min, y_max = int(df[y_name].min()), int(df[y_name].max())
    x_vals = np.arange(x_min, x_max + 1)
    y_vals = np.arange(y_min, y_max + 1)

    # Build a complete grid (y, x), fill missing pairs with 0
    grid = pd.MultiIndex.from_product([y_vals, x_vals], names=[y_name, x_name])
    hm = (
        df.set_index([y_name, x_name])["cnt"]
          .reindex(grid, fill_value=0)
          .unstack(level=1)  # columns = x
    )

    # Log scale of counts for color; zeros stay 0 after log1p
    log_hm = np.log1p(hm)

    # Mask only the (min y, min x) cell so it's blank; everything else shows
    mask = np.zeros_like(log_hm, dtype=bool)
    mask[0, 0] = True

    plt.figure(figsize=(6, 6))    # square figure
    ax = sns.heatmap(
        log_hm,
        mask=mask,
        annot=hm.to_numpy(),       # annotate with original counts, including zeros
        fmt=".0f",
        cmap="viridis_r",          # low = bright, high = dark
        cbar=False,                # remove legend
        annot_kws={"size": 12},
        vmin=0                     # ensure zeros map to the lowest color, not "bad"
    )

    # Put lower values at bottom (like your original)
    ax.invert_yaxis()

    # Force every tick to render; no skipping in the middle
    ax.set_xticks(np.arange(len(x_vals)) + 0.5)
    ax.set_yticks(np.arange(len(y_vals)) + 0.5)
    ax.set_xticklabels(x_vals, rotation=0)
    ax.set_yticklabels(y_vals, rotation=0)

    ax.set_xlabel(x_name, fontsize=14)
    ax.set_ylabel(y_name, fontsize=14)
    ax.tick_params(axis="both", labelsize=12)
    plt.tight_layout()
    plt.savefig(pdf_path)
    plt.close()

# === Generate all three heatmaps ============================================
tasks = [
    ("provenance-size-depth", ("Size",  "Depth"),   "heatmap-size-depth.pdf"),
    ("provenance-depth-leaf", ("Depth", "Leafcnt"), "heatmap-depth-leaf.pdf"),
    ("provenance-size-leaf",  ("Size",  "Leafcnt"), "heatmap-size-leaf.pdf"),
]

for csv, (x, y), pdf in tasks:
    make_heatmap(Path(csv), x, y, Path(pdf))

print("PDFs written.")
