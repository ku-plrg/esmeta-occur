#!/usr/bin/env python3
"""
Generate log‑scaled heatmaps (square figure, bigger text, no legend)
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

# Publication‑friendly font & proper PDF embedding
mpl.rcParams["font.family"] = "Helvetica"     # fallback to Arial if missing
mpl.rcParams["pdf.fonttype"] = 42             # embed TrueType glyphs

def make_heatmap(csv_path: Path, x_name: str, y_name: str, pdf_path: Path) -> None:
    """Read three‑column CSV (x, y, count) and save a log‑scaled heatmap."""
    df = pd.read_csv(csv_path, header=None, names=[x_name, y_name, "cnt"])

    # Pivot to matrix (missing pairs → 0)
    hm = (
        df.pivot(index=y_name, columns=x_name, values="cnt")
          .sort_index()           # ascending order for axes
          .sort_index(axis=1)
          .fillna(0)
    )

    # Ignore the top‑left cell (min x, min y)
    hm.loc[hm.index.min(), hm.columns.min()] = np.nan

    log_hm = np.log1p(hm)         # log–scale (log(1+cnt))

    plt.figure(figsize=(6, 6))    # square figure
    ax = sns.heatmap(
        log_hm,
        annot=hm,                 # show original counts
        fmt=".0f",
        cmap="viridis_r",         # low = bright, high = dark
        cbar=False,               # remove legend
        annot_kws={"size": 12}
    )
    ax.invert_yaxis()             # lower values at bottom
    ax.set_xlabel(x_name,  fontsize=14)
    ax.set_ylabel(y_name,  fontsize=14)
    # ax.set_title(f"Log‑scaled heatmap of ({x_name}, {y_name})", fontsize=16)
    ax.tick_params(axis="both", labelsize=12)
    plt.tight_layout()
    plt.savefig(pdf_path)
    plt.close()

# === Generate all three heatmaps ============================================
tasks = [
    ("provenance-size-depth", ("Size",  "Depth"),   "heatmap_size_depth.pdf"),
    ("provenance-depth-leaf", ("Depth", "Leafcnt"), "heatmap_depth_leafcnt.pdf"),
    ("provenance-size-leaf",  ("Size",  "Leafcnt"), "heatmap_size_leafcnt.pdf"),
]

for csv, (x, y), pdf in tasks:
    make_heatmap(Path(csv), x, y, Path(pdf))

print("PDFs written.")

