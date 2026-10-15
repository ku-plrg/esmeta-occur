#!/usr/bin/env python3

import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import matplotlib as mpl
from pathlib import Path
import argparse

# Optional caps: values >= cap are binned into the last cell (labeled "N+")
_args = argparse.ArgumentParser()
_args.add_argument("--cap-size", type=int, default=None)
_args.add_argument("--cap-leaf", type=int, default=None)
CAPS = {"Size": _args.parse_args().cap_size, "Leaf Count": _args.parse_args().cap_leaf}

# Publication-friendly font & proper PDF embedding
mpl.rcParams["pdf.fonttype"] = 42             # embed TrueType glyphs
plt.rc("font", size=7)

# Each heatmap is printed at about 1.8 in wide (a third of the text width),
# so it is drawn at that size: colors only (no numbers), white for zero
# cells, a log color scale, and a slim color bar.
FIG_SIZE = (1.8, 1.75)
# Skip the palest part of YlGnBu so that a count of 1 is still visible
CMAP = mpl.colors.LinearSegmentedColormap.from_list(
    "YlGnBu_trunc", mpl.colormaps["YlGnBu"](np.linspace(0.15, 1.0, 256)))
CMAP.set_under("white")                       # zero cells are white

def make_heatmap(csv_path: Path, x_name: str, y_name: str, pdf_path: Path) -> None:
    """Read three-column CSV (x, y, count) and save a log-scaled heatmap."""
    df = pd.read_csv(csv_path, header=None, names=[x_name, y_name, "cnt"])

    # Ensure numeric; drop rows without valid x/y; counts default to 0 if bad
    df[x_name] = pd.to_numeric(df[x_name], errors="coerce")
    df[y_name] = pd.to_numeric(df[y_name], errors="coerce")
    df["cnt"]  = pd.to_numeric(df["cnt"],  errors="coerce").fillna(0)
    df = df.dropna(subset=[x_name, y_name])
    for col in (x_name, y_name):
        if CAPS.get(col) is not None:
            df[col] = df[col].clip(upper=CAPS[col])
    df = df.groupby([x_name, y_name], as_index=False)["cnt"].sum()

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
    ).to_numpy()

    # Fixed axes positions so that all heatmaps have the same size on paper
    fig = plt.figure(figsize=FIG_SIZE)
    ax = fig.add_axes([0.20, 0.16, 0.64, 0.82])
    cax = fig.add_axes([0.86, 0.16, 0.035, 0.82])
    vmax = max(hm.max(), 10)
    im = ax.imshow(
        hm, cmap=CMAP, origin="lower", aspect="auto",
        norm=mpl.colors.LogNorm(vmin=1, vmax=vmax),   # zero cells fall below vmin
        extent=(x_min - 0.5, x_max + 0.5, y_min - 0.5, y_max + 0.5),
    )
    # Thin grid lines between cells
    ax.set_xticks(np.arange(x_min, x_max + 1) - 0.5, minor=True)
    ax.set_yticks(np.arange(y_min, y_max + 1) - 0.5, minor=True)
    ax.grid(which="minor", color="#cccccc", linewidth=0.3)
    ax.tick_params(which="minor", length=0)
    ax.tick_params(which="major", length=2, pad=1)

    # Label every integer when there are few, every other one otherwise
    def ticks(vals, name):
        cap = CAPS.get(name)
        step = 1 if len(vals) <= 10 else (2 if len(vals) <= 14 else 4)
        shown = [v for v in vals if (v - vals[0]) % step == 0]
        if shown[-1] != vals[-1]:             # always label the capped last cell
            shown[-1] = vals[-1]
        labels = [f"{v}+" if cap is not None and v == cap else str(v) for v in shown]
        return shown, labels
    xt, xl = ticks(x_vals, x_name)
    yt, yl = ticks(y_vals, y_name)
    ax.set_xticks(xt); ax.set_xticklabels(xl)
    ax.set_yticks(yt); ax.set_yticklabels(yl)
    ax.set_xlabel(x_name, labelpad=1)
    ax.set_ylabel(y_name, labelpad=1)
    for side in ax.spines.values():
        side.set_linewidth(0.4)

    cbar = fig.colorbar(im, cax=cax)
    cbar.ax.tick_params(length=2, pad=1, labelsize=6)
    cbar.ax.minorticks_off()
    cbar.outline.set_linewidth(0.4)
    fig.savefig(pdf_path)
    plt.close(fig)

# === Generate all three heatmaps ============================================
tasks = [
    ("provenance-size-depth", ("Size",  "Depth"),   "heatmap-size-depth.pdf"),
    ("provenance-depth-leaf", ("Depth", "Leaf Count"), "heatmap-depth-leaf.pdf"),
    ("provenance-size-leaf",  ("Size",  "Leaf Count"), "heatmap-size-leaf.pdf"),
]

for csv, (x, y), pdf in tasks:
    make_heatmap(Path(csv), x, y, Path(pdf))

print("PDFs written.")
