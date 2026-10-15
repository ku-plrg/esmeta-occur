# Draw Fig. 12: line charts of iterations and analysis time per version
# for Syn / Ours_Bool / Ours, in the style of the precision chart (Fig. 11 (g)).
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.ticker
import pandas as pd
import os

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "result")
OUT = os.path.join(HERE, "fig", "perf")

# (result dir, legend label, color, line style, marker), as in draw_alarm.py
SERIES = [
    ("syn", "Syn", "#1f77b4", ":", "o"),
    ("boolean", r"Ours$_\mathsf{Bool}$", "#d4a05a", "--", "^"),
    ("our", "Ours", "#196b24", "-", "s"),
]

# Figure size matches the printed size (.49 of the 5.5 in text width).
PERF_SIZE = (2.7, 1.5)
plt.rc("font", size=7)

def load(name):
    df = pd.read_csv(os.path.join(ROOT, name, "summary.tsv"), sep="\t")
    df = df.dropna(subset=["iter"])
    return df

def draw(column, fname, lo):
    """Draw one chart; `lo` is the lower bound of the (zoomed) y-axis."""
    fig, ax = plt.subplots(figsize=PERF_SIZE)
    for i, (name, label, color, style, marker) in enumerate(SERIES):
        df = load(name)
        ax.plot(df["#"], df[column], color=color, linestyle=style, linewidth=(1.4 if label == "Ours" else 1.0),
                marker=marker, markersize=4, markevery=(5 * i, 16),
                markerfacecolor=(color if label == "Ours" else "white"), markeredgewidth=0.8, label=label,
                zorder=3 if name == "boolean" else 2)
    # The x-axis (version) and the quantity are explained in the captions.
    ax.set_xlim(0, 252)
    ax.set_xticks(range(0, 253, 40))
    hi = max(load(name)[column].max() for name, *_ in SERIES)
    ax.set_ylim(lo, hi + (hi - lo) * 0.3)   # leave room for the legend
    ax.yaxis.set_major_formatter(matplotlib.ticker.FuncFormatter(lambda v, _: f"{int(v):,}"))
    ax.grid(axis="y", color="#dddddd", linewidth=0.5)
    ax.legend(ncol=3, loc="upper center", frameon=False, handlelength=2.2, columnspacing=1.0, fontsize=7)
    os.makedirs(OUT, exist_ok=True)
    fig.savefig(os.path.join(OUT, fname), bbox_inches="tight", pad_inches=0.02)
    plt.close(fig)

draw("iter", "iter.pdf", 80000)
draw("duration (ms)", "time.pdf", 4000)
