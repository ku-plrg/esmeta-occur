# Draw Fig. 17: line charts of iterations and analysis time per version
# for Syn / Ours_Bool / Ours_Full, in the style of the precision chart (Fig. 16 (g)).
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.ticker
import pandas as pd
import os

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "result")
OUT = os.path.join(HERE, "fig", "perf")

SERIES = [
    ("syn", "Syn", "#1f77b4", ":"),
    ("boolean", "Bool", "#ff7f0e", "--"),
    ("our", "Full", "#7030a0", "-"),
]

plt.rc("font", size=9)

def load(name):
    df = pd.read_csv(os.path.join(ROOT, name, "summary.tsv"), sep="\t")
    df = df.dropna(subset=["iter"])
    return df

def draw(column, ylabel, fname):
    fig, ax = plt.subplots(figsize=(3.2, 2.3))
    for name, label, color, style in SERIES:
        df = load(name)
        ax.plot(df["#"], df[column], color=color, linestyle=style, linewidth=1.5, label=label)
    ax.set_xlabel("version")
    ax.set_ylabel(ylabel)
    ax.set_xlim(0, 252)
    ax.set_xticks(range(0, 253, 40))
    ax.set_ylim(bottom=0)
    ax.yaxis.set_major_formatter(matplotlib.ticker.FuncFormatter(lambda v, _: f"{int(v):,}"))
    ax.grid(axis="y", color="#dddddd", linewidth=0.5)
    ax.set_ylim(top=ax.get_ylim()[1] * 1.25)
    ax.legend(ncol=3, loc="upper center", frameon=False, handlelength=2.2, columnspacing=1.0, fontsize=8)
    fig.tight_layout()
    os.makedirs(OUT, exist_ok=True)
    fig.savefig(os.path.join(OUT, fname))
    plt.close(fig)

draw("iter", "# iterations", "iter.pdf")
draw("duration (ms)", "time (ms)", "time.pdf")
