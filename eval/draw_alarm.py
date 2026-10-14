# Draw Fig. 16 from raw data: (a)-(f) TP/FP alarms per version for each setting,
# (g) precision lines. Inputs: ../result/<setting>/summary.tsv and ../tp.tsv
# (the number of true positives per version, classified by hand).
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import pandas as pd
import os

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "result")
TP = os.path.join(HERE, "tp.tsv")
OUT = os.path.join(HERE, "fig")

# (result dir, output name, legend label, color, line style)
SETTINGS = [
    ("base", "base", "Base", None, None),
    ("syn", "syn", "Syn", "#1f77b4", ":"),
    ("pre", "no-mut", "NoMut", "#d62728", "-."),
    ("boolean", "bool", "Bool", "#ff7f0e", "--"),
    ("our", "full", "Full", "#7030a0", "-"),
    ("inval", "flow", "Inval", "#7f7f7f", (0, (5, 2, 1, 2))),
]
TP_COLOR = "#196b24"
FP_COLOR = "#c00000"

plt.rc("font", size=9)
tp = pd.read_csv(TP, sep="\t")["tp"].values

def load(name):
    df = pd.read_csv(os.path.join(ROOT, name, "summary.tsv"), sep="\t")
    return df.dropna(subset=["# errors"])

def xaxis(ax):
    ax.set_xlabel("version")
    ax.set_xlim(0, 252)
    ax.set_xticks(range(0, 253, 40))

def draw_alarm(name, out):
    df = load(name)
    x = df["#"].values
    alarms = df["# errors"].values
    fp = alarms - tp
    fig, ax = plt.subplots(figsize=(3.2, 2.3))
    ax.fill_between(x, 0, tp, color=TP_COLOR, label="TP", step="mid")
    ax.fill_between(x, tp, alarms, facecolor="white", edgecolor=FP_COLOR,
                    hatch="//////", linewidth=0.5, label="FP", step="mid")
    xaxis(ax)
    ax.set_ylabel("# alarms")
    ax.set_ylim(0, alarms.max() * 1.25)
    ax.yaxis.set_major_locator(matplotlib.ticker.MaxNLocator(8, steps=[1, 2, 5, 10]))
    ax.legend(ncol=2, loc="upper right", frameon=False)
    fig.tight_layout()
    os.makedirs(os.path.join(OUT, "alarm"), exist_ok=True)
    fig.savefig(os.path.join(OUT, "alarm", out + ".pdf"))
    plt.close(fig)

def draw_prec():
    fig, ax = plt.subplots(figsize=(3.2, 2.3))
    for name, _, label, color, style in SETTINGS:
        if color is None:
            continue
        df = load(name)
        prec = tp / df["# errors"].values * 100
        ax.plot(df["#"], prec, color=color, linestyle=style, linewidth=1.5, label=label)
    xaxis(ax)
    ax.set_ylabel("precision (%)")
    ax.set_ylim(0, 75)
    ax.set_yticks(range(0, 71, 10))
    ax.yaxis.set_major_formatter(matplotlib.ticker.FuncFormatter(lambda v, _: f"{int(v)}%"))
    ax.legend(ncol=3, loc="upper right", frameon=False, handlelength=2.2,
              columnspacing=1.0, fontsize=8)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "prec.pdf"))
    plt.close(fig)

for name, out, *_ in SETTINGS:
    draw_alarm(name, out)
draw_prec()
