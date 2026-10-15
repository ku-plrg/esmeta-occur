# Draw Fig. 11 from raw data: (a)-(f) TP/FP alarms per version for each setting,
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
TP_COLOR = "#196b24"
FP_COLOR = "#c00000"

# (result dir, output name, legend label, color, line style, marker)
SETTINGS = [
    ("base", "base", "Base", "#000000", (0, (1, 1)), "x"),
    ("syn", "syn", "Syn", "#1f77b4", ":", "o"),
    ("our", "full", "Ours", TP_COLOR, "-", "s"),
    ("boolean", "bool", r"Ours$_\mathsf{Bool}$", "#d4a05a", "--", "^"),
    ("pre", "no-mut", r"Ours$_\mathsf{NoMut}$", "#d62728", "-.", "v"),
    ("inval", "flow", r"Ours$_\mathsf{Inval}$", "#7f7f7f", (0, (5, 2, 1, 2)), "d"),
]
# Figure sizes match the printed sizes in the paper (text width 5.5 in):
# (a)-(f) at .32 of the text width and (g) at .62 of the text width.
ALARM_SIZE = (1.76, 1.05)
PREC_SIZE = (3.41, 1.7)
SAVE = dict(bbox_inches="tight", pad_inches=0.02)

plt.rc("font", size=7)
tp = pd.read_csv(TP, sep="\t")["tp"].values

def load(name):
    df = pd.read_csv(os.path.join(ROOT, name, "summary.tsv"), sep="\t")
    return df.dropna(subset=["# errors"])

def xaxis(ax):
    # The x-axis (version) is explained in the caption.
    ax.set_xlim(0, 252)
    ax.set_xticks(range(0, 253, 40))

def draw_alarm(name, out):
    df = load(name)
    x = df["#"].values
    alarms = df["# errors"].values
    fp = alarms - tp
    fig, ax = plt.subplots(figsize=ALARM_SIZE)
    ax.fill_between(x, 0, tp, color=TP_COLOR, label="TP", step="mid")
    ax.fill_between(x, tp, alarms, facecolor="white", edgecolor=FP_COLOR,
                    hatch="//////", linewidth=0.5, label="FP", step="mid")
    xaxis(ax)
    ax.set_ylim(0, alarms.max() * 1.25)
    ax.yaxis.set_major_locator(matplotlib.ticker.MaxNLocator(8, steps=[1, 2, 5, 10]))
    ax.legend(ncol=2, loc="upper right", frameon=False, fontsize=6.5,
              handlelength=1.5, columnspacing=0.8)
    os.makedirs(os.path.join(OUT, "alarm"), exist_ok=True)
    fig.savefig(os.path.join(OUT, "alarm", out + ".pdf"), **SAVE)
    plt.close(fig)

def draw_prec():
    fig, ax = plt.subplots(figsize=PREC_SIZE)
    lines = []  # (average precision, line) to order the legend by precision
    for i, (name, _, label, color, style, marker) in enumerate(SETTINGS):
        df = load(name)
        prec = tp / df["# errors"].values * 100
        (line,) = ax.plot(df["#"], prec, color=color, linestyle=style, linewidth=(1.4 if label == "Ours" else 1.0),
                          marker=marker, markersize=4, markevery=(3 * i, 16),
                          markerfacecolor="white", markeredgewidth=0.8, label=label)
        lines.append((prec.mean(), line))
    lines.sort(key=lambda x: -x[0])
    xaxis(ax)
    ax.set_ylim(0, 60)
    ax.set_yticks(range(0, 61, 10))
    ax.grid(axis="y", color="#dddddd", linewidth=0.5)
    ax.set_axisbelow(True)
    ax.yaxis.set_major_formatter(matplotlib.ticker.FuncFormatter(lambda v, _: f"{int(v)}%"))
    ax.legend(handles=[line for _, line in lines], ncol=1, loc="center left",
              bbox_to_anchor=(1.02, 0.5), frameon=False, handlelength=2.2, fontsize=7)
    fig.savefig(os.path.join(OUT, "prec.pdf"), **SAVE)
    plt.close(fig)

for name, out, *_ in SETTINGS:
    draw_alarm(name, out)
draw_prec()
