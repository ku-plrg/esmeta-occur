# Compute the numbers reported in the paper from result/<setting>/summary.tsv
# and tp.tsv: average alarms, false positives, precision (Figure 16 and the
# text of Section 6.1), and the iteration/time ratios (Section 6.2).
import os
import pandas as pd

HERE = os.path.dirname(os.path.abspath(__file__))
SETTINGS = [
    ("base", "Base"),
    ("syn", "Syn"),
    ("pre", "NoMut"),
    ("boolean", "Ours_Bool"),
    ("inval", "Inval"),
    ("our", "Ours_Full"),
]
tp = pd.read_csv(os.path.join(HERE, "tp.tsv"), sep="\t")["tp"].values

def load(name):
    path = os.path.join(HERE, "result", name, "summary.tsv")
    if not os.path.exists(path):
        return None
    return pd.read_csv(path, sep="\t").dropna(subset=["iter"])

print(f"{'setting':10s} {'alarms':>8s} {'FP':>8s} {'precision':>10s}")
data = {}
for name, label in SETTINGS:
    df = load(name)
    if df is None:
        continue
    data[name] = df
    alarms = df["# errors"].values
    # precision is averaged per version, as in the paper
    prec = (tp / alarms).mean() * 100
    print(f"{label:10s} {alarms.mean():8.1f} {(alarms - tp).mean():8.1f} {prec:9.1f}%")

if "our" in data and "syn" in data:
    print(f"FP reduction (Ours_Full vs Syn): "
          f"{(1 - (data['our']['# errors'] - tp).mean() / (data['syn']['# errors'] - tp).mean()) * 100:.1f}%")
for other, label in [("syn", "Syn"), ("boolean", "Ours_Bool")]:
    if "our" in data and other in data:
        o, s = data["our"], data[other]
        print(f"Ours_Full / {label}: iterations x{o['iter'].mean() / s['iter'].mean():.2f}, "
              f"time x{o['duration (ms)'].mean() / s['duration (ms)'].mean():.2f}")
if "our" in data:
    print(f"Ours_Full average time: {data['our']['duration (ms)'].mean() / 1000:.1f} s")
