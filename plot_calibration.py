import pandas as pd
import matplotlib.pyplot as plt

df = pd.read_csv("calibration.csv")
ops = df["op"].unique()

fig, axes = plt.subplots(1, len(ops), figsize=(4 * len(ops), 4), sharey=False)
if len(ops) == 1:
    axes = [axes]

for ax, op in zip(axes, ops):
    times = df[df["op"] == op]["time_s"] * 1e6
    ax.hist(times, bins=100, edgecolor="none")
    ax.set_title(op)
    ax.set_xlabel("time (µs)")
    ax.set_ylabel("count")
    ax.axvline(times.max(), color="red", linestyle="--", linewidth=0.8, label=f"max {times.max():.2f}µs")
    ax.set_yscale("log")
    ax.legend(fontsize=7)

plt.tight_layout()
plt.savefig("calibration.png", dpi=150)
print("saved calibration.png")
