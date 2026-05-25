import os
import re
import matplotlib.pyplot as plt

def parse_result(path):
    with open(path) as f:
        text = f.read()
    c = re.search(r"calibration time:\s+([\d.]+)s", text)
    p = re.search(r"program runtime:\s+([\d.]+)s", text)
    if not c or not p:
        return None
    return float(p.group(1)) - float(c.group(1))

def parse_size(s):
    s = s.lower()
    if s.endswith("k"):
        return int(s[:-1]) * 1000
    return int(s)

# ── ORAM data ─────────────────────────────────────────────────────────────────

oram_dir = "results/oram"
oram = {"priv_read": [], "priv_write": [], "pub_read": []}

for fname in os.listdir(oram_dir):
    if not fname.endswith(".txt"):
        continue
    m = re.match(r"(pub|priv)_arr_(read|write)_(\w+)\.txt", fname)
    if not m:
        continue
    level, op, size_str = m.group(1), m.group(2), m.group(3)
    size  = parse_size(size_str)
    exec_s = parse_result(os.path.join(oram_dir, fname))
    if exec_s is not None:
        oram[f"{level}_{op}"].append((size, exec_s))

for key in oram:
    oram[key].sort()

# ── New benchmark data ────────────────────────────────────────────────────────
# n_ops from benchmark.oio: priv read = 20000*5 = 100k, priv write = 100000*5 = 500k
# pub read/write = same counts

new = {
    "priv_read":  (100_000,  parse_result("results/array_priv_read.txt")),
    "priv_write": (500_000,  parse_result("results/array_priv_write.txt")),
    "pub_read":   (100_000,  parse_result("results/array_pub_read.txt")),
    "pub_write":  (500_000,  parse_result("results/array_pub_write.txt")),
}


# ── Plot ──────────────────────────────────────────────────────────────────────

cases = [
    ("priv_read",  "Private array read"),
    ("priv_write", "Private array write"),
]

fig, axes = plt.subplots(1, len(cases), figsize=(5 * len(cases), 5))

for ax, (key, title) in zip(axes, cases):
    if oram.get(key):
        xs, ys = zip(*oram[key])
        ax.plot(xs, ys, "o-", label="Linear scan", color="steelblue")

    n_new, t_new = new[key]
    if t_new is not None:
        ax.axhline(t_new, color="crimson", linestyle="--", linewidth=1.2, label="Timing pad")

    ax.set_title(title)
    ax.set_xlabel("operations")
    ax.set_ylabel("exec time (s)")
    ax.legend(fontsize=8)
    ax.ticklabel_format(style="sci", axis="x", scilimits=(0, 0))
    ax.grid(True, linestyle="--", alpha=0.4)

plt.tight_layout()
plt.savefig("oram_comparison.png", dpi=150)
print("saved oram_comparison.png")
