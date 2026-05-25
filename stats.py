import os
import re
import pandas as pd
import numpy as np

# ── Calibration stats ────────────────────────────────────────────────────────

calib = pd.read_csv("calibration.csv")

calib_stats = []
for op, grp in calib.groupby("op"):
    t = grp["time_s"] * 1e6
    calib_stats.append({
        "op":     op,
        "n":      len(t),
        "mean_us":   t.mean(),
        "median_us": t.median(),
        "std_us":    t.std(),
        "p95_us":    t.quantile(0.95),
        "p99_us":    t.quantile(0.99),
        "max_us":    t.max(),
    })

pd.DataFrame(calib_stats).to_csv("stats_calibration.csv", index=False)
print("wrote stats_calibration.csv")

print("\n" + "=" * 60)
print("CALIBRATION STATISTICS")
print("=" * 60)
for r in calib_stats:
    print(f"\n  {r['op']}")
    print(f"    n          = {r['n']}")
    print(f"    mean       = {r['mean_us']:.4f} µs")
    print(f"    median     = {r['median_us']:.4f} µs")
    print(f"    std        = {r['std_us']:.4f} µs")
    print(f"    p95        = {r['p95_us']:.4f} µs")
    print(f"    p99        = {r['p99_us']:.4f} µs")
    print(f"    max        = {r['max_us']:.4f} µs")

# ── Benchmark result stats ────────────────────────────────────────────────────

results_dir = "results"
rows = []

for fname in sorted(os.listdir(results_dir)):
    if not fname.endswith(".txt"):
        continue
    path = os.path.join(results_dir, fname)
    bench = fname[:-4]

    with open(path) as f:
        text = f.read()

    calib_t = re.search(r"calibration time:\s+([\d.]+)s", text)
    prog_t  = re.search(r"program runtime:\s+([\d.]+)s", text)
    if not calib_t or not prog_t:
        continue

    calib_s = float(calib_t.group(1))
    prog_s  = float(prog_t.group(1))
    exec_s  = prog_s - calib_s

    total_m = re.search(r"\s*total\s+[\d.]*\s+([\d.]+)\s+([\d.]+)", text)
    total_sleep = float(total_m.group(1)) if total_m else 0.0
    total_wc    = float(total_m.group(2)) if total_m else 0.0
    pad_pct = (total_sleep / total_wc * 100) if total_wc > 0 else 0.0

    for line in text.splitlines():
        m = re.match(r"\s*(\w+)\s+([\d.]+)\s+([\d.]+)\s+([\d.]+)", line)
        if m and m.group(1) not in ("operation",):
            op      = m.group(1)
            sleep_s = float(m.group(3))
            wc_s    = float(m.group(4))
            rows.append({
                "bench":       bench,
                "op":          op,
                "calib_s":     calib_s,
                "exec_s":      exec_s,
                "total_sleep": total_sleep,
                "total_wc":    total_wc,
                "pad_pct":     pad_pct,
                "op_calib_s":  float(m.group(2)),
                "sleep_s":     sleep_s,
                "wc_s":        wc_s,
            })

pd.DataFrame(rows).to_csv("stats_benchmarks.csv", index=False)
print("wrote stats_benchmarks.csv")

# dedupe to one row per bench for summary
seen = {}
for r in rows:
    if r["bench"] not in seen:
        seen[r["bench"]] = r

print("\n" + "=" * 60)
print("SUMMARY")
print("=" * 60)
print(f"\n  {'benchmark':<30} {'calib_s':>9} {'exec_s':>9} {'sleep_s':>9} {'wc_s':>9} {'pad%':>7} {'util%':>7}")
print(f"  {'-'*30} {'-'*9} {'-'*9} {'-'*9} {'-'*9} {'-'*7} {'-'*7}")
for r in sorted(seen.values(), key=lambda x: x["pad_pct"], reverse=True):
    pad  = r["pad_pct"]
    util = 100 - pad
    print(f"  {r['bench']:<30} {r['calib_s']:>9.3f} {r['exec_s']:>9.3f} {r['total_sleep']:>9.3f} {r['total_wc']:>9.3f} {pad:>6.1f}% {util:>6.1f}%")
