# BUILD — how to reproduce the receipts

Native pins (zeta23's own): Lean **v4.33.0-rc2**, Mathlib **51e6992efd06126df61a496bebf8f49482a4e129**.

```sh
# 1. zeta23 checkout at the audited commit
git clone https://github.com/anthropics/formal-math
cd formal-math && git checkout 16a5ce41 && cd zeta23

# 2. Mathlib oleans (network) — the standard cache path
lake exe cache get

# 3. drop in the Scratch layer from this repo
cp -r <this-repo>/lean <here>/Scratch   # lean/ contents map to Scratch/
cat >> lakefile.toml <<'EOF'

[[lean_lib]]
name = "Scratch"
roots = ["Scratch.HGe269", "Scratch.Bridge269", "Scratch.P2Plugs", "Scratch.adapter.RaceBound"]
EOF

# 4. build + receipts (LEAN_NUM_THREADS caps concurrency; this Lake has no -j)
LEAN_NUM_THREADS=3 lake build Scratch.Bridge269 2>&1 | tee build.log

# expected: rc=0, zero 'declaration uses sorry' warnings, and #print axioms lines:
#   'H269.h_ge_269_400' depends on axioms: [propext, Classical.choice, Quot.sound]
#   'Race.bound_269_400' depends on axioms: [propext, Classical.choice, Quot.sound]
#   'Race.bound_269_400_zeta23' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Reference build: Apple M4 Max, host under load (loadavg ~70), 8890 jobs total (warm Mathlib),
Scratch layer seconds-to-minutes. The original integration log is receipts/build-final.log.

File sha256 (16-hex prefixes at integration time; full values in receipts/shasums.txt):
HGe269.lean f2069375b8457176… · Bridge269.lean 1a12497d09aebf14… ·
P2Plugs.lean 7fb821c4383da1d8… · adapter/RaceBound.lean 1d98d747f01f98b4…
