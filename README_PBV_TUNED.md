# Tuned PBV rewrite flags: per-family ablation of `--pbv-rewrites` (rr) and `--learned-rewrite-rules` (lr)

Goal: find the subset of rr and of lr that each improve on CVC5-EXP **independently** (no row of the table worse), while keeping CVC5-PBV at 197/200 on alive.

All numbers below are generated from the experiment logs. Runs: this branch (`pbv-theory`), local WSL machine, 14 cores, 12 parallel jobs, **60 s** per benchmark, 6 GB memory cap. Benchmarks: `/home/zvbe/benchmarks/pbv/{sat25,QF_PBV,fvfp-book}` (15,938 files). The 151 files that already take >10 s to *preprocess* with no rr/lr flag (149 of them qf-two) are excluded from the comparisons: they time out under every configuration.

> Local counts are not the cluster's. Use the deltas (Δ) here; confirm absolute numbers on the cluster.

## TL;DR: the new flags

| Column | Flags on top of the base line | Status |
|---|---|---|
| CVC5-EXP (baseline) | `--learned-rewrite-rules=int` | unchanged |
| CVC5-EXP+rr (tuned) | `--learned-rewrite-rules=int --pbv-rewrites-tuned` | every row ≥ CVC5-EXP locally |
| CVC5-EXP+lr (tuned) | `--learned-rewrite-rules=int,pbv-tuned` | every row ≥ CVC5-EXP locally |
| CVC5-PBV (tuned) | `--learned-rewrite-rules=int,pbv-tuned,shift-bitwise --pbv-rewrites-tuned --piand-lemmas=complement` | measured, see below |

Base line (every column): `--nl-ext-tplanes --full-saturate-quant --exp-solver=rewrites,lemmas,phasing --exp-preprocess=multiply --fermat-little-theorem`

- **`--pbv-rewrites-tuned`** (new bool option) = `--pbv-rw-bool --pbv-mw-shift-bitwise --pbv-rw-and-not --pbv-rw-or-not --pbv-uts-mode=flip --pbv-div-lemmas`. Each is a default only; an explicit flag wins.
- CVC5-PBV adds the lr token `shift-bitwise` on top of `pbv-tuned`: it is worth +9 on alive there (the row CVC5-PBV must keep), but loses five rows in the +lr column alone, so it is NOT part of `pbv-tuned`.
- **`pbv-tuned`** (new `--learned-rewrite-rules` aggregate token) = `sign-idioms,mask-facts`.
- Verified: on 200 random benchmarks the new flags give a byte-identical preprocessed formula to the explicit family list. Code: `src/options/smt_options.toml`, `src/smt/set_defaults.cpp`, `src/preprocessing/passes/learned_rewrite_rules.cpp`. Defaults are unchanged.

### Cluster commands

```sh
/private/zohar-lab/scripts/submit-job.sh $SOLVERS_DIR/cvc5 --solver-options "--nl-ext-tplanes --full-saturate-quant --exp-solver=rewrites,lemmas,phasing --exp-preprocess=multiply --fermat-little-theorem --learned-rewrite-rules=int --pbv-rewrites-tuned" --benchmark-sets "$BENCHMARK_SET" --time-limit $TIME_LIMIT --working-dir "$WD_BASE/cvc5-exp+rr-tuned"
/private/zohar-lab/scripts/submit-job.sh $SOLVERS_DIR/cvc5 --solver-options "--nl-ext-tplanes --full-saturate-quant --exp-solver=rewrites,lemmas,phasing --exp-preprocess=multiply --fermat-little-theorem --learned-rewrite-rules=int,pbv-tuned" --benchmark-sets "$BENCHMARK_SET" --time-limit $TIME_LIMIT --working-dir "$WD_BASE/cvc5-exp+lr-tuned"
/private/zohar-lab/scripts/submit-job.sh $SOLVERS_DIR/cvc5 --solver-options "--nl-ext-tplanes --full-saturate-quant --exp-solver=rewrites,lemmas,phasing --exp-preprocess=multiply --fermat-little-theorem --learned-rewrite-rules=int,pbv-tuned,shift-bitwise --pbv-rewrites-tuned --piand-lemmas=complement" --benchmark-sets "$BENCHMARK_SET" --time-limit $TIME_LIMIT --working-dir "$WD_BASE/cvc5-pbv-tuned"
```
`$SOLVERS_DIR/cvc5` must be this build; older binaries reject the new flags.

## Result 1: the tuned columns against the paper table

Δ is measured locally against the column's own baseline (CVC5-EXP, or CVC5-EXP+piand for CVC5-PBV); *projected* = paper baseline + local Δ. Bold = beats the current column of the same kind.

| Row | # | EXP | EXP+rr (now) | Δ rr-tuned | **EXP+rr tuned** | EXP+lr (now) | Δ lr-tuned | **EXP+lr tuned** | EXP+piand | PBV (now) | Δ pbv-tuned | **PBV tuned** |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| alive | 200 | 133 | 154 | +34 | **167** | 142 | +1 | 134 | 177 | 197 | +21 | **198** |
| ic | 180 | 103 | 104 | +2 | **105** | 102 | +1 | **104** | 105 | 108 | +1 | 106 |
| rewrite | 2006 | 1572 | 1625 | +70 | **1642** | 1571 | +6 | **1578** | 1633 | 1649 | +31 | **1664** |
| syrew | 1500 | 1176 | 1179 | +4 | **1180** | 1172 | +1 | **1177** | 1199 | 1187 | -4 | **1195** |
| lemmas | 70 | 35 | 36 | +1 | 36 | 35 | +0 | 35 | 36 | 37 | +1 | 37 |
| icfb | 46 | 4 | 3 | +1 | **5** | 5 | +0 | 4 | 18 | 18 | +1 | **19** |
| mut | 9441 | 8688 | 8638 | +32 | **8720** | 8683 | +14 | **8702** | 8758 | 8691 | +3 | **8761** |
| qf-single | 2014 | 1564 | 1627 | +74 | **1638** | 1560 | +6 | **1570** | 1649 | 1675 | +34 | **1683** |
| qf-two | 202 | 12 | 12 | +1 | **13** | 12 | +1 | **13** | 12 | 12 | +0 | 12 |
| qf-multi | 252 | 245 | 246 | +1 | 246 | 246 | +1 | 246 | 246 | 246 | +1 | **247** |
| fvfp | 26 | 20 | 21 | +0 | 20 | 19 | +0 | **20** | 21 | 22 | +4 | **25** |
| **total** | 15937 | 13552 | 13645 | +220 | **13772** | 13547 | +31 | **13583** | 13854 | 13842 | +93 | **13947** |

- `+rr' tuned (bool,shift-bitwise,and-not,uts-flip,div-lemmas)` (piand=False): 13593 files with a changed preprocessed formula; +275 / −55; sat↔unsat flips: 0.
- `+lr' sign-idioms(lr),mask-facts(lr)` (piand=False): 13568 files with a changed preprocessed formula; +40 / −9; sat↔unsat flips: 0.
- `pbv' tuned (rr-tuned + pbv-tuned + lr:shift-bitwise + piand)` (piand=True): 13595 files with a changed preprocessed formula; +220 / −127; sat↔unsat flips: 0.
- The current EXP+rr column loses to CVC5-EXP on **mut** (8638 < 8688) and **icfb** (3 < 4); the current EXP+lr column loses on **rewrite, syrew, mut, qf-single, ic, fvfp**. The tuned columns have no negative row.
- About half of the tuned +lr gain is the pbv-mw pass itself: switching it on asserts `_k >= 1`, which changes ~13,600 formulas and is net positive. `mask-facts` + `sign-idioms` alone are +6.

### Leave-one-out inside the tuned subsets

Each row removes ONE family from the tuned subset. **Negative net = the family helps** (removing it loses).

| Family | Changed | + | − | Net | alive | ic | rewrite | syrew | lemmas | icfb | mut | qf-single | qf-two | qf-multi | fvfp | Flips |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `loo-rr:rr:ac in bool,shift-bitwise,ac,and-not,ext-bitwise,uts-flip,sign-idioms,div-lemmas` | 1449 | 15 | 11 | **+4** | +1 (2/−1) |  | +2 (3/−1) | +0 (2/−2) |  |  | +3 (5/−2) | -2 (3/−5) |  |  |  | 0 |
| `loo-pbv:rr:ac in bool,shift-bitwise,ac,and-not,ext-bitwise,uts-flip,sign-idioms,div-lemmas,sign-idioms(lr),mask-facts(lr)` | 1446 | 17 | 14 | **+3** | -1 | -1 | +3 | +5 |  | -2 | -2 (5/−7) | +0 (3/−3) | +1 |  |  | 0 |
| `loo-rr:rr:sign-idioms in bool,shift-bitwise,ac,and-not,ext-bitwise,uts-flip,sign-idioms,div-lemmas` | 78 | 3 | 2 | **+1** | +1 (3/−2) |  |  |  |  |  |  |  |  |  |  | 0 |
| `loo-pbv:rr:sign-idioms in bool,shift-bitwise,ac,and-not,ext-bitwise,uts-flip,sign-idioms,div-lemmas,sign-idioms(lr),mask-facts(lr)` | 81 | 1 | 0 | **+1** |  |  |  |  |  |  | +1 |  |  |  |  | 0 |
| `loo-rr:rr:ext-bitwise in bool,shift-bitwise,ac,and-not,ext-bitwise,uts-flip,sign-idioms,div-lemmas` | 9 | 0 | 0 | **+0** |  |  |  |  |  |  |  |  |  |  |  | 0 |
| `loo-lr:lr:sign-idioms in sign-idioms(lr),mask-facts(lr)` | 2 | 0 | 0 | **+0** |  |  |  |  |  |  |  |  |  |  |  | 0 |
| `loo-pbv:rr:ext-bitwise in bool,shift-bitwise,ac,and-not,ext-bitwise,uts-flip,sign-idioms,div-lemmas,sign-idioms(lr),mask-facts(lr)` | 4 | 0 | 0 | **+0** |  |  |  |  |  |  |  |  |  |  |  | 0 |
| `loo-pbv:lr:mask-facts in bool,shift-bitwise,ac,and-not,ext-bitwise,uts-flip,sign-idioms,div-lemmas,sign-idioms(lr),mask-facts(lr)` | 9 | 0 | 0 | **+0** |  |  |  |  |  |  |  |  |  |  |  | 0 |
| `loo-rr:rr:div-lemmas in bool,shift-bitwise,ac,and-not,ext-bitwise,uts-flip,sign-idioms,div-lemmas` | 13 | 0 | 3 | **-3** | -3 |  |  |  |  |  |  |  |  |  |  | 0 |
| `loo-pbv:rr:div-lemmas in bool,shift-bitwise,ac,and-not,ext-bitwise,uts-flip,sign-idioms,div-lemmas,sign-idioms(lr),mask-facts(lr)` | 13 | 0 | 3 | **-3** | -3 |  |  |  |  |  |  |  |  |  |  | 0 |
| `loo-lr:lr:mask-facts in sign-idioms(lr),mask-facts(lr)` | 12 | 0 | 4 | **-4** | -3 |  |  |  |  |  | -1 |  |  |  |  | 0 |
| `loo-pbv:rr:and-not in bool,shift-bitwise,ac,and-not,ext-bitwise,uts-flip,sign-idioms,div-lemmas,sign-idioms(lr),mask-facts(lr)` | 334 | 7 | 11 | **-4** | +0 (1/−1) |  | +2 (3/−1) | -2 (1/−3) | -1 |  | -1 | -2 (2/−4) |  |  |  | 0 |
| `loo-pbv:lr:sign-idioms in bool,shift-bitwise,ac,and-not,ext-bitwise,uts-flip,sign-idioms,div-lemmas,sign-idioms(lr),mask-facts(lr)` | 21 | 0 | 4 | **-4** | -4 |  |  |  |  |  |  |  |  |  |  | 0 |
| `loo-pbv:rr:bool in bool,shift-bitwise,ac,and-not,ext-bitwise,uts-flip,sign-idioms,div-lemmas,sign-idioms(lr),mask-facts(lr)` | 85 | 0 | 5 | **-5** | -1 |  | -1 |  |  |  | -2 | -1 |  |  |  | 0 |
| `loo-pbv:rr:shift-bitwise in bool,shift-bitwise,ac,and-not,ext-bitwise,uts-flip,sign-idioms,div-lemmas,sign-idioms(lr),mask-facts(lr)` | 557 | 25 | 32 | **-7** | -5 |  | -2 (9/−11) | +8 |  |  | -4 (1/−5) | -4 (7/−11) |  |  |  | 0 |
| `loo-rr:rr:uts-flip in bool,shift-bitwise,ac,and-not,ext-bitwise,uts-flip,sign-idioms,div-lemmas` | 954 | 19 | 29 | **-10** |  | -2 (2/−4) |  |  |  |  | -8 (17/−25) |  |  |  |  | 0 |
| `loo-rr:rr:shift-bitwise in bool,shift-bitwise,ac,and-not,ext-bitwise,uts-flip,sign-idioms,div-lemmas` | 560 | 20 | 34 | **-14** | -5 |  | -4 (8/−12) | +5 |  |  | -4 (1/−5) | -6 (6/−12) |  |  |  | 0 |
| `loo-rr:rr:and-not in bool,shift-bitwise,ac,and-not,ext-bitwise,uts-flip,sign-idioms,div-lemmas` | 336 | 9 | 26 | **-17** | +3 |  | -4 (2/−6) | -8 | -1 | -1 |  | -7 (3/−10) |  |  | +1 | 0 |
| `loo-pbv:rr:uts-flip in bool,shift-bitwise,ac,and-not,ext-bitwise,uts-flip,sign-idioms,div-lemmas,sign-idioms(lr),mask-facts(lr)` | 949 | 19 | 41 | **-22** |  | -3 (2/−5) | -4 |  |  | -1 | -14 (17/−31) |  |  |  |  | 0 |
| `loo-rr:rr:bool in bool,shift-bitwise,ac,and-not,ext-bitwise,uts-flip,sign-idioms,div-lemmas` | 83 | 0 | 45 | **-45** | -22 |  | -6 |  |  |  | -10 | -6 |  |  | -1 | 0 |

### How the subsets were finalized (phase 4)

Whole-column runs after the leave-one-out. `pbv-current` is the CURRENT CVC5-PBV line (`--pbv-rewrites --learned-rewrite-rules=int,pbv --piand-lemmas=complement`) measured on the same machine: its local Δ vs CVC5-EXP+piand (alive +23, syrew −15, mut −64) tracks the cluster table (+20, −12, −67), so the local deltas are trustworthy. Like-for-like on alive the tuned line is 2 below the current one (+21 vs +23) and far ahead elsewhere.

| Family | Changed | + | − | Net | alive | ic | rewrite | syrew | lemmas | icfb | mut | qf-single | qf-two | qf-multi | fvfp | Flips |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `+rr'' reduced` | 13593 | 275 | 55 | **+220** | +34 (35/−1) | +2 (5/−3) | +70 (79/−9) | +4 (13/−9) | +1 | +1 | +32 (56/−24) | +74 (82/−8) | +1 | +1 | +0 (1/−1) | 0 |
| `pbv'' reduced` | 13595 | 178 | 84 | **+94** | +12 (14/−2) | +2 (5/−3) | +27 (45/−18) | +1 (11/−10) | +1 | +1 (3/−2) | +15 (50/−35) | +30 (44/−14) |  | +1 | +4 | 0 |
| `pbv-current (all rr+lr) locally` | 13607 | 215 | 207 | **+8** | +23 (25/−2) | +2 (6/−4) | +23 (52/−29) | -15 (17/−32) | +1 | +3 (4/−1) | -64 (51/−115) | +30 (53/−23) | -1 | +1 | +5 | 0 |
| `pbv'' + lr:shift-bitwise (vs pbv'')` | 269 | 42 | 43 | **-1** | +9 | -1 | +4 (16/−12) | -5 |  |  | -12 (1/−13) | +4 (16/−12) |  |  |  | 0 |

## Result 2: each family alone against CVC5-EXP (the selection table)

CVC5-EXP = base line + `--learned-rewrite-rules=int` (confirmed by the user). Each family is switched on alone. Families that switch on the pbv-mw pass (which adds `_k >= 1` even when no rule fires) are compared against CVC5-EXP + `--pbv-mw-sext-idioms`, a pass-on proxy that fires on a single file, so the Δ is the rules' own. Cells: Δ, with (gain/−loss) when both are non-zero.

| Family | Changed | + | − | Net | alive | ic | rewrite | syrew | lemmas | icfb | mut | qf-single | qf-two | qf-multi | fvfp | Flips | Decision |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `rr:bool` | 287 | 137 | 0 | **+137** | +27 |  | +48 |  |  |  | +13 | +48 |  |  | +1 | 0 | in `--pbv-rewrites-tuned` |
| `rr:shift-bitwise` | 2070 | 116 | 34 | **+82** | +4 (8/−4) |  | +38 (46/−8) | -6 (1/−7) |  |  | +7 (14/−7) | +40 (46/−6) | -1 | +1 | -1 | 0 | in |
| `rr:ac` | 2098 | 92 | 13 | **+79** | -2 (3/−5) |  | +37 (38/−1) |  |  |  | +4 (10/−6) | +40 (41/−1) |  |  |  | 0 | out: redundant (LOO +4) |
| `rr:and-not` | 493 | 56 | 8 | **+48** |  | -1 | +18 (19/−1) | +10 | +1 | +1 | -1 (3/−4) | +21 (22/−1) |  |  | -1 | 0 | in |
| `rr:ext-bitwise` | 153 | 27 | 0 | **+27** |  |  | +12 |  |  |  | +3 | +12 |  |  |  | 0 | out: redundant (LOO 0) |
| `rr:uts-flip` | 1014 | 33 | 20 | **+13** | +1 (2/−1) | +2 (4/−2) |  |  |  |  | +10 (27/−17) |  |  |  |  | 0 | in |
| `rr:sign-idioms` | 251 | 10 | 4 | **+6** | +0 (2/−2) |  | +3 |  |  |  | +0 (1/−1) | +3 | -1 | +1 |  | 0 | out: redundant (LOO +1) |
| `lr:mask-facts` | 118 | 6 | 1 | **+5** | +3 |  |  |  |  |  | +2 |  | -1 | +1 |  | 0 | in `pbv-tuned` |
| `rr:mask-slice-M1` | 55 | 4 | 0 | **+4** |  |  | +2 |  |  |  |  | +2 |  |  |  | 0 | out: inverts W1 of shift-bitwise, loops with ac |
| `rr:div-lemmas` | 50 | 3 | 0 | **+3** | +3 |  |  |  |  |  |  |  |  |  |  | 0 | in |
| `rr:cav26` | 989 | 27 | 25 | **+2** | -5 |  | +6 | -6 (11/−17) |  |  | +0 (3/−3) | +7 |  |  |  | 0 | out: syrew/alive losses |
| `lr:sign-idioms` | 112 | 2 | 1 | **+1** |  |  |  |  |  |  | +1 |  | -1 | +1 |  | 0 | in `pbv-tuned` (alive +4 in CVC5-PBV) |
| `rr:low-mask` | 126 | 0 | 0 | **+0** |  |  |  |  |  |  |  |  |  |  |  | 0 | out: no effect |
| `lr:shift-bitwise` | 354 | 24 | 42 | **-18** | +7 | -1 | -5 (7/−12) | -5 |  |  | -9 (2/−11) | -5 (7/−12) | -1 | +1 |  | 0 | not in `pbv-tuned`; added to CVC5-PBV only (alive +9 there) |

## Result 3: first round, baseline WITHOUT `--learned-rewrite-rules=int`

All 30 families, each added alone to the base line *without* witness search / reduce-mods (before the CVC5-EXP flags were confirmed). Superseded by Result 2, kept for the record.

> **Caveat.** Rows from `rr:sext-idioms` downward in run order (the second half: the pbv-mw-group families, `rr:ac`, `rr:shift-bitwise`, `lr:shift-bitwise`, `lr:witness`) ran while up to 32 orphaned cvc5 processes were competing for the CPU (load ≈ 40 on 14 cores), so their effective limit was nearer 20 s and their losses are inflated. Rows before that (`shift-add-G` … `uts-flip`) are clean.

| Family | Changed | + | − | Net | alive | ic | rewrite | syrew | lemmas | icfb | mut | qf-single | qf-two | qf-multi | fvfp | Flips |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `lr:witness` | 7770 | 1524 | 0 | **+1524** |  |  | +63 | +54 |  |  | +1339 | +64 | +3 | +1 |  | 9 |
| `rr:bool` | 262 | 141 | 0 | **+141** | +28 |  | +49 |  |  |  | +14 | +49 |  |  | +1 | 0 |
| `rr:shift-bitwise` | 2078 | 229 | 91 | **+138** | +4 (8/−4) |  | +42 (50/−8) | -8 (1/−9) |  |  | +56 (120/−64) | +42 (48/−6) | +1 | +1 |  | 0 |
| `rr:ac` | 2104 | 146 | 60 | **+86** | -2 (3/−5) | -1 | +39 (40/−1) |  |  | -1 | +10 (60/−50) | +42 (43/−1) | -1 |  |  | 0 |
| `rr:and-not` | 459 | 89 | 26 | **+63** |  | -1 | +18 (19/−1) | +13 | +1 |  | +12 (34/−22) | +21 (22/−1) |  |  | -1 | 0 |
| `rr:ext-bitwise` | 105 | 39 | 1 | **+38** |  |  | +12 |  |  |  | +14 (15/−1) | +12 |  |  |  | 0 |
| `rr:cav26` | 951 | 65 | 48 | **+17** | -4 |  | +6 | -7 (10/−17) |  |  | +15 (42/−27) | +7 |  |  |  | 1 |
| `rr:sign-idioms` | 258 | 16 | 4 | **+12** | +0 (2/−2) |  | +3 |  |  |  | +4 (6/−2) | +3 | +1 | +1 |  | 0 |
| `rr:uts-flip` | 976 | 42 | 33 | **+9** | +1 (2/−1) | +2 (4/−2) |  |  |  |  | +6 (36/−30) |  |  |  |  | 0 |
| `lr:reduce-mods-width` | 493 | 19 | 12 | **+7** |  |  |  | -1 |  |  | +8 (19/−11) |  |  |  |  | 0 |
| `lr:mask-facts` | 100 | 8 | 1 | **+7** | +3 |  |  |  |  |  | +2 (3/−1) |  | +1 | +1 |  | 0 |
| `rr:mask-slice-M1` | 16 | 4 | 0 | **+4** |  |  | +2 |  |  |  |  | +2 |  |  |  | 0 |
| `lr:sign-idioms` | 92 | 4 | 0 | **+4** |  |  |  |  |  |  | +2 |  | +1 | +1 |  | 0 |
| `rr:div-lemmas` | 16 | 3 | 0 | **+3** | +3 |  |  |  |  |  |  |  |  |  |  | 0 |
| `rr:low-mask` | 78 | 1 | 0 | **+1** |  |  |  |  |  |  | +1 |  |  |  |  | 0 |
| `rr:shift-add-G` | 7 | 0 | 0 | **+0** |  |  |  |  |  |  |  |  |  |  |  | 0 |
| `lr:sext-to-zext` | 7 | 0 | 0 | **+0** |  |  |  |  |  |  |  |  |  |  |  | 0 |
| `lr:shift-add-distrib` | 7 | 0 | 0 | **+0** |  |  |  |  |  |  |  |  |  |  |  | 0 |
| `lr:mask-slice` | 10 | 0 | 0 | **+0** |  |  |  |  |  |  |  |  |  |  |  | 0 |
| `lr:preprocess-mw` | 25 | 0 | 0 | **+0** |  |  |  |  |  |  |  |  |  |  |  | 0 |
| `rr:sext-idioms` | 1 | 0 | 0 | **+0** |  |  |  |  |  |  |  |  |  |  |  | 0 |
| `rr:sext-bv1` | 8 | 0 | 0 | **+0** |  |  |  |  |  |  |  |  |  |  |  | 0 |
| `lr:signed-range` | 8 | 0 | 0 | **+0** |  |  |  |  |  |  |  |  |  |  |  | 0 |
| `lr:sext-idioms` | 9 | 0 | 0 | **+0** |  |  |  |  |  |  |  |  |  |  |  | 0 |
| `lr:trunc-push` | 18 | 0 | 0 | **+0** |  |  |  |  |  |  |  |  |  |  |  | 0 |
| `lr:ext-bitwise` | 18 | 0 | 0 | **+0** |  |  |  |  |  |  |  |  |  |  |  | 0 |
| `rr:trunc-push` | 21 | 0 | 0 | **+0** |  |  |  |  |  |  |  |  |  |  |  | 0 |
| `lr:sext-bv1` | 24 | 0 | 0 | **+0** |  |  |  |  |  |  |  |  |  |  |  | 0 |
| `lr:reduce-mods` | 49 | 0 | 2 | **-2** |  |  |  |  |  |  | -1 |  |  | -1 |  | 0 |
| `lr:shift-bitwise` | 337 | 47 | 69 | **-22** | +7 | -1 | -3 (10/−13) | -6 |  |  | -18 (19/−37) | -3 (9/−12) | +1 | +1 |  | 2 |

Families with **no effect at all** in either round (identical answers on every file they change): `rr:trunc-push`, `rr:sext-idioms`, `rr:sext-bv1`, `rr:shift-add-G`, `lr:preprocess-mw`, `lr:sext-to-zext`, `lr:shift-add-distrib`, `lr:mask-slice`, `lr:trunc-push`, `lr:ext-bitwise`, `lr:sext-bv1`, `lr:sext-idioms`, `lr:signed-range`.

## Problems found along the way

### 1. `--pbv-rewrites` contains a non-terminating rewrite loop

`--pbv-mw-shift-bitwise` rule W1 rewrites `(a & b) << z` → `(a << z) & (b << z)`; `--pbv-mask-slice=all` rule M1 rewrites `(a << z) & (b << z)` → `(a & b) << z`. With `--pbv-rw-ac` sorting the operands both keep matching, and preprocessing never ends. All three are in `--pbv-rewrites`. Reproducer: `sat25/mut/alive_mutant/alive-sat-bvnot-to-bvneg/AndOrXor_210_values_0.smt2` (each family alone: 0.01 s; all of `--pbv-rewrites`: never finishes).

| Preprocessing > 10 s | qf-single | qf-multi | qf-two | lemmas | mut | rewrite | syrew |
|---|---|---|---|---|---|---|---|
| all rr+lr families on | 12 | 4 | 192 | 1 | 73 | 23 | 3 |
| none on | 2 | 0 | 149 | 0 | 0 | 0 | 0 |

`--pbv-rewrites-tuned` leaves M1 out, so it cannot loop. The old flag is unchanged.

### 2. Wrong `unsat` from an unsound flatten-monomial lemma (affects EVERY column)

Satisfiable benchmarks came back `unsat`. Verified sat by `--check-models` and by brute force over all values at widths 1-8:

| Benchmark (`sat25/mut/cade19_mutant/…`) | Witness |
|---|---|
| `terms_size3-sat-bv0-to-bv1/test-pbv1390.smt2` (with `t & 1` rewritten, as cav26 does) | s=0, t=3, width 4 |
| `terms_size3-sat-bvadd-to-bvsub/test-pbv1430.smt2` | width ≥ 3, s=1 |
| `terms_size3-sat-bvlshr-to-bvshl/test-pbv559.smt2` | width ≥ 2, s=1 |

**Root cause (verified).** It is NOT phasing (first suspected): the phasing split `g ⇔ −2^b ≤ t ≤ 2^b` is a definition and cannot cause `unsat`. Every lemma of the failing run was checked against a full model of the preprocessed formula; the only false one is `ARITH_NL_FLATTEN_MON: t·2^(t−1) = t·2^(k−1)` (12 = 24 at t=3, k=4), emitted with NO antecedent. `flatten_monomial_check.cpp` substitutes with `ArithSubs::applyArith`, which also rewrites inside `**` exponents (`isExtendedNonLinearKind(EXP)` is true), but `addToFlattenMonMap` collects the explanation only through `NONLINEAR_MULT` children, so the equality `k = t` used inside the exponent is dropped. All three wrong `unsat`s disappear with `--no-nl-ext-flatten-mon`. Phasing, `halving` (creates `2^(t−1)`) and `--arith-pow2-norm` only steer the search into the branch where it fires. `lr:witness` also turned 9 baseline `unsat` answers into model-verified `sat` (mut), likely the same bug. **Some `unsat` counts in the paper table are probably wrong.** Not fixed. Suggested fix: expand the explanation through every node `applyArith` traverses (or call `applyArith(n, false)` there), and run the existing assertion-build double-check in production, dropping a lemma that fails it.

### 3. Rule-level notes

- `pbv-c26-and-one` (`t & 1 → zext(t[0:0])`, in `--pbv-rw-mw=cav26`) is sound; the cav26 flip was problem 2.
- The known cav26 n-ary `pbvand` arity bug still exists; cav26 is not in the tuned flags.
- `rr:ac` and `rr:shift-bitwise` gain on almost the same files (rewrite +37/+38, qf-single +40/+40): both AC-normalize and/or/xor chains.

## Method

1. **Families.** `--pbv-rewrites` = 15 sub-flags; `--learned-rewrite-rules=int,pbv` = 12 `pbv` tokens + `reduce-mods`, `reduce-mods-width` + witness search (`--arith-witness-search=200 --arith-witness-search-signed --arith-witness-enum=20000`, which an explicit `int` token switches on). 30 families.
2. **Fingerprints.** `cvc5 <flags> --preprocess-only -o post-asserts` hashed. Same preprocessed formula + same solve-time flags ⇒ same run, so only files whose formula a family changes are solved, and identical formulas are solved once. Witness search is a deterministic pass, so it is excluded from the fingerprint and tagged in the solve key instead.
3. **Solve.** 60 s, 12 jobs, answers from the first output line; sat↔unsat disagreements are reported as flips and checked by hand.
4. **Selection.** Keep a family if it is net-positive alone against CVC5-EXP and does not hurt syrew/alive more than another kept family repays; then measure the subset as a whole column (Result 1) and leave each family out in turn.

Scripts and raw logs: `/tmp/claude-1000/-home-zvbe-cvc5/4554b365-f704-434a-b864-0074758b5d7c/scratchpad/` (`fam.py`, `run.py`, `cmp.py`, `phase2.py`, `phase3.py`, `*.log`, `cache/`). Regenerate this file with `python3 mkreadme.py`.
