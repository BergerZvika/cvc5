# Flag changes (pbv-theory branch)

Summary of option changes made while tuning the EXP nl-ext solver and the
BV/PBV-to-int translation.

## 1. Added: `--pbv-to-int-partial-mod`

- **Type:** bool, **category:** expert, **default:** `false` (disabled).
- **Defined in:** `src/options/smt_options.toml` (`pbvToIntPartialMod`).
- **Effect:** in the `bv-to-int` *preprocessing* translation, reduce `mod 2^k`
  with the partial `INTS_MODULUS` instead of `INTS_MODULUS_TOTAL`.
  Divisors are always positive powers of two, so this changes only how the
  arithmetic solver handles the mod term (the partial kind introduces the
  standard `@mod_by_zero` abstraction for e.g. `bvurem`), not the satisfiability.
- **Applies to:** the classic int-blaster `src/theory/bv/int_blaster.cpp`
  (used by `--solve-bv-as-int=sum|iand|piand|bitwise`). It does **not** touch the
  PBV-theory int-blaster (`--solve-bv-as-int=pbv`) or the PIAND solver lemmas.
- **Implementation:** `IntBlaster::modKind()` returns the chosen kind; all 7
  modulus-construction sites route through it.

**Usage**
```
# default (INTS_MODULUS_TOTAL)
cvc5 --nl-ext-tplanes --solve-bv-as-int=piand bench.smt2

# partial INTS_MODULUS
cvc5 --nl-ext-tplanes --solve-bv-as-int=piand --pbv-to-int-partial-mod bench.smt2
```

## 1b. Added: `--dump-int-blast` (export the int-blasted benchmark)

- **Type:** bool, **category:** expert, **default:** `false` (disabled).
- **Defined in:** `src/options/smt_options.toml` (`dumpIntBlast`).
- **Effect:** after int-blasting (bv-to-int / pbv-to-int), print the translated
  benchmark to the **regular output channel** and **skip solving**. The dump is
  a clean, self-contained, re-parseable SMT2 file:
  - `(set-logic UFNIA)` (for PBV input; computed post-blast logic),
  - all declarations, the int-blasted assertions (`**` = EXP, `piand`,
    `int.pow2`, `mod_total`/`div_total`), and a final `(check-sat)`,
  - no comment markers, no result line,
  - reserved-prefix skolem names (`@purify_*`, `.`) renamed to `bv2int_*` so the
    file parses back in (SMT-LIB forbids leading `@`/`.`).
- **Implementation:** reuses the post-asserts dump path in
  `ProcessAssertions::dumpAssertionsToStream` (new `renameReserved` arg);
  `SmtDriverSingleCall::checkSatNext` skips solving (like `--preprocess-only`);
  `CommandExecutor` runs commands via `invoke()` (no result print) in this mode.

**Usage**
```bash
# PBV benchmark -> UFNIA(+EXP/piand) file (keep pow2 symbolic via EXP)
cvc5 --solve-bv-as-int=pbv --pbv-to-int-use-pow2 \
     --dump-int-blast --out=translated.smt2 -q input_pbv.smt2

# also works for the classic int-blaster modes (iand/piand/sum)
cvc5 --solve-bv-as-int=piand --dump-int-blast --out=out.smt2 -q in.smt2

# the dumped file re-parses and re-solves with the same answer:
cvc5 --nl-ext-tplanes -q translated.smt2
```
Verified round-trip on PBV benchmarks: parse-only OK; direct-solve vs
dump+resolve agree (sat↔sat, unsat↔unsat).

## 2. Removed: `--exp-lemmas` (doubling lemma is now always on)

- The `expLemmaMode` option (`--exp-lemmas=none|all|doubling`) was **deleted**.
- The EXP "doubling" full-refine lemma now fires unconditionally in
  `src/theory/arith/nl/exp_solver.cpp`:
  `s_x = s_y /\ t_y = t_x + 1  =>  exp(s_y, t_y) = s_x * exp(s_x, t_x)`
  (generalized from the old base-2-only form).
- **Migration:** drop `--exp-lemmas=all`/`--exp-lemmas=doubling` from any
  scripts — the behavior is now the default and the flag is no longer accepted.

## 3. Removed: `--nl-ext-exp-induction-axioms` (induction lemmas are now always on)

- The `nlExtExpInductionAxioms` option was **deleted** (it defaulted to `true`).
- The two EXP induction lemmas (base `exp(s,0)=1`, step
  `t>=1 => exp(s,t) = s*exp(s,t-1)`) in `exp_solver.cpp` now always fire.
- **Migration:** `--no-nl-ext-exp-induction-axioms` no longer exists; the
  lemmas can no longer be disabled via a flag.

## 4. Made opt-in: everything after induction-lemma + exp-preprocess

To keep the EXP induction lemmas (`exp(s,0)=1`, `t>=1 => exp(s,t)=s*exp(s,t-1)`)
and the `exp-analyzer` preprocess as the only always-on / default additions, the
remaining behavior changes were moved behind flags (all off by default):

- **EXP doubling lemma** — new `--nl-ext-exp-doubling` (bool, default `false`).
  Gates the full-refine lemma `s_x=s_y /\ t_y=t_x+1 => exp(s_y,t_y)=s_x*exp(s_x,t_x)`
  in `exp_solver.cpp`. The base/step induction lemmas remain always-on.
- **PIAND diagonal lemma** — folded into `--piand-lemmas` as a new `diagonal`
  mode (`x=y => piand(k,x,y)=x mod 2^k`). Was unconditional in
  `piand_solver.cpp` init-refine; now emitted only under
  `--piand-lemmas=diagonal` (or `=all`). Default `none` => off.
- **uts encoding** — renamed `--pbv-to-int-uts-sat25` to `--pbv-uts-with-k`
  and inverted: default (`false`) is the sat25 `pow2(k-1)` / `exp(2,k-1)` form;
  `--pbv-uts-with-k` selects the full-k `pow2(k)` / `exp(2,k)` form (as
  `pow2(k) div 2`). The new encoding is now opt-in rather than the default.

## Related pre-existing flags (NOT added this session)

These already existed on the branch and still work as before:
`--piand-lemmas=MODE` (now also has a `diagonal` mode), `--arith-exp-rewrites=MODE`,
`--arith-exp-unroll-bound=N`, `--pbv-to-int-use-pow2`.
