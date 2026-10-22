# Lean 4 proofs of two bounds for the Schur–Siegel–Smyth trace constant

For a totally positive algebraic integer α of degree d, with conjugates α_1, ..., α_d, let tr(α) = α_1 + ... + α_d. The
trace constant C_86 (Tao's constant 86a) is the lower limit of tr(α)/deg(α). It is the largest c such that, for each
ε > 0, only finitely many totally positive algebraic integers satisfy tr(α) < (c - ε) deg(α).

This directory contains Lean 4 proofs of

- the lower bound C_86 >= λ_L = 901111277/500000000 = 1.802222554, with no hypotheses;
- the upper bound C_86 <= λ_U = 81383685642728309283453/45035996273705240000000 = 1.8070808325..., conditional on one
  named hypothesis, `SmithThm15`. This is Smith's Theorem 1.5 (arXiv:2111.12660v2), stated for an interval.

The certificate checks run by `native_decide`, so Lean's compiler is trusted for them (§ 4). Both bounds also have
kernel-only proofs, whose certificate checks run by `decide +kernel` and whose axioms are the three standard ones (§ 5).

## 1. Building

- Toolchain: `leanprover/lean4:v4.35.0-rc3` (file `lean-toolchain`).
- Mathlib: tag v4.35.0-rc3, commit c55e6e786f49 (`lake-manifest.json`).

```
lake exe cache get
lake build Trace86.LowerN Trace86.AxiomsN Trace86U.Upper Trace86U.AxiomsU Trace86.SanityU
```

Running `Trace86/AxiomsN.lean` and `Trace86U/AxiomsU.lean` (for example with `lake env lean Trace86/AxiomsN.lean`)
prints the statements and their axioms.

The kernel-only proofs (§ 5) are built by

```
lake build Trace86.AxiomsK Trace86U.AxiomsUK
```

The upper bound needs about 55 CPU-hours for its 7,192 modules, with peak memory about 7.5 GB per module. The lower
bound needs about 310 CPU-hours for its 24,818 modules (172 for the 14,957 end-point modules, 134 for the 9,142 energy
modules), with peak memory at most 5 GB per module; these times were measured with every hyperthread of the machine
busy, and are about half that on idle cores.

The native proof of the lower bound evaluates the energy over 10,388 records in `T86N/Globals.lean`, which takes about
10 minutes.

There is no `sorry` in the project.

## 2. Definitions

The following definitions are quoted from `AuxCommon/Basic.lean` and `Trace86/Statement.lean`:

```lean
noncomputable abbrev toC (P : ℤ[X]) : ℂ[X] := P.map (Int.castRingHom ℂ)
def IsMinpolyZ (P : ℤ[X]) (α : ℂ) : Prop := Irreducible P ∧ 0 < P.natDegree ∧ aeval α P = 0
def AllRootsPos (P : ℤ[X]) : Prop := ∀ z ∈ (toC P).roots, 0 < z.re ∧ z.im = 0
noncomputable def traceP (P : ℤ[X]) : ℝ := ((toC P).roots.sum).re
def TPTraceLe (B : ℝ) : Set ℂ :=
  {α | IsIntegral ℤ α ∧ ∃ P : ℤ[X], IsMinpolyZ P α ∧ AllRootsPos P ∧ traceP P ≤ B * P.natDegree}
noncomputable def lamL : ℝ := 901111277 / 500000000
noncomputable def lamU : ℝ := 81383685642728309283453 / 45035996273705240000000
```

How these definitions match the mathematics:

- **Minimal polynomial.** `Irreducible P` in ℤ[X] with positive degree means that P is primitive and irreducible over ℚ
  (Gauss's lemma). So P is ± the minimal polynomial of α, and its complex roots, counted with multiplicity, are the
  conjugates of α.
- **The other definitions.**
  - `AllRootsPos P` says that α is totally positive.
  - `traceP P` is tr(α), and `P.natDegree` is deg(α).
  - The sign of P changes neither.
- **What the set contains.** `TPTraceLe B` is a set of numbers α, not of polynomials.
- **Why C_86 is not defined in Lean.** The constant is not defined by `sSup`, whose junk value would need a separate
  boundedness proof. Instead, the two bounds are stated through the defining property of C_86:
  - finiteness of `TPTraceLe (λ_L - ε)` for every ε > 0 gives C_86 >= λ_L;
  - infinitude of `TPTraceLe (λ_U + ε)` for every ε > 0 gives C_86 <= λ_U.
  - Using `≤` instead of `<` is equivalent, because ε is arbitrary.

## 3. Theorems

From `Trace86/LowerN.lean`:
```lean
theorem Trace86.trace_lower_N (ε : ℝ) (hε : 0 < ε) : (TPTraceLe (lamL - ε)).Finite
theorem Trace86.trace_lower_dec_N : (TPTraceLe (18022225 / 10000000)).Finite
```

From `Trace86U/Upper.lean`:
```lean
theorem Trace86.trace_upper_N (hS : SmithThm15) (ε : ℝ) (hε : 0 < ε) : (TPTraceLe (lamU + ε)).Infinite
theorem Trace86.trace_upper_dec_N (hS : SmithThm15) : (TPTraceLe (18070809 / 10000000)).Infinite
```

The decimal forms round outward: 1.8022225 < λ_L, and λ_U < 1.8070809.

## 4. Axioms

`#print axioms`, as run in `Trace86/AxiomsN.lean` and `Trace86U/AxiomsU.lean`, reports the following.

- **Lower bound.** `propext`, `Classical.choice` and `Quot.sound`, plus 153 auxiliary axioms
  `T86Core.T86N.<check>._native.native_decide.ax_1_1`, one for each `native_decide` check:
  - `chunk_000` ... `chunk_149`: the tiling of [1/100, 30), in the end-point form of § 5;
  - `energy_ok`;
  - `left_tail_ok`: (0, 1/100];
  - `right_tail_ok`: [30, ∞).
- **Upper bound.** The same three axioms, plus 78 auxiliaries `T86UCore.T86UN.<check>._native.native_decide.ax_1_1`:
  - `chunk_000` ... `chunk_072`: the tiling of [x_0, 6], with x_0 = 1/100;
  - `budget_ok`, `irred_ok`, `left_tail_ok`, `moments_ok` and `trace_ok`.

Each auxiliary axiom states `decide p = true`, where p is the statement of its check. Each check is a run of the
certificate checker (`T86Core/Check.lean` with `T86Core/CheckE.lean`, or `T86UCore/Check.lean`; core Lean only) on the
certificate data. The checks are combined with soundness theorems that the kernel verifies.

## 5. Kernel-only proofs

### 5.1 The chord leaves of the lower bound, end-point form

The lower-bound tiling checks each chord leaf [p, q] from node sums at its two end points, computed once per point and
shared by the two leaves that meet there (`T86Core/CheckE.lean`: `epData`, `chordLBC`, `leavesOKE`):

- at each end point x: an upper bound of the potential U(x), a lower bound of ∑ C_i log |x - e_i| over the nodes
  e_i ≠ x, upper bounds of 2 ∑ |C_i| / (x - e_i)² over the nodes with C_i < 0 left and right of x, the numbers of
  nodes with C_i ≠ 0 left of x, and the slope jumps of the nodes at x;
- the node part of the curvature on (p, q) is bounded by a second-order bound: with R the nodes outside [p, q] and
  g_R(x) = ∑_R C_i log |x - e_i|, `-2 g_R(x) ≤ max(-2 g_R(p), -2 g_R(q)) + K h² / 8`, where K = 2 ∑ |C_i| /
  dist(e_i, [p, q])² over the nodes of R with C_i < 0, because each term `-2 C_i log |x - e_i| + K_i (x - p)(x - q) / 2`
  is convex on [p, q]; a node at p or q with C_i < 0 adds at most `2 |C_i| log h`, one with C_i > 0 is a singular
  term (≥ 0), as in `chordLB`.

The rest of the leaf check (polynomials, chord and tangent, main term) is that of `chordLB`. The soundness proofs are
`Trace86/CheckSoundE1.lean` (the end-point pass), `CheckSoundE2.lean` (the convexity), `CheckSoundE3.lean` (the node
facts of a leaf), `CheckSoundE4.lean` (`chordLBC_sound`, the proof of `chordLB_sound` with the node pass replaced by
these facts) and `CheckSoundE5.lean` (`leafOKE_sound`, `leavesOKE_sound`).

### 5.2 Lower bound

From `Trace86/LowerK.lean`:
```lean
theorem Trace86.trace_lower_K (ε : ℝ) (hε : 0 < ε) : (TPTraceLe (lamL - ε)).Finite
theorem Trace86.trace_lower_dec_K : (TPTraceLe (18022225 / 10000000)).Finite
```

`#print axioms`, as run in `Trace86/AxiomsK.lean`, reports `propext`, `Classical.choice` and `Quot.sound` only, for
both.

The certificate, the checker and the soundness theorems are those of the native proof. The checks are split into
modules that the kernel evaluates with `decide +kernel`:
  - `T86KE/Ep00000` ... `T86KE/Ep14956`: the end-point data of the tiling, one point each, stated for `epDataKA`, the
    same pass on recursor-level integer operations (`T86Core/CheckE.lean` proves `epDataKA = epData`);
  - `T86KL/Chunk0000` ... `T86KL/Chunk0598`: the tiling, 25 leaves each, from the end-point theorems
    (`leafOKE_of_parts`);
  - `T86K/Echk0000` ... `T86K/Echk9141`: the energy, by chunks of at most 200 terms of a row, over the literal records
    of `T86K/ELits` (`T86K/ELitsEq` checks the literals), summed in `Trace86/EKR000` ... `EKR103` and
    `Trace86/EnergyK`;
  - `T86K/Globals`: the data and the two tails;
  - `T86K/Lits`: the literal checker context `ctxLit` (`T86Core/Lits.lean`) equals the computed one.

### 5.3 Upper bound

From `Trace86U/UpperK.lean`:
```lean
theorem Trace86.trace_upper_K (hS : SmithThm15) (ε : ℝ) (hε : 0 < ε) : (TPTraceLe (lamU + ε)).Infinite
theorem Trace86.trace_upper_dec_K (hS : SmithThm15) : (TPTraceLe (18070809 / 10000000)).Infinite
```

`#print axioms`, as run in `Trace86U/AxiomsUK.lean`, reports `propext`, `Classical.choice` and `Quot.sound` only, for
both.

The certificate, the checker and the soundness theorems are those of the native proof. The checks are split into
modules that the kernel evaluates with `decide +kernel`:
  - `T86UK/Chunk0000` ... `T86UK/Chunk7168`: the tiling, two leaves each;
  - `T86UK/Mom00` ... `T86UK/Mom20`: condition (M), one module per polynomial;
  - `T86UK/Globals`: the data, the budget, the trace and the left tail;
  - `T86UK/Lits`: the literal checker context `ctxULit` (`T86UCore/Lits.lean`) equals the computed one.

The native helpers `Bench/T86K.lean` and `Bench/T86UK.lean` printed the literal contexts, records and end-point data.
They are not trusted: the kernel checks every value they supplied.

## 6. The named hypothesis `SmithThm15`

`SmithThm15` (`Trace86/Statement.lean`) concerns an interval [a, b] with b - a > 4, so that its capacity (b - a)/4
exceeds 1. Let μ be a Borel probability measure on ℝ supported in [a, b]. Suppose that, for every nonzero Q ∈ ℤ[X],
- μ {x | Q(x) = 0} = 0,
- log|Q| is μ-integrable, and
- ∫ log|Q| dμ >= 0.

Then there are distinct irreducible monic R_k ∈ ℤ[X], all of whose roots lie in [a, b], whose normalized root measures
converge weakly to μ (tested against every continuous f : ℝ → ℝ).

The three conditions are Smith's condition (1) in exact form. log|Q| is bounded above on [a, b], and Smith's integral
(with log 0 = -∞) is -∞ exactly when μ charges a root of Q.

The first condition is needed because Mathlib has `Real.log 0 = 0`. Without it, μ = δ_0 would satisfy the premise, since
∫ log|Q| dδ_0 = log|Q(0)| >= 0 for every nonzero Q ∈ ℤ[X]. The conclusion fails for δ_0, so the hypothesis would be
false and the conditional theorem empty. `Trace86/SanityU.lean` proves that δ_0, and more generally any measure with an
atom at a root of a nonzero Q ∈ ℤ[X], fails the premise.

With this condition, `SmithThm15` follows from Smith's theorem. `trace_upper_N` applies it to the measure
μ = (1 - ε) μ_0 + ε ω on [0, 6], where:
- μ_0 has the piecewise-linear density of the certificate;
- ω is the arcsine measure of [0, 6];
- ε = 1/100000.

## 7. Proved in Lean, not assumed

- **Energy smoothing** (lower bound). `AuxCommon.energySmoothing` (`AuxCommon/EnergyProof.lean`, `AuxCommon/Energy/*`)
  proves `AuxCommon.EnergySmoothing`. This is the analytic step of the energy method.
- **Closed forms** of the potential and energy of a piecewise-linear density: `Trace86.pwLinClosedForm`
  (`Trace86/ClosedForm.lean`).
- **Minimum principle** (step 1 of Lemma U1 of the paper): `Trace86.minPrinciple` (`Trace86/MinPrincipleProof.lean`).
- **Arcsine measure.** The facts used about the arcsine measure, `AuxCommon/Energy/Arcsine.lean` and
  `Trace86/Arcsine.lean`:
  - it is a probability measure;
  - its potential equals log(3/2) on [0, 6];
  - potentials are continuous (`AuxCommon/Energy/Continuity.lean`, `AuxCommon/Energy/PotentialSum.lean`).
- **Integrality** (step 2 of Lemma U1): `AuxCommon/Integrality.lean`. It gives the premise of `SmithThm15` from the
  certificate conditions. The irreducibility of the certificate polynomials is proved from root brackets and root sums
  (`Trace86U/IrredSound.lean`, `AuxCommon/RootSum.lean`).
- **From the measure to infinitely many α** (step 3 of Lemma U1): `Trace86/TraceUpper.lean`. It applies `SmithThm15`
  on [0, 6] and uses the mean of μ.
- **The reduction for the lower bound**: `Trace86/Reduction.lean`. It uses the discriminant and resultant bounds of
  `AuxCommon/Averaging.lean` and `AuxCommon/Resultant.lean`, and the finiteness of the set of α of bounded degree and
  trace (`AuxCommon/Northcott.lean`).

## 8. Certificates and regeneration

| file | sha256 |
|---|---|
| data/cert_L4_1802222_915a52c7.json (lower bound, as published: 15 polynomials, all with nonzero weight, 10,386 nodes) | 915a52c7a29583f55505e38b36a6bc4571ff7cf04160db53e189bb18759d15e1 |
| data/cert_L4_1802222_915a52c7_grid.json (the same, prepared for the checker by tools/prep86_cert.py) | f2e3ce25a74479acb71441ed8924827370fee00e351378bca62509d5692d6057 |
| data/cert_ub_A22v2_1807081_d773f831.json (upper bound: 21 polynomials, ε = 1/100000) | d773f83150881e3ef7d841d758bfc8ede45c782dd5cfce3926b13bb86aad3d4b |

The other files in `data/` (roots, moments, leaves) are untrusted hints. The Lean checker verifies every leaf.

From the project root, the Lean data and shard files are regenerated by:

```
# lower bound (t86_roots.py needs python-flint)
python3 -I tools/prep86_cert.py data/cert_L4_1802222_915a52c7.json data/cert_L4_1802222_915a52c7_grid.json
python3 -I tools/gen86_data.py data/cert_L4_1802222_915a52c7_grid.json T86Core/Data.lean
python3 -I tools/t86_roots.py data/cert_L4_1802222_915a52c7_grid.json data/roots_915a52c7.json
python3 -I tools/t86_check_ref.py data/cert_L4_1802222_915a52c7_grid.json data/leaves86e_915a52c7.json 8 data/roots_915a52c7.json -7.8738e-7
python3 -I tools/gen86_leaves.py data/leaves86e_915a52c7.json T86Core/Leaves.lean data/leaves86e.txt 10000000000 30000000000000
python3 -I tools/gen86_nshards.py data/leaves86e_915a52c7.json 150 N T86N 10000000000 30000000000000 10388
# upper bound (t86u_roots.py and the --moments step need python-flint)
python3 -I tools/gen86u_data.py data/cert_ub_A22v2_1807081_d773f831.json T86UCore/Data.lean 10000000000
python3 tools/t86u_roots.py data/cert_ub_A22v2_1807081_d773f831.json data/roots_ub_d773f831.json 10000000000
python3 tools/t86u_check_ref.py --moments data/cert_ub_A22v2_1807081_d773f831.json 10000000000 data/moments_ub_d773f831.json 80
SKIP_MOMENTS=1 python3 tools/t86u_check_ref.py data/cert_ub_A22v2_1807081_d773f831.json data/leaves_ub_d773f831.json 8 data/roots_ub_d773f831.json 10000000000
python3 -I tools/gen86u_leaves.py data/leaves_ub_d773f831.json T86UCore/Leaves.lean data/leaves_ub.txt 10000000000 6000000000000 data/moments_ub_d773f831.json
python3 -I tools/gen86u_nshards.py data/leaves_ub_d773f831.json 73 N T86UN 10000000000 6000000000000
```

In the `t86*_check_ref.py` commands, the number after the output file is the number of worker processes. The last
argument of the lower-bound command, -7.8738e-7, is the claimed lower bound of the energy (the energy of this measure is
negative); the native energy check `energy_ok` confirms it.

The published lower-bound certificate has nodes that are not multiples of 10^-12, and its support is [0.0489, 5.352].
The checker stores nodes as integers at scale 10^12, with the first node at 0 and the last at 29/5. So
`tools/prep86_cert.py` rounds every node to the nearest multiple of 10^-12 (at most 5e-13 away; the smallest gap is
1.93e-7, so the order is kept) and adds the nodes 0 and 29/5 with zero hat weights next to them, which does not change
the measure. The polynomials, their weights, λ_L, x_lo and x_hi are unchanged. The Lean checks verify the prepared
certificate itself: its energy, F > 0 on (0, ∞) and the tails.

`Trace86/LeavesN.lean` and `Trace86U/LeavesN.lean` compose the shards; `python3 -I tools/gen86_leavesN.py` and
`python3 -I tools/gen86u_leavesN.py` write them.

The kernel-only modules of the lower bound are regenerated, after `lake build t86k`, by (the number is `iLoNum`, the
claimed energy bound at scale 2^128, from `T86Core/Leaves.lean`):

```
mkdir -p scratch T86K
lake exe t86k ctx -267931530066208527361791898399625 128 > scratch/ctxlit.txt
python3 -I tools/gen86_ctxlit.py scratch/ctxlit.txt
python3 -I tools/gen86_nshards.py data/leaves86e_915a52c7.json 1 K T86K 10000000000 30000000000000 10388
python3 -I tools/gen86_epshards.py list data/leaves86e_915a52c7.json
lake exe t86k eps -267931530066208527361791898399625 128 scratch/eps.txt > scratch/eplits.txt
python3 -I tools/gen86_epshards.py emit data/leaves86e_915a52c7.json 30000000000000 25
lake exe t86k elits > scratch/elits.txt
python3 -I tools/gen86_elits.py scratch/elits.txt
python3 -I tools/gen86_echunk_list.py
lake exe t86k irows scratch/echunks.txt > scratch/echunk_vals.txt
python3 -I tools/gen86_echunks.py
python3 -I tools/gen86_ekassembly.py
python3 -I tools/gen86_kassembly.py
```

The kernel-only modules of the upper bound are regenerated, after `lake build t86uk`, by:

```
mkdir -p scratch/u2k
lake exe t86uk > scratch/u2k/ctxulit.txt
python3 -I tools/gen86u_ctxlit.py scratch/u2k/ctxulit.txt
python3 -I tools/gen86u_nshards.py data/leaves_ub_d773f831.json 7169 K T86UK 10000000000 6000000000000
python3 -I tools/gen86u_kassembly.py
```

## 9. Layout

- `AuxCore/`, `T86Core/`, `T86UCore/`: the checkers, in core Lean only (no Mathlib), precompiled for `native_decide`.
- `T86N/`, `T86UN/`: the `native_decide` shards.
- `T86K/`, `T86KE/`, `T86KL/`: the `decide +kernel` modules of the kernel-only proof of the lower bound (context, data,
  tails and energy; end-point data; tiling chunks).
- `T86UK/`: the `decide +kernel` modules of the kernel-only proof of the upper bound.
- `AuxCommon/`: shared definitions and proofs (energy smoothing, potentials, integrality, resultants, finiteness).
- `Trace86/`: statements, lower-bound soundness, the minimum principle and the step from the measure to the trace.
- `Trace86U/`: upper-bound soundness and the measure μ.
- `tools/`: generators and exact reference checkers in Python. They are untrusted; Lean re-checks everything.
- `Bench/`: small executables used during development.
- `PROVENANCE.md`: files shared with, or adapted from, a companion formalization.
