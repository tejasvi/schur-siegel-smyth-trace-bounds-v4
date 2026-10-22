# Upper and lower bounds for the Schur–Siegel–Smyth trace problem: certificates and programs (version 4)

This repository accompanies version 4 of the paper *Upper and lower bounds for the Schur–Siegel–Smyth trace problem* by
Tejasvi Singh Tomar (doi:10.5281/zenodo.23563968; version 1: doi:10.5281/zenodo.23540816; version 2: doi:10.5281/zenodo.23548809;
version 3: doi:10.5281/zenodo.23553617). Version 4 adds a kernel-only Lean proof of the lower bound of Theorem 1.1,
and its native Lean proof of that bound needs 153 checks instead of the 303 of version 3. Certificates, programs, logs
and controls are those of version 2.

## What the paper proves

An algebraic integer is totally positive if all of its conjugates are real and positive. The constant C_86 is the
lower limit of tr(α)/deg(α) over the totally positive algebraic integers α; Orloski, Talebizadeh Sardari and Smith
(Math. Comp. 94 (2025), 2005–2040) call it λ_SSS.

- **Theorem 1.1.** 901111277/500000000 ≤ C_86 ≤ 81383685642728309283453/45035996273705240000000, so
  1.8022225 < C_86 < 1.8070809.
- **Lower bound (Lemma 2.1).** C_86 ≥ λ whenever
  F(x) = x − λ − Σ_Q λ_Q log|Q(x)| − 2 U_g(x) + I(g)/s ≥ 0 for every x > 0 that is not a root of one of the Q,
  where the Q are nonzero integer polynomials, λ_Q ≥ 0, g is a bounded nonnegative density with compact support
  and mass s > 0, U_g(x) = ∫ log|x − y| g(y) dy and I(g) = ∫ U_g g.
- **Upper bound (Lemma 3.1).** C_86 ≤ ∫ x dμ for a probability measure μ on [0, X], X > 4, with a continuous
  potential, if for some primitive irreducible integer polynomials Q with weights b_Q ≥ 0 and Σ b_Q deg Q < 1:
  (U1) U_μ(x) − Σ_Q b_Q log|Q(x)| ≥ 0 on the support of μ, and (U2) ∫ log|Q| dμ ≥ 0 for each Q. The proof uses
  Smith's Theorem 1.5 (Ann. of Math. 200 (2024), 71–122). The certificates use μ = (1 − ε) μ_0 + ε ω, where μ_0
  has a continuous piecewise-linear density on [0, 6] and ω is the equilibrium (arcsine) measure of [0, 6].

## Contents

| Path | What it is |
|---|---|
| `certificates/lower/cert_L4_1802222_915a52c7.json` | Certificate of the lower bound of Theorem 1.1, 901111277/500000000. |
| `certificates/lower/variant_cert_L4_1802221_4645ac71.json` | The same measure and multipliers with λ = 1400190571/776924729, 2·10^-6 instead of 1.1·10^-6 below the value of the linear program, which leaves more room in the checks. |
| `certificates/lower/cert_L3_1802217_4040e266.json` | Earlier certificate found by the same method: C_86 ≥ 63361515736283/35157522000000 > 1.8022179. |
| `certificates/lower/cert_A15_1802203_d1747e6a.json` | Lower certificate of version 1: C_86 ≥ 901101631/500000000. |
| `certificates/lower/cert_A12_1802189_f1a60531.json` | Earlier certificate without the polynomials of degree 10: C_86 ≥ 185185220/102755699 > 1.8021892. |
| `certificates/upper/cert_ub_A22v2_1807081_d773f831.json` | Certificate of the upper bound of Theorem 1.1 (ε = 1/100000). |
| `certificates/upper/cert_ub_A22_1807129_83e03d16.json` | Earlier certificate with the same polynomials and nodes, other weights and ε = 1/20000: C_86 ≤ 1660935360692531465493/919101964769480000000 < 1.8071286. |
| `CERT_FORMAT.md` | The two certificate formats. |
| `checkers/check86.py` | First program for the lower bound: potential and energy by the closed forms of Lemma 2.3 of the paper, 200-bit balls, real roots counted by a Sturm sequence and their brackets bisected exactly to width at most 2^-100, polynomials enclosed on intervals through exact Taylor coefficients at the midpoint. |
| `checkers/indep86.py` | Second program for the lower bound, written separately: potential and energy integrated piece by piece, 256-bit balls, all complex roots enclosed, real root brackets bisected exactly to width at most 2^-110, polynomials bounded on intervals through their roots. |
| `checkers/check86ub.py` | First program for the upper bound: the chord bound of Lemma 2.4 of the paper, with root windows. |
| `checkers/ub86audit.py` | Second program for the upper bound, written independently of the first from Lemma 3.1 and the certificate format only: second-order Taylor bounds at midpoints. |
| `logs/` | Output of the programs on the certificates, and `COMMANDS.txt`. |
| `controls/` | Modified certificates and the output of both programs on them (Table 2 of the paper). |
| `search/` | The programs that found the certificates (numerics only; not needed to check them). `search/lower/` holds those for the collocation certificate of the lower bound, with the commands in `search/lower/README_search.txt`. |
| `lean/` | Lean 4 sources of the formal proofs (Section 5 of the paper). |

`SHA256SUMS` lists all files. How the logged runs relate to the released programs is described under *Notes on the
shipped files*.

## Requirements

Linux, Python 3 (we used 3.12.13 and 3.13.5) and python-flint 0.9 (FLINT 3.6.0); `check86.py` and `check86ub.py` also
need numpy. All four programs set the `multiprocessing` start method to `fork` explicitly (on Linux the default is
`forkserver` from Python 3.14 on). The search programs need numpy, scipy, cvxpy and the Clarabel solver.

## How to run

From the root of this repository, with the number of worker processes as the last argument:

```
python3 -I checkers/check86.py    certificates/lower/cert_L4_1802222_915a52c7.json 16
python3 -I checkers/indep86.py    certificates/lower/cert_L4_1802222_915a52c7.json 16
python3 -I checkers/check86ub.py  certificates/upper/cert_ub_A22v2_1807081_d773f831.json 16
python3 -I checkers/ub86audit.py  certificates/upper/cert_ub_A22v2_1807081_d773f831.json 16
```

Each program exits with status 0 if and only if the certificate is verified; it ends with a verdict line, or stops with an
error when it cannot confirm a root window. On the lower certificate, with 192 processes, `check86.py` took 174 s and
`indep86.py` 597 s; each upper-bound program needs about 3.5 CPU-minutes. `indep86.py`, `ub86audit.py` and
`check86ub.py` refuse to run under `python -O`, which would disable assertions; `check86.py` does not rely on
assertions.

## The Lean proofs

`lean/` is a Lean 4 project (toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib at commit c55e6e786f49; see
`lean-toolchain` and `lake-manifest.json`). From `lean/`:

```
lake exe cache get
lake build Trace86.LowerN Trace86.AxiomsN Trace86U.Upper Trace86U.AxiomsU Trace86.SanityU
lake env lean Trace86/AxiomsN.lean
lake env lean Trace86U/AxiomsU.lean
```

The last two commands print the two theorems and the axioms they use. `Trace86.trace_lower_N` states that, for every
ε > 0, only finitely many totally positive algebraic integers α satisfy tr(α) ≤ (901111277/500000000 − ε) deg(α). This
is the lower bound of Theorem 1.1 (certificate `cert_L4_1802222_915a52c7.json`), and `Trace86.trace_lower_dec_N` is its
form for the decimal bound 1.8022225. The theorem has no hypotheses. `Trace86.trace_upper_N` states that, if `SmithThm15` (Smith's Theorem 1.5
for an interval) holds, then for every ε > 0 infinitely many totally positive algebraic integers satisfy
tr(α) ≤ (λ_U + ε) deg(α), where λ_U = 81383685642728309283453/45035996273705240000000 is the upper bound of Theorem 1.1
(certificate `cert_ub_A22v2_1807081_d773f831.json`). The finite checks on the certificates are evaluated with
`native_decide` (153 checks for the lower bound and 78 for the upper bound); besides the three standard axioms of Lean,
each proof uses one auxiliary axiom per check.

The kernel-only versions are built by

```
lake build Trace86.AxiomsK Trace86U.AxiomsUK
```

which takes about 310 CPU-hours for the lower bound and about 55 for the upper bound (up to about 7.6 GB of memory for
one module). The theorems `Trace86.trace_lower_K` and `Trace86.trace_upper_K` have the same statements as the two
theorems above, and `trace_lower_dec_K` and `trace_upper_dec_K` are their forms for the decimal bounds 1.8022225 and
1.8070809. In these proofs every check is decided by Lean's kernel with `decide +kernel`, and the theorems depend only
on the three standard axioms; Lean's compiler is not trusted for them.

`STATEMENTS.md` in `lean/` lists the definitions and the theorems. The certificate data in `lean/data/` are turned into
Lean files by the programs in `lean/tools/`.

## The logs and controls

`logs/COMMANDS.txt` gives the commands that produced the logs.

- `controls/lower/`: 22 modified copies of the lower certificate of Theorem 1.1, made by `make_neg.py`, with the output
  of both programs (`logs/`). `run_controls.sh CHECK86 NPROC` reruns them together with the variant. Run it from a
  directory that holds `indep86.py`, the program named by CHECK86, the certificates and the modified copies in a
  subdirectory `negs/`.
- `controls/lower_A15/`: the 19 modified copies of the version 1 lower certificate, with the output of both programs.
- `controls/upper/`: modified copies of the upper certificate, made by `make_controls_ub2.py`, with the output of both
  programs (`logs/`).
- `controls/upper/switches_A22v2/` and `switches_A22/`: runs of `ub86audit.py` on the two upper certificates with the
  environment switches described in its docstring. `negs.sh` is run from a directory that holds `ub86audit.py` and the
  certificate; the results are in `negs.txt` and `neg_*.log`.

## Notes on the shipped files

- The logs were produced by frozen copies of the programs. The SHA-256 hashes of these copies begin with 23983407 for
  `check86.py`, f3f503c9 for `indep86.py`, a69381c1 for `check86ub.py` and 3ae244be for `ub86audit.py`. The logs that
  version 1 shipped for its lower certificates used the predecessor 5ca8ed61 of `check86.py`, which differs only in the
  bisection of the root brackets. They also used the predecessor 7aa227fd of `indep86.py`, which differs only in that
  bisection and in the narrowest windows. The released copies differ from the frozen copies only in
  their docstrings.
- In the tracebacks in `controls/lower/logs/` and `controls/lower_A15/logs/`, the home directory of the machine that
  ran them was removed from the paths.
- `lean/STATEMENTS.md` differs from the Lean release in one place: in Section 8, the commands that regenerate the
  kernel-only modules of the lower bound first create `T86K/`, which a clean tree lacks. `lean/SHA256SUMS` lists the
  edited file.
- Some comments in the lower-bound programs refer to Lemma 2.1 of the paper as Lemma "T1", and the upper-bound programs
  refer to Lemma 3.1 as Lemma "U1".

## Licence

Apache-2.0 for the programs (see `LICENSE`); the certificates, the data and the logs are released under CC BY 4.0 with the
paper.
