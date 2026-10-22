# Certificate formats

All rationals are JSON strings `p/q` or `p`; polynomials are lists of integer coefficients, highest degree first.

## Lower bound (`certificates/lower/`)

A JSON object with the keys

- `A`: the polynomials Q;
- `lamQ`: the multipliers λ_Q ≥ 0, one per polynomial;
- `nodes`: increasing rationals e_0 < e_1 < … < e_N;
- `rho`: N − 1 nonnegative rationals; `rho[k-1]` is the weight of the hat function h_k on [e_{k−1}, e_{k+1}] with
  peak at e_k, normalized to ∫ h_k = 1, so that g = Σ_k rho[k−1] h_k and s = Σ rho;
- `lambda`: the bound λ;
- `x_lo`, `x_hi`: the cut points 0 < x_lo < x_hi used by the programs (tails (0, x_lo] and [x_hi, ∞)).

## Upper bound (`certificates/upper/`)

A JSON object with the keys

- `A`: the polynomials Q (monic, irreducible, real-rooted);
- `b`: the weights b_Q ≥ 0, one per polynomial;
- `nodes`: rationals 0 = e_0 < e_1 < … < e_N = 6;
- `w`: N − 1 nonnegative rationals with Σ w = 1; `w[k-1]` is the weight of the unit-mass hat function h_k, so
  that μ_0 = Σ_k w[k−1] h_k(x) dx;
- `eps`: ε, the weight of the equilibrium measure ω of [0, 6] in μ = (1 − ε) μ_0 + ε ω.

Lemma 3.1 of the paper is applied with the weights (1 − ε) b_Q, and the bound is
∫ x dμ = (1 − ε) Σ_k w[k−1] (e_{k−1} + e_k + e_{k+1})/3 + 3ε.
