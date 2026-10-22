Search programs for the two collocation certificates of the lower bound on C_86 (polynomial set A15 = A15.json).
They produce the reference measure and multipliers; the certificates are checked only by check86v4 (shipped separately).

Software: Python 3.12, numpy 2.5.4, scipy 1.18.1 (HiGHS linear programs), cvxpy 1.9.3 with Clarabel 0.11.1 (steps 1-2).
Run every command from the directory holding these files; outputs are written to the current directory. The linear algebra
is multithreaded, so a rerun reproduces our numbers only up to floating-point rounding; the certificates that were checked
are the frozen JSON files themselves.

Certificate L3 (C_86 >= 63361515736283/35157522000000 = 1.8022179...)
  1. python run_primal_json.py A15.json 1300 5.8 A15n1300
       step-density primal on [0, 5.8], 1300 cells -> mu_A15n1300.npy (value 1.8022490)
  2. python lb_primal_hat.py A15.json mu_A15n1300.npy 0.0025 0.0003 20 A15p2
       hat-density primal on nodes adapted to that support -> lbph_A15p2_primal.npy (value 1.80223287, 4149 hats)
  3. python lb_colloc_v3.py A15.json lbph_A15p2_primal.npy 4500 80 e4500 60
       collocation on the support envelope split at every active root, at least 60 cosine nodes per interval; converged
       after 26 rounds (6041 hats); then the 17-variable multiplier LP -> colloc_e4500.npy (lambda 1.802219008)
  4. python export_cert.py colloc_e4500.npy A15.json 2.6e-6 cert_L3_margin26.json
       rational export (weights in multiples of 2^-48), lambda = 63361463/35157522 = 1.802216408
  5. python raise_lambda.py cert_L3_margin26.json 15 10000000 cert_L3.json
       lambda = 63361515736283/35157522000000 (margin 1.1e-6 below the LP value)

Certificate L4 (C_86 >= 901111277/500000000 = 1.802222554)
  6. python lb_colloc4.py A15.json colloc_e4500_state.npy 8 g4 1e-6
       restart from the converged L3 state; intervals whose F dips below -1e-6 between nodes get 30% more nodes; the state
       after round 7 (10,254 hats) is colloc_g4_state.npy (the script then also runs its own final LP, which may be skipped)
  7. python finalize_par.py A15.json colloc_g4_state.npy colloc_g4_it7LP.npy 40
       multiplier LP with the potentials computed by 40 processes -> lambda 1.802223655
  8. python export_cert.py colloc_g4_it7LP.npy A15.json 1.1e-6 cert_L4.json
       lambda = 901111277/500000000

Each script is the version that was run, except that the import path is taken from the script's own directory and output
files go to the current directory (the run versions used fixed directories).
