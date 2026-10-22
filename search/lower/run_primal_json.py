# Step primal (min int x dmu s.t. int log|Q| dmu >= 0, I(mu) >= 0) for a polynomial set read from JSON; saves [a; b; mu].
import sys, json, time
import numpy as np
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from primal import solve_primal
A = json.load(open(sys.argv[1])); n = int(sys.argv[2]); xmax = float(sys.argv[3]); tag = sys.argv[4]
t = time.time()
val, rv, a, b, K, L, duals = solve_primal(A, 0.0, xmax, n)
print(f"{tag}: |A|={len(A)} n={n} xmax={xmax} primal={val:.7f} energy={rv @ K @ rv:.3e} ({time.time()-t:.0f}s)", flush=True)
print("  duals logQ:", np.round(duals[1], 6).tolist(), " energy dual:", duals[2], flush=True)
print("  int log|Q| dmu:", np.round(L @ rv, 7).tolist(), flush=True)
np.save(f"mu_{tag}.npy", np.vstack([a, b, rv]))
