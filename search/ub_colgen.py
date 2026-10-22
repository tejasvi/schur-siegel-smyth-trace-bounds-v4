import os
# Column generation for the SO24 upper-bound LP: repeatedly add the candidate polynomials with the most negative
# reduced cost sum_x tau_x log|P(x)| + s deg P (P irreducible, totally positive, not yet in A).
import sys, json, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from so24_ub import solve_ub, make_grid, support
from tp_util import factors
A = [list(q) for q in json.load(open(sys.argv[1]))]
cand_files = sys.argv[2].split(','); n = int(sys.argv[3]); xmax = float(sys.argv[4]); rounds = int(sys.argv[5])
kadd = int(sys.argv[6]); tag = sys.argv[7]
C = []
seen = set(tuple(q) for q in A)
for f in cand_files:
    for q in json.load(open(f)):
        q = [int(c) for c in q]
        if tuple(q) in seen or len(q) < 2: continue
        seen.add(tuple(q)); C.append(q)
# keep irreducible candidates only
C = [q for q in C if (lambda cf: abs(cf[0]) == 1 and len(cf[1]) == 1 and cf[1][0][1] == 1)(factors(q))]
roots = {tuple(q): np.sort(np.roots(q).real) for q in C}
print(f"{tag}: |A|={len(A)}, {len(C)} irreducible candidates, n={n}, xmax={xmax}", flush=True)
hist = []
for it in range(rounds + 1):
    t = time.time()
    sol = solve_ub(A, xmax, n)
    m = sol['tau'] > 1e-12; xs = sol['x'][m]; tw = sol['tau'][m]
    red = []
    for q in C:
        r = roots[tuple(q)]
        dd = np.abs(xs[:, None] - r[None, :])
        if dd.min() < 1e-12: continue
        red.append((float(tw @ np.log(dd).sum(axis=1)) + sol['s']*(len(q) - 1), q))
    red.sort()
    bdeg = float(sum(b*(len(q)-1) for b, q in zip(sol['bq'], A)))
    print(f"  round {it}: Lambda={sol['val']:.7f} |A|={len(A)} sum b deg={bdeg:.4f} s={sol['s']:.3e} |tau|={tw.sum():.4f} "
          f"ncomp={len(support(sol))} best red={red[0][0] if red else 0:+.3e} ({time.time()-t:.0f}s)", flush=True)
    hist.append((len(A), sol['val']))
    act = [(round(float(b), 7), q) for b, q in zip(sol['bq'], A) if b > 1e-9]
    json.dump(dict(A=A, hist=hist, active=act), open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "data") + f"/colgen_{tag}.json", 'w'))
    if it == rounds or not red or red[0][0] >= -1e-9: break
    new = [q for v, q in red[:kadd] if v < -1e-9]
    print("    adding:", [(round(v, 5), q) for v, q in red[:kadd] if v < -1e-9][:kadd], flush=True)
    A = A + new
    C = [q for q in C if q not in new]
print("final", tag, hist[-1])
