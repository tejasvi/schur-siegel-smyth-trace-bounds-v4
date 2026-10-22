import os
# Column generation for the SO24 upper-bound LP with vectorized pricing over a large pool of irreducible totally
# positive polynomials: reduced cost of P = sum_{roots r} U_tau(r) + s deg P (P monic, real-rooted).
import sys, json, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from so24_ub import solve_ub, support
A = [list(q) for q in json.load(open(sys.argv[1]))]
cand_files = sys.argv[2].split(','); n = int(sys.argv[3]); xmax = float(sys.argv[4]); rounds = int(sys.argv[5])
kadd = int(sys.argv[6]); tag = sys.argv[7]
seen = set(tuple(q) for q in A); C = []
for f in cand_files:
    for q in json.load(open(f)):
        q = tuple(int(c) for c in q)
        if q in seen or len(q) < 2 or q[0] != 1: continue
        seen.add(q); C.append(q)
t = time.time()
roots = []; starts = [0]
for q in C:
    r = np.roots(q).real; roots.append(r); starts.append(starts[-1] + len(r))
R = np.concatenate(roots); starts = np.array(starts[:-1]); deg = np.array([len(q) - 1 for q in C])
print(f"{tag}: |A|={len(A)}, pool {len(C)} polys, {len(R)} roots ({time.time()-t:.0f}s)", flush=True)
alive = np.ones(len(C), bool); hist = []
for it in range(rounds + 1):
    t = time.time()
    sol = solve_ub(A, xmax, n)
    m = sol['tau'] > 1e-12; xs = sol['x'][m]; tw = sol['tau'][m]
    UR = np.empty(len(R))
    for i0 in range(0, len(R), 20000):
        UR[i0:i0+20000] = np.log(np.abs(R[i0:i0+20000, None] - xs[None, :]) + 1e-300) @ tw
    red = np.add.reduceat(UR, starts) + sol['s']*deg
    red[~alive] = np.inf
    order = np.argsort(red)
    bdeg = float(sum(b*(len(q)-1) for b, q in zip(sol['bq'], A)))
    print(f"  round {it}: Lambda={sol['val']:.7f} |A|={len(A)} sum b deg={bdeg:.4f} s={sol['s']:.2e} |tau|={tw.sum():.4f} "
          f"ncomp={len(support(sol))} best red={red[order[0]]:+.3e} ({time.time()-t:.0f}s)", flush=True)
    hist.append((len(A), sol['val']))
    act = [(round(float(b), 7), q) for b, q in zip(sol['bq'], A) if b > 1e-9]
    json.dump(dict(A=A, hist=hist, active=act), open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "data") + f"/colgen2_{tag}.json", 'w'))
    if it == rounds or red[order[0]] >= -1e-9: break
    new = [list(C[j]) for j in order[:kadd] if red[j] < -1e-9]
    print("    adding:", [(round(float(red[j]), 5), list(C[j])) for j in order[:kadd] if red[j] < -1e-9], flush=True)
    for j in order[:kadd]: alive[j] = False
    A = A + new
print("final", tag, hist[-1], flush=True)
