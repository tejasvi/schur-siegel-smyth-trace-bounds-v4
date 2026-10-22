import os
# Parallel enumeration of irreducible monic integer polynomials of degree d with all roots real in [0, R] and trace <= T,
# split into tasks by the three leading free coefficients (derivative pruning as in enum_tp.py). Results are appended
# as JSON lines (one per finished task) so partial results survive.
import sys, json, time
import numpy as np
from math import comb
import multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enum_tp import realroots_in, crit_interval
def crange(c, m, d, R):
    s = [0.0] + [comb(k, m)*c[k] for k in range(m+1, d+1)]
    lo, hi = crit_interval(np.array(s, dtype=float), R)
    return s, lo, hi
def tasks(d, R, T):
    out = []
    c = [0]*(d+1); c[d] = 1
    for t in range(0, int(T) + 1):
        c[d-1] = -t
        if not realroots_in(np.array([1.0, -t/d][::-1][::-1], dtype=float), R) and False: pass
        s2, lo2, hi2 = crange(c, d-2, d, R)
        for a2 in range(int(np.ceil(lo2 - 1e-9)), int(np.floor(hi2 + 1e-9)) + 1):
            c[d-2] = a2
            if not realroots_in(np.array(([a2] + s2[1:])[::-1], dtype=float), R): continue
            if d - 3 < 0: out.append((t, a2, None)); continue
            s3, lo3, hi3 = crange(c, d-3, d, R)
            for a3 in range(int(np.ceil(lo3 - 1e-9)), int(np.floor(hi3 + 1e-9)) + 1):
                c[d-3] = a3
                if not realroots_in(np.array(([a3] + s3[1:])[::-1], dtype=float), R): continue
                out.append((t, a2, a3))
            c[d-3] = 0
        c[d-2] = 0
    return out
D = R_ = None
def work(task):
    import flint
    d, R = D, R_
    t, a2, a3 = task
    c = [0]*(d+1); c[d] = 1; c[d-1] = -t; c[d-2] = a2; c[d-3] = a3
    found = []
    def rec(m):
        s, lo, hi = crange(c, m, d, R)
        if hi < lo - 1e-9: return
        for cm in range(int(np.ceil(lo - 1e-9)), int(np.floor(hi + 1e-9)) + 1):
            c[m] = cm
            if not realroots_in(np.array(([cm] + s[1:])[::-1], dtype=float), R): continue
            if m == 0:
                p = c[::-1]
                fac = flint.fmpz_poly(c).factor()
                if len(fac[1]) == 1 and fac[1][0][1] == 1 and fac[1][0][0].degree() == d: found.append(list(p))
            else: rec(m-1)
        c[m] = 0
    if d - 4 >= 0: rec(d-4)
    return task, found
if __name__ == '__main__':
    d = int(sys.argv[1]); R = float(sys.argv[2]); T = float(sys.argv[3]); out = sys.argv[4]; nproc = int(sys.argv[5])
    D, R_ = d, R
    t0 = time.time()
    tk = tasks(d, R, T)
    print(f"d={d} R={R} T={T}: {len(tk)} tasks ({time.time()-t0:.1f}s)", flush=True)
    n = 0; npoly = 0
    with mp.get_context('fork').Pool(nproc) as pool, open(out, 'a') as fh:
        for task, found in pool.imap_unordered(work, tk, chunksize=1):
            fh.write(json.dumps({"task": task, "polys": found}) + "\n"); fh.flush()
            n += 1; npoly += len(found)
            if n % 200 == 0: print(f"  {n}/{len(tk)} tasks, {npoly} irreducible ({time.time()-t0:.0f}s)", flush=True)
    print(f"done d={d}: {npoly} irreducible polys ({time.time()-t0:.0f}s)", flush=True)
