import os
# SO24 upper-bound LP with piecewise-linear (hat) densities on adaptive nodes and cutting planes on [0, 6].
# min int x dmu  s.t.  U_mu(x) - sum_Q b_Q log|Q(x)| >= 0 on [0,6] (grid, refined by cutting planes),
#                       int log|Q| dmu >= 0 (Q in A), mass 1, b >= 0, sum b deg <= bdeg_max.
# Lemma U1 needs the potential inequality on supp mu only; [0,6] covers the mixture with the arcsine measure of [0,6].
import sys, json, time
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import ld_hat_potential, logQ, poly_roots, hat_coefs
from so24_ub import solve_ub, support

def build_nodes(comps, base, fine, m_out, m_in, lo=0.0, hi=6.0):
    pts = set()
    for L, R in comps:
        a0, b0 = max(lo, L - m_out), min(hi, R + m_out)
        for x in np.arange(a0, b0 + 1e-12, base): pts.add(round(float(x), 12))
        for E in (L, R):
            for x in np.arange(max(lo, E - m_out), min(hi, E + m_in) + 1e-12, fine): pts.add(round(float(x), 12))
            for x in np.arange(max(lo, E - m_in), min(hi, E + m_out) + 1e-12, fine): pts.add(round(float(x), 12))
    pts.add(lo); pts.add(hi)
    return np.array(sorted(pts))

def U_of(e, w, x, chunk=4000):
    # potential of g = sum w_k hat_k at points x via slope jumps (longdouble closed form)
    out = np.empty(len(x))
    for i0 in range(0, len(x), chunk):
        out[i0:i0+chunk] = ld_hat_potential(e, x[i0:i0+chunk]) @ w
    return out

def solve_hat(A, e, xg, bdeg_max=1.0):
    n = len(e) - 2; k = len(A)
    U = ld_hat_potential(e, xg)
    LQx = np.array([logQ(q, xg) for q in A]).T
    roots = [poly_roots(q)[1] for q in A]
    LQc = np.array([ld_hat_potential(e, r).sum(axis=0) + np.log(abs(q[0])) for q, r in zip(A, roots)])
    mean = (e[:-2] + e[1:-1] + e[2:])/3.0
    deg = np.array([len(q)-1 for q in A], float)
    c = np.concatenate([mean, np.zeros(k)])
    A_ub = np.vstack([np.hstack([-U, LQx]), np.hstack([-LQc, np.zeros((k, k))]), np.concatenate([np.zeros(n), deg])[None, :]])
    b_ub = np.concatenate([np.zeros(len(xg)), np.zeros(k), [bdeg_max]])
    A_eq = np.concatenate([np.ones(n), np.zeros(k)])[None, :]
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=[1.0], bounds=(0, None), method='highs')
    if res.status != 0: raise RuntimeError(res.message)
    return res.fun, res.x[:n], res.x[n:], LQc @ res.x[:n]

def h_eval(A, e, w, bq, x):
    return U_of(e, w, x) - sum(b*logQ(q, x) for b, q in zip(bq, A) if b > 0)

if __name__ == '__main__':
    A = [list(q) for q in json.load(open(sys.argv[1]))]
    base = float(sys.argv[2]); fine = float(sys.argv[3]); tag = sys.argv[4]
    nstep = int(sys.argv[5]) if len(sys.argv) > 5 else 1000
    t0 = time.time()
    st = solve_ub(A, 5.5, nstep)
    comps = support(st, 1e-6)
    print(f"{tag}: step LP n={nstep}: {st['val']:.7f}, {len(comps)} components ({time.time()-t0:.0f}s)", flush=True)
    e = build_nodes(comps, base, fine, 0.012, 0.012)
    roots_all = np.concatenate([poly_roots(q)[1] for q in A])
    xg = np.unique(np.concatenate([e, 0.5*(e[1:] + e[:-1]), np.linspace(0, 6, 1201)]))
    xg = xg[np.min(np.abs(xg[:, None] - roots_all[None, :]), axis=1) > 1e-9]
    xf = np.unique(np.concatenate([np.linspace(0, 6, 600001), (e[:, None] + np.array([-1e-4, -3e-5, -1e-5, -2e-6, 2e-6, 1e-5, 3e-5, 1e-4])[None, :]).ravel()]))
    xf = xf[(xf >= 0) & (xf <= 6)]
    xf = xf[np.min(np.abs(xf[:, None] - roots_all[None, :]), axis=1) > 1e-9]
    print(f"  hats {len(e)-2}, grid {len(xg)}, fine {len(xf)}", flush=True)
    for it in range(25):
        t = time.time()
        val, w, bq, mom = solve_hat(A, e, xg)
        hf = h_eval(A, e, w, bq, xf)
        i = np.argmin(hf)
        print(f"  it {it}: Lambda_hat={val:.7f} min h fine={hf[i]:.3e} at {xf[i]:.5f} sum b deg={sum(b*(len(q)-1) for b, q in zip(bq, A)):.5f} "
              f"min mom={mom.min():.2e} grid={len(xg)} ({time.time()-t:.0f}s)", flush=True)
        np.save(os.path.join(os.path.dirname(os.path.abspath(__file__)), "data") + f"/ubhat_{tag}.npy", np.concatenate([[val, len(e), len(A)], e, w, bq]))
        if hf[i] > -2e-7: break
        viol = np.nonzero(hf < -1e-9)[0]
        lm = [j for j in viol if (j == 0 or hf[j] <= hf[j-1]) and (j == len(hf)-1 or hf[j] <= hf[j+1])]
        lm = sorted(lm, key=lambda j: hf[j])[:400]
        xg = np.unique(np.concatenate([xg, xf[lm]]))
    print("final", tag, val, "b:", np.round(bq, 7).tolist(), flush=True)
