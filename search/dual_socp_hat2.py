# Dual SOCP with piecewise-linear (hat) reference densities on adaptive nodes, cutting planes in x.
import os
import numpy as np, cvxpy as cp, sys, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import *
def adaptive_nodes(A, lo, hi, base, fine, halfwin, extra=()):
    pts = set(np.round(np.arange(lo, hi + 1e-12, base), 12))
    centers = [r for q in A for r in np.roots(q).real if lo < r < hi] + list(extra)
    for r in centers:
        for x in np.arange(r - halfwin, r + halfwin + 1e-12, fine):
            if lo < x < hi: pts.add(round(float(x), 12))
    return np.array(sorted(pts))
def solve(A, e, xgrid, C=10.0, xsmin=0.01):
    n = len(e) - 2
    K = stable_hat_energy_matrix(e)
    P = -(K - C*np.ones((n, n))); ev, V = np.linalg.eigh(P)
    R = (V*np.sqrt(np.maximum(ev, 0))).T
    U = ld_hat_potential(e, xgrid); LQ = np.array([logQ(q, xgrid) for q in A]).T
    lam = cp.Variable(); lQ = cp.Variable(len(A), nonneg=True); rho = cp.Variable(n, nonneg=True); t = cp.Variable()
    s = cp.sum(rho)
    cons = [xgrid - lam - LQ @ lQ - 2*(U @ rho) + t >= 0, t <= C*s - cp.quad_over_lin(R @ rho, s), s >= 1e-3]
    zero = np.nonzero(e[:-2] < xsmin)[0]          # hats whose left foot is below xsmin carry no mass
    if len(zero): cons.append(rho[zero] == 0)
    prob = cp.Problem(cp.Maximize(lam), cons)
    try:
        prob.solve(solver='CLARABEL')
    except Exception as ex:
        print("  clarabel failed, retry with relaxed settings:", ex, flush=True)
        prob.solve(solver='CLARABEL', max_iter=400, tol_gap_abs=1e-7, tol_gap_rel=1e-7, tol_feas=1e-7, static_regularization_constant=1e-7)
    return lam.value, lQ.value, np.maximum(rho.value, 0), t.value, K, ev.min()
def F_eval(A, e, lamv, lQv, rhov, K, x):
    s = rhov.sum(); c = (rhov @ K @ rhov)/s
    return x - lamv - sum(lQv[i]*logQ(q, x) for i, q in enumerate(A)) - 2*(ld_hat_potential(e, x) @ rhov) + c
HW = 8
if __name__ == '__main__':
    A = json.load(open(sys.argv[1])); base = float(sys.argv[2]); fine = float(sys.argv[3]); tag = sys.argv[4]
    hi = float(sys.argv[5]) if len(sys.argv) > 5 else 5.8
    if len(sys.argv) > 6:   # node set from a support estimate (step primal npy: a, b, mu)
        sa, sb, smu = np.load(sys.argv[6]); dens = smu/(sb - sa); on = dens > 1e-3*dens.max()
        d_ = np.diff(np.concatenate([[0], on.astype(int), [0]])); st = np.nonzero(d_ == 1)[0]; en = np.nonzero(d_ == -1)[0]
        pts = set()
        for i0, i1 in zip(st, en):
            L, R = sa[i0], sb[i1-1]
            for x in np.arange(L - 0.02, R + 0.02 + 1e-12, base): pts.add(round(float(x), 12))
            for edge in (L, R):
                for x in np.arange(edge - HW*fine, edge + HW*fine + 1e-12, fine): pts.add(round(float(x), 12))
        pts = sorted(p_ for p_ in pts if 0.0 <= p_ <= hi)
        e = np.array(pts)
    else:
        e = adaptive_nodes(A, 0.0, hi, base, fine, 15*fine)
    print(f"{tag}: hats {len(e)-2} on [0,{hi}] (base {base}, fine {fine})", flush=True)
    xgrid = np.unique(np.concatenate([np.geomspace(1e-6, 0.02, 200), np.linspace(0.02, 6.5, 2500), np.linspace(6.5, 14, 100), e[1:-1]]))
    xf = np.unique(np.concatenate([np.geomspace(1e-8, 0.02, 3000), np.linspace(0.02, 6.5, 150000), np.linspace(6.5, 20, 2000)]))
    roots_all = np.array([r for q in A for r in np.roots(q).real])
    def drop_roots(xs): return xs[np.min(np.abs(xs[:, None] - roots_all[None, :]), axis=1) > 1e-9]
    xgrid = drop_roots(xgrid); xf = drop_roots(xf)
    import os
    gfile = f"grid_{tag}.npy"
    if os.path.exists(gfile): xgrid = np.unique(np.concatenate([xgrid, np.load(gfile)])); print("  loaded grid", len(xgrid), flush=True)
    for it in range(12):
        t0 = time.time()
        lamv, lQv, rhov, tv, K, mineig = solve(A, e, xgrid)
        F = F_eval(A, e, lamv, lQv, rhov, K, xf); ok = np.isfinite(F); Fmin = F[ok].min()
        print(f"  it {it}: lambda={lamv:.7f} l0={rhov.sum():.5f} min F fine={Fmin:.3e} at x={xf[ok][np.argmin(F[ok])]:.5f} grid={len(xgrid)} ({time.time()-t0:.0f}s)", flush=True)
        np.save(f"socphat_{tag}.npy",
                np.concatenate([[lamv, len(e)], lQv, e, rhov]))
        if Fmin > -1e-9: break
        Fv = np.where(ok, F, np.inf); viol = np.nonzero(Fv < 0)[0]
        lm = [i for i in viol if (i == 0 or Fv[i] <= Fv[i-1]) and (i == len(Fv)-1 or Fv[i] <= Fv[i+1])]
        lm = sorted(lm, key=lambda i: Fv[i])[:300]
        xgrid = np.unique(np.concatenate([xgrid, xf[lm]])); np.save(gfile, xgrid)
    print("final:", tag, "lambda", lamv, "lQ", np.round(lQv, 6).tolist())
