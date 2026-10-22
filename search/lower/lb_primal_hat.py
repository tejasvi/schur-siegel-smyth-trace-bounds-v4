# Lower bound, fast route: (1) hat-density primal SOCP (min int x dmu s.t. int log|Q| dmu >= 0, I(mu) >= 0) on nodes
# adapted to a step-primal support; (2) reference measure nu := the hat optimum; (3) LP in the multipliers
# (lambda, lambda_Q, lambda_0) on a fine grid. Saves [lambda, ne, lQ, e, rho = lambda_0 w] for export_cert.py.
import sys, json, time
import numpy as np, cvxpy as cp
from scipy.optimize import linprog
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import stable_hat_energy_matrix, ld_hat_potential, logQ, poly_roots
def support_nodes(sfile, base, fine, hw, hi=5.8, margin=0.02):
    sa, sb, smu = np.load(sfile); dens = smu/(sb - sa); on = dens > 1e-3*dens.max()
    d_ = np.diff(np.concatenate([[0], on.astype(int), [0]])); st = np.nonzero(d_ == 1)[0]; en = np.nonzero(d_ == -1)[0]
    pts = set([0.0])
    for i0, i1 in zip(st, en):
        L, R = sa[i0], sb[i1-1]
        for x in np.arange(L - margin, R + margin + 1e-12, base): pts.add(round(float(x), 12))
        for edge in (L, R):
            for x in np.arange(edge - hw*fine, edge + hw*fine + 1e-12, fine): pts.add(round(float(x), 12))
    return np.array(sorted(p for p in pts if 0.0 <= p <= hi)), len(st)
def hat_primal(A, e, C=10.0, xsmin=0.01):
    n = len(e) - 2
    K = stable_hat_energy_matrix(e)
    P = -(K - C*np.ones((n, n))); ev, V = np.linalg.eigh(P)
    R = (V*np.sqrt(np.maximum(ev, 0))).T
    LQc = np.array([ld_hat_potential(e, poly_roots(q)[1]).sum(axis=0) + np.log(abs(q[0])) for q in A])
    mean = (e[:-2] + e[1:-1] + e[2:])/3.0
    w = cp.Variable(n, nonneg=True)
    cons = [cp.sum(w) == 1, LQc @ w >= 0, cp.sum_squares(R @ w) <= C]
    zero = np.nonzero(e[:-2] < xsmin)[0]
    if len(zero): cons.append(w[zero] == 0)
    prob = cp.Problem(cp.Minimize(mean @ w), cons)
    prob.solve(solver='CLARABEL')
    wv = np.maximum(w.value, 0); wv /= wv.sum()
    return prob.value, wv, K, LQc, ev.min()
def multiplier_lp(A, e, w, K, xf):
    U = np.empty(len(xf))
    for i0 in range(0, len(xf), 10000): U[i0:i0+10000] = ld_hat_potential(e, xf[i0:i0+10000]) @ w
    I = float(w @ K @ w)
    LQ = np.array([logQ(q, xf) for q in A]).T
    k = len(A)
    # variables [lam, lQ (k), l0]; constraints: lam + LQ lQ + l0 (2U - I) <= x
    A_ub = np.hstack([np.ones((len(xf), 1)), LQ, (2*U - I)[:, None]])
    c = np.zeros(k + 2); c[0] = -1.0
    bounds = [(None, None)] + [(0, None)]*(k + 1)
    res = linprog(c, A_ub=A_ub, b_ub=xf, bounds=bounds, method='highs')
    if res.status != 0: raise RuntimeError(res.message)
    lam = res.x[0]; lQ = res.x[1:k+1]; l0 = res.x[-1]
    F = xf - lam - LQ @ lQ - l0*(2*U - I)
    return lam, lQ, l0, I, F
if __name__ == '__main__':
    A = json.load(open(sys.argv[1])); sfile = sys.argv[2]; base = float(sys.argv[3]); fine = float(sys.argv[4])
    hw = int(sys.argv[5]); tag = sys.argv[6]
    t0 = time.time()
    e, ncomp = support_nodes(sfile, base, fine, hw)
    print(f"{tag}: {len(e)-2} hats, {ncomp} support components (base {base}, fine {fine}, hw {hw})", flush=True)
    val, w, K, LQc, mineig = hat_primal(A, e)
    print(f"  hat primal = {val:.8f}  I = {w @ K @ w:.3e}  min mom = {(LQc @ w).min():.2e}  P mineig {mineig:.1e} ({time.time()-t0:.0f}s)", flush=True)
    roots_all = np.concatenate([poly_roots(q)[1] for q in A])
    xf = np.unique(np.concatenate([np.geomspace(1e-8, 0.02, 3000), np.linspace(0.02, 6.5, 200001), np.linspace(6.5, 20, 2000),
                                   (e[1:-1, None] + np.array([-1e-6, 1e-6, -1e-4, 1e-4])[None, :]).ravel()]))
    xf = xf[(xf > 0)]
    xf = xf[np.min(np.abs(xf[:, None] - roots_all[None, :]), axis=1) > 1e-9]
    lam, lQ, l0, I, F = multiplier_lp(A, e, w, K, xf)
    print(f"  multiplier LP: lambda = {lam:.8f}  l0 = {l0:.6f}  I(nu) = {I:.3e}  min F = {F.min():.2e}  lQ = {np.round(lQ, 6).tolist()} ({time.time()-t0:.0f}s)", flush=True)
    np.save(f"lbph_{tag}.npy", np.concatenate([[lam, len(e)], lQ, e, l0*w]))
    np.save(f"lbph_{tag}_primal.npy", np.concatenate([[val, len(e)], e, w]))
