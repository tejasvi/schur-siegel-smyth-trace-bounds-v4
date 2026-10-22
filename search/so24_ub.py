import os
# Upper-bound LP of Orloski-Sardari (SO24, (11)): minimize int x dmu over step densities mu on cells of [0, xmax]
# subject to U_mu(x) >= sum_Q b_Q log|Q(x)| on a grid of x in R, int log|Q| dmu >= 0 (Q in A), mass 1,
# b_Q >= 0, sum_Q b_Q deg Q <= 1 (the point at infinity).  Duals: tau (grid multipliers of the potential
# constraint) and s (multiplier of sum b deg <= 1); a new polynomial P lowers the value iff
# sum_x tau_x log|P(x)| + s deg P < 0 (reduced cost of b_P).
import sys, json, time
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import G, cells, potential, logQ_cell_avg, logQ, poly_roots

def make_grid(A, xmax, n, extra=()):
    a, b = cells(0.0, xmax, n)
    xs = [-np.geomspace(1e-5, 4.0, 120), np.linspace(0.0, xmax, 4*n + 1), xmax + np.geomspace(1e-4, 40.0, 150), np.asarray(extra, float)]
    x = np.unique(np.concatenate(xs))
    roots = np.concatenate([poly_roots(q)[1] for q in A]) if A else np.zeros(0)
    if len(roots):
        x = x[np.min(np.abs(x[:, None] - roots[None, :]), axis=1) > 1e-7]
    return x

def solve_ub(A, xmax=6.0, n=600, x=None, verbose=False):
    a, b = cells(0.0, xmax, n); m = 0.5*(a + b); k = len(A)
    if x is None: x = make_grid(A, xmax, n)
    U = potential(a, b, x)                                   # (nx, n)
    LQx = np.array([logQ(q, x) for q in A]).T if k else np.zeros((len(x), 0))      # (nx, k)
    LQc = np.array([logQ_cell_avg(q, a, b) for q in A]) if k else np.zeros((0, n))  # (k, n)
    deg = np.array([len(q) - 1 for q in A], float)
    # variables z = [r (n), bQ (k)]
    c = np.concatenate([m, np.zeros(k)])
    A_ub = np.vstack([np.hstack([-U, LQx]),                  # -(U r - LQx b) <= 0
                      np.hstack([-LQc, np.zeros((k, k))]),   # -int log|Q| dmu <= 0
                      np.concatenate([np.zeros(n), deg])[None, :]])   # sum b deg <= 1
    b_ub = np.concatenate([np.zeros(len(x)), np.zeros(k), [1.0]])
    A_eq = np.concatenate([np.ones(n), np.zeros(k)])[None, :]; b_eq = [1.0]
    t = time.time()
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=(0, None), method='highs')
    if res.status != 0: raise RuntimeError(res.message)
    r = res.x[:n]; bq = res.x[n:]
    y = -res.ineqlin.marginals
    tau = y[:len(x)]; cQ = y[len(x):len(x)+k]; s = y[-1]
    return dict(val=res.fun, r=r, bq=bq, tau=tau, cQ=cQ, s=s, x=x, a=a, b=b, secs=time.time()-t,
                logQ_mom=LQc @ r, slack=U @ r - LQx @ bq)

def price(sol, P):
    # reduced cost of adding polynomial P as a new b column (P coprime to A): sum tau log|P| + s deg P
    x, tau = sol['x'], sol['tau']; m = tau > 0
    lead, roots = poly_roots(P)
    d = np.min(np.abs(x[m][:, None] - roots[None, :]), axis=1)
    if np.any(d < 1e-12): return -np.inf
    return float(tau[m] @ logQ(P, x[m]) + sol['s']*(len(P) - 1))

def support(sol, thr=1e-9):
    dens = sol['r']/(sol['b'] - sol['a']); on = dens > thr*dens.max()
    d = np.diff(np.concatenate([[0], on.astype(int), [0]])); st = np.nonzero(d == 1)[0]; en = np.nonzero(d == -1)[0]
    return [(float(sol['a'][i]), float(sol['b'][j-1])) for i, j in zip(st, en)]

if __name__ == '__main__':
    A = json.loads(sys.argv[1]) if sys.argv[1].startswith('[') else json.load(open(sys.argv[1]))
    n = int(sys.argv[2]); xmax = float(sys.argv[3])
    sol = solve_ub(A, xmax, n)
    print(f"Lambda_A = {sol['val']:.7f}  (|A|={len(A)}, n={n}, xmax={xmax}, grid={len(sol['x'])}, {sol['secs']:.1f}s)")
    print("  b_Q:", np.round(sol['bq'], 6).tolist(), " sum b deg =", round(float(sum(bb*(len(q)-1) for bb, q in zip(sol['bq'], A))), 6))
    print("  int log|Q| dmu:", np.round(sol['logQ_mom'], 6).tolist())
    print("  min slack on grid:", sol['slack'].min(), " s =", sol['s'], " |tau| =", sol['tau'].sum())
    print("  support:", [(round(p, 4), round(q, 4)) for p, q in support(sol)])
