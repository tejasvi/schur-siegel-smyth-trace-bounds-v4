# Parallel finalize of a collocation state [lam', ne, lamQ, e, rho_all]: nu = rho+/s, potentials on a fine grid computed in
# parallel (longdouble closed form), 17-variable multiplier LP, export-format solution [lambda, ne, lamQ, e, lambda_0 nu].
import sys, json, time
import numpy as np
import multiprocessing as mp
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import stable_hat_energy_matrix, ld_hat_potential, logQ, poly_roots
from scipy.optimize import linprog
_E = None; _NU = None
def _pot(xs): return ld_hat_potential(_E, xs) @ _NU
if __name__ == '__main__':
    A = json.load(open(sys.argv[1])); v = np.load(sys.argv[2]); out = sys.argv[3]; nproc = int(sys.argv[4]); k = len(A)
    t0 = time.time()
    lamp = v[0]; ne = int(v[1]); e = v[2+k:2+k+ne]; rho = v[2+k+ne:]
    nu = np.maximum(rho, 0); nu /= nu.sum()
    roots = np.concatenate([poly_roots(q)[1] for q in A])
    nzn = e[1:-1][nu > 0]
    xf = np.unique(np.concatenate([np.geomspace(1e-8, 0.02, 3000), np.linspace(0.02, 6.5, 300001), np.linspace(6.5, 20, 2000),
                                   (nzn[:, None] + np.array([-1e-5, -2e-6, 2e-6, 1e-5])[None, :]).ravel()]))
    xf = xf[xf > 0]; xf = xf[np.min(np.abs(xf[:, None] - roots[None, :]), axis=1) > 1e-9]
    _E, _NU = e, nu
    chunks = np.array_split(xf, nproc*8)
    with mp.get_context('fork').Pool(nproc) as pool: U = np.concatenate(pool.map(_pot, chunks))
    K = stable_hat_energy_matrix(e); I = float(nu @ K @ nu)
    print(f"potentials on {len(xf)} points + K ({time.time()-t0:.0f}s); I(nu) = {I:.3e}", flush=True)
    LQ = np.array([logQ(q, xf) for q in A]).T
    A_ub = np.hstack([np.ones((len(xf), 1)), LQ, (2*U - I)[:, None]])
    c = np.zeros(k + 2); c[0] = -1.0
    res = linprog(c, A_ub=A_ub, b_ub=xf, bounds=[(None, None)] + [(0, None)]*(k + 1), method='highs')
    lam, lQ, l0 = res.x[0], res.x[1:k+1], res.x[-1]
    F = xf - lam - LQ @ lQ - l0*(2*U - I)
    print(f"lam' {lamp:.9f} -> LP lambda {lam:.9f}  l0 {l0:.6f}  min F (LP grid) {F.min():.2e} at {xf[np.argmin(F)]:.6f} ({time.time()-t0:.0f}s)", flush=True)
    np.save(out, np.concatenate([[lam, ne], lQ, e, l0*nu]))
