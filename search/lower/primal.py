# Primal: minimize int x dmu over step densities mu on cells subject to int log|Q| dmu >= 0 (Q in A) and I(mu) >= 0.
import numpy as np, cvxpy as cp, sys, json, time
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import *
def solve_primal(A, xmin=0.0, xmax=6.0, n=600, C=None, verbose=False):
    a, b = cells(xmin, xmax, n); m = 0.5*(a + b)
    K = energy_matrix(a, b)
    if C is None: C = 10.0
    P = -(K - C*np.ones((n, n)))
    ev, V = np.linalg.eigh(P); 
    if ev.min() < -1e-9: print("warning: P min eig", ev.min())
    ev = np.maximum(ev, 0); R = (V*np.sqrt(ev)).T     # P = R^T R
    L = np.array([logQ_cell_avg(q, a, b) for q in A])
    r = cp.Variable(n, nonneg=True)
    cons = [cp.sum(r) == 1, L @ r >= 0, cp.sum_squares(R @ r) <= C]
    prob = cp.Problem(cp.Minimize(m @ r), cons)
    prob.solve(solver='CLARABEL', verbose=verbose)
    rv = np.maximum(r.value, 0); rv /= rv.sum()
    return prob.value, rv, a, b, K, L, [c.dual_value for c in cons]
if __name__ == '__main__':
    which = sys.argv[1]; n = int(sys.argv[2]); xmax = float(sys.argv[3])
    A = {'A7': A7, 'A11': A11_PIN, 'x': [[1,0]], 'empty': [], 'x,x-1': [[1,0],[1,-1]]}[which]
    t = time.time()
    val, rv, a, b, K, L, duals = solve_primal(A, 0.0, xmax, n)
    E = rv @ K @ rv
    print(f"{which} n={n} xmax={xmax}: primal = {val:.7f}  energy={E:.3e}  logQ moments={np.round(L@rv,6).tolist()}  ({time.time()-t:.1f}s)")
    print("  duals: logQ", np.round(duals[1], 5).tolist() if duals[1] is not None else None, " energy", duals[2])
    np.save(f"primal_{which}_n{n}.npy", rv)
