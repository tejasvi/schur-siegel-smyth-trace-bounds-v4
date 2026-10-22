# Collocation v4: restart from a converged state (components + node counts), refine components whose interior F dips,
# edge rule with geometric near-edge sampling; then the multiplier LP. Functions from lb_colloc.py.
import sys, json, time
import numpy as np
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import stable_hat_energy_matrix, ld_hat_potential, logQ, poly_roots
from lb_colloc import build, solve_fixed, F_eval, multiplier_lp, comps_from_state

A = json.load(open(sys.argv[1])); sfile = sys.argv[2]; iters = int(sys.argv[3]); tag = sys.argv[4]
dip_tol = float(sys.argv[5]) if len(sys.argv) > 5 else 1e-6
k = len(A); t0 = time.time()
roots_all = np.concatenate([poly_roots(q)[1] for q in A])
actQ = [i for i, q in enumerate(A) if q != [1, -6, 9, -1]]
rset = np.array(sorted(set(round(float(r), 12) for q in actQ for r in poly_roots(A[q])[1])))
C0 = comps_from_state(sfile, k)
comps = [[a, b] for a, b, n in C0]; Nc = [n for a, b, n in C0]
step = [[1e-5, 1e-5] for _ in comps]; lastdir = [[0, 0] for _ in comps]
print(f"{tag}: restart from {sfile}: {len(comps)} components, {sum(Nc)} nodes; dip tol {dip_tol}", flush=True)
for it in range(iters):
    t = time.time()
    e, cid, act = build(comps, 0, 0, Nc)
    K = stable_hat_energy_matrix(e)
    lamp, rho, lq = solve_fixed(A, e, act, actQ, K)
    rho_all = np.zeros(len(e) - 2); rho_all[act] = rho
    lamQ = np.zeros(len(A)); lamQ[actQ] = lq
    moves = 0; refined = 0; worst_in = 0.0; worst_out = 0.0
    for i, (a, b) in enumerate(comps):
        cn = e[cid == i]
        # interior dips: F on 8 points inside every node interval of the component
        xs = (cn[:-1, None] + (cn[1:] - cn[:-1])[:, None]*np.linspace(0.1, 0.9, 8)[None, :]).ravel()
        xs = xs[np.min(np.abs(xs[:, None] - roots_all[None, :]), axis=1) > 1e-9]
        Fi = F_eval(A, e, rho_all, lamQ, lamp, 0.0, xs) if len(xs) else np.array([0.0])
        worst_in = min(worst_in, Fi.min())
        if Fi.min() < -dip_tol and Nc[i] < 2000:
            Nc[i] = int(Nc[i]*1.3) + 2; refined += 1
        idx = act[cid[act + 1] == i]
        if len(idx) < 3: continue
        prev_b = comps[i-1][1] if i > 0 else 0.0
        next_a = comps[i+1][0] if i + 1 < len(comps) else 20.0
        for side, (hat, out_lo, out_hi) in enumerate([(idx[0], max(a - 0.004, prev_b), a), (idx[-1], b, min(b + 0.004, next_a))]):
            gl = out_hi - out_lo
            if gl <= 0: continue
            geo = np.geomspace(1e-7, 1.0, 30)*gl
            xo = np.unique(np.concatenate([np.linspace(out_lo, out_hi, 41)[1:-1], (out_lo + geo) if side == 1 else (out_hi - geo)]))
            xo = xo[(xo > max(out_lo, 1e-6)) & (xo < out_hi)]
            xo = xo[np.min(np.abs(xo[:, None] - roots_all[None, :]), axis=1) > 1e-9]
            Fo = F_eval(A, e, rho_all, lamQ, lamp, 0.0, xo) if len(xo) else np.array([1.0])
            worst_out = min(worst_out, Fo.min())
            wn = rho_all[hat]; direction = 0
            if wn < 0: direction = +1 if side == 0 else -1
            elif Fo.min() < -1e-8: direction = -1 if side == 0 else +1
            if direction != 0:
                if lastdir[i][side] != 0 and direction != lastdir[i][side]: step[i][side] *= 0.5
                elif lastdir[i][side] == direction: step[i][side] = min(5e-4, step[i][side]*1.5)
                lastdir[i][side] = direction
                comps[i][side] += direction*step[i][side]; moves += 1
    # keep root gaps open, merge gapless neighbours (carry node counts)
    newc, news, newd, newn = [comps[0]], [step[0]], [lastdir[0]], [Nc[0]]
    for i in range(1, len(comps)):
        a, b = comps[i]; pa, pb = newc[-1]
        inside = rset[(rset > min(pb, a) - 1e-12) & (rset < max(pb, a) + 1e-12)]
        if len(inside):
            r = inside[0]; newc[-1][1] = min(pb, r - 1e-7); a = max(a, r + 1e-7)
            newc.append([a, b]); news.append(step[i]); newd.append(lastdir[i]); newn.append(Nc[i])
        elif a - pb < 1e-6:
            newc[-1][1] = max(pb, b); newn[-1] = newn[-1] + Nc[i]
        else:
            newc.append([a, b]); news.append(step[i]); newd.append(lastdir[i]); newn.append(Nc[i])
    comps, step, lastdir, Nc = newc, news, newd, newn
    print(f"  it {it}: lam'={lamp:.9f} hats={len(act)} min rho={rho.min():.2e} (neg {np.sum(rho<0)}) moves={moves} refined={refined} "
          f"worst F inside={worst_in:.2e} outside={worst_out:.2e} ({time.time()-t:.0f}s)", flush=True)
    np.save(f"colloc_{tag}_state.npy", np.concatenate([[lamp, len(e)], lamQ, e, rho_all]))
    if moves == 0 and refined == 0 and rho.min() >= 0: break
nu = np.maximum(rho_all, 0); nu /= nu.sum()
nzn = e[1:-1][nu > 0]
xf = np.unique(np.concatenate([np.geomspace(1e-8, 0.02, 3000), np.linspace(0.02, 6.5, 300001), np.linspace(6.5, 20, 2000),
                               (nzn[:, None] + np.array([-1e-5, -2e-6, 2e-6, 1e-5])[None, :]).ravel()]))
xf = xf[xf > 0]; xf = xf[np.min(np.abs(xf[:, None] - roots_all[None, :]), axis=1) > 1e-9]
lam, lQ, l0, I, F = multiplier_lp(A, e, nu, K, xf)
print(f"final LP: lambda={lam:.9f} l0={l0:.6f} I(nu)={I:.3e} min F (LP grid)={F.min():.2e} at {xf[np.argmin(F)]:.6f} ({time.time()-t0:.0f}s)", flush=True)
np.save(f"colloc_{tag}.npy", np.concatenate([[lam, len(e)], lQ, e, l0*nu]))
