# Lower bound by collocation (Giraudin-style), A = polynomial set (JSON).
# Support = union of components [a_i, b_i]; hats on cosine-spaced nodes inside each component (zero weight on hats centred
# at component ends). For fixed components, the first-order conditions
#     2 U_rho(x_k) + sum_Q lamQ_Q log|Q(x_k)| + lam' = x_k      at every active hat centre x_k,
#     int log|Q| drho = 0                                       for every active Q,
#     I(rho) = rho^T K rho = 0                                  (energy constraint active)
# are linear in (rho, lamQ) for fixed lam' plus one scalar quadratic in lam'. Edges move until rho >= 0 near the edges and
# F >= 0 just outside. Then nu = rho/s and an LP in the multipliers (lambda, lamQ, lambda_0) on a fine grid gives the dual
# certificate; saved in the export_cert.py format [lambda, ne, lamQ, e, rho_all].
import sys, json, time
import numpy as np
from scipy.optimize import linprog
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import stable_hat_energy_matrix, ld_hat_potential, logQ, poly_roots

def comps_from_primal(pfile, thr=1e-4, mingap=1e-3):
    v = np.load(pfile); ne = int(v[1]); e = v[2:2+ne]; w = v[2+ne:2+ne+ne-2]
    on = w > thr*w.max(); out = []; k = 0
    while k < len(on):
        if on[k]:
            j = k
            while j + 1 < len(on) and on[j+1]: j += 1
            out.append([e[k], e[j+2]])        # hats k..j are centred at e[k+1..j+1]; support [e[k], e[j+2]]
            k = j + 1
        else: k += 1
    merged = [out[0]]
    for a, b in out[1:]:
        if a - merged[-1][1] < mingap: merged[-1][1] = max(merged[-1][1], b)
        else: merged.append([a, b])
    return merged

def initial_comps(pfile, A, actQ, g0):
    # envelope of the primal support, split by a gap of half-width g0 at every root of an active polynomial inside it
    env = comps_from_primal(pfile, 1e-6, 3e-3)
    roots = sorted(set(round(float(r), 12) for q in actQ for r in poly_roots(A[q])[1]))
    out = []
    for a, b in env:
        cur = a
        for r in roots:
            if a < r < b:
                if r - g0 - cur > 2*g0: out.append([cur, r - g0])
                cur = max(cur, r + g0)
        if b - cur > 2*g0: out.append([cur, b])
    return out

def comps_from_state(sfile, k):
    v = np.load(sfile); ne = int(v[1]); e = v[2+k:2+k+ne]; rho = v[2+k+ne:]
    endp = [0] + [m for m in range(1, ne - 1) if rho[m-1] == 0] + [ne - 1]
    out = []
    for s_, t_ in zip(endp, endp[1:]):
        if t_ - s_ >= 2: out.append([float(e[s_]), float(e[t_]), t_ - s_])
    return out

def build(comps, N_total, Nmin, Nc=None):
    L = np.array([b - a for a, b in comps]); tot = L.sum()
    xs, cid = [], []
    for i, ((a, b), l) in enumerate(zip(comps, L)):
        N = max(Nmin, int(round(N_total*l/tot))) if Nc is None else Nc[i]
        x = (a + b)/2 - (b - a)/2*np.cos(np.pi*np.arange(N + 1)/N)
        xs.append(x); cid.append(np.full(N + 1, i))
    e = np.concatenate(xs); cid = np.concatenate(cid)
    assert np.all(np.diff(e) > 0), "components overlap"
    # global hat m = 1..ne-2 centred at e[m]; active iff e[m-1], e[m], e[m+1] lie in the same component
    m = np.arange(1, len(e) - 1)
    act = (cid[m-1] == cid[m]) & (cid[m+1] == cid[m])
    return e, cid, m[act] - 1          # indices into the hat list (0-based column of ld_hat_potential)

def solve_fixed(A, e, act, actQ, K):
    xc = e[act + 1]                                   # centres of the active hats
    U = ld_hat_potential(e, xc)[:, act]               # (n, n)
    LQx = np.array([logQ(A[q], xc) for q in actQ]).T  # (n, q)
    LQbar = np.array([ld_hat_potential(e, poly_roots(A[q])[1]).sum(axis=0)[act] + np.log(abs(A[q][0])) for q in actQ])  # (q, n)
    n, q = len(act), len(actQ)
    M = np.zeros((n + q, n + q)); M[:n, :n] = 2*U; M[:n, n:] = LQx; M[n:, :n] = LQbar
    r0 = np.concatenate([xc, np.zeros(q)]); r1 = np.concatenate([np.ones(n), np.zeros(q)])
    S = np.linalg.solve(M, np.stack([r0, r1], axis=1)); s0, s1 = S[:, 0], S[:, 1]
    Ka = K[np.ix_(act, act)]
    p0, p1 = s0[:n], s1[:n]
    a2 = p1 @ Ka @ p1; a1 = -2*(p0 @ Ka @ p1); a0 = p0 @ Ka @ p0
    disc = a1*a1 - 4*a2*a0
    if disc < 0: raise RuntimeError(f"no real root (disc {disc:.3e})")
    best = None
    for lp in [(-a1 + np.sqrt(disc))/(2*a2), (-a1 - np.sqrt(disc))/(2*a2)]:
        sol = s0 - lp*s1; rho = sol[:n]
        score = (rho.sum() > 0, -np.sum(np.minimum(rho, 0)), lp)
        if 1.0 < lp < 2.5 and rho.sum() > 0 and (best is None or lp > best[0]): best = (lp, rho, sol[n:])
    if best is None: raise RuntimeError("no admissible root")
    return best

def F_eval(A, e, rho_all, lamQ, lamp, Iover_s, x, chunk=20000):
    U = np.empty(len(x))
    for i0 in range(0, len(x), chunk): U[i0:i0+chunk] = ld_hat_potential(e, x[i0:i0+chunk]) @ rho_all
    return x - lamp - sum(l*logQ(q, x) for l, q in zip(lamQ, A) if l != 0) - 2*U + Iover_s

def multiplier_lp(A, e, nu, K, xf):
    U = np.empty(len(xf))
    for i0 in range(0, len(xf), 20000): U[i0:i0+20000] = ld_hat_potential(e, xf[i0:i0+20000]) @ nu
    I = float(nu @ K @ nu); LQ = np.array([logQ(q, xf) for q in A]).T; k = len(A)
    A_ub = np.hstack([np.ones((len(xf), 1)), LQ, (2*U - I)[:, None]])
    c = np.zeros(k + 2); c[0] = -1.0
    res = linprog(c, A_ub=A_ub, b_ub=xf, bounds=[(None, None)] + [(0, None)]*(k + 1), method='highs')
    if res.status != 0: raise RuntimeError(res.message)
    lam, lQ, l0 = res.x[0], res.x[1:k+1], res.x[-1]
    return lam, lQ, l0, I, xf - lam - LQ @ lQ - l0*(2*U - I)

if __name__ == '__main__':
    A = json.load(open(sys.argv[1])); pfile = sys.argv[2]; N_total = int(sys.argv[3]); iters = int(sys.argv[4]); tag = sys.argv[5]
    Nmin = int(sys.argv[6]) if len(sys.argv) > 6 else 12
    t0 = time.time()
    roots_all = np.concatenate([poly_roots(q)[1] for q in A])
    actQ = [i for i, q in enumerate(A) if q != [1, -6, 9, -1]]
    comps = initial_comps(pfile, A, actQ, 1e-4)
    step = [[3e-5, 3e-5] for _ in comps]; lastdir = [[0, 0] for _ in comps]
    print(f"{tag}: {len(comps)} components from {pfile}; N_total {N_total}; active Q {len(actQ)}/{len(A)}", flush=True)
    for it in range(iters):
        t = time.time()
        e, cid, act = build(comps, N_total, Nmin)
        K = stable_hat_energy_matrix(e)
        lamp, rho, lq = solve_fixed(A, e, act, actQ, K)
        rho_all = np.zeros(len(e) - 2); rho_all[act] = rho
        lamQ = np.zeros(len(A)); lamQ[actQ] = lq
        s = rho_all.sum()
        # edge diagnostics: weights of the two hats next to each edge; F just outside each edge
        moves = 0; worstF = 0.0; negw = 0
        for i, (a, b) in enumerate(comps):
            idx = act[cid[act + 1] == i]                # active hats of component i (hat index = node index - 1)
            if len(idx) < 3: continue
            prev_b = comps[i-1][1] if i > 0 else 0.0
            next_a = comps[i+1][0] if i + 1 < len(comps) else 20.0
            for side, (hat, out_lo, out_hi) in enumerate([(idx[0], max(a - 0.004, prev_b), a), (idx[-1], b, min(b + 0.004, next_a))]):
                gl = out_hi - out_lo
                geo = np.geomspace(1e-7, 1.0, 25)*gl
                xo = np.unique(np.concatenate([np.linspace(out_lo, out_hi, 41)[1:-1], (out_lo + geo) if side == 1 else (out_hi - geo)]))
                xo = xo[(xo > out_lo) & (xo < out_hi)]
                xo = xo[(xo > 1e-6)]
                xo = xo[np.min(np.abs(xo[:, None] - roots_all[None, :]), axis=1) > 1e-9]
                Fo = F_eval(A, e, rho_all, lamQ, lamp, 0.0, xo) if len(xo) else np.array([1.0])
                # inside test: F between the first three nodes next to the edge
                cn = e[cid == i]
                xin = np.linspace(cn[0], cn[min(3, len(cn)-1)], 61)[1:-1] if side == 0 else np.linspace(cn[max(-4, -len(cn))], cn[-1], 61)[1:-1]
                xin = xin[np.min(np.abs(xin[:, None] - roots_all[None, :]), axis=1) > 1e-9]
                Fi = F_eval(A, e, rho_all, lamQ, lamp, 0.0, xin) if len(xin) else np.array([1.0])
                wn = rho_all[hat]
                direction = 0
                if wn < 0: direction = +1 if side == 0 else -1; negw += 1   # shrink
                elif Fo.min() < -1e-8: direction = -1 if side == 0 else +1                      # grow
                worstF = min(worstF, Fi.min())
                worstF = min(worstF, Fo.min())
                if direction != 0:
                    if lastdir[i][side] != 0 and direction != lastdir[i][side]: step[i][side] *= 0.5
                    elif lastdir[i][side] == direction: step[i][side] = min(2e-3, step[i][side]*1.5)
                    lastdir[i][side] = direction
                    if side == 0: comps[i][0] += direction*step[i][side]
                    else: comps[i][1] += direction*step[i][side]
                    moves += 1
        negpos = act[rho < 0]
        nedge = 0
        for i in range(len(comps)):
            idx = act[cid[act + 1] == i]
            if len(idx): nedge += np.sum(np.isin(negpos, idx[:3])) + np.sum(np.isin(negpos, idx[-3:]))
        for i in range(len(comps)):
            if comps[i][1] - comps[i][0] < 1e-5:
                mid = 0.5*(comps[i][0] + comps[i][1]); comps[i] = [mid - 5e-6, mid + 5e-6]; step[i] = [step[i][0]*0.5, step[i][1]*0.5]
        # keep root gaps open (edges may not cross a root) and merge components whose gap has no active root
        rset = np.sort(np.array(sorted(set(round(float(r), 12) for q in actQ for r in poly_roots(A[q])[1]))))
        newc, newstep, newdir = [comps[0]], [step[0]], [lastdir[0]]
        for i in range(1, len(comps)):
            a, b = comps[i]; pa, pb = newc[-1]
            inside = rset[(rset > min(pb, a) - 1e-12) & (rset < max(pb, a) + 1e-12)]
            if len(inside):
                r = inside[0]
                newc[-1][1] = min(pb, r - 1e-7); a = max(a, r + 1e-7)
                newc.append([a, b]); newstep.append(step[i]); newdir.append(lastdir[i])
            elif a - pb < 1e-6:
                newc[-1][1] = max(pb, b); newstep[-1] = [newstep[-1][0], step[i][1]]; newdir[-1] = [newdir[-1][0], lastdir[i][1]]
            else:
                newc.append([a, b]); newstep.append(step[i]); newdir.append(lastdir[i])
        comps, step, lastdir = newc, newstep, newdir
        print(f"    negative weights: {len(negpos)} total, {nedge} within 3 hats of an edge; most negative at x = {e[act[np.argmin(rho)] + 1]:.5f}; components now {len(comps)}", flush=True)
        print(f"  it {it}: lam'={lamp:.8f} s={s:.5f} n_hats={len(act)} min rho={rho.min():.2e} (neg {np.sum(rho<0)}) "
              f"min lamQ={lq.min():.2e} edge moves={moves} (neg-edge {negw}) worst F outside={worstF:.2e} ({time.time()-t:.0f}s)", flush=True)
        np.save(f"colloc_{tag}_state.npy",
                np.concatenate([[lamp, len(e)], lamQ, e, rho_all]))
        if moves == 0 and rho.min() >= 0: break
    # final: multiplier LP with nu = rho+/s on a fine grid, then min F on a finer grid
    nu = np.maximum(rho_all, 0); nu /= nu.sum()
    xf = np.unique(np.concatenate([np.geomspace(1e-8, 0.02, 3000), np.linspace(0.02, 6.5, 250001), np.linspace(6.5, 20, 2000),
                                   (e[1:-1, None] + np.array([-1e-5, -2e-6, 2e-6, 1e-5])[None, :]).ravel()]))
    xf = xf[(xf > 0)]; xf = xf[np.min(np.abs(xf[:, None] - roots_all[None, :]), axis=1) > 1e-9]
    lam, lQ, l0, I, F = multiplier_lp(A, e, nu, K, xf)
    print(f"final LP: lambda={lam:.9f} l0={l0:.6f} I(nu)={I:.3e} min F (LP grid)={F.min():.2e} ({time.time()-t0:.0f}s)", flush=True)
    np.save(f"colloc_{tag}.npy", np.concatenate([[lam, len(e)], lQ, e, l0*nu]))
