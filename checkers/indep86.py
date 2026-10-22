"""Independent re-verification of a lower-bound certificate (Lemma T1), written separately from check86.py and without
using its code.
Version 4: the polynomial parts of the F'' bound, the root-window bound and the left tail use the root form
(Q = lc prod (x - rho), roots enclosed once by flint): -(log|Q|)'' = sum Re 1/(x - rho)^2 <= sum 1/dist(rho, I)^2 and
|Q| <= |lc| prod max_I |x - rho|, so no Horner enclosure on wide balls is used (degree-10 polynomials with large coefficients).
Version 5: every real-root bracket is bisected exactly (signs of q at rational points) to width <= 2^-110, and
the window half-widths go down to 2^-110, so a window can be narrow enough for the ball evaluation of U next to a root
whose polynomial has a tiny multiplier (version 4 fails closed on such certificates).

Differences from check86:
  * density g from node HEIGHTS (hat k normalised to mass 1 has height 2/(e_{k+1}-e_{k-1})); segments with
    g(y) = alpha + beta*y;
  * potential U_g(x) = int log|x-y| g(y) dy by the segment antiderivative
        int (alpha + beta y) log|x-y| dy = (alpha + beta x) G(y-x) + beta K(y-x),
    G(t) = t log|t| - t, K(t) = t^2/2 log|t| - t^2/4    (no g'' / H representation);
  * energy I(g) = int int g g log|x-y| by exact double integration over pairs of segments (polynomial x t^n log|t|
    primitives; no J);
  * roots of the polynomials enclosed with flint complex_roots; a root whose imaginary enclosure excludes 0 is non-real
    and skipped; every other root must be simple and get a bracket with an exact rational sign change, the brackets
    pairwise disjoint (so all real roots are isolated);
  * chord bound with the singular endpoint terms integrated correctly for every interval length h;
  * own tails.
Usage: indep86.py CERT.json NPROC      (exit status 0 iff VERIFIED)
Requirements: Python >= 3.10, python-flint >= 0.9 (arb, fmpz_poly.complex_roots); Linux (multiprocessing "fork").
Validity checks use assert, so the script refuses to run under python -O.
"""
import json, sys, os, time
from fractions import Fraction as Fr
from flint import arb, acb, fmpz_poly, ctx
if not __debug__:
    raise SystemExit("refusing to run with assertions disabled (python -O / PYTHONOPTIMIZE)")
ctx.prec = 256

LOGC = {}


def A(fr):
    return arb(fr.numerator) / arb(fr.denominator)


CACHE = [True]


def logabs_fr(t):          # t Fraction != 0 (cached while computing the energy: t are node differences)
    if not CACHE[0]:
        return A(abs(t)).log()
    v = LOGC.get(t)
    if v is None:
        v = A(abs(t)).log(); LOGC[t] = v
    return v


class Cert:
    def __init__(self, path):
        d = json.load(open(path))
        self.A = [[int(c) for c in q] for q in d["A"]]
        self.lamQ = [Fr(x) for x in d["lamQ"]]
        self.e = [Fr(x) for x in d["nodes"]]
        self.rho = [Fr(x) for x in d["rho"]]
        self.lam = Fr(d["lambda"]); self.x_lo = Fr(d["x_lo"]); self.x_hi = Fr(d["x_hi"])
        assert all(l >= 0 for l in self.lamQ) and all(r >= 0 for r in self.rho)
        assert len(self.A) == len(self.lamQ) and all(any(c != 0 for c in q) for q in self.A)
        assert len(set(tuple(q) for q in self.A)) == len(self.A), "the polynomials in A must be distinct"
        assert all(a < b for a, b in zip(self.e, self.e[1:])) and len(self.rho) == len(self.e) - 2
        N = len(self.e) - 1
        v = [Fr(0)] * (N + 1)
        for k in range(1, N):
            v[k] = self.rho[k - 1] * 2 / (self.e[k + 1] - self.e[k - 1])
        self.v = v
        self.s = sum(self.rho)
        segs = []
        mass = Fr(0)
        for k in range(N):
            a, b = self.e[k], self.e[k + 1]
            if v[k] == 0 and v[k + 1] == 0:
                continue
            beta = (v[k + 1] - v[k]) / (b - a); alpha = v[k] - beta * a
            segs.append((a, b, alpha, beta))
            mass += (v[k] + v[k + 1]) / 2 * (b - a)
        assert mass == self.s, "density mass != sum rho"
        self.segs = segs
        self.supp = (segs[0][0], segs[-1][1])
        # slope jumps at nodes, from node heights (U'' = sum_k C_k log|x - e_k|)
        Cn = {}
        for k in range(N + 1):
            sr = (v[k + 1] - v[k]) / (self.e[k + 1] - self.e[k]) if k < N else Fr(0)
            sl = (v[k] - v[k - 1]) / (self.e[k] - self.e[k - 1]) if k > 0 else Fr(0)
            if sr != sl:
                Cn[self.e[k]] = sr - sl
        self.Cn = Cn
        assert sum(self.Cn.values()) == 0 and sum(c * k for k, c in self.Cn.items()) == 0
        self.active = [(q, l) for q, l in zip(self.A, self.lamQ) if l != 0]
        self.segA = [(A(a), A(b), A(al), A(be), a, b, al, be) for (a, b, al, be) in segs]


def Gt(t):  # t Fraction
    if t == 0: return arb(0)
    return A(t) * logabs_fr(t) - A(t)


def Kt(t):
    if t == 0: return arb(0)
    tt = A(t) * A(t)
    return tt / 2 * logabs_fr(t) - tt / 4


def U_exact(c, x):
    """int log|x-y| g(y) dy at rational x (exact differences)."""
    tot = arb(0)
    for (aA, bA, alA, beA, a, b, al, be) in c.segA:
        lin = alA + beA * A(x)
        tot += lin * (Gt(b - x) - Gt(a - x)) + beA * (Kt(b - x) - Kt(a - x))
    return tot


def G_ball(T):
    if not T.contains(0):
        return T * abs(T).log() - T
    r = abs(T).upper(); assert r < arb("0.36")
    B = r * (1 / r).log() + r
    return arb(0).union(B).union(-B)


def K_ball(T):
    if not T.contains(0):
        return T * T / 2 * abs(T).log() - T * T / 4
    r = abs(T).upper(); assert r < arb("0.6")
    B = r * r / 2 * (1 / r).log() + r * r / 4
    return arb(0).union(B).union(-B)


def U_ball(c, X):
    tot = arb(0)
    for (aA, bA, alA, beA, a, b, al, be) in c.segA:
        lin = alA + beA * X
        tot += lin * (G_ball(bA - X) - G_ball(aA - X)) + beA * (K_ball(bA - X) - K_ball(aA - X))
    return tot


# ---------- energy by exact double integration over segment pairs ----------
def Lprim(n, t):       # primitive of t^n log|t| (n >= 0), value at rational t
    if t == 0: return arb(0)
    tn1 = A(t) ** (n + 1)
    return tn1 * (logabs_fr(t) / (n + 1) - arb(1) / ((n + 1) ** 2))


def Mprim(n, t):
    return A(t) ** (n + 1) / (n + 1)


def pair_energy(sm, sk):
    """int_{c}^{d} (al_m + be_m x) * [ (al_k + be_k x) G(y - x) + be_k K(y - x) ]_{y=a_k}^{b_k} dx  (exact rationals)"""
    c, d, alm, bem = sm
    a, b, alk, bek = sk
    tot = arb(0)
    for y, sg in ((b, 1), (a, -1)):
        u = alm + bem * y; w = alk + bek * y
        p1 = [u * w, -(u * bek + w * bem), bem * bek]     # (u - bem t)(w - bek t)
        p2 = [u * bek, -bem * bek]                         # (u - bem t) bek
        t0, t1 = y - d, y - c
        val = arb(0)
        for j, pj in enumerate(p1):
            if pj == 0: continue
            val += A(pj) * ((Lprim(j + 1, t1) - Lprim(j + 1, t0)) - (Mprim(j + 1, t1) - Mprim(j + 1, t0)))
        for j, pj in enumerate(p2):
            if pj == 0: continue
            val += A(pj) * ((Lprim(j + 2, t1) - Lprim(j + 2, t0)) / 2 - (Mprim(j + 2, t1) - Mprim(j + 2, t0)) / 4)
        tot += sg * val
    return tot


_C = None


def _energy_rows(idx):
    c = _C
    tot = arb(0)
    for m in idx:
        sm = c.segs[m]
        for sk in c.segs:
            tot += pair_energy((sm[0], sm[1], sm[2], sm[3]), (sk[0], sk[1], sk[2], sk[3]))
    return tot.str(80, radius=True)


def energy(c, nproc):
    import multiprocessing as mp
    global _C
    _C = c
    M = len(c.segs)
    chunks = [list(range(i, M, nproc * 4)) for i in range(nproc * 4)]
    with mp.get_context("fork").Pool(nproc) as pool:
        res = pool.map(_energy_rows, chunks)
    tot = arb(0)
    for st in res:
        tot += arb(st)
    return tot


# ---------- F, F'' bound, roots, tails ----------
def polyval_fr(q, x):
    v = Fr(0)
    for a in q: v = v * x + a
    return v


def polyval_ball(q, X):
    v = arb(0)
    for a in q: v = v * X + a
    return v


_ROOTS = {}
def roots_of(q):
    # rigorous enclosures (acb) of all roots of q, with multiplicity; cached per polynomial
    key = tuple(q)
    if key not in _ROOTS:
        P = fmpz_poly(list(reversed(q)))
        rts = []
        for r, mult in P.complex_roots():
            rts += [r] * mult
        assert len(rts) == len(q) - 1
        _ROOTS[key] = rts
    return _ROOTS[key]


def dist_lower(r, p, q):
    # lower bound of the distance from the root ball r (acb) to the real interval [p, q]; 0 if it may meet it
    re, im = r.real, r.imag
    dre = arb(0)
    if (re - A(q)).lower() > 0: dre = re - A(q)
    elif (A(p) - re).lower() > 0: dre = A(p) - re
    d2 = dre * dre + im * im
    lo = d2.lower()
    return arb(lo).sqrt().lower() if lo > 0 else arb(0)


def logq_dd_upper(qq, p, q):
    # upper bound of -(log|Q|)'' on [p, q]: sum over roots of 1/dist^2 (infinite if a root may meet the interval)
    s = arb(0)
    for r in roots_of(qq):
        d = dist_lower(r, p, q)
        if not (d > 0): return arb('inf')
        s += 1 / (arb(d) * arb(d))
    return s


def absq_upper(qq, p, q):
    # upper bound of |Q| on [p, q]: |lc| prod max(|p - rho|, |q - rho|)
    v = arb(abs(qq[0]))
    for r in roots_of(qq):
        a = abs(acb(A(p)) - r).upper(); b = abs(acb(A(q)) - r).upper()
        v *= arb(max(a, b))
    return v.upper()


def polyder(q):
    d = len(q) - 1
    return [q[i] * (d - i) for i in range(d)]


def F_at(c, x, Ig_s):
    v = A(x) - A(c.lam) + Ig_s
    for q, l in c.active:
        Qx = polyval_fr(q, x); assert Qx != 0
        v -= A(l) * logabs_fr(Qx)
    v -= 2 * U_exact(c, x)
    return v


def chord_ok(c, p, q, Ig_s, Fp, Fq):
    h = q - p
    X = (A(p) + A(q)) / 2; X = X.union(A(p)).union(A(q))
    R = arb(0)
    for qq, l in c.active:
        R += A(l) * logq_dd_upper(qq, p, q)          # -(log|Q|)'' <= sum 1/dist(rho, [p, q])^2
    sing = arb(0)
    for e, Ce in c.Cn.items():
        kappa = -2 * Ce                       # F'' contains kappa * log|x - e|
        if e == p or e == q:
            if kappa < 0:
                m = min(h, Fr(1))
                sing += A(-kappa) * A(m) * (1 - A(m).log())
            else:
                H = max(h, Fr(1))
                if H > 1:
                    sing += A(kappa) * (A(H) * A(H).log() - A(H) + 1)
        else:
            assert not (p < e < q)
            R += A(kappa) * abs(A(e) - X).log()
    if not (R.is_finite() and sing.is_finite()):
        return False
    Ru = R.upper()
    Rpos = Ru if Ru > 0 else arb(0)
    pen = A(h) / 4 * (A(h) * Rpos + sing)
    lo = min(Fp.lower(), Fq.lower())
    return (arb(lo) - pen).lower() > 0


def root_brackets(q):
    """the real roots of q, rigorously isolated: rational brackets with an exact sign change.
    flint's complex_roots isolates all deg(q) roots (with multiplicity); a root whose imaginary enclosure excludes 0 is
    non-real; every other root must be simple and get a sign-change bracket, and the brackets must be disjoint."""
    P = fmpz_poly(list(reversed(q)))
    rts = P.complex_roots()
    assert sum(m for _, m in rts) == len(q) - 1
    out = []
    for r, mult in rts:
        if not r.imag.contains(0):
            continue                                   # non-real root: no singularity of log|q| on the real line
        assert mult == 1, "multiple root"
        mid = Fr(float(r.real.mid()))
        for dl in (Fr(1, 10**12), Fr(1, 10**10), Fr(1, 10**8)):
            a, b = mid - dl, mid + dl
            if polyval_fr(q, a) * polyval_fr(q, b) < 0:
                out.append((a, b)); break
        else:
            raise RuntimeError("no sign-change bracket for a root with real enclosure")
    tight = []
    W = Fr(1, 2**110)
    for a, b in out:                                   # exact bisection, keeping the sign change
        fa = polyval_fr(q, a)
        assert fa != 0 and fa * polyval_fr(q, b) < 0
        while b - a > W:
            m = (a + b) / 2
            fm = polyval_fr(q, m)
            if fm == 0:                                # exact (rational) root: a tiny bracket around it
                a, b = m - W / 4, m + W / 4
                assert polyval_fr(q, a) * polyval_fr(q, b) < 0
                break
            if (fm > 0) == (fa > 0):
                a, fa = m, fm
            else:
                b = m
        tight.append((a, b))
    out = tight
    out.sort()
    assert all(out[i][1] < out[i + 1][0] for i in range(len(out) - 1)), "brackets overlap"
    return out


def window_ok(c, L, R, Ig_s):
    X = (A(L) + A(R)) / 2; X = X.union(A(L)).union(A(R))
    v = X - A(c.lam) + Ig_s
    for qq, l in c.active:
        mx = absq_upper(qq, L, R)
        v -= A(l) * arb(mx).log()
    v -= 2 * U_ball(c, X)
    return v.lower() > 0


_G = {}


def _check_intervals(jobs):
    """returns (ok, number of checks, (min lower bound of F over all checked endpoints as float, its x), message)"""
    c, Ig_s = _G["c"], _G["Ig"]
    n = 0; worst = None; worst_x = None
    for (p, q) in jobs:
        stack = [(p, q, 0)]
        while stack:
            a, b, dep = stack.pop()
            Fa = F_at(c, a, Ig_s); Fb = F_at(c, b, Ig_s); n += 1
            for xv, Fv in ((a, Fa), (b, Fb)):
                lv = float(Fv.lower())
                if worst is None or lv < worst:
                    worst, worst_x = lv, xv
            lo = min(Fa.lower(), Fb.lower())
            if lo > 0 and chord_ok(c, a, b, Ig_s, Fa, Fb):
                continue
            if dep >= 50 or not (lo > 0):
                return False, n, (worst, worst_x), f"FAIL [{float(a)},{float(b)}] F-lower {float(lo):.3e}"
            m = (a + b) / 2
            m2 = Fr(round(m * 2**40), 2**40)
            if a < m2 < b: m = m2
            stack += [(a, m, dep + 1), (m, b, dep + 1)]
    return True, n, (worst, worst_x), ""


def main():
    import multiprocessing as mp
    path, nproc = sys.argv[1], int(sys.argv[2])
    t0 = time.time()
    c = Cert(path)
    print(f"segments {len(c.segs)}, support [{float(c.supp[0])}, {float(c.supp[1])}], s = {float(c.s):.9f}, "
          f"nodes with slope jump {len(c.Cn)}", flush=True)
    Ig = energy(c, nproc)
    CACHE[0] = False; LOGC.clear()
    Ig_s = Ig / A(c.s)
    print(f"I(g) = s^2 I(nu) = {Ig}  -> I(nu) = {Ig / A(c.s)**2}  ({time.time()-t0:.0f}s)", flush=True)
    # left tail (0, x_lo]
    x_lo, x_hi = c.x_lo, c.x_hi
    assert 0 < x_lo < x_hi
    assert x_lo <= c.supp[0]
    lx = [l for q, l in c.active if q == [1, 0]]; assert lx
    v = -A(c.lam) - A(lx[0]) * A(x_lo).log() + Ig_s - 2 * U_exact(c, Fr(0))
    X = arb(0).union(A(x_lo))
    for q, l in c.active:
        if q == [1, 0]: continue
        assert all(dist_lower(r, Fr(0), x_lo) > 0 for r in roots_of(q))   # no root of q in [0, x_lo]
        v -= A(l) * arb(absq_upper(q, Fr(0), x_lo)).log()
    okL = v.lower() > 0
    print(f"left tail (0, {float(x_lo)}]: {okL}  margin {v}", flush=True)
    # right tail [x_hi, inf): needs supp g in [0, x_hi], x_hi >= 1
    assert c.supp[0] >= 0 and c.supp[1] <= x_hi and x_hi >= 1
    alpha = 2 * A(c.s); beta = A(c.lam) - Ig_s
    for q, l in c.active:
        alpha += A(l) * (len(q) - 1); beta += A(l) * arb(sum(abs(a) for a in q)).log()
    g = A(x_hi) - alpha * A(x_hi).log() - beta
    okR = (A(x_hi) - alpha).lower() > 0 and g.lower() > 0
    print(f"right tail [{float(x_hi)}, inf): {okR}  g(x_hi) = {g}", flush=True)
    # roots and windows
    pts = set([x_lo, x_hi]) | set(e for e in c.e if x_lo < e < x_hi)
    windows = []
    for q, l in c.active:
        for (a, b) in root_brackets(q):
            if b <= x_lo or a >= x_hi:
                continue                      # roots <= x_lo: left tail (x itself: x > 0); roots >= x_hi: right tail
            assert x_lo < a and b < x_hi
            ok = False
            for d in [Fr(1, 10**k) for k in range(4, 17)] + [Fr(1, 2**k) for k in (60, 70, 80, 90, 100, 110)]:
                L, R = a - d, b + d
                if L > x_lo and R < x_hi and window_ok(c, L, R, Ig_s):
                    ok = True; break
            assert ok, f"window failed for root in [{float(a)},{float(b)}] of {q}"
            windows.append((L, R)); pts |= {L, R}
    pts = sorted(pts)
    jobs = [(p, q) for p, q in zip(pts, pts[1:]) if not any(L <= p and q <= R for (L, R) in windows)]
    print(f"{len(windows)} root windows; {len(jobs)} base intervals on [{float(x_lo)}, {float(x_hi)}]", flush=True)
    _G["c"] = c; _G["Ig"] = Ig_s
    K = nproc * 8
    parts = [jobs[i::K] for i in range(K)]
    with mp.get_context("fork").Pool(nproc) as pool:
        res = pool.map(_check_intervals, parts)
    okM = all(r[0] for r in res)
    n = sum(r[1] for r in res)
    for r in res:
        if not r[0]: print("  ", r[3])
    mins = [r[2] for r in res if r[2][0] is not None]
    if mins:
        wv, wx = min(mins, key=lambda t: t[0])
        where = f"min endpoint F-lower {wv:.6e} at x = {float(wx):.12f}"
    else:
        where = "no interval checked"
    print(f"main range: {okM}  ({n} interval checks; {where})  t={time.time()-t0:.0f}s")
    verified = okL and okR and okM
    print("INDEPENDENT VERDICT:", "VERIFIED" if verified else "NOT VERIFIED", "lambda =", c.lam, float(c.lam))
    return verified


if __name__ == "__main__":
    sys.exit(0 if main() else 1)
