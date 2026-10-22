"""Second checker for the 86a upper-bound certificate (C_86 <= int x dmu), written from Lemma U1 and the certificate
format only, without reading check86ub.py. Adapted from an earlier checker of the same author for a different
certificate.

Certificate: A (21 integer polynomials, leading coefficient first), b (rationals), nodes n_0 < ... < n_N in [0, 6],
w (N - 1 hat weights), eps. mu_0 = sum_j w_j hat_j, hat_j the unit-mass triangle on [n_j, n_{j+2}] with apex n_{j+1};
equivalently mu_0 = G dx with G piecewise linear on the nodes, G(n_i) = 2 w_{i-1} / (n_{i+1} - n_{i-1}), G(n_0) = G(n_N) = 0.
mu = (1 - eps) mu_0 + eps omega, omega the arcsine (equilibrium) measure of [0, 6] (U_omega = log(3/2) on [0, 6]).
Lemma U1 is applied with the weights b'_Q = (1 - eps) b_Q. Checked:
  (D) data: sum w = 1, w >= 0, nodes strictly increasing from 0 to 6, b >= 0, polynomials distinct, primitive, irreducible
      over Z, all roots real and in [0, 6];
  (S) beta = (1 - eps) sum b_Q deg Q < 1 (exact);
  (M) int log|Q| dmu = (1 - eps)(log|lc Q| + sum_theta U_mu0(theta)) + eps (log|lc Q| + deg Q log(3/2)) > 0 for every Q
      (roots of Q in [0, 6], so U_omega = log(3/2) there);
  (P) h_mu = (1 - eps) [U_mu0 - sum b_Q log|Q|] + eps log(3/2) >= 0 on supp mu = [0, 6], i.e.
      F(x) := U_mu0(x) - sum_Q b_Q log|Q(x)| + eps log(3/2)/(1 - eps) >= 0 on [0, 6];
  (T) the exact trace int x dmu = (1 - eps) sum_j w_j (n_j + n_{j+1} + n_{j+2})/3 + 3 eps.
Machinery for (P): U, U' by closed forms per grid piece; U'' = sum_i C_i log|x - n_i| with the exact slope jumps C_i;
on each interval between breakpoints (nodes, rational roots, windows of irrational roots) a second-order Taylor bound
at the midpoint, F >= F(m) - |F'(m)| h - N h^2/2 - h S + (split roots), with N from the regular part of F'' and S the
integral bound of the singular term C_i log|x - n_i| (C_i > 0) at an end node; bisection on failure. 160-bit balls.
Usage: ub86audit.py CERT.json NPROC   (exit 0 iff VERIFIED). Refuses to run under python -O.
Environment (negative tests only): UB_EPS (override eps), UB_SCALEB (multiply all b), UB_DROP (0-based indices with
b set to 0), UB_DEPTH (max bisection depth, default 40), UB_SHIFT (subtract a constant from F, to locate the margin).
"""
import json, sys, os, time, bisect
from fractions import Fraction as Fr
from flint import arb, ctx, fmpz_poly
if not __debug__:
    raise SystemExit("refusing to run with assertions disabled (python -O)")
ctx.prec = 160


def A(fr):
    return arb(fr.numerator) / arb(fr.denominator)


def _tlog(t, p):
    """t^p log|t| for an arb ball t (p >= 1), safe if t contains 0."""
    if not t.contains(0):
        return t ** p * abs(t).log()
    r = abs(t).upper()
    if r == 0:
        return arb(0)
    assert r < arb("0.3")
    bb = r ** p * (1 / r).log()
    return arb(0).union(bb).union(-bb)


def K1(t):          # K1' = log|t|
    return _tlog(t, 1) - t


def L2(t):          # L2' = t log|t|
    return _tlog(t, 2) / 2 - t * t / 4


class Cert:
    def __init__(self, path, eps_override=None, scaleb=None, drop=()):
        d = json.load(open(path))
        self.polys = [[int(a) for a in q] for q in d["A"]]
        for q in self.polys:
            assert len(q) >= 2 and q[0] != 0, "nonconstant integer polynomials"
        assert len(set(tuple(q) for q in self.polys)) == len(self.polys), "distinct polynomials"
        self.b = [Fr(x) for x in d["b"]]
        if scaleb is not None:
            self.b = [x * scaleb for x in self.b]
        for j in drop:
            self.b[j] = Fr(0)
        assert len(self.b) == len(self.polys) and all(x >= 0 for x in self.b), "b >= 0"
        self.eps = Fr(d["eps"]) if eps_override is None else Fr(eps_override)
        assert 0 < self.eps < 1
        self.n = [Fr(x) for x in d["nodes"]]
        self.w = [Fr(x) for x in d["w"]]
        N = len(self.n) - 1
        self.N = N
        assert len(self.w) == N - 1, "N - 1 hat weights for N + 1 nodes"
        assert self.n[0] == 0 and self.n[N] == 6, "nodes from 0 to 6"
        assert all(self.n[k] < self.n[k + 1] for k in range(N)), "nodes strictly increasing"
        assert all(x >= 0 for x in self.w) and sum(self.w) == 1, "hat weights >= 0 with sum exactly 1"
        n = self.n
        self.G = [Fr(0)] + [2 * self.w[i - 1] / (n[i + 1] - n[i - 1]) for i in range(1, N)] + [Fr(0)]
        mass = sum((n[k + 1] - n[k]) * (self.G[k] + self.G[k + 1]) / 2 for k in range(N))
        assert mass == 1, "mu_0 has mass 1"
        self.slope = [(self.G[k + 1] - self.G[k]) / (n[k + 1] - n[k]) for k in range(N)]
        C = [self.slope[0]] + [self.slope[k] - self.slope[k - 1] for k in range(1, N)] + [-self.slope[N - 1]]
        assert sum(C) == 0 and sum(Ci * ei for Ci, ei in zip(C, n)) == 0
        self.C = C
        self.active = [k for k in range(N) if self.G[k] != 0 or self.G[k + 1] != 0]
        self.beta = (1 - self.eps) * sum(bq * (len(q) - 1) for bq, q in zip(self.b, self.polys))
        # trace: mean of a unit-mass triangle on [a, c] with apex m is (a + m + c)/3
        mean0 = sum(self.w[j] * (n[j] + n[j + 1] + n[j + 2]) / 3 for j in range(N - 1))
        mean0_G = sum(((n[k + 1] - n[k]) * (self.G[k] * (2 * n[k] + n[k + 1]) + self.G[k + 1] * (n[k] + 2 * n[k + 1])) / 6)
                      for k in range(N))
        assert mean0 == mean0_G, "trace: hat form and G form agree"
        self.trace = (1 - self.eps) * mean0 + 3 * self.eps
        # irreducibility, primitivity, real roots in [0, 6]
        self.info = []
        for q in self.polys:
            P = fmpz_poly(list(reversed(q)))
            cont, facs = P.factor()
            assert abs(int(cont)) == 1 and len(facs) == 1 and facs[0][1] == 1, "primitive irreducible: %s" % q
            self.info.append(P)


class Ctx:
    def __init__(self, c, window_bits=110):
        self.c = c
        N = c.N
        self.E = [A(x) for x in c.n]
        self.Gv = [A(x) for x in c.G]
        self.gam = [A(x) for x in c.slope]
        self.Cnz = [(i, c.n[i], A(c.C[i]), c.C[i]) for i in range(N + 1) if c.C[i] != 0]
        eps = A(c.eps)
        self.shift = A(Fr(os.environ["UB_SHIFT"])) if os.environ.get("UB_SHIFT") else arb(0)
        const = eps * (arb(3) / 2).log() / (1 - eps) - self.shift
        self.roots = []          # dict(theta, w, rat, win, q)
        self.qroots = []         # per polynomial: list of root balls (for (M))
        for jq, (q, P, bq) in enumerate(zip(c.polys, c.info, c.b)):
            lead = abs(q[0])
            if bq != 0 and lead != 1:
                const -= A(bq) * arb(lead).log()
            rts = []
            if P.degree() == 1:
                r = Fr(-q[1], q[0])
                assert 0 <= r <= 6, "root in [0, 6]"
                rts.append(A(r))
                if bq != 0:
                    self.roots.append(dict(theta=A(r), w=A(bq), rat=r, win=None, q=jq))
            else:
                for rt, mult in P.complex_roots():
                    assert mult == 1
                    assert rt.imag == 0, "all roots real: %s" % q
                    th = rt.real
                    assert th > 0 and th < 6, "root in (0, 6): %s" % q
                    rts.append(th)
                    if bq == 0:
                        continue
                    sc = 2 ** window_bits
                    p = Fr(int((th.lower() * sc).floor().unique_fmpz()), sc)
                    qq = Fr(int((th.upper() * sc).ceil().unique_fmpz()), sc)
                    if p == qq:
                        qq = p + Fr(1, sc)
                    while not (A(p) < th.lower()):
                        p -= Fr(1, sc)
                    while not (A(qq) > th.upper()):
                        qq += Fr(1, sc)
                    self.roots.append(dict(theta=th, w=A(bq), rat=None, win=(p, qq), q=jq))
            assert len(rts) == P.degree()
            self.qroots.append(rts)
        self.const = const
        wins = sorted(r["win"] for r in self.roots if r["win"] is not None)
        for (p1, q1), (p2, q2) in zip(wins, wins[1:]):
            assert q1 < p2, "overlapping windows"
        for (p, q) in wins:
            i = bisect.bisect_left(c.n, p)
            assert i > c.N or c.n[i] > q, "node inside a root window"
        rats = [r["rat"] for r in self.roots if r["rat"] is not None]
        for r in rats:
            assert not any(p <= r <= q for p, q in wins)

    def U_and_dU(self, x, need_d=True):
        E, Gv, gam = self.E, self.Gv, self.gam
        U = arb(0)
        dU = arb(0)
        logs = {}
        tt = {}
        for k in self.c.active:
            for i in (k, k + 1):
                if i not in tt:
                    t = E[i] - x
                    tt[i] = t
                    if not t.contains(0):
                        logs[i] = abs(t).log()
                    elif t.is_zero():
                        logs[i] = arb(0)     # x = n_i: the two log|0| terms of U' have coefficients -G_i and +G_i
            a, b = tt[k], tt[k + 1]
            Ak = Gv[k] - gam[k] * a
            U += Ak * (K1(b) - K1(a)) + gam[k] * (L2(b) - L2(a))
            if need_d:
                dU += -Ak * (logs[k + 1] - logs[k]) - gam[k] * (b - a)
        return U, dU


def moments(X):
    """(M): int log|Q| dmu for every Q (lower endpoints)."""
    c = X.c
    eps = A(c.eps)
    out = []
    for q, rts in zip(c.polys, X.qroots):
        lead = arb(abs(q[0])).log()
        s0 = lead
        for th in rts:
            U, _ = X.U_and_dU(th, need_d=False)
            s0 += U
        val = (1 - eps) * s0 + eps * (lead + (len(q) - 1) * (arb(3) / 2).log())
        out.append(val)
    return out


def F_point(X, m):
    """F(m), F'(m) at a rational point m (not a node, not a root)."""
    x = A(m)
    F = X.const
    dF = arb(0)
    for r in X.roots:
        d = x - r["theta"]
        F -= r["w"] * abs(d).log()
        dF -= r["w"] / d
    U, dU = X.U_and_dU(x)
    F += U
    dF += dU
    return F, dF


NEAR = 3


def _dist(a, b, y):
    yf = float(y)
    return min(abs(yf - float(a)), abs(yf - float(b)))


def Fpp_lower(X, a, b, m, splits):
    """lower bound of the regular part of F'' on [a, b]; also the slope jumps at end nodes."""
    xm = A(m)
    T = A(a).union(A(b))
    h = (A(b) - A(a)) / 2
    thr = NEAR * float(b - a)
    v2 = arb(0)
    v3 = arb(0)
    vnear = arb(0)
    for idx, r in enumerate(X.roots):
        if idx in splits:
            continue
        th, w = r["theta"], r["w"]
        if _dist(a, b, th.mid()) < thr:
            da, db = A(a) - th, A(b) - th
            vnear += (w / (da * da)).union(w / (db * db))
        else:
            dm = xm - th
            v2 += w / (dm * dm)
            dT = T - th
            v3 += -2 * w / dT ** 3
    sing = []
    for (i, ei, Ci, Cfr) in X.Cnz:
        if ei == a or ei == b:
            sing.append(Cfr)
            continue
        if _dist(a, b, ei) < thr:
            la = abs(A(a) - X.E[i]).log()
            lb = abs(A(b) - X.E[i]).log()
            vnear += Ci * la.union(lb)
        else:
            v2 += Ci * abs(xm - X.E[i]).log()
            v3 += Ci / (T - X.E[i])
    m3 = arb(abs(v3).upper())
    return v2 - h * arb(0).union(m3).union(-m3) + vnear, sing, h


def interval_check(X, a, b):
    m = (a + b) / 2
    Fm, dFm = F_point(X, m)
    Ffull = Fm
    xm = A(m)
    low_root = arb(0)
    splits = set()
    for idx, r in enumerate(X.roots):
        side = None
        if r["rat"] is not None:
            if r["rat"] == b:
                side = "right"
            elif r["rat"] == a:
                side = "left"
        elif r["win"] is not None:
            if r["win"][0] == b:
                side = "right"
            elif r["win"][1] == a:
                side = "left"
        if side is None:
            continue
        splits.add(idx)
        th, w = r["theta"], r["w"]
        d = xm - th
        Fm -= -w * abs(d).log()
        dFm -= -w / d
        if side == "right":
            far = (A(r["win"][1]) if r["win"] else A(r["rat"])) - A(a)
        else:
            far = A(b) - (A(r["win"][0]) if r["win"] else A(r["rat"]))
        low_root += -w * far.log()
    lowpp, sing, h = Fpp_lower(X, a, b, m, splits)
    if not (lowpp.is_finite() and Fm.is_finite() and dFm.is_finite()):
        return False, None, Ffull
    Nn = -lowpp.lower()
    Nn = arb(Nn) if Nn > 0 else arb(0)
    L = A(b - a)
    assert L < 1
    S = arb(0)
    for Cfr in sing:
        if Cfr > 0:                     # C_i log|x - n_i| -> -inf at the end node: integral bound
            S += A(Cfr) * L * (1 - L.log())
    low = Fm - abs(dFm) * h - Nn * h * h / 2 - h * S + low_root
    return low.lower() > 0, low, Ffull


def window_check(X, idx):
    r = X.roots[idx]
    p, q = r["win"]
    T = A(p).union(A(q))
    val = X.const
    for j, r2 in enumerate(X.roots):
        if j == idx:
            continue
        val -= r2["w"] * abs(T - r2["theta"]).log()
    U, _ = X.U_and_dU(T, need_d=False)
    val += U
    val += -r["w"] * A(q - p).log()
    return val.lower() > 0, val


_X = None


def _jobs(jobs):
    X = _X
    maxdep = int(os.environ.get("UB_DEPTH", "40"))
    n = 0
    worst = None
    fmin = None
    deep = 0
    for (p, q) in jobs:
        stack = [(p, q, 0)]
        while stack:
            a, b, dep = stack.pop()
            ok, low, Fm = interval_check(X, a, b)
            n += 1
            if Fm is not None and Fm.is_finite() and (fmin is None or Fm.lower() < fmin[0]):
                fmin = (float(Fm.lower()), float((a + b) / 2))
            if ok:
                lv = float(low.lower())
                if worst is None or lv < worst[0]:
                    worst = (lv, float(a), float(b))
                deep = max(deep, dep)
                continue
            if Fm is not None and Fm.is_finite() and Fm.upper() < 0:
                return False, n, worst, fmin, deep, "F < 0 at x = %.15g: F = %s" % (float((a + b) / 2), Fm.str(10))
            if dep >= maxdep:
                return False, n, worst, fmin, deep, "FAIL on [%.15g, %.15g] depth %d: bound %s" % (float(a), float(b), dep, low)
            mid = (a + b) / 2
            stack += [(a, mid, dep + 1), (mid, b, dep + 1)]
    return True, n, worst, fmin, deep, ""


def _win(idx):
    ok, val = window_check(_X, idx)
    return ok, idx, float(val.lower())


def main():
    import multiprocessing as mp
    global _X
    path = sys.argv[1]
    nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    t0 = time.time()
    eps_o = os.environ.get("UB_EPS")
    scaleb = Fr(os.environ["UB_SCALEB"]) if os.environ.get("UB_SCALEB") else None
    drop = tuple(int(x) for x in os.environ.get("UB_DROP", "").split(",") if x.strip() != "")
    c = Cert(path, eps_override=eps_o, scaleb=scaleb, drop=drop)
    print("certificate: |A| = %d, nodes %d, hats %d, eps = %s" % (len(c.polys), len(c.n), len(c.w), c.eps), flush=True)
    print("(D) data, irreducibility, real roots: checked", flush=True)
    okS = c.beta < 1
    print("(S) beta = (1 - eps) sum b deg = %s = %.9f < 1: %s" % (c.beta, float(c.beta), okS), flush=True)
    X = Ctx(c)
    _X = X
    ms = moments(X)
    okM = all(v.lower() > 0 for v in ms)
    for q, v in zip(c.polys, ms):
        print("  int log|Q| dmu in %s   Q = %s" % (v.str(12), q), flush=True)
    print("(M) all > 0: %s (min lower endpoint %.6e)" % (okM, min(float(v.lower()) for v in ms)), flush=True)
    # breakpoints: nodes, rational roots, windows
    pts = set(c.n)
    for r in X.roots:
        if r["rat"] is not None:
            pts.add(r["rat"])
        else:
            pts.add(r["win"][0]); pts.add(r["win"][1])
    pts = sorted(p for p in pts if 0 <= p <= 6)
    wins = set(r["win"] for r in X.roots if r["win"] is not None)
    jobs = [(p, q) for p, q in zip(pts, pts[1:]) if (p, q) not in wins]
    widx = [i for i, r in enumerate(X.roots) if r["win"] is not None]
    print("intervals: %d, root windows: %d" % (len(jobs), len(widx)), flush=True)
    with mp.get_context("fork").Pool(nproc) as pool:
        wres = pool.map(_win, widx)
        chunks = [jobs[i::nproc * 8] for i in range(nproc * 8)]
        res = pool.map(_jobs, chunks)
    okW = all(ok for ok, _, _ in wres)
    print("root windows: %s (min %.6e)" % (okW, min(v for _, _, v in wres) if wres else float("nan")), flush=True)
    okP = all(r[0] for r in res)
    nint = sum(r[1] for r in res)
    worst = min((r[2] for r in res if r[2] is not None), default=None)
    fmin = min((r[3] for r in res if r[3] is not None), default=None)
    deep = max(r[4] for r in res)
    for r in res:
        if not r[0]:
            print("  " + r[5], flush=True)
    print("(P) F >= 0 on [0, 6]: %s; %d interval checks, max bisection depth %d; smallest lower bound %s on [%s, %s]; "
          "smallest F(midpoint) %s at %s" % (okP, nint, deep, worst[0] if worst else None, worst[1] if worst else None,
                                             worst[2] if worst else None, fmin[0] if fmin else None, fmin[1] if fmin else None),
          flush=True)
    print("(T) trace = (1 - eps) int x dmu_0 + 3 eps = %s = %.12f" % (c.trace, float(c.trace)), flush=True)
    ok = okS and okM and okW and okP
    print("%s (%.0f s)" % ("VERIFIED: C_86 <= %.10f" % float(c.trace) if ok else "NOT VERIFIED", time.time() - t0), flush=True)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
