"""Exact integer reference implementation of the 86a lower-bound checker (adapted from the companion Mahler-measure mirror for
the trace main term), and the generator of its leaves (the tiling of [x_lo, x_hi] into chord intervals and root windows).
Changes from the companion checker: DEC = 10^12; main term x (instead of log+ x, no kink at 1); constant lambda; slope jumps C_i from the
hat weights (unit-mass hats) exactly; s = sum rho; zero-weight polynomials dropped; right tail for x - kappa log x;
no degree budget. Not part of any proof: the Lean checker re-verifies every leaf.
Chord leaves use the end-point form of the checker (T86Core.CheckE): node sums at each end point (computed once per
point at the reduced scale) and the second-order bound max(-2 g_R(p), -2 g_R(q)) + K h^2/8 for the node part of the
curvature.

usage: python3 -I t86_check_ref.py CERT.json OUT_leaves.json workers ROOTS.json [I_LO]
(I_LO: claimed lower bound of the energy I(g) as a decimal, default 7.98221e-5 for certificate f1a60531)
"""
import json, sys, math, os
from fractions import Fraction as Fr

P = 64           # scale of point quantities (logs, F)
MAXK = 110       # refinement limit (scale exponent k) of the chord leaves; root-window ends start near k = 60
QS = 64          # scale of the C_i
J = 7            # series terms after table reduction (z <= 1/33)
W = 66           # table field width
DEC = 10 ** 12   # node denominator

# ---------------------------------------------------------------- logarithm (mirror of AuxCore.LogK)
def atanhK(p, z2, n, j, pw, acc):
    for _ in range(n):
        acc += pw // (2 * j + 1)
        pw = (pw * z2) >> p
        j += 1
    return acc, pw

def logRatK(p, Jn, A, B):
    zl = ((A - B) * (1 << p)) // (A + B)
    acc, pw = atanhK(p, (zl * zl) >> p, Jn, 0, zl, 0)
    d = 8 * (2 * Jn + 1)
    tail = (9 * (pw + 6) + d - 1) // d
    return 2 * acc, 2 * (acc + 7 * Jn + tail)

def roundOut(g, r):
    return (r[0] >> g, (r[1] + (1 << g) - 1) >> g)

def mkTable(p, g, Jn, Wd):
    T = 0
    for i in range(16):
        lo, hi = roundOut(g, logRatK(p + g, Jn, 16 + i, 16))
        T |= (lo << (Wd * 2 * i)) | (hi << (Wd * (2 * i + 1)))
    return T

TAB = mkTable(P, 24, 48, W)
L2 = roundOut(24, logRatK(P + 24, 48, 2, 1))

def logK(a, b):
    """enclosure (lo, hi) of 2^P log(a/b), a, b > 0"""
    s = a.bit_length() - 1; t = b.bit_length() - 1
    A0 = a << t; B = b << s
    if B <= A0: A, e = A0, s - t
    else: A, e = A0 << 1, s - t - 1
    i = (16 * (A - B)) // B
    lo, hi = logRatK(P, J, 16 * A, (16 + i) * B)
    m = (1 << W) - 1
    lo += (TAB >> (W * 2 * i)) & m
    hi += (TAB >> (W * (2 * i + 1))) & m
    if e >= 0: return lo + e * L2[0], hi + e * L2[1]
    return lo + e * L2[1], hi + e * L2[0]

# ---------------------------------------------------------------- interval helpers (integers)
def fdiv(a, b):  # floor(a/b), b > 0
    return a // b
def cdiv(a, b):  # ceil(a/b), b > 0
    return -((-a) // b)
def encl1(g, H):  # enclosure of sum g_n v^n for v in [0, H] (one-sided)
    lo = g[0] if g else 0; hi = lo
    for n in range(1, len(g)):
        t = g[n] * H ** n
        if t < 0: lo += t
        else: hi += t
    return (lo, hi)

def deriv(g):
    return [n * g[n] for n in range(1, len(g))]

def imul(a, b):  # interval product, a=(lo,hi), b=(lo,hi)
    xs = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return (min(xs), max(xs))

# ---------------------------------------------------------------- certificate
class Cert:
    def __init__(self, path):
        c = json.load(open(path))
        lam = [Fr(x) for x in c['lamQ']]
        self.polys = [q for q, l in zip(c['A'], lam) if l != 0]   # descending coefficients, active only
        self.cw = [l for l in lam if l != 0]
        for x in self.cw: assert x.denominator & (x.denominator - 1) == 0  # dyadic
        assert self.polys[0] == [1, 0]
        nodes = [Fr(x) for x in c['nodes']]
        assert all((x * DEC).denominator == 1 for x in nodes)
        self.n = [int(x * DEC) for x in nodes]
        rho = [Fr(x) for x in c['rho']]
        self.RS = max(x.denominator for x in rho).bit_length() - 1
        assert all((x * (1 << self.RS)).denominator == 1 for x in rho)
        self.r = [int(x * (1 << self.RS)) for x in rho]
        self.lam = Fr(c['lambda'])
        self.xlo, self.xhi = Fr(c['x_lo']), Fr(c['x_hi'])
        self.N = len(self.n) - 1
        N = self.N
        # slope jumps C_i (exact rationals) of g = sum rho_k h_k, h_k the unit-mass hat on [e_{k-1}, e_{k+1}]
        Cq = [Fr(0)] * (N + 1)
        for k in range(1, N):
            rr = Fr(self.r[k - 1], 1 << self.RS)
            if rr == 0: continue
            wl = Fr(self.n[k] - self.n[k - 1], DEC); wr = Fr(self.n[k + 1] - self.n[k], DEC); sc = 2 / (wl + wr)
            Cq[k - 1] += rr * sc / wl; Cq[k] -= rr * sc * (1 / wl + 1 / wr); Cq[k + 1] += rr * sc / wr
        assert sum(Cq) == 0 and sum(Cq[i] * Fr(self.n[i], DEC) for i in range(N + 1)) == 0
        self.C = []   # (num, den, clo, chi)
        for i in range(N + 1):
            num, den = Cq[i].numerator, Cq[i].denominator
            self.C.append((num, den, fdiv(num << QS, den), cdiv(num << QS, den)))
        # s exact = sum rho
        self.s_num = sum(self.r); self.s_den = 1 << self.RS
        # constants at scale 2^P
        self.m0hi = cdiv(self.lam.numerator << P, self.lam.denominator)
        self.cw_num = [x.numerator for x in self.cw]; self.cw_sh = [x.denominator.bit_length() - 1 for x in self.cw]
        self.deg = [len(q) - 1 for q in self.polys]
        self.sumabsC = sum(max(abs(c[2]), abs(c[3])) for c in self.C)

# ---------------------------------------------------------------- per-point pieces
def poly_taylor(coeffs_desc, X, D):
    """beta_n (ascending): R(v) = D^d Q((X+v)/D) = sum beta_n v^n (exact integers)"""
    d = len(coeffs_desc) - 1
    a = list(reversed(coeffs_desc))   # ascending a_m
    b = [a[m] * D ** (d - m) for m in range(d + 1)]
    for i in range(d):
        for j in range(d - 1, i - 1, -1):
            b[j] += X * b[j + 1]
    return b

def Is_lo(cert, Ilo_num, Ilo_sh):
    """lower bound of 2^P I/s given I >= Ilo_num / 2^Ilo_sh"""
    # I/s >= Ilo * s_den / s_num (s > 0)
    return fdiv(Ilo_num * cert.s_den << P, cert.s_num << Ilo_sh)

def canon(X, k):
    """(X, k) with factors 2 removed from X while k > 0 (mirror of T86Core.canon)"""
    while k > 0 and X % 2 == 0:
        X >>= 1; k -= 1
    return X, k

class Ctx:
    def __init__(self, cert, Ilo_num, Ilo_sh):
        self.c = cert
        self.Islo = Is_lo(cert, Ilo_num, Ilo_sh)
        self.epc = {}

    def __getstate__(self):
        d = dict(self.__dict__); d['epc'] = {}
        return d

    def node_pass(self, Xp, Xq, k):
        """one pass over the nodes for a leaf [Xp, Xq]/D (Xq may equal Xp for a point).
        Returns dict with U-sum intervals at p and q (scale 2^(P+QS+2), times D^2), the node part of M (scale 2^(P+QS)),
        the singular-node info, and whether a node lies strictly inside."""
        c = self.c
        D = DEC << k
        LD = logK(D, 1)
        Sp = [0, 0]; Sq = [0, 0]; M = 0; inside = False
        twoP34 = 3 << P
        for i in range(c.N + 1):
            num, den, clo, chi = c.C[i]
            if num == 0: continue
            ni = c.n[i] << k
            dp = ni - Xp; dq = ni - Xq
            if dp > 0 and dq < 0: inside = True; continue
            ap = abs(dp); aq = abs(dq)
            Lp = logK(ap, 1) if ap else None
            Lq = logK(aq, 1) if aq else None
            singular_pos = (num > 0) and (ap == 0 or aq == 0)
            # U terms: 4 Y 2^P = a^2 (2 (L - LD) - 3 2^P)
            if ap and not (singular_pos):
                Y = (ap * ap * (2 * (Lp[0] - LD[1]) - twoP34), ap * ap * (2 * (Lp[1] - LD[0]) - twoP34))
                t = imul((clo, chi), Y); Sp[0] += t[0]; Sp[1] += t[1]
            if aq and not (singular_pos):
                Y = (aq * aq * (2 * (Lq[0] - LD[1]) - twoP34), aq * aq * (2 * (Lq[1] - LD[0]) - twoP34))
                t = imul((clo, chi), Y); Sq[0] += t[0]; Sq[1] += t[1]
            # M node term: upper bound of -2 C_i log|x - e_i| on [p,q] (not for singular_pos)
            if Xq > Xp and not singular_pos:
                if ap and aq:
                    vlo = min(Lp[0], Lq[0]) - LD[1]; vhi = max(Lp[1], Lq[1]) - LD[0]
                elif ap:   # node at q, C < 0: log|x-e_i| <= log|p - e_i| = log h
                    vlo = None; vhi = Lp[1] - LD[0]
                else:
                    vlo = None; vhi = Lq[1] - LD[0]
                if num > 0:
                    M += -2 * (clo * vlo if vlo >= 0 else chi * vlo)
                else:
                    # -2 C v = 2 |C| v,  |C| in [-chi, -clo]
                    M += 2 * ((-clo) * vhi if vhi >= 0 else (-chi) * vhi)
        return dict(Sp=Sp, Sq=Sq, M=M, inside=inside, LD=LD, D=D)

    def U_hi(self, S, D):
        """upper bound of 2^P U from S (scale 2^(P+QS+2) D^2)"""
        return cdiv(S[1], (D * D) << (QS + 2))

    def logplus_lo(self, X, D):
        """main term x = X/D, lower bound at scale 2^P (name kept from the companion mirror)"""
        return fdiv(X << P, D)

    def ep(self, X, k):
        """node data at X / (DEC 2^k), at the reduced scale (mirror of T86Core.epAt): (uhi, g0, kl, kr, cl, cle,
        apl, aph, anl, anh)"""
        X, k = canon(X, k)
        key = (X, k)
        r = self.epc.get(key)
        if r is not None: return r
        c = self.c
        D = DEC << k; LD = logK(D, 1); DD = D * D; t3 = 3 << P
        S1 = 0; g0 = 0; kl = 0; kr = 0; cl = 0; cle = 0; apl = aph = anl = anh = 0
        for i in range(c.N + 1):
            num, den, clo, chi = c.C[i]
            if num == 0: continue
            ni = c.n[i] << k
            if ni == X:
                cle += 1
                if num > 0: apl += clo; aph += chi
                else: anl += clo; anh += chi
                continue
            ad = ni - X if ni > X else X - ni
            L = logK(ad, 1)
            v0 = L[0] - LD[1]; v1 = L[1] - LD[0]
            a2 = ad * ad
            S1 += imul((clo, chi), (a2 * (2 * v0 - t3), a2 * (2 * v1 - t3)))[1]
            g0 += imul((clo, chi), (v0, v1))[0]
            kt = cdiv(2 * (-clo) * DD, a2) if num < 0 else 0
            if ni < X: kl += kt; cl += 1; cle += 1
            else: kr += kt
        r = (cdiv(S1, DD << (QS + 2)), g0, kl, kr, cl, cle, apl, aph, anl, anh)
        self.epc[key] = r
        return r

    def chord_leaf(self, Xp, Xq, k, x0q, convmask):
        """lower bounds L(p), L(q) at scale 2^P; None if a structural check fails (mirror of T86Core.chordLBC)"""
        c = self.c
        D = DEC << k; H = Xq - Xp
        if not (Xp < Xq and H <= D): return None    # h <= 1
        A = self.ep(Xp, k); B = self.ep(Xq, k)
        if B[4] != A[5]: return None                # a node with C != 0 strictly inside (p, q)
        LD = logK(D, 1); Lh = logK(H, 1)
        lh = (Lh[0] - LD[1], Lh[1] - LD[0])         # 2^P log h
        t3 = 3 << P
        Yh = (H * H * (2 * lh[0] - t3), H * H * (2 * lh[1] - t3))   # 4 2^P D^2 Hk(h)
        uP = A[0] - fdiv(imul((B[6], B[7]), Yh)[0], (D * D) << (QS + 2))   # minus the singular nodes at q
        uQ = B[0] - fdiv(imul((A[6], A[7]), Yh)[0], (D * D) << (QS + 2))
        gp = A[1] - imul((B[6] + B[8], B[7] + B[9]), lh)[1]                 # g_R(p): without the nodes at q
        gq = B[1] - imul((A[6] + A[8], A[7] + A[9]), lh)[1]
        def eterm(nl, nh):   # 2 |C| log h for the nodes with C < 0 at an end point (scale 2^(P+QS))
            return 2 * ((-nl) * lh[1] if lh[1] >= 0 else (-nh) * lh[1])
        Mt = eterm(A[8], A[9]) + eterm(B[8], B[9]) + max(-2 * gp, -2 * gq) + \
            cdiv((A[2] + B[3]) * H * H << P, 8 * D * D)          # node part of M: scale 2^(P+QS)
        Ap = self.logplus_lo(Xp, D) - c.m0hi + self.Islo - 2 * uP
        Aq = self.logplus_lo(Xq, D) - c.m0hi + self.Islo - 2 * uQ
        Tx0 = 0; slope = 0      # slope term added to the far end (lower bound, scale 2^P)
        Mpoly = 0               # scale 2^P, already times h^2 (= H^2 / D^2 ... see below)
        for j, coef in enumerate(c.polys):
            beta = poly_taylor(coef, Xp, D)
            d = len(beta) - 1
            b1 = deriv(beta); b2 = deriv(b1)
            Wp = beta[0]; Wq = sum(beta[n] * H ** n for n in range(d + 1))
            R0 = encl1(beta, H); R1 = encl1(b1, H); R2 = encl1(b2, H)
            ex0 = R0[0] > 0 or R0[1] < 0
            mono = R1[0] > 0 or R1[1] < 0
            if not (ex0 or (mono and Wp * Wq > 0)): return None    # possible root in [p,q]
            cn, cs = c.cw_num[j], c.cw_sh[j]
            def mclog_lo(Wv):   # lower bound of -c_j log|Q_j| at scale 2^P
                Lw = logK(abs(Wv), 1)
                return fdiv(-cn * (Lw[1] - d * LD[0]), 1 << cs)
            sq = imul(R1, R1); sq = (max(sq[0], 0) if R1[0] * R1[1] >= 0 else 0, sq[1])
            RR = imul(R0, R2)
            if (convmask >> j) & 1:
                if sq[0] - RR[1] < 0: return None
                if x0q:
                    Tx0 += mclog_lo(Wq)
                    R1H = sum(b1[n] * H ** n for n in range(len(b1)))
                    slope += fdiv(cn * R1H * H << P, Wq << cs) if Wq > 0 else fdiv((-cn) * R1H * H << P, (-Wq) << cs)
                else:
                    Tx0 += mclog_lo(Wp)
                    R10 = b1[0] if b1 else 0
                    slope += fdiv(-cn * R10 * H << P, Wp << cs) if Wp > 0 else fdiv(cn * R10 * H << P, (-Wp) << cs)
            else:
                Ap += mclog_lo(Wp); Aq += mclog_lo(Wq)
                Nhi = sq[1] - RR[0]
                rlo = min(abs(R0[0]), abs(R0[1])) if ex0 else 0
                if mono: rlo = max(rlo, min(abs(Wp), abs(Wq)))
                if Nhi > 0:
                    Mpoly += cdiv(cn * H * H * Nhi << P, (rlo * rlo) << cs)
        # node M part times h^2/8:  M (scale 2^(P+QS)) * H^2 / D^2 -> scale 2^P
        Mn = cdiv(max(Mt, 0) * H * H, (D * D) << QS) if Mt > 0 else 0
        Mtot = Mn + Mpoly
        corr = cdiv(Mtot, 8)
        if x0q:
            Lp = Ap + Tx0 + slope - corr
            Lq = Aq + Tx0 - corr
        else:
            Lp = Ap + Tx0 - corr
            Lq = Aq + Tx0 + slope - corr
        return Lp, Lq

    def window_leaf(self, Xu, Xv, k):
        c = self.c
        D = DEC << k; H = Xv - Xu
        if not Xu < Xv: return None
        if not Xv <= 22 * D: return None   # windows lie in [0, 22] (checker's windowOK)
        r = self.node_pass(Xu, Xu, k)
        LD = r['LD']
        F = self.logplus_lo(Xu, D) - c.m0hi + self.Islo
        for j, coef in enumerate(c.polys):
            beta = poly_taylor(coef, Xu, D)
            d = len(beta) - 1
            R0 = encl1(beta, H); B = max(abs(R0[0]), abs(R0[1]))
            Lb = logK(B, 1)
            F += fdiv(-c.cw_num[j] * (Lb[1] - d * LD[0]), 1 << c.cw_sh[j])
        # U(x) <= U(u) + h * 46 * sum|C_i|
        Uu = self.U_hi(r['Sp'], D)
        dU = cdiv(47 * c.sumabsC * H << P, D << QS)
        return F - 2 * (Uu + dU)

# ---------------------------------------------------------------- tiling generator
def pt_val(X, k):
    return Fr(X, DEC << k)

def common(a, b):
    """bring points a=(X,k), b=(X,k) to a common k"""
    k = max(a[1], b[1])
    return a[0] << (k - a[1]), b[0] << (k - b[1]), k

def check_interval(args):
    """bisect [a, b] (points (X, k)) until every chord leaf passes; returns (leaves, fails)"""
    ctx, a, b, maxk = args
    leaves = []; fails = []; stack = [(a, b)]
    while stack:
        a, b = stack.pop()
        Xp, Xq, k = common(a, b)
        best = None
        for x0q in (True, False):
            # convex mask: try all polynomials convex on [p,q]
            mask = 0
            for j in range(len(ctx.c.polys)):
                mask |= (1 << j)
            res = None
            # first try with the full mask; the checker returns None if some j is not convex: then drop such j
            res = ctx.chord_leaf(Xp, Xq, k, x0q, mask)
            if res is None:
                mask = convex_mask(ctx, Xp, Xq, k)
                if mask is None: break
                res = ctx.chord_leaf(Xp, Xq, k, x0q, mask)
            if res is not None:
                lb = min(res)
                if best is None or lb > best[0]: best = (lb, x0q, mask)
        if best is not None and best[0] > 0:
            leaves.append(dict(Xp=Xp, Xq=Xq, k=k, x0q=best[1], mask=best[2], lb=best[0]))
        elif k >= maxk:
            fails.append(dict(Xp=Xp, Xq=Xq, k=k, lb=None if best is None else best[0]))
        else:
            m = (Xp + Xq, k + 1)
            stack.append(((Xp << 1, k + 1), m)); stack.append((m, (Xq << 1, k + 1)))
    return leaves, fails

def convex_mask(ctx, Xp, Xq, k):
    c = ctx.c; D = DEC << k; H = Xq - Xp; mask = 0
    for j, coef in enumerate(c.polys):
        beta = poly_taylor(coef, Xp, D); d = len(beta) - 1
        b1 = deriv(beta); b2 = deriv(b1)
        Wq = sum(beta[n] * H ** n for n in range(d + 1))
        R0 = encl1(beta, H); R1 = encl1(b1, H); R2 = encl1(b2, H)
        ex0 = R0[0] > 0 or R0[1] < 0; mono = R1[0] > 0 or R1[1] < 0
        if not (ex0 or (mono and beta[0] * Wq > 0)): return None
        sq = imul(R1, R1); sq = (max(sq[0], 0) if R1[0] * R1[1] >= 0 else 0, sq[1])
        RR = imul(R0, R2)
        if sq[0] - RR[1] >= 0: mask |= 1 << j
    return mask

KW = 60

def right_tail_lb(ctx, Xt):
    """lower bound (scale 2^P) of x_t - kappa' log x_t - lambda + I/s - sum c_j log A_j(x_t), x_t = Xt / DEC, with
    kappa' = sum c_j deg_j + 2 s (valid for x >= x_t when x_t >= max(1, e_N, kappa'))"""
    c = ctx.c
    lx = logK(Xt, DEC)
    S = max(c.cw_sh)
    kNum = sum(c.cw_num[j] * c.deg[j] * (1 << (S - c.cw_sh[j])) * c.s_den for j in range(len(c.polys))) + 2 * c.s_num * (1 << S)
    kDen = (1 << S) * c.s_den
    assert Fr(kNum, kDen) <= Fr(Xt, DEC) and Fr(c.n[-1], DEC) <= Fr(Xt, DEC) and DEC <= Xt
    klog = cdiv(kNum * lx[1], kDen)
    part = 0
    for j, coef in enumerate(c.polys):
        d = len(coef) - 1
        num = sum(abs(a) * DEC ** n * Xt ** (d - n) for n, a in enumerate(coef))   # coef descending: a_n x^(d-n)
        part += fdiv(-c.cw_num[j] * logK(num, Xt ** d)[1], 1 << c.cw_sh[j])
    return fdiv(Xt << P, DEC) - klog - c.m0hi + ctx.Islo + part

def left_tail_lb(ctx, X0, k):
    """(0, x0], x0 = X0 / (DEC 2^k) <= 1 and x0 <= the first node with C_i != 0 (U is decreasing left of the support):
    F >= 0 - lambda - c_0 log x0 - sum_{j>=1} c_j log B_j - 2 U(0) + I/s"""
    c = ctx.c
    D = DEC << k
    LD = logK(D, 1)
    r = ctx.node_pass(0, 0, k)
    part = 0
    for j, coef in enumerate(c.polys):
        if j == 0:
            part += fdiv(-c.cw_num[0] * logK(X0, D)[1], 1 << c.cw_sh[0])
        else:
            beta = poly_taylor(coef, 0, D); d = len(beta) - 1
            R0 = encl1(beta, X0); B = max(abs(R0[0]), abs(R0[1]))
            part += fdiv(-c.cw_num[j] * (logK(B, 1)[1] - d * LD[0]), 1 << c.cw_sh[j])
    assert 0 < X0 <= D
    assert all(r == 0 or X0 <= c.n[j] << k for j, r in enumerate(c.r))   # leftTailPre: rho_j = 0 if e_{j-1} < x0
    return ctx.Islo - c.m0hi + part - 2 * ctx.U_hi(r['Sp'], D)

def make_breaks(cert, roots):
    """initial chord intervals and windows on [x_lo, x_hi]; windows: (Xu, Xv, k)"""
    XL = int(cert.xlo * DEC); XH = int(cert.xhi * DEC)
    assert Fr(XL, DEC) == cert.xlo and Fr(XH, DEC) == cert.xhi
    x0 = (XL, 0); xhi = (XH, 0)
    wins = []
    for r in roots:
        assert r['mult'] == 1
        wins.append((r['X0'] - 1, r['X1'] + 1, KW))
    wins.sort(key=lambda w: Fr(w[0], DEC << w[2]))
    merged = []
    for w in wins:
        if merged and Fr(w[0], DEC << w[2]) <= Fr(merged[-1][1], DEC << merged[-1][2]):
            a, b, k = merged[-1]; kk = max(k, w[2])
            merged[-1] = (a << (kk - k), max(b << (kk - k), w[1] << (kk - w[2])), kk)
        else: merged.append(w)
    wins = merged
    bps = {(X, 0) for X in cert.n if cert.xlo <= Fr(X, DEC) <= cert.xhi} | {x0, xhi}
    wpts = []
    for u, v, k in wins:
        bps |= {(u, k), (v, k)}; wpts.append((Fr(u, DEC << k), Fr(v, DEC << k)))
    bps = sorted(bps, key=lambda t: pt_val(*t)); uniq = []
    for t in bps:
        if uniq and pt_val(*uniq[-1]) == pt_val(*t): continue
        uniq.append(t)
    ivs = [(uniq[i], uniq[i + 1]) for i in range(len(uniq) - 1)
           if not any(wu <= pt_val(*uniq[i]) and pt_val(*uniq[i + 1]) <= wv for wu, wv in wpts)]
    return ivs, wins

def main():
    import multiprocessing as mp, time
    cert = Cert(sys.argv[1]); out = sys.argv[2]; workers = int(sys.argv[3]) if len(sys.argv) > 3 else os.cpu_count()
    roots = json.load(open(sys.argv[4]))
    # claimed lower bound of I(g) (verified by the energy check); optional 5th argument, default for certificate f1a60531
    Ilo_sh = 128; Ilo_num = int(Fr(sys.argv[5] if len(sys.argv) > 5 else '7.98221e-5') * (1 << Ilo_sh))
    ctx = Ctx(cert, Ilo_num, Ilo_sh)
    XH = int(cert.xhi * DEC)
    rt = right_tail_lb(ctx, XH)
    lt = left_tail_lb(ctx, int(cert.xlo * DEC), 0)
    print('right tail lb at', float(cert.xhi), rt / 2**P, ' left tail lb on (0,', float(cert.xlo), ']', lt / 2**P, flush=True)
    ivs, wins = make_breaks(cert, roots)
    print('windows', len(wins), 'initial chord intervals', len(ivs), flush=True)
    t0 = time.time()
    with mp.Pool(workers) as pool:
        res = pool.map(check_interval, [(ctx, a, b, MAXK) for a, b in ivs], chunksize=1)
    leaves = [l for r in res for l in r[0]]; fails = [f for r in res for f in r[1]]
    print('chord leaves', len(leaves), 'fails', len(fails), 'min lb', min(l['lb'] for l in leaves) / 2**P, f'{time.time()-t0:.0f}s', flush=True)
    wl = []
    for u, v, k in wins:
        lb = ctx.window_leaf(u, v, k)
        wl.append(dict(Xu=u, Xv=v, k=k, lb=lb))
    print('windows min lb', min(w['lb'] for w in wl) / 2**P, 'bad', sum(w['lb'] <= 0 for w in wl), flush=True)
    json.dump(dict(chord=leaves, windows=wl, fails=fails, Ilo=[Ilo_num, Ilo_sh], xhi=XH, rt=rt, lt=lt), open(out, 'w'))

if __name__ == '__main__':
    main()
