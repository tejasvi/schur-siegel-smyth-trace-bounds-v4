"""First checker for a lower bound on the Schur-Siegel-Smyth trace constant C_86 (Lemma 2.1 of the paper; "Lemma T1" below).
v3 (from v2 84ec283f): polynomial enclosures over intervals use exact Taylor coefficients at the rational midpoint
(Horner on arb balls blows up for degree-10 polynomials with large coefficients); exit status 0 iff VERIFIED;
at most 3e6 interval checks per chunk (fails closed).
v4 (from v3 5ca8ed61): every real-root bracket is bisected exactly (sign of Q at rational points) to width <= 2^-100
before the exclusion windows are built, so a window can be made narrow enough for the ball evaluation of U.

Certificate (JSON): A = list of nonzero integer polynomials (coefficients, highest degree first),
lamQ = list of nonnegative rationals (one per polynomial), nodes = increasing rationals e_0 < ... < e_N,
rho = nonnegative rationals (N-1 values; weight of the hat on [e_{k-1}, e_{k+1}] normalized to mass 1),
lambda = rational. Optional: x_lo, x_hi (rationals).
Claim verified: F(x) = x - lambda - sum_Q lamQ_Q log|Q(x)| - (2 U_nu(x) - I(nu)) * s >= 0 for all x > 0,
where s = sum rho, nu = (sum_k rho_k h_k)/s (piecewise-linear probability density), U_nu(x) = int log|x-y| dnu(y),
I(nu) = int U_nu dnu. By Lemma T1 (lambda_0 = s), this implies C_86 >= lambda.

Formulas (rebuilt from definitions): the density g = sum_k rho_k h_k is continuous, piecewise linear, compactly
supported, so g'' = sum_i C_i delta_{e_i} (distributional) with C_i computed below. Integrating by parts twice,
int log|x-y| g(y) dy = sum_i C_i H(e_i - x) with H'' = log|t|, H(t) = t^2/2 log|t| - 3 t^2 / 4; and
int int log|y-z| g(y) g(z) = sum_{i,j} C_i C_j J(e_i - e_j) with J'''' = log|t|, J(t) = t^4/24 log|t| - 25 t^4/288.
(Boundary terms vanish because g and g' vanish outside [e_0, e_N]; H, J and their first derivatives are continuous.)
"""
import json, sys, math
from fractions import Fraction as Fr
from flint import arb, ctx
ctx.prec = 200
class CheckError(Exception): pass
def require(cond, msg):
    if not cond: raise CheckError(msg)
def A(fr): return arb(fr.numerator)/arb(fr.denominator)
def logabs(t):   # t arb, nonzero
    return abs(t).log()
def Hf(t):
    if t.is_zero(): return arb(0)
    if t.contains(0):
        r = abs(t).upper()
        require(r < arb('0.6'), "ball too wide around a node")
        B = r*r*((1/r).log()/2 + arb(3)/4)
        return arb(0).union(B).union(-B)
    return t*t/2*logabs(t) - arb(3)/4*t*t
def Jf(t):
    if t.is_zero(): return arb(0)
    t2 = t*t; t4 = t2*t2
    return t4/24*logabs(t) - arb(25)/288*t4
def polyval(c, x):   # c highest first (ints), x arb
    v = arb(0)
    for a in c: v = v*x + a
    return v
def polyder(c):
    d = len(c) - 1; return [c[i]*(d - i) for i in range(d)]
def taylor_coeffs(c, m):
    # coefficients a_k of Q(m + t) = sum_k a_k t^k (exact), c integers highest first, m Fraction
    a = [Fr(x) for x in c]; n = len(a) - 1; out = []
    for k in range(n + 1):
        b = [a[0]]
        for x in a[1:]: b.append(b[-1]*m + x)
        out.append(b[-1]); a = b[:-1]
        if not a: break
    return out
def taylor_ball(c, p, q):
    # arb enclosures of Q, Q', Q'' over [p, q] (p < q Fractions)
    m = (p + q)/2; r = (q - p)/2; a = taylor_coeffs(c, m); n = len(a) - 1
    def enc(coefs):
        tail = sum(abs(coefs[k])*r**k for k in range(1, len(coefs)))
        return A(coefs[0]) + arb(0, 1)*A(tail) if len(coefs) > 1 else A(coefs[0])
    Q0 = enc(a)
    Q1 = enc([k*a[k] for k in range(1, n + 1)]) if n >= 1 else arb(0)
    Q2 = enc([k*(k-1)*a[k] for k in range(2, n + 1)]) if n >= 2 else arb(0)
    return Q0, Q1, Q2
class Cert:
    def __init__(self, path):
        d = json.load(open(path))
        self.Apolys = [list(map(int, q)) for q in d['A']]
        self.lamQ = [Fr(x) for x in d['lamQ']]
        self.e = [Fr(x) for x in d['nodes']]
        self.rho = [Fr(x) for x in d['rho']]
        self.lam = Fr(d['lambda'])
        require(all(x >= 0 for x in self.lamQ) and all(x >= 0 for x in self.rho), "negative weight")
        require(all(self.e[i] < self.e[i+1] for i in range(len(self.e)-1)), "nodes not increasing")
        require(len(self.rho) == len(self.e) - 2 and len(self.lamQ) == len(self.Apolys), "length mismatch")
        require(all(any(c != 0 for c in q) for q in self.Apolys), "zero polynomial")
        require(len(set(tuple(q) for q in self.Apolys)) == len(self.Apolys), "duplicate polynomial")
        self.s = sum(self.rho); require(self.s > 0, "zero mass")
        # node coefficients C_i of g'' (exact)
        N = len(self.e) - 1; C = [Fr(0)]*(N+1)
        for k in range(1, N):
            wl = self.e[k] - self.e[k-1]; wr = self.e[k+1] - self.e[k]; sc = 2/(wl + wr)
            r = self.rho[k-1]
            if r == 0: continue
            C[k-1] += r*sc/wl; C[k] -= r*sc*(1/wl + 1/wr); C[k+1] += r*sc/wr
        require(sum(C) == 0 and sum(C[i]*self.e[i] for i in range(N+1)) == 0, "g'' moments")   # zero mass, zero first moment
        self.C = C; self.Ca = [A(c) for c in C]; self.ea = [A(x) for x in self.e]
        self.nz = [i for i in range(N+1) if C[i] != 0]
    def energy_times_s2(self):
        # I(g) = int int log|y-z| g g = sum C_i C_j J(e_i - e_j); returns arb
        tot = arb(0); idx = self.nz
        for a_ in idx:
            row = arb(0); ea = self.ea[a_]
            for b_ in idx:
                if b_ == a_: continue
                row += self.Ca[b_]*Jf(ea - self.ea[b_])
            tot += self.Ca[a_]*row
        return tot
    def U_times_s(self, x):    # x arb (ball): int log|x-y| g(y) dy
        v = arb(0)
        for i in self.nz: v += self.Ca[i]*Hf(self.ea[i] - x)
        return v
    def U_times_s_exact(self, xf):   # xf Fraction: differences computed exactly
        v = arb(0)
        for i in self.nz:
            t = self.e[i] - xf
            if t != 0: v += self.Ca[i]*Hf(A(t))
        return v

def setup(cert):
    cert.active = [(q, A(l)) for q, l in zip(cert.Apolys, cert.lamQ) if l != 0]
    cert.Is2 = cert.energy_times_s2()            # s^2 I(nu)
    cert.const = cert.Is2/A(cert.s) - A(cert.lam)
    return cert
def F_ball(cert, x):
    # F(x) for arb x (possibly a ball): x - lambda - sum lamQ log|Q(x)| - 2 U_s(x) + I_s2/s
    v = x + cert.const
    for q, l in cert.active: v -= l*logabs(polyval(q, x))
    v -= 2*cert.U_times_s(x)
    return v
def Fpp_upper(cert, p, q):
    # upper bound of the regular part of F'' on [p,q] (arb ball over the interval) + singular endpoint contributions
    X = (A(p) + A(q))/2; X = X.union(A(p)).union(A(q))   # ball covering [p,q]
    h = q - p
    reg = arb(0)
    for qq, l in cert.active:
        Qv, Q1, Q2 = taylor_ball(qq, p, q)
        if Qv.contains(0): return arb('nan'), arb('nan')
        reg += l*(Q1*Q1 - Qv*Q2)/(Qv*Qv)
    sing = arb(0)
    for i in cert.nz:
        ei = cert.e[i]
        if ei == p or ei == q:
            c = cert.C[i]
            if c > 0:   # -2 c log|e - x| >= 0 singular: integral bound 2 c h (1 + log(1/h)), valid for h <= 1
                if h > 1: return arb('nan'), arb('nan')
                hh = A(h); sing += 2*cert.Ca[i]*hh*(1 + (1/hh).log())
            else:       # -2 c log|e-x| = 2|c| log|e-x| <= 2|c| log h
                reg += -2*cert.Ca[i]*A(h).log()
        else:
            reg += -2*cert.Ca[i]*logabs(cert.ea[i] - X)
    return reg, sing
def F_exact(cert, xf):
    # F at a rational point (exact differences; Q(x) exact)
    v = A(xf) + cert.const
    for q, l in cert.active:
        Qx = sum(Fr(c)*xf**(len(q)-1-i) for i, c in enumerate(q))
        require(Qx != 0, "evaluation exactly at a root")
        v -= l*logabs(A(Qx))
    v -= 2*cert.U_times_s_exact(xf)
    return v
def check_interval(cert, p, q):
    # returns True if F >= 0 proven on [p,q] (no root of an active polynomial in [p,q])
    Fp = F_exact(cert, p); Fq = F_exact(cert, q)
    if not (Fp.lower() > 0 and Fq.lower() > 0): return False, (Fp if not (Fp.lower() > 0) else Fq).lower()
    lo = Fp.lower() if Fp.lower() < Fq.lower() else Fq.lower()
    reg, sing = Fpp_upper(cert, p, q)
    h = A(q - p)
    if not (reg.is_finite() and sing.is_finite()): return False, lo
    regu = reg.upper()
    pen = h/4*(h*(regu if regu > 0 else arb(0)) + sing)
    ok = (arb(lo) - pen).lower() > 0
    return bool(ok), lo

def real_root_brackets(q, lo, hi):
    # rigorous isolation of real roots of integer polynomial q in [lo,hi] via numpy guesses + arb sign changes;
    # also verifies the count with a Sturm sequence over Fractions.
    import numpy as np
    from fractions import Fraction as Fr
    # Sturm count of distinct real roots in (lo, hi]
    def pdiv(a, b):   # polynomial remainder over Fractions, highest first
        a = a[:]; 
        while len(a) >= len(b) and any(a):
            f = a[0]/b[0]; 
            for i in range(len(b)): a[i] -= f*b[i]
            a.pop(0)
        while a and a[0] == 0: a.pop(0)
        return a
    def ev(p, x): 
        v = Fr(0)
        for c in p: v = v*x + c
        return v
    P0 = [Fr(c) for c in q]; P1 = [Fr(c)*(len(q)-1-i) for i, c in enumerate(q[:-1])]
    seq = [P0, P1]
    while seq[-1] and len(seq[-1]) > 0:
        r = pdiv(seq[-2], seq[-1]); 
        if not r: break
        seq.append([-c for c in r])
    def V(x):
        vals = [ev(p, x) for p in seq]; vals = [v for v in vals if v != 0]
        return sum(1 for a, b in zip(vals, vals[1:]) if (a > 0) != (b > 0))
    count = V(Fr(lo)) - V(Fr(hi))
    guesses = sorted(set(float(r.real) for r in np.roots(q) if abs(r.imag) < 1e-9 and lo < r.real < hi))
    brackets = []
    for g in guesses:
        for dlt in [1e-12, 1e-10, 1e-8, 1e-6]:
            a_ = Fr(g) - Fr(dlt); b_ = Fr(g) + Fr(dlt)
            if ev(P0, a_)*ev(P0, b_) < 0: brackets.append((a_, b_)); break
        else:
            raise RuntimeError(f"could not bracket root {g} of {q}")
    require(len(brackets) == count, f"root isolation mismatch {q} {count} {len(brackets)}")
    tight = []
    for a_, b_ in brackets:
        fa = ev(P0, a_)
        require(fa != 0 and fa*ev(P0, b_) < 0, "bracket without a sign change")
        while b_ - a_ > Fr(1, 2**100):
            m = (a_ + b_)/2; fm = ev(P0, m)
            if fm == 0:
                a_, b_ = m - Fr(1, 2**101), m + Fr(1, 2**101); break
            if (fm > 0) == (fa > 0): a_, fa = m, fm
            else: b_ = m
        tight.append((a_, b_))
    return tight
def verify(cert, x_lo, x_hi, delta0=Fr(1, 10**4), max_depth=60, log=print):
    # Breakpoints: nodes in [x_lo,x_hi], and exclusion windows around active-polynomial roots.
    pts = set([x_lo, x_hi]) | set(e for e in cert.e if x_lo < e < x_hi)
    excl = []
    for q, l in cert.active:
        for (a_, b_) in real_root_brackets(q, x_lo, x_hi):
            excl.append((a_, b_, q))
    # handle exclusion windows: grow window to [r-d, r+d] where F>0 is proven by the log blow-up
    windows = []
    for (a_, b_, q) in excl:
        d = delta0; ok = False
        while d >= Fr(1, 10**14):
            L = a_ - d; R = b_ + d
            if L <= x_lo or R >= x_hi: d /= 10; continue
            X = (A(L) + A(R))/2; X = X.union(A(L)).union(A(R))
            v = X + cert.const
            for qq, l in cert.active:
                # log|Q(x)| <= log(max|Q|) on window (Taylor enclosure at the window midpoint)
                mx = abs(taylor_ball(qq, L, R)[0]).upper()
                v -= l*arb(mx).log()
            v -= 2*cert.U_times_s(X)
            if v.lower() > 0: ok = True; break
            d /= 10
        if not ok: log(f"FAIL exclusion window for root in [{float(a_)},{float(b_)}] of {q}"); return False
        windows.append((a_ - d, b_ + d))
        pts |= {a_ - d, b_ + d}
    pts = sorted(pts)
    # merge: intervals to check = consecutive breakpoints not inside a window
    def in_window(p, q):
        return any(L <= p and q <= R for (L, R) in windows)
    stack = [(p, q, 0) for p, q in zip(pts, pts[1:]) if not in_window(p, q)]
    nchk = 0; minlo = None
    while stack:
        p, q, dep = stack.pop()
        ok, lo = check_interval(cert, p, q); nchk += 1
        if minlo is None or lo < minlo: minlo = lo
        if ok: continue
        if nchk > 3000000:
            log(f"FAIL: more than 3e6 interval checks in chunk starting {float(x_lo):.6f}"); return False
        if dep >= max_depth or not (lo > 0):
            log(f"FAIL on [{float(p):.12f},{float(q):.12f}] depth {dep} F-lower {float(lo):.3e}"); return False
        m = (p + q)/2; m = Fr(round(m*2**40), 2**40) if p < Fr(round(m*2**40), 2**40) < q else m
        stack += [(p, m, dep+1), (m, q, dep+1)]
    log(f"verified [{float(x_lo)},{float(x_hi)}]: {nchk} interval checks, min endpoint F-lower {float(minlo):.3e}")
    return True

def tail_left(cert, x_lo):
    # (0, x_lo]: requires x_lo <= first node carrying density (U decreasing & concave left of supp nu), x in A with lamQ>0,
    # and no root of other active polynomials in [0, x_lo].
    first = min(cert.e[i] for i in cert.nz)
    require(first >= 0, "support of nu must lie in [0, inf)")
    require(0 < x_lo <= first and x_lo < 1, "x_lo must be in (0,1) and left of the support of nu")
    lx = [l for q, l in cert.active if q == [1, 0]]
    require(len(lx) == 1, "need the polynomial x exactly once with positive multiplier")
    v = -A(cert.lam) - lx[0]*A(x_lo).log() + cert.Is2/A(cert.s)
    X = arb(0).union(A(x_lo))
    for q, l in cert.active:
        if q == [1, 0]: continue
        Qb = polyval(q, X)
        require(not Qb.contains(0), "another active polynomial vanishes in [0,x_lo]")
        v -= l*arb(abs(Qb).upper()).log()
    v -= 2*cert.U_times_s_exact(Fr(0))   # U(x) <= U(0) on [0, x_lo]
    return v.lower() > 0, v
def tail_right(cert, x_hi):
    last = max(cert.e[i] for i in cert.nz); first = min(cert.e[i] for i in cert.nz)
    require(x_hi >= last and x_hi >= 1 and first >= 0, "x_hi must exceed the support (inside [0,inf)) and 1")
    alpha = 2*A(cert.s); beta = A(cert.lam) - cert.Is2/A(cert.s)
    for q, l in cert.active:
        alpha += l*(len(q) - 1); beta += l*arb(sum(abs(c) for c in q)).log()
    # all real roots of active polys must be <= x_hi (checked via |Q(x)| <= sum|q_k| x^d needing only x >= 1)
    g = A(x_hi) - alpha*A(x_hi).log() - beta
    return (A(x_hi) - alpha).lower() >= 0 and g.lower() > 0, g, alpha
_CERT = None
def _worker(args):
    p, q = args            # Fractions; the certificate is inherited from the parent via fork (global _CERT)
    out = []
    ok = verify(_CERT, p, q, log=lambda s: out.append(s))
    return ok, out
if __name__ == '__main__':
    import multiprocessing as mp, time
    path = sys.argv[1]; nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    d = json.load(open(path)); t0 = time.time()
    cert = setup(Cert(path))
    print(f"loaded: |A|={len(cert.Apolys)} nodes={len(cert.e)} s={float(cert.s):.6f} lambda={float(cert.lam):.9f}")
    print(f"s^2 I(nu) = {cert.Is2}   I(nu) = {cert.Is2/A(cert.s)**2}  ({time.time()-t0:.0f}s)")
    x_lo = Fr(d['x_lo']); x_hi = Fr(d['x_hi'])
    okL, vL = tail_left(cert, x_lo); print("left tail (0, x_lo]:", okL, vL)
    okR, gR, al = tail_right(cert, x_hi); print("right tail [x_hi, inf):", okR, gR, "alpha", al)
    # split [x_lo, x_hi] into chunks at nodes
    import numpy as _np
    allroots = [float(r.real) for qq, l in cert.active for r in _np.roots(qq) if abs(r.imag) < 1e-9]
    inner = [e for e in cert.e if x_lo < e < x_hi and min([abs(float(e) - r) for r in allroots] + [1.0]) > 1e-3]
    K = max(1, nproc*4); cuts = [x_lo] + [inner[int(i*len(inner)/K)] for i in range(1, K)] + [x_hi]
    cuts = sorted(set(cuts))
    _CERT = cert
    jobs = [(a_, b_) for a_, b_ in zip(cuts, cuts[1:])]
    with mp.get_context('fork').Pool(nproc) as pool:
        res = pool.map(_worker, jobs)
    okM = all(r[0] for r in res)
    nchecks = 0
    for r in res:
        for s_ in r[1]:
            if 'FAIL' in s_ or not r[0]: print("  ", s_)
            if 'interval checks' in s_: nchecks += int(s_.split(':')[1].split()[0])
    print(f"total interval checks: {nchecks}")
    print(f"main range [{float(x_lo)}, {float(x_hi)}] in {len(jobs)} chunks: {okM}  ({time.time()-t0:.0f}s)")
    verdict = okL and okR and okM
    print("VERDICT:", "C_86 >=", d['lambda'], "=", float(cert.lam), "VERIFIED" if verdict else "NOT VERIFIED")
    sys.exit(0 if verdict else 1)
