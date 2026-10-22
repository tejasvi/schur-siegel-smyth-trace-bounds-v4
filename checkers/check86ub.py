"""Checker for an UPPER bound on the Schur-Siegel-Smyth trace constant C_86 (Lemma 3.1 of the paper; "Lemma U1" below).

Certificate (JSON): A = list of integer polynomials (coefficients, highest degree first), b = nonnegative rationals
(one per polynomial), nodes = increasing rationals 0 <= e_0 < ... < e_N <= 6, w = nonnegative rationals (N-1 values,
sum exactly 1; weight of the hat on [e_{k-1}, e_{k+1}] normalized to mass 1), eps = rational in (0,1).
Measure: mu = (1-eps) mu_0 + eps omega, mu_0 = sum_k w_k h_k (piecewise-linear density), omega = equilibrium
(arcsine) measure of [0,6] (U_omega = log(3/2) on [0,6], U_omega >= log(3/2) on C, int x domega = 3).
Weights: b'_Q = (1-eps) b_Q.
Verified:
  (S) every Q in A is primitive, irreducible over Z, has only real roots (Sturm), A has no duplicates;
      beta = sum_Q b'_Q deg Q < 1 (exact).
  (M) int log|Q| dmu >= (1-eps)(log|lc Q| + sum_rho U_mu0(rho)) + eps (log|lc Q| + deg Q log(3/2)) > 0 for Q in A
      (rho over the real roots, rigorous brackets).
  (P) h(x) = (1-eps) U_mu0(x) + eps log(3/2) - sum_Q b'_Q log|Q(x)| >= 0 for all x in [0,6] = supp mu.
Then Lemma U1 gives C_86 <= int x dmu = (1-eps) sum_k w_k (e_{k-1}+e_k+e_{k+1})/3 + 3 eps (exact rational).
Formulas: g = sum_k w_k h_k has g'' = sum_i C_i delta_{e_i}; U_mu0(x) = int log|x-y| g(y) dy = sum_i C_i H(e_i - x),
H(t) = t^2/2 log|t| - 3t^2/4 (H'' = log|t|); U_mu0'' = sum_i C_i log|e_i - x|.
Pointwise bound on [p,q] (no node inside, no root of an active Q): h >= min(h(p),h(q)) - (q-p)/4 * int_p^q (h'')_+.
Usage: check86ub.py CERT.json NPROC      (exit status 0 iff VERIFIED)
"""
import json, sys
from fractions import Fraction as Fr
from flint import arb, ctx, fmpz_poly
ctx.prec = 96
if not __debug__: raise SystemExit("refusing to run with assertions disabled")
class CheckError(Exception): pass
def require(cond, msg):
    if not cond: raise CheckError(msg)
def A(fr): return arb(fr.numerator)/arb(fr.denominator)
def logabs(t): return abs(t).log()
def Hf(t):
    if t.is_zero(): return arb(0)
    if t.contains(0):
        r = abs(t).upper()
        require(r < arb('0.6'), "ball too wide around a node")
        B = r*r*((1/r).log()/2 + arb(3)/4)
        return arb(0).union(B).union(-B)
    return t*t/2*logabs(t) - arb(3)/4*t*t
def polyval(c, x):
    v = arb(0)
    for a in c: v = v*x + a
    return v
def polyder(c):
    d = len(c) - 1; return [c[i]*(d - i) for i in range(d)]
def taylor_coeffs(c, m):
    # coefficients a_k of Q(m + t) = sum_k a_k t^k (exact), c integers highest first, m Fraction
    a = [Fr(x) for x in c]; n = len(a) - 1; out = []
    for k in range(n + 1):
        # synthetic division by (x - m): remainder = current value at m
        b = [a[0]]
        for x in a[1:]: b.append(b[-1]*m + x)
        out.append(b[-1]); a = b[:-1]
        if not a: break
    return out   # a_0, a_1, ..., a_n
def taylor_ball(c, p, q):
    # arb enclosures of Q, Q', Q'' over [p, q]
    m = (p + q)/2; r = (q - p)/2; a = taylor_coeffs(c, m); n = len(a) - 1
    def enc(coefs):   # coefs[k] multiplies t^k
        tail = sum(abs(coefs[k])*r**k for k in range(1, len(coefs)))
        return A(coefs[0]) + arb(0, 1)*A(tail) if len(coefs) > 1 else A(coefs[0])
    Q0 = enc(a)
    Q1 = enc([k*a[k] for k in range(1, n + 1)]) if n >= 1 else arb(0)
    Q2 = enc([k*(k-1)*a[k] for k in range(2, n + 1)]) if n >= 2 else arb(0)
    return Q0, Q1, Q2
def ev_fr(p, x):
    v = Fr(0)
    for c in p: v = v*x + c
    return v
def sturm_seq(q):
    def prem(a, b):
        a = a[:]
        while len(a) >= len(b) and any(a):
            f = a[0]/b[0]
            for i in range(len(b)): a[i] -= f*b[i]
            a.pop(0)
        while a and a[0] == 0: a.pop(0)
        return a
    P0 = [Fr(c) for c in q]; P1 = [Fr(c)*(len(q)-1-i) for i, c in enumerate(q[:-1])]
    seq = [P0, P1]
    while True:
        r = prem(seq[-2], seq[-1])
        if not r: break
        seq.append([-c for c in r])
    return seq
def sturm_count(seq, lo, hi):   # distinct real roots in (lo, hi]; lo/hi Fractions or None for -inf/+inf
    def V(x, sgn=None):
        if x is None:
            vals = [p[0]*(sgn**(len(p)-1)) for p in seq]
        else:
            vals = [ev_fr(p, x) for p in seq]
        vals = [v for v in vals if v != 0]
        return sum(1 for a, b in zip(vals, vals[1:]) if (a > 0) != (b > 0))
    return (V(lo) if lo is not None else V(None, -1)) - (V(hi) if hi is not None else V(None, 1))
def root_brackets(q, lo, hi):
    # disjoint rational brackets (a, b) with q(a) q(b) < 0, one per real root of q in (lo, hi); verified count (Sturm)
    import numpy as np
    seq = sturm_seq(q); cnt = sturm_count(seq, lo, hi)
    P0 = [Fr(c) for c in q]
    guesses = sorted(set(float(r.real) for r in np.roots(q) if abs(r.imag) < 1e-7 and float(lo) < r.real < float(hi)))
    br = []
    for g in guesses:
        for dlt in [1e-13, 1e-11, 1e-9, 1e-7]:
            a_ = Fr(g) - Fr(dlt); b_ = Fr(g) + Fr(dlt)
            if lo < a_ and b_ < hi and ev_fr(P0, a_)*ev_fr(P0, b_) < 0: br.append((a_, b_)); break
        else:
            raise CheckError(f"could not bracket root {g} of {q}")
    require(len(br) == cnt, f"root isolation mismatch for {q}: Sturm {cnt}, brackets {len(br)}")
    require(all(br[i][1] < br[i+1][0] for i in range(len(br)-1)), "brackets not disjoint")
    tight = []
    for a_, b_ in br:
        fa = ev_fr(P0, a_)
        while b_ - a_ > Fr(1, 2**110):
            m = (a_ + b_)/2; fm = ev_fr(P0, m)
            if fm == 0: a_ = b_ = m; break
            if (fm > 0) == (fa > 0): a_, fa = m, fm
            else: b_ = m
        tight.append((a_, b_))
    return tight
class Cert:
    def __init__(self, path):
        d = json.load(open(path))
        self.Apolys = [list(map(int, q)) for q in d['A']]
        self.b = [Fr(x) for x in d['b']]
        self.e = [Fr(x) for x in d['nodes']]
        self.w = [Fr(x) for x in d['w']]
        self.eps = Fr(d['eps'])
        require(0 < self.eps < 1, "eps must be in (0,1)")
        require(len(self.b) == len(self.Apolys) and len(self.w) == len(self.e) - 2, "length mismatch")
        require(all(x >= 0 for x in self.b) and all(x >= 0 for x in self.w), "negative weight")
        require(sum(self.w) == 1, "mass of mu_0 must be exactly 1")
        require(all(self.e[i] < self.e[i+1] for i in range(len(self.e)-1)), "nodes not increasing")
        require(self.e[0] >= 0 and self.e[-1] <= 6, "nodes must lie in [0,6]")
        require(len(set(tuple(q) for q in self.Apolys)) == len(self.Apolys), "duplicate polynomial")
        for q in self.Apolys:
            require(len(q) >= 2 and q[0] != 0, f"bad polynomial {q}")
            c, fac = fmpz_poly(q[::-1]).factor()
            require(abs(int(c)) == 1 and len(fac) == 1 and fac[0][1] == 1 and fac[0][0].degree() == len(q) - 1,
                    f"not primitive irreducible: {q}")
            require(sturm_count(sturm_seq(q), None, None) == len(q) - 1, f"not real-rooted: {q}")
        self.bp = [(1 - self.eps)*x for x in self.b]
        self.beta = sum(x*(len(q) - 1) for x, q in zip(self.bp, self.Apolys))
        require(self.beta < 1, "sum b' deg Q must be < 1")
        N = len(self.e) - 1; C = [Fr(0)]*(N+1)
        for k in range(1, N):
            wl = self.e[k] - self.e[k-1]; wr = self.e[k+1] - self.e[k]; sc = 2/(wl + wr)
            r = self.w[k-1]
            if r == 0: continue
            C[k-1] += r*sc/wl; C[k] -= r*sc*(1/wl + 1/wr); C[k+1] += r*sc/wr
        require(sum(C) == 0 and sum(C[i]*self.e[i] for i in range(N+1)) == 0, "g'' moments")
        self.C = C; self.Ca = [A(c) for c in C]; self.ea = [A(x) for x in self.e]
        self.nz = [i for i in range(N+1) if C[i] != 0]
        self.trace = (1 - self.eps)*sum(self.w[k-1]*(self.e[k-1] + self.e[k] + self.e[k+1])/3 for k in range(1, N)) + 3*self.eps
        self.L15 = (arb(3)/2).log()
        self.active = [(q, A(x)) for q, x in zip(self.Apolys, self.bp) if x != 0]
        self.oe = A(1 - self.eps); self.const = A(self.eps)*self.L15
    def U(self, x):          # x arb ball
        v = arb(0)
        for i in self.nz: v += self.Ca[i]*Hf(self.ea[i] - x)
        return v
    def U_exact(self, xf):   # xf Fraction
        v = arb(0)
        for i in self.nz:
            t = self.e[i] - xf
            if t != 0: v += self.Ca[i]*Hf(A(t))
        return v
def moments(cert, log=print):
    ok = True
    for q, bq in zip(cert.Apolys, cert.b):
        tot = arb(0)
        for a_, b_ in root_brackets(q, Fr(-10**6), Fr(10**6)):
            X = (A(a_) + A(b_))/2; X = X.union(A(a_)).union(A(b_))
            tot += cert.U(X)
        lc = arb(abs(q[0])).log()
        M = cert.oe*(lc + tot) + A(cert.eps)*(lc + (len(q) - 1)*cert.L15)
        log(f"  int log|Q| dmu >= {M.lower()}   (b = {float(bq):.3e})  Q = {q}")
        if not (M.lower() > 0): ok = False
    return ok
_HMEMO = {}
def h_exact(cert, xf):
    if xf in _HMEMO: return _HMEMO[xf]
    v = h_exact0(cert, xf); _HMEMO[xf] = v
    return v
def h_exact0(cert, xf):
    v = cert.oe*cert.U_exact(xf) + cert.const
    for q, l in cert.active:
        Qx = ev_fr([Fr(c) for c in q], xf)
        require(Qx != 0, "evaluation exactly at a root")
        v -= l*logabs(A(Qx))
    return v
def hpp_upper(cert, p, q):
    X = (A(p) + A(q))/2; X = X.union(A(p)).union(A(q))
    hw = q - p
    reg = arb(0); sing = arb(0)
    for qq, l in cert.active:
        Qv, Q1, Q2 = taylor_ball(qq, p, q)
        if Qv.contains(0): return arb('nan'), arb('nan')
        reg += l*(Q1*Q1 - Qv*Q2)/(Qv*Qv)
    m = (p + q)/2; ma = A(m); half = A(hw)/2
    Fm = arb(0); F1 = arb(0); F2 = arb(0)
    for i in cert.nz:
        ei = cert.e[i]; c = cert.C[i]
        if ei == p or ei == q:
            if c < 0:   # (1-eps) c log|e-x| = (1-eps)|c| log(1/|e-x|) >= 0: integral <= (1-eps)|c| h (1 + log(1/h)), h <= 1
                if hw > 1: return arb('nan'), arb('nan')
                hh = A(hw); sing += -cert.oe*cert.Ca[i]*hh*(1 + (1/hh).log())
            else:       # (1-eps) c log|e-x| <= (1-eps) c log h
                reg += cert.oe*cert.Ca[i]*A(hw).log()
            continue
        require(ei < p or ei > q, "node inside an interval")
        dist = (p - ei) if ei < p else (ei - q)          # distance from e_i to [p,q] (> 0)
        if dist <= 4*hw:   # near node: exact termwise supremum of c log|e - x| over [p,q]
            far_d = (q - ei) if ei < p else (ei - p)
            reg += cert.oe*cert.Ca[i]*(A(far_d).log() if c > 0 else A(dist).log())
        else:              # far node: Taylor at the midpoint, remainder via sum |c| / dist^2
            Fm += cert.Ca[i]*(abs(cert.ea[i] - ma)).log()
            F1 += cert.Ca[i]/(ma - cert.ea[i])
            F2 += abs(cert.Ca[i])/(A(dist)*A(dist))
    reg += cert.oe*(Fm + abs(F1)*half + F2*half*half/2)
    return reg, sing
def check_interval(cert, p, q):
    hp = h_exact(cert, p); hq = h_exact(cert, q)
    if not (hp.lower() > 0 and hq.lower() > 0): return False, (hp if not (hp.lower() > 0) else hq).lower()
    lo = hp.lower() if hp.lower() < hq.lower() else hq.lower()
    reg, sing = hpp_upper(cert, p, q)
    if not (reg.is_finite() and sing.is_finite()): return False, lo
    hw = A(q - p); regu = reg.upper()
    pen = hw/4*(hw*(regu if regu > 0 else arb(0)) + sing)
    return bool((arb(lo) - pen).lower() > 0), lo
def verify(cert, x_lo, x_hi, windows, max_depth=48, log=print):
    pts = set([x_lo, x_hi]) | set(e for e in cert.e if x_lo < e < x_hi)
    for L, R in windows:
        for t in (L, R):
            if x_lo < t < x_hi: pts.add(t)
    pts = sorted(pts)
    def in_window(p, q): return any(L <= p and q <= R for (L, R) in windows)
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
            log(f"FAIL on [{float(p):.12f},{float(q):.12f}] depth {dep} h-lower {float(lo):.3e}"); return False
        m = (p + q)/2; mm = Fr(round(m*2**44), 2**44)
        m = mm if p < mm < q else m
        stack += [(p, m, dep+1), (m, q, dep+1)]
    log(f"verified [{float(x_lo)},{float(x_hi)}]: {nchk} interval checks, min endpoint h-lower {float(minlo):.3e}")
    return True
def root_windows(cert, log=print):
    # around every root (in [0,6]) of an active polynomial: [r-d, r+d] cap [0,6] with h > 0 proven by the log blow-up
    wins = []
    for q, l in cert.active:
        for a_, b_ in root_brackets(q, Fr(-1, 10**9), Fr(6) + Fr(1, 10**9)):
            d = Fr(1, 10**4); ok = False
            while d >= Fr(1, 10**15):
                L = max(Fr(0), a_ - d); R = min(Fr(6), b_ + d)
                X = (A(L) + A(R))/2; X = X.union(A(L)).union(A(R))
                v = cert.oe*cert.U(X) + cert.const
                for qq, ll in cert.active:
                    v -= ll*arb(abs(taylor_ball(qq, L, R)[0]).upper()).log()
                if v.lower() > 0: ok = True; break
                d /= 10
            if not ok: log(f"FAIL window at root in [{float(a_)},{float(b_)}] of {q}"); return None
            wins.append((L, R))
    return wins
_CERT = None; _WIN = None
def _worker(args):
    p, q = args; out = []
    ok = verify(_CERT, p, q, _WIN, log=lambda s: out.append(s))
    return ok, out
if __name__ == '__main__':
    import multiprocessing as mp, time
    path = sys.argv[1]; nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    t0 = time.time()
    try:
        cert = Cert(path)
        print(f"loaded: |A|={len(cert.Apolys)} nodes={len(cert.e)} eps={cert.eps} beta={float(cert.beta):.6f}")
        okM = moments(cert)
        print("moments (M):", okM)
        wins = root_windows(cert)
        okW = wins is not None
        print(f"root windows: {okW} ({len(wins) if wins else 0})")
        okP = False
        if okW:
            inner = [e for e in cert.e if 0 < e < 6 and not any(L <= e <= R for L, R in wins)]
            K = max(1, nproc*6); cuts = sorted(set([Fr(0)] + [inner[int(i*len(inner)/K)] for i in range(1, K)] + [Fr(6)]))
            _CERT = cert; _WIN = wins
            jobs = list(zip(cuts, cuts[1:]))
            with mp.get_context('fork').Pool(nproc) as pool:
                res = pool.map(_worker, jobs)
            okP = all(r[0] for r in res); nchecks = 0
            for r in res:
                for s_ in r[1]:
                    if 'FAIL' in s_ or not r[0]: print("  ", s_)
                    if 'interval checks' in s_: nchecks += int(s_.split(':')[1].split()[0])
            print(f"pointwise (P) on [0,6]: {okP}; {nchecks} interval checks in {len(jobs)} chunks ({time.time()-t0:.0f}s)")
    except CheckError as ex:
        print("CHECK ERROR:", ex); okM = okW = okP = False; cert = None
    verdict = okM and okW and okP
    if cert is not None:
        print(f"trace of mu = {cert.trace.numerator}/{cert.trace.denominator} = {float(cert.trace):.12f}")
    print("VERDICT:", f"C_86 <= {float(cert.trace):.10f}" if cert is not None else "", "VERIFIED" if verdict else "NOT VERIFIED")
    sys.exit(0 if verdict else 1)
