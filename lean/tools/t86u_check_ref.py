"""Exact integer reference implementation of the 86a UPPER-bound checker (T86UCore.Check), a fork of t86_check_ref.py:
records C'_i = -C_i/2 of U' = -U_mu0/2 (unit-mass hats, weights w = rho/WD), no main term, constant
c0 = eps log(3/2)/(1-eps) (field Islo; m0hi = 0), left tail (0, x0] by U_mu0(x) >= U_mu0(x0), condition (M) from root
brackets, (S) budget, (T) trace; tiling of [x0, 6] into chord intervals and root windows. Not part of any proof: the
Lean checker re-verifies everything.
usage: python3 t86u_check_ref.py CERT_UB.json OUT_leaves.json workers ROOTS.json XLO [KM]   (SKIP_MOMENTS=1: no (M))
       python3 t86u_check_ref.py --moments CERT_UB.json XLO OUT_moments.json KM   (needs python-flint)"""
import os, sys, json, math
from fractions import Fraction as Fr
_here = os.path.dirname(os.path.abspath(__file__))
_src = open(os.path.join(_here, 't86_check_ref.py')).read().replace("if __name__ == '__main__':\n    main()", '')
exec(compile(_src, 't86_check_ref.py', 'exec'))

class CertU:
    def __init__(self, path, XLO):
        c = json.load(open(path))
        self.polys = c['A']
        self.cw = [Fr(x) for x in c['b']]
        assert self.polys[0] == [1, 0] and all(x > 0 for x in self.cw)
        nodes = [Fr(x) for x in c['nodes']]
        self.n = [int(x * DEC) for x in nodes]
        w = [Fr(x) for x in c['w']]
        WD = 1
        for x in w: WD = WD * x.denominator // math.gcd(WD, x.denominator)
        self.WD = WD
        self.r = [int(x * WD) for x in w]
        self.eps = Fr(c['eps'])
        self.xlo, self.xhi = Fr(XLO, DEC), Fr(6)
        self.N = len(self.n) - 1
        N = self.N
        Cq = [Fr(0)] * (N + 1)
        for k in range(1, N):
            rr = Fr(self.r[k - 1], WD)
            if rr == 0: continue
            wl = Fr(self.n[k] - self.n[k - 1], DEC); wr = Fr(self.n[k + 1] - self.n[k], DEC); sc = 2 / (wl + wr)
            Cq[k - 1] += rr * sc / wl; Cq[k] -= rr * sc * (1 / wl + 1 / wr); Cq[k + 1] += rr * sc / wr
        assert sum(Cq) == 0
        Cq = [-x / 2 for x in Cq]          # C' = -C/2
        self.C = []
        for i in range(N + 1):
            num, den = Cq[i].numerator, Cq[i].denominator
            self.C.append((num, den, fdiv(num << QS, den), cdiv(num << QS, den)))
        self.m0hi = 0
        self.cw_num = [x.numerator for x in self.cw]; self.cw_sh = [x.denominator.bit_length() - 1 for x in self.cw]
        self.deg = [len(q) - 1 for q in self.polys]
        self.sumabsC = sum(max(abs(t[2]), abs(t[3])) for t in self.C)

def c0lo(cert):
    L32 = logK(3, 2)
    return fdiv(cert.eps.numerator * L32[0], cert.eps.denominator - cert.eps.numerator)

def mk_ctx(cert):
    ctx = Ctx.__new__(Ctx)
    ctx.c = cert
    ctx.Islo = c0lo(cert)
    return ctx

Ctx.logplus_lo = lambda self, X, D: 0     # no main term

def left_tail_lb_u(ctx, X0, k):
    """(0, x0]: F >= c0 - b_0 log x0 - sum_{j>=1} b_j log B_j - 2 U'(x0) (U_mu0 decreasing left of the support)"""
    c = ctx.c
    D = DEC << k
    LD = logK(D, 1)
    r = ctx.node_pass(X0, X0, k)
    part = 0
    for j, coef in enumerate(c.polys):
        if j == 0:
            part += fdiv(-c.cw_num[0] * logK(X0, D)[1], 1 << c.cw_sh[0])
        else:
            beta = poly_taylor(coef, 0, D); d = len(beta) - 1
            R0 = encl1(beta, X0); B = max(abs(R0[0]), abs(R0[1]))
            part += fdiv(-c.cw_num[j] * (logK(B, 1)[1] - d * LD[0]), 1 << c.cw_sh[j])
    assert 0 < X0 <= D
    assert all(rr == 0 or X0 <= c.n[j] << k for j, rr in enumerate(c.r))   # leftTailPre
    return ctx.Islo - c.m0hi + part - 2 * ctx.U_hi(r['Sp'], D)

def poly_val(q, X, D):   # D^d Q(X/D)
    v = 0
    for m, a in enumerate(q):
        v = v * X + a * D ** m
    return v

def brackets(q, k):
    """all roots of q (all real in [0, 6]): brackets (l, u) at scale D = DEC 2^k, sign change or exact root"""
    import flint
    D = DEC << k
    f = flint.fmpz_poly(list(reversed(q)))
    out = []
    for r in f.complex_roots():
        r = r[0] if isinstance(r, tuple) else r
        assert r.imag.contains(0), 'complex root'
        x = Fr(r.real.mid().str(60, radius=False))
        X = int(x * D)
        for cand in (X - 1, X, X + 1):
            if poly_val(q, cand, D) == 0:
                out.append((cand, cand)); break
        else:
            lo, hi = X - 2 ** 20, X + 2 ** 20
            while poly_val(q, lo, D) * poly_val(q, hi, D) > 0:
                lo -= 2 ** 20; hi += 2 ** 20
            while hi - lo > 1:
                mid = (lo + hi) // 2
                v = poly_val(q, mid, D)
                if v == 0: lo = hi = mid; break
                if poly_val(q, lo, D) * v < 0: hi = mid
                else: lo = mid
            out.append((lo, hi))
    out.sort()
    assert len(out) == len(q) - 1 and all(a[1] < b[0] for a, b in zip(out, out[1:]))
    assert all(0 <= b[0] and b[1] <= 6 * D for b in out)
    return out

def moment_lb(ctx, k, bs):
    c = ctx.c
    D = DEC << k
    acc = 0
    for (l, u) in bs:
        r = ctx.node_pass(l, l, k)
        dU = cdiv((47 * c.sumabsC * (u - l)) << P, D << QS)
        acc += ctx.Islo - c.m0hi - 2 * (ctx.U_hi(r['Sp'], D) + dU)
    return acc

def moments(ctx, KM):
    out = []
    for j, q in enumerate(ctx.c.polys):
        bs = brackets(q, KM)
        m = moment_lb(ctx, KM, bs)
        out.append(dict(j=j, k=KM, bs=bs, lb=m))
        print('moment', j, 'deg', len(q) - 1, 'lb', m / 2 ** P, flush=True)
    return out

def main():
    if sys.argv[1] == '--moments':   # usage: --moments CERT_UB XLO OUT.json KM  (needs python-flint)
        cert = CertU(sys.argv[2], int(sys.argv[3])); ctx = mk_ctx(cert)
        json.dump(moments(ctx, int(sys.argv[5])), open(sys.argv[4], 'w'))
        return
    import multiprocessing as mp, time
    cert = CertU(sys.argv[1], int(sys.argv[5])); out = sys.argv[2]
    workers = int(sys.argv[3]); roots = json.load(open(sys.argv[4]))
    KM = int(sys.argv[6]) if len(sys.argv) > 6 else 80
    ctx = mk_ctx(cert)
    # (S), (T)
    beta = sum(b * d for b, d in zip(cert.cw, cert.deg))
    print('budget beta', float(beta), beta < 1, ' c0lo', ctx.Islo / 2 ** P, flush=True)
    lt = left_tail_lb_u(ctx, int(cert.xlo * DEC), 0)
    print('left tail lb on (0,', float(cert.xlo), ']', lt / 2 ** P, flush=True)
    moms = []
    if os.environ.get('SKIP_MOMENTS') != '1':
        moms = moments(ctx, KM)
    ivs, wins = make_breaks(cert, roots)
    print('windows', len(wins), 'initial chord intervals', len(ivs), flush=True)
    t0 = time.time()
    with mp.Pool(workers) as pool:
        res = pool.map(check_interval, [(ctx, a, b, 70) for a, b in ivs], chunksize=1)
    leaves = [l for r in res for l in r[0]]; fails = [f for r in res for f in r[1]]
    print('chord leaves', len(leaves), 'fails', len(fails), 'min lb', min(l['lb'] for l in leaves) / 2 ** P,
          f'{time.time() - t0:.0f}s', flush=True)
    wl = []
    for u, v, k in wins:
        lb = ctx.window_leaf(u, v, k)
        wl.append(dict(Xu=u, Xv=v, k=k, lb=lb))
    print('windows min lb', min(w['lb'] for w in wl) / 2 ** P, 'bad', sum(w['lb'] <= 0 for w in wl), flush=True)
    json.dump(dict(chord=leaves, windows=wl, fails=fails, xhi=int(cert.xhi * DEC), lt=lt, moments=moms), open(out, 'w'))

if __name__ == '__main__':
    main()
