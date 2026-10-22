# Exact utilities for integer polynomials (coefficients highest-first): Sturm counts, factorization via flint.
from fractions import Fraction
import flint
def _rem(a, b):
    a = list(a)
    while len(a) >= len(b) and any(a):
        if a[0] == 0: a.pop(0); continue
        f = a[0]/b[0]
        for i in range(len(b)): a[i] -= f*b[i]
        a.pop(0)
    while a and a[0] == 0: a.pop(0)
    return a
def sturm(q):
    p0 = [Fraction(c) for c in q]; n = len(q) - 1
    p1 = [Fraction(c*(n - i)) for i, c in enumerate(q[:-1])]
    seq = [p0, p1]
    while True:
        r = _rem(seq[-2], seq[-1])
        if not r: break
        seq.append([-c for c in r])
    return seq
def _ev(p, x):
    v = Fraction(0)
    for c in p: v = v*x + c
    return v
def _sgnchanges(vals):
    s = [v for v in vals if v != 0]
    return sum(1 for a, b in zip(s, s[1:]) if (a > 0) != (b > 0))
def count_real_roots(q, lo=None, hi=None):
    # number of distinct real roots in (lo, hi] (None = infinity); uses leading-coefficient signs at +-inf
    seq = sturm(q)
    def at(x):
        if x is None: return None
        return _sgnchanges([_ev(p, Fraction(x)) for p in seq])
    def at_inf(sign):
        vals = []
        for p in seq:
            d = len(p) - 1; vals.append(p[0]*(sign**d))
        return _sgnchanges(vals)
    vlo = at_inf(-1) if lo is None else at(lo)
    vhi = at_inf(1) if hi is None else at(hi)
    return vlo - vhi
def factors(q):
    c, fl = flint.fmpz_poly(q[::-1]).factor()
    return int(c), [([int(t) for t in reversed(f.coeffs())], e) for f, e in fl]
def is_tp_irreducible(q, hi=6):
    # irreducible over Z (content 1), all roots real, distinct and in (0, hi)
    c, fl = factors(q)
    if abs(c) != 1 or len(fl) != 1 or fl[0][1] != 1: return False
    d = len(q) - 1
    return count_real_roots(q, 0, hi) == d and count_real_roots(q) == d
