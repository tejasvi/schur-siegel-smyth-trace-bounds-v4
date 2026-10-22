"""Real roots of the polynomials of the 86a upper-bound certificate in (x_lo, 6], refined by exact bisection
on integer sign changes to brackets [X0, X1]/D with D = 10^12 2^K (K = 60). Untrusted hints for the window leaves (the
Lean checker verifies the windows and the root-freeness of every chord leaf).
Fork of tools/t86_roots.py.
usage: python3 -I t86u_roots.py CERT_UB OUT.json XLO"""
import json, sys
from fractions import Fraction as Fr
import flint
cert = json.load(open(sys.argv[1]))
polys = cert['A']
XLO, XHI = Fr(int(sys.argv[3]), 10**12), Fr(6)
DEC = 10**12; K = 60; D = DEC << K
def sgn(P, X):  # sign of D^d Q(X/D), P descending
    v = 0
    for m, a in enumerate(P):
        v = v * X + a * D**m
    return (v > 0) - (v < 0)
out = []
for j, P in enumerate(polys):
    f = flint.fmpz_poly(list(reversed(P)))
    for (fac, e) in f.factor()[1]:
        for r in fac.complex_roots():
            r = r[0] if isinstance(r, tuple) else r
            if not r.imag.contains(0): continue
            x = Fr(r.real.mid().str(40, radius=False))
            if not (XLO < x <= XHI): continue
            fP = list(reversed([int(c) for c in fac.coeffs()]))
            X = int(x * D); lo, hi = X - 2**50, X + 2**50
            while sgn(fP, lo) * sgn(fP, hi) > 0:
                lo -= 2**50; hi += 2**50
            while hi - lo > 2:
                mid = (lo + hi) // 2
                if sgn(fP, mid) == 0: lo, hi = mid - 1, mid + 1; break
                if sgn(fP, lo) * sgn(fP, mid) <= 0: hi = mid
                else: lo = mid
            out.append(dict(j=j, mult=e, X0=lo, X1=hi, K=K, approx=float(x)))
out.sort(key=lambda t: t['X0'])
json.dump(out, open(sys.argv[2], 'w'))
print(len(out), 'roots; first', out[0]['approx'], 'last', out[-1]['approx'], 'mults', sorted(set(t['mult'] for t in out)))
