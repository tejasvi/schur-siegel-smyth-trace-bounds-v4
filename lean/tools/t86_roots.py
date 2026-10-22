"""Real roots of the active polynomials of the 86a lower-bound certificate in (x_lo, x_hi), refined by exact bisection
on integer sign changes to brackets [X0, X1]/D with D = 10^12 2^K (K = 60). Untrusted hints for the window leaves (the
Lean checker verifies the windows and the root-freeness of every chord leaf).
Adapted from the companion roots tool (DEC 10^12, range from the certificate, zero-weight polynomials dropped).
usage: python3 -I t86_roots.py CERT OUT.json"""
import json, sys
from fractions import Fraction as Fr
import flint
cert = json.load(open(sys.argv[1]))
polys = [q for q, c in zip(cert['A'], cert['lamQ']) if Fr(c) != 0]
XLO, XHI = Fr(cert['x_lo']), Fr(cert['x_hi'])
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
            if not (XLO < x < XHI): continue
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
