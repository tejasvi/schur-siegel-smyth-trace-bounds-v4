import os
# Export a hat-SOCP solution to a rational JSON certificate for checker/check86.py.
import numpy as np, sys, json
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
src, Afile, margin, out = sys.argv[1], sys.argv[2], float(sys.argv[3]), sys.argv[4]
A = json.load(open(Afile)); v = np.load(src)
lam = v[0]; ne = int(v[1]); nQ = len(A)
lQ = v[2:2+nQ]; e = v[2+nQ:2+nQ+ne]; rho = v[2+nQ+ne:]
assert len(rho) == ne - 2
def fr(x, bits=48): return Fr(int(round(max(x, 0.0)*2**bits)), 2**bits)
nodes = [Fr(repr(float(x))).limit_denominator(10**13) for x in e]
assert all(nodes[i] < nodes[i+1] for i in range(len(nodes)-1))
rho_r = [fr(x) for x in rho]
# drop tiny weights (below 1e-12 relative) to keep the certificate small
smax = max(rho_r); thr = Fr(sys.argv[5]) if len(sys.argv) > 5 else Fr(1, 10**12); rho_r = [r if r > smax*thr else Fr(0) for r in rho_r]
lQ_r = [fr(x) for x in lQ]
lam_c = Fr(lam - margin).limit_denominator(10**9)
lam_c = Fr(int(lam_c*10**9 - 1), 10**9) if lam_c > Fr(lam - margin) else lam_c   # ensure <= lam - margin
supp = [nodes[k] for k in range(1, ne-1) if rho_r[k-1] > 0]
x_lo = min(supp) - (nodes[1] - nodes[0])   # left of the support: first hat with weight starts one spacing earlier
x_lo = max(Fr(1, 10**6), min(x_lo, Fr(1, 100)))
x_hi = Fr(max(30, int(max(supp)) + 10))
cert = {"A": A, "lamQ": [str(x) for x in lQ_r], "nodes": [str(x) for x in nodes], "rho": [str(x) for x in rho_r],
        "lambda": str(lam_c), "x_lo": str(x_lo), "x_hi": str(x_hi)}
json.dump(cert, open(out, 'w'))
print(f"exported: lambda_num={lam:.9f} lambda_cert={float(lam_c):.9f} hats_nonzero={sum(1 for r in rho_r if r>0)} x_lo={float(x_lo)} x_hi={float(x_hi)}")
