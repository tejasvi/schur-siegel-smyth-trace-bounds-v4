# Export a hat upper-bound LP solution (ub_hat.py .npy) to a rational certificate for ubcheck/check86ub.py.
# usage: export_ub.py SOL.npy A.json EPS OUT.json      (eps rational string, e.g. 1/100000)
import sys, json
import numpy as np
from fractions import Fraction as Fr
src, Afile, eps, out = sys.argv[1], sys.argv[2], Fr(sys.argv[3]), sys.argv[4]
A = json.load(open(Afile)); v = np.load(src)
val = v[0]; ne = int(v[1]); k = int(v[2]); assert k == len(A)
e = v[3:3+ne]; w = v[3+ne:3+ne+ne-2]; bq = v[3+ne+ne-2:]
assert len(bq) == k
nodes = [Fr(repr(float(x))).limit_denominator(10**12) for x in e]
assert all(nodes[i] < nodes[i+1] for i in range(len(nodes)-1)) and nodes[0] >= 0 and nodes[-1] <= 6
wr = [Fr(int(round(max(x, 0.0)*2**50)), 2**50) for x in w]
S = sum(wr); wr = [x/S for x in wr]
br = [Fr(int(max(x, 0.0)*2**44), 2**44) for x in bq]          # rounded down
keep = [i for i in range(k) if br[i] > 0]
cert = {"A": [A[i] for i in keep], "b": [str(br[i]) for i in keep], "nodes": [str(x) for x in nodes],
        "w": [str(x) for x in wr], "eps": str(eps)}
json.dump(cert, open(out, 'w'))
tr = (1 - eps)*sum(wr[j-1]*(nodes[j-1] + nodes[j] + nodes[j+1])/3 for j in range(1, ne-1)) + 3*eps
print(f"exported: LP value {val:.9f}, trace of mixture {float(tr):.9f}, {len(keep)} polynomials with b > 0, {sum(1 for x in wr if x > 0)} hats > 0")
