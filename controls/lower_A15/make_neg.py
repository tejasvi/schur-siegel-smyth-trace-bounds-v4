#!/usr/bin/env python3
"""Perturbed copies of the frozen A15 lower certificate (d1747e6a) for the negative tests: negs/<name>.json.
Exact rational edits of one field each; the frozen file is only read."""
import json, sys
from fractions import Fraction as Fr

SRC = "cert_A15_1802203_d1747e6a.json"
c0 = json.load(open(SRC))
lam = Fr(c0["lambda"])


def out(name, **edit):
    c = json.loads(json.dumps(c0))
    for k, v in edit.items():
        c[k] = v
    with open(f"negs/{name}.json", "w") as f:
        json.dump(c, f)
    print(name, {k: (v if not isinstance(v, list) else f"list[{len(v)}]") for k, v in edit.items()})


def lamq(i, factor):
    l = list(c0["lamQ"]); l[i] = str(Fr(l[i]) * factor); return l


for d, tag in ((Fr(1, 10**6), "1e-6"), (Fr(2, 10**6), "2e-6"), (Fr(25, 10**7), "2.5e-6"), (Fr(3, 10**6), "3e-6"),
               (Fr(1, 10**5), "1e-5")):
    out(f"lam_p{tag}", **{"lambda": str(lam + d)})
A = c0["A"]
assert A[0] == [1, 0] and A[1] == [1, -1] and A[3] == [1, -3, 1] and A[7] == [1, -9, 28, -35, 15, -1] \
    and A[11] == [1, -9, 27, -31, 12, -1] and A[10] == [1, -6, 9, -1] and Fr(c0["lamQ"][10]) == 0
assert [len(A[i]) for i in (12, 13, 14)] == [11, 11, 11] and all(A[i][1] == -18 for i in (12, 13, 14))
out("drop_xm1", lamQ=lamq(1, 0))
out("drop_q3", lamQ=lamq(3, 0))
out("drop_quint7", lamQ=lamq(7, 0))
out("drop_quint11", lamQ=lamq(11, 0))
for i, t in ((12, "a"), (13, "b"), (14, "c")):
    out(f"drop_ms10{t}", lamQ=lamq(i, 0))
out("drop_ms10all", lamQ=[x if i < 12 else "0" for i, x in enumerate(c0["lamQ"])])
a2 = json.loads(json.dumps(A)); a2[13][5] += 1      # MS10b with its x^5 coefficient changed by one
out("ms10b_coef5", A=a2)
out("lamx_p1pct", lamQ=lamq(0, Fr(101, 100)))
out("lamms10a_p10pct", lamQ=lamq(12, Fr(11, 10)))
out("rho_x1001", rho=[str(Fr(r) * Fr(1001, 1000)) for r in c0["rho"]])
imax = max(range(len(c0["rho"])), key=lambda i: Fr(c0["rho"][i]))
r = list(c0["rho"]); r[imax] = str(Fr(r[imax]) * Fr(11, 10))
out("rho_max_p10", rho=r)
out("x_hi_6", x_hi="6")
print("largest rho index", imax, c0["rho"][imax], file=sys.stderr)
