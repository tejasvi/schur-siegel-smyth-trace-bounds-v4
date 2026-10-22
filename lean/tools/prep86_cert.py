#!/usr/bin/env python3
"""Prepare a lower-bound certificate for the Lean checker, whose nodes are integers at scale 10^12 with the first node
at 0 and the last at 29/5:
1. every node is rounded to the nearest multiple of 10^-12 (the order must be kept);
2. if the first node is positive, a node 0 is prepended, and if the last node is below 29/5, a node 29/5 is appended,
   each with a zero hat weight next to it. The padding does not change the measure (the density is zero outside the
   original support); the rounding perturbs it by at most half a grid step per node.
The polynomials, their weights, lambda, x_lo and x_hi are copied unchanged. The Lean checks verify the prepared
certificate itself, so the rounding needs no separate argument.
usage: python3 -I prep86_cert.py CERT_IN.json CERT_OUT.json"""
import json, sys
from fractions import Fraction as Fr
DEC = 10 ** 12
c = json.load(open(sys.argv[1]))
nodes = [Fr(x) for x in c['nodes']]
rho = [Fr(x) for x in c['rho']]
assert len(rho) == len(nodes) - 2 and all(a < b for a, b in zip(nodes, nodes[1:]))
def rnd(x):
    n = x * DEC
    q, r = divmod(n.numerator, n.denominator)
    return Fr(q + (1 if 2 * r >= n.denominator else 0), DEC)
rn = [rnd(x) for x in nodes]
err = max(abs(a - b) for a, b in zip(rn, nodes))
assert all(a < b for a, b in zip(rn, rn[1:])), 'rounding broke the order of the nodes'
assert rn[0] >= 0 and rn[-1] <= Fr(29, 5)
pre, post = rn[0] > 0, rn[-1] < Fr(29, 5)
if pre:
    rn = [Fr(0)] + rn; rho = [Fr(0)] + rho
if post:
    rn = rn + [Fr(29, 5)]; rho = rho + [Fr(0)]
assert len(rho) == len(rn) - 2
out = dict(c)
out['nodes'] = [str(x) for x in rn]
out['rho'] = [str(x) for x in rho]
json.dump(out, open(sys.argv[2], 'w'))
print(f'nodes {len(nodes)} -> {len(rn)} (prepended 0: {pre}, appended 29/5: {post}); max rounding error {float(err):.3e}; '
      f'min gap {float(min(b - a for a, b in zip(rn, rn[1:]))):.3e}')
