#!/usr/bin/env python3
"""Modified copies of the improved upper certificate (d773f831) for Table 2: eps = 1e-6, eps = 1e-7, eps = 1e-14, all b x 1.001,
polynomial 2 (x - 1) dropped, polynomial 22 (x^3 - 6x^2 + 9x - 3) dropped. Usage: make_controls_ub2.py CERT OUTDIR"""
import json, sys, os, hashlib
from fractions import Fraction as Fr
src, out = sys.argv[1], sys.argv[2]
raw = open(src, 'rb').read()
assert hashlib.sha256(raw).hexdigest().startswith('d773f831')
base = json.loads(raw)
def save(name, c):
    p = os.path.join(out, name)
    assert not os.path.exists(p), p
    json.dump(c, open(p, 'w'))
    print(name, hashlib.sha256(open(p, 'rb').read()).hexdigest()[:16])
c = json.loads(raw); c['eps'] = '1/1000000'; save('ub2_eps_1e-6.json', c)
c = json.loads(raw); c['eps'] = '1/10000000'; save('ub2_eps_1e-7.json', c)
c = json.loads(raw); c['eps'] = '1/100000000000000'; save('ub2_eps_1e-14.json', c)
c = json.loads(raw); c['b'] = [str(Fr(x) * Fr(1001, 1000)) for x in c['b']]; save('ub2_b_x1.001.json', c)
for name, poly in (('ub2_drop_poly2.json', [1, -1]), ('ub2_drop_poly22.json', [1, -6, 9, -3])):
    c = json.loads(raw); i = c['A'].index(poly); del c['A'][i]; del c['b'][i]; save(name, c)
