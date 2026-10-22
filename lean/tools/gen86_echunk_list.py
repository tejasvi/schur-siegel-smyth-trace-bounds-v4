#!/usr/bin/env python3
"""Write scratch/echunks.txt, the energy chunks for `t86k irows`: one line `i a m` per piece of row i (records with
nonzero weight only) over the records a .. a+m-1, covering i+1 .. NREC-1 in pieces of at most 200 records. Reads the
record signs from T86K/ELits.lean. Paths are relative to the project root (the parent of tools/).
usage: python3 -I gen86_echunk_list.py"""
import os, re
H = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
M = 200
s = open(f'{H}/T86K/ELits.lean').read()
i0 = s.index('def recsILit'); j0 = s.index(']', s.index('[', i0))
sg = [int(r.strip('()')) for r in re.findall(r'⟨\d+, (\(?-?\d+\)?), \(?-?\d+\)?, \(?-?\d+\)?⟩', s[i0:j0 + 1])]
NREC = len(sg)
n = 0
with open(f'{H}/scratch/echunks.txt', 'w') as f:
    for i in range(NREC):
        if sg[i] == 0:
            continue
        for a in range(i + 1, NREC, M):
            f.write(f'{i} {a} {min(M, NREC - a)}\n'); n += 1
print(NREC, 'records,', sum(1 for x in sg if x != 0), 'nonzero rows,', n, 'chunks')
