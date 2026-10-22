#!/usr/bin/env python3
"""Write T86UCore/Lits.lean from the output of the native helper `t86uk` (the upper checker context as a Lean literal;
the kernel checks `mkCtx = ctxULit` in T86UK/Lits.lean). Paths are relative to the project root.
usage: python3 -I gen86u_ctxlit.py CTX_OUT"""
import os, sys
H = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
body = open(sys.argv[1]).read()
assert body.startswith('def ctxULit : Ctx where')
open(f'{H}/T86UCore/Lits.lean', 'w').write(
    'import T86UCore.Check\n\n'
    '/-! The upper checker context `mkCtx` as a literal (printed by the native helper `t86uk`, Bench/T86UK.lean). The\n'
    'kernel checks `mkCtx = ctxULit` in `T86UK.Lits`, so the literal is not trusted. -/\n\n'
    'set_option maxRecDepth 200000\n\nnamespace T86UCore\n\n' + body + '\nend T86UCore\n')
print('ok', len(body))
