#!/bin/bash
# Rerun the A15 lower-bound checks and controls: both programs on the certificate and on each perturbed copy in negs/
# (made by make_neg.py from the certificate in the current directory). Usage: run_controls.sh CHECK86 NPROC
# Each run writes logs/<name>.<program>.log; the verdict is the last VERDICT line (exit status 0 iff VERIFIED).
C=$1; NP=$2; CERT=cert_A15_1802203_d1747e6a.json
mkdir -p logs
python3 -I -B $C $CERT $NP > logs/base.check86v3.log 2>&1
python3 -I -B indep86.py $CERT $NP > logs/base.indep86v4.log 2>&1
for n in lam_p1e-6 lam_p2e-6 lam_p2.5e-6 lam_p3e-6 lam_p1e-5 drop_ms10a drop_ms10b drop_ms10c drop_ms10all drop_xm1 drop_q3 \
         drop_quint7 drop_quint11 ms10b_coef5 lamx_p1pct lamms10a_p10pct rho_x1001 rho_max_p10 x_hi_6; do
  python3 -I -B $C negs/$n.json $NP > logs/$n.check86v3.log 2>&1
  python3 -I -B indep86.py negs/$n.json $NP > logs/$n.indep86v4.log 2>&1
done
