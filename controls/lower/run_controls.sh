#!/bin/bash
# Rerun the L4 lower-bound checks and controls: both programs on the certificate, the variant and each perturbed copy in negs/
# (negs/ from make_neg.py, plus lam_p1.1e-6 and drop_cubic10). Usage: run_controls.sh CHECK86 NPROC
# Each run writes logs/<name>.<program>.log; the verdict is the last VERDICT line (exit status 0 iff VERIFIED).
C=$1; NP=$2; CERT=cert_L4_1802222_915a52c7.json; VAR=variant_cert_L4_1802221_4645ac71.json
mkdir -p logs
python3 -I -B $C $CERT $NP > logs/base.check86v4.log 2>&1
python3 -I -B indep86.py $CERT $NP > logs/base.indep86v5.log 2>&1
python3 -I -B $C $VAR $NP > logs/variant.check86v4.log 2>&1
python3 -I -B indep86.py $VAR $NP > logs/variant.indep86v5.log 2>&1
for n in lam_p5e-7 lam_p1e-6 lam_p1.1e-6 lam_p1.2e-6 lam_p2e-6 lam_p3e-6 lam_p1e-5 drop_ms10a drop_ms10b drop_ms10c drop_ms10all \
         drop_cubic10 drop_xm1 drop_q3 drop_quint7 drop_quint11 ms10b_coef5 lamx_p1pct lamms10a_p10pct rho_x1001 rho_max_p10 x_hi_6; do
  python3 -I -B $C negs/$n.json $NP > logs/$n.check86v4.log 2>&1
  python3 -I -B indep86.py negs/$n.json $NP > logs/$n.indep86v5.log 2>&1
done
