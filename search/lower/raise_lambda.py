# Raise the lambda of a check86 certificate by an exact rational amount (used once: the L3 certificate is the
# exported certificate with margin 2.6e-6 plus 15/10^7, i.e. margin 1.1e-6 below the LP value).
# usage: raise_lambda.py IN.json NUMERATOR DENOMINATOR OUT.json
import sys, json
from fractions import Fraction as Fr
d = json.load(open(sys.argv[1])); d["lambda"] = str(Fr(d["lambda"]) + Fr(int(sys.argv[2]), int(sys.argv[3])))
json.dump(d, open(sys.argv[4], "w"))
print("lambda =", d["lambda"], "=", float(Fr(d["lambda"])))
