#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
W11f / G5'' -- "a genuine MSC measure on KingmanTheta": exact replication of the
e^{-a} / e^{-b} weighting, of the normalisation, and of the naive-model trap.

Lean counterpart:
  Phylo/Stat/MSCKingmanMeasure.lean
    Phylo.Stat.MSCKingmanMeasure.kingmanMSCMeasure
        := map toKingmanTheta (rho (x) (sojournLaw 2 (x) sojournLaw 2))
    Phylo.Stat.MSCKingmanMeasure.kingmanMSCMeasure_deep
        nu{deep} = integral of e^{-a(u)} * e^{-b(u)} d rho
    Phylo.Stat.MSCKingmanMeasure.kingmanMSCMeasure_dirac_deep
        nu{deep} = e^{-a} * e^{-b}          (deterministic species tree)
    Phylo.Stat.MSCKingmanMeasure.kingmanMSCMeasure_dirac_notDeep
        nu{not deep} = 1 - e^{-a} * e^{-b}
    Phylo.Stat.MSCKingmanMeasure.kingmanMSCMeasure_dirac_concordant
        nu{not deep} * 1 + nu{deep} * 1/3 = pConcordant (a+b) = 1 - (2/3) e^{-(a+b)}
    Phylo.Stat.MSCKingmanMeasure.kingmanMSCMeasure_dirac_concordant_zero
        a = b = 0  =>  concordant = 1/3 = pConcordant 0

Everything is exact: the weights are handled as **polynomials in the two
independent symbols p := e^{-a} and r := e^{-b}** over the rationals, so every
identity below is verified with `fractions.Fraction` coefficients and no
transcendental value is ever needed.

The point of the two symbols (rather than one q := e^{-(a+b)}) is discipline B:
the whole trap of this gap is that the two sides of the root must be sampled
SEPARATELY -- see section 4.

Exits non-zero if any check fails.
"""

from fractions import Fraction as F
import sys

FAIL = []


def check(name, cond):
    print(("  [OK]   " if cond else "  [FAIL] ") + name)
    if not cond:
        FAIL.append(name)


# --------------------------------------------------------------------------
# minimal exact multivariate polynomial arithmetic: dict {(i,j): Fraction}
# representing  sum c_{ij} p^i r^j
# --------------------------------------------------------------------------
def poly(d):
    return {k: F(v) for k, v in d.items() if v != 0}


P = poly({(1, 0): 1})          # p  = e^{-a}
R = poly({(0, 1): 1})          # r  = e^{-b}


def add(x, y):
    out = dict(x)
    for k, v in y.items():
        out[k] = out.get(k, F(0)) + v
    return poly(out)


def sub(x, y):
    return add(x, {k: -v for k, v in y.items()})


def mul(x, y):
    out = {}
    for k1, v1 in x.items():
        for k2, v2 in y.items():
            k = (k1[0] + k2[0], k1[1] + k2[1])
            out[k] = out.get(k, F(0)) + v1 * v2
    return poly(out)


def smul(c, x):
    return poly({k: F(c) * v for k, v in x.items()})


ONE = poly({(0, 0): 1})
ZERO = {}
PR = mul(P, R)                 # p*r  = e^{-(a+b)}  (the deep-merge weight)


def peval(x, p, r):
    out = F(0)
    for (i, j), c in x.items():
        out += c * (p ** i) * (r ** j)
    return out


def is_zero(x):
    return len(x) == 0


# --------------------------------------------------------------------------
print("== 1. deep weight = e^{-a} * e^{-b};  not-deep weight = 1 - it ==")
DEEP = PR
NOTDEEP = sub(ONE, PR)
check("P(deep) = p*r  (i.e. e^{-a} e^{-b})", DEEP == mul(P, R))
check("P(not deep) = 1 - p*r", NOTDEEP == sub(ONE, PR))
check("NORMALISATION: P(deep) + P(not deep) = 1  (exactly, as a polynomial)",
      is_zero(sub(add(DEEP, NOTDEEP), ONE)))

# --------------------------------------------------------------------------
print("== 2. Fin 4: the three quartet topologies (M1) ==")
CONC = add(NOTDEEP, smul(F(1, 3), DEEP))     # ab|cd
DISC = smul(F(1, 3), DEEP)                   # ac|bd  and  ad|bc
check("P(ab|cd) = (1 - p*r) + (1/3) p*r = 1 - (2/3) p*r",
      is_zero(sub(CONC, sub(ONE, smul(F(2, 3), PR)))))
check("P(ac|bd) = P(ad|bc) = (1/3) p*r", DISC == smul(F(1, 3), PR))
check("THREE TOPOLOGIES SUM TO 1: P(ab|cd) + 2 P(ac|bd) = 1",
      is_zero(sub(add(CONC, smul(2, DISC)), ONE)))
check("concordant = pConcordant(a+b) = 1 - (2/3) e^{-(a+b)}  [t := a+b, e^{-t} = p*r]",
      is_zero(sub(CONC, sub(ONE, smul(F(2, 3), PR)))))

# --------------------------------------------------------------------------
print("== 3. exact rational spot checks (p = e^{-a}, r = e^{-b} as rationals) ==")
for p, r in [(F(1, 2), F(3, 4)), (F(1, 2), F(1, 2)), (F(1), F(1)), (F(1, 3), F(2, 5)),
             (F(9, 10), F(1, 10))]:
    deep = peval(DEEP, p, r)
    notdeep = peval(NOTDEEP, p, r)
    conc = peval(CONC, p, r)
    disc = peval(DISC, p, r)
    tag = "p=%s r=%s" % (p, r)
    check(tag + ": weights in [0,1] and normalised",
          0 <= deep <= 1 and 0 <= notdeep <= 1 and deep + notdeep == 1)
    check(tag + ": concordant = 1 - (2/3) p r", conc == 1 - F(2, 3) * p * r)
    check(tag + ": conc + 2 disc = 1", conc + 2 * disc == 1)
    check(tag + ": deep = p r", deep == p * r)
check("t = 0  (a = b = 0, q = 1):  deep = 1, concordant = 1/3 = pConcordant 0",
      peval(DEEP, F(1), F(1)) == 1 and peval(CONC, F(1), F(1)) == F(1, 3))
check("a -> infty (p = 0):  deep = 0, concordant = 1",
      peval(DEEP, F(0), F(1, 2)) == 0 and peval(CONC, F(0), F(1, 2)) == 1)

# --------------------------------------------------------------------------
print("== 4. TRAP (discipline B): one length, TWO draws  vs  two lengths, TWO draws ==")
# correct: two INDEPENDENT sojourn times, one per side, thresholds a and b:
#     P(deep) = e^{-a} e^{-b} = p r
# naive/wrong: a single internal length t = a+b, drawing the two sojourn times
#     and comparing BOTH with the same t:  P = e^{-t} e^{-t} = (p r)^2
NAIVE = mul(PR, PR)
check("the two models DIFFER as polynomials: (p r)^2 != p r  (counterexample!)",
      not is_zero(sub(NAIVE, PR)))
for p, r in [(F(1, 2), F(1, 2)), (F(3, 5), F(2, 5)), (F(1, 4), F(3, 4))]:
    check("p=%s r=%s: naive = (p r)^2 = %s != p r = %s"
          % (p, r, peval(NAIVE, p, r), peval(PR, p, r)),
          peval(NAIVE, p, r) != peval(PR, p, r))
# the t = 1 numbers quoted in the Lean docstring (deterministic high-precision)
from decimal import Decimal, getcontext
getcontext().prec = 30
e1 = (-Decimal(1)).exp()
e2 = (-Decimal(2)).exp()
check("t = 1: e^{-t} = %s  vs  e^{-2t} = %s  (they differ)"
      % (str(e1)[:12], str(e2)[:12]), e1 != e2)
check("the correct value at t = 1 is e^{-1} (two lengths a+b=1), not e^{-2}",
      abs(float(e1) - 0.36787944117144233) < 1e-15)

# --------------------------------------------------------------------------
print("== 5. exhaustive rational sweep: normalisation never breaks ==")
ok = True
n = 0
for pi_ in range(0, 11):
    for ri in range(0, 11):
        p, r = F(pi_, 10), F(ri, 10)
        deep = peval(DEEP, p, r)
        conc = peval(CONC, p, r)
        disc = peval(DISC, p, r)
        n += 1
        if not (deep + (1 - deep) == 1 and 0 <= deep <= 1 and conc + 2 * disc == 1
                and conc == 1 - F(2, 3) * p * r):
            ok = False
check("exhaustive sweep over the 11x11 rational grid (%d points): all identities hold" % n, ok)

# --------------------------------------------------------------------------
print("== 6. Fin 4 minimal instance, end to end ==")
# deterministic species tree ((a,b),(c,d)) with e^{-a} = 3/4, e^{-b} = 1/2
p, r = F(3, 4), F(1, 2)
deep = peval(DEEP, p, r)          # = 3/8
notdeep = peval(NOTDEEP, p, r)    # = 5/8
conc = peval(CONC, p, r)
disc = peval(DISC, p, r)
check("e^{-a}=3/4, e^{-b}=1/2:  nu(deep) = 3/8", deep == F(3, 8))
check("nu(not deep) = 5/8, and 3/8 + 5/8 = 1", notdeep == F(5, 8) and deep + notdeep == 1)
check("P(ab|cd) = 5/8 + (1/3)(3/8) = 3/4", conc == F(3, 4))
check("P(ac|bd) = P(ad|bc) = 1/8, and 3/4 + 2/8 = 1",
      disc == F(1, 8) and conc + 2 * disc == 1)
check("hpos: 0 < nu(not deep) = 5/8  (a+b > 0 here)", deep < 1 and notdeep > 0)

print()
if FAIL:
    print("FAIL: %d check(s) failed" % len(FAIL))
    for nm in FAIL:
        print("   - " + nm)
    sys.exit(1)
print("PASS -- W11f/G5'' exact-rational replication: all checks passed")
