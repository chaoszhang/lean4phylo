#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W13h F84 positivity audit -- independent numerical check of
`Phylo/Stat/CASTERF84Pos.lean`.

Checks (all against the SAME definitions as the Lean file):
  1. lamF84 pi kappa > 0 for random positive probability vectors and kappa >= 0;
  2. the denominator of lamF84 is strictly > 0 (the Lean lemma `f84_denom_pos`);
  3. f84Amp pi (lamF84 pi kappa) lx > 0 for lx > 0 (`f84Amp_pos`);
  4. Sigma pi_i^2 < 1 (`sum_sq_lt_one_of_pos`) -- and that the Cauchy-Schwarz
     NON-strict bound (Sigma^2 <= 4 Sigma pi_i^2) is NOT enough;
  5. degenerate consistency: kappa = 0 -> F81 form; pi = (1/4)^4, kappa = 0
     -> lamF84 = 4/3 (the JC69 constant);
  6. the claimed strict-converse: pi_0 != pi_1 is FALSE (counterexample), i.e.
     the Lagrange-style route that W13h first tried is invalid.

Run:  python3 scripts/msc/w13h_f84_positivity_audit.py
"""
import random
import math

FAILS = []


def check(cond, msg):
    if not cond:
        FAILS.append(msg)
        print("  FAIL:", msg)


def rand_pi(rng):
    """random strictly positive probability vector on 4 states"""
    xs = [rng.random() + 1e-6 for _ in range(4)]
    s = sum(xs)
    return [x / s for x in xs]


def piR(pi):
    return pi[0] + pi[1]


def piY(pi):
    return pi[2] + pi[3]


def lamF84(pi, kap):
    den = ((1 - sum(p * p for p in pi)) * piR(pi) * piY(pi)
           + 2 * kap * (pi[0] * pi[1] * piY(pi) + pi[2] * pi[3] * piR(pi)))
    return piR(pi) * piY(pi) / den, den


def f84Amp(pi, lam, lx):
    return 2 * pi[0] * pi[2] * pi[1] * pi[3] * piR(pi) * piY(pi) * (1 - math.exp(-lam * lx))


def main():
    rng = random.Random(20261012)
    N = 200000

    print("[1/2/3] random positive pi x kappa in {0, U(0,5), U(0,100), U(0,1e4)}")
    worst_den = float("inf")
    for _ in range(N):
        pi = rand_pi(rng)
        kap = rng.choice([0.0, rng.uniform(0, 5), rng.uniform(0, 100), rng.uniform(0, 1e4)])
        lam, den = lamF84(pi, kap)
        worst_den = min(worst_den, den)
        if not (den > 0):
            check(False, "denominator <= 0")
            break
        if not (lam > 0):
            check(False, "lamF84 <= 0")
            break
        lx = rng.uniform(1e-9, 10)
        if not (f84Amp(pi, lam, lx) > 0):
            check(False, "f84Amp <= 0")
            break
    print("  ok; smallest denominator seen = %.6e (must be > 0)" % worst_den)

    print("[4] Sigma pi_i^2 < 1, and Cauchy-Schwarz (Sigma^2 <= 4 Sigma pi_i^2) is too weak")
    for _ in range(20000):
        pi = rand_pi(rng)
        check(sum(p * p for p in pi) < 1, "sum of squares >= 1")
        # Cauchy-Schwarz direction: it bounds Sigma^2 from ABOVE by 4*Sigma pi^2,
        # i.e. gives Sigma pi_i^2 >= 1/4 -- a LOWER bound, so it cannot give < 1.
        cs = (sum(pi) ** 2) <= 4 * sum(p * p for p in pi) + 1e-12
        check(cs, "Cauchy-Schwarz violated")
    print("  ok; note CS gives only Sigma pi_i^2 >= 1/4 (non-strict lower bound)")

    print("[5] degeneracies")
    pi = [0.25] * 4
    lam, den = lamF84(pi, 0.0)
    check(abs(lam - 4.0 / 3.0) < 1e-12, "pi=1/4, kappa=0 must give lamF84 = 4/3, got %r" % lam)
    print("  pi=(1/4)^4, kappa=0  ->  lamF84 = %.15f  (4/3 = %.15f)" % (lam, 4.0 / 3.0))
    # kappa = 0 -> F81 form: lamF84 = 1/(1 - Sigma pi_i^2), independent of kappa
    for _ in range(2000):
        pi = rand_pi(rng)
        lam0, _ = lamF84(pi, 0.0)
        check(abs(lam0 - 1.0 / (1 - sum(p * p for p in pi))) < 1e-9, "kappa=0 F81 form mismatch")
    print("  kappa=0  ->  lamF84 = 1/(1-Sigma pi_i^2)  (F81 form) verified")

    print("[6] strict-converse FALSE: exists pi>0, Sum pi = 1 with pi_0 == pi_1")
    pi = [0.1, 0.1, 0.4, 0.4]
    check(abs(sum(pi) - 1) < 1e-15 and all(p > 0 for p in pi), "counterexample malformed")
    check(pi[0] == pi[1], "counterexample should have pi_0 == pi_1")
    lam, den = lamF84(pi, 0.0)
    check(den > 0 and lam > 0, "counterexample must still make lamF84 > 0")
    print("  pi = (0.1, 0.1, 0.4, 0.4): pi_0 == pi_1 yet pi>0, Sum pi=1, lamF84 = %.6f > 0" % lam)
    print("  => the Lagrange route claiming pi_0 != pi_1 was INVALID (as the Lean file records)")

    print()
    if FAILS:
        print("AUDIT FAILED (%d)" % len(FAILS))
        return 1
    print("AUDIT PASSED: all checks ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
