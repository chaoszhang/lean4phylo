"""Verify the KEY STRUCTURAL SIMPLIFICATION for F84 (this is the route worth formalizing):

The appendix's aggregated formula (sm.tex 1559-1562) sums over (chi,psi) in R x Y.  Because the
sum over chi of pi_chi^2 * 1[sigma_a = sigma_b = chi] picks out chi = sigma_a, the whole four-line
expression COLLAPSES to a handful of *side-wise* indicator events -- no 256-pattern table needed:

  E[w(ab|cd)] = pi_R^2 pi_Y^2 * [ E(a=b in R, c=d in Y) + E(a=b in Y, c=d in R) ]
              - sqR * pi_Y^2   * [ E(a,b in R, c=d in Y) + E(c,d in R, a=b in Y) ]
              - pi_R^2 * sqY   * [ E(a=b in R, c,d in Y) + E(c=d in R, a,b in Y) ]
              + sqR * sqY      * [ E(a,b in R, c,d in Y) + E(c,d in R, a,b in Y) ]

where sqR = pi_A^2+pi_G^2, sqY = pi_C^2+pi_T^2, and E(...) is the probability of that event.
Check: this must equal the delta-P-dumped aggregated table exactly (as a function of P)."""
import numpy as np
from itertools import product

A, G, C, T = 0, 1, 2, 3
R, Y = (A, G), (C, T)
pi = np.array([0.1, 0.2, 0.3, 0.4])
pR, pY = pi[A] + pi[G], pi[C] + pi[T]
sqR, sqY = pi[A] ** 2 + pi[G] ** 2, pi[C] ** 2 + pi[T] ** 2


def Ew_aggregated(P, split):
    tot = 0.0
    for chi in R:
        for psi in Y:
            pX, pPsi = pi[chi], pi[psi]

            def Pc(i, j, k, l):
                s = [0] * 4
                s[split[0]], s[split[1]], s[split[2]], s[split[3]] = i, j, k, l
                return P[tuple(s)]
            agg = lambda U, V: sum(Pc(i, j, k, l) for i in U for j in U for k in V for l in V)
            tot += pR ** 2 * pY ** 2 * (Pc(chi, chi, psi, psi) + Pc(psi, psi, chi, chi))
            tot -= pX ** 2 * pY ** 2 * (agg(R, (psi,)) + agg((psi,), R))
            tot -= pR ** 2 * pPsi ** 2 * (agg((chi,), Y) + agg(Y, (chi,)))
            tot += pX ** 2 * pPsi ** 2 * (agg(R, Y) + agg(Y, R))
    return tot


def Ew_collapsed(P, split=(0, 1, 2, 3)):
    """The collapsed side-wise-event form."""
    def Pc(i, j, k, l):
        s = [0] * 4
        s[split[0]], s[split[1]], s[split[2]], s[split[3]] = i, j, k, l
        return P[tuple(s)]
    mon = lambda U, V: sum(Pc(i, i, j, j) for i in U for j in V)      # ab monomorphic in U, cd monomorphic in V
    pure_mon = lambda U, V: sum(Pc(i, j, k, k) for i in U for j in U for k in V)  # ab pure U, cd monomorphic in V
    mon_pure = lambda U, V: sum(Pc(i, i, k, l) for i in U for k in V for l in V)  # ab monomorphic in U, cd pure V
    pure = lambda U, V: sum(Pc(i, j, k, l) for i in U for j in U for k in V for l in V)
    return (pR ** 2 * pY ** 2 * (mon(R, Y) + mon(Y, R))
            - sqR * pY ** 2 * (pure_mon(R, Y) + mon_pure(Y, R))
            - pR ** 2 * sqY * (mon_pure(R, Y) + pure_mon(Y, R))
            + sqR * sqY * (pure(R, Y) + pure(Y, R)))


rng = np.random.default_rng(7)
worst = 0.0
for _ in range(40):
    P = {s: float(rng.random()) for s in product(range(4), repeat=4)}
    for split in [(0, 1, 2, 3), (0, 2, 1, 3), (0, 3, 1, 2)]:
        a, b = Ew_aggregated(P, split), Ew_collapsed(P, split)
        worst = max(worst, abs(a - b) / max(1e-12, abs(a) + abs(b)))
print("aggregated (256-pattern) form  vs  collapsed side-wise-event form:")
print("  worst relative difference (40 random P vectors x 3 topologies) =", worst)
print()
print("=> the two forms are IDENTICAL as functions of P."
      "  So the F84 derivation needs only ~8 side-wise event expectations,")
print("   each of which is a short sum over the 2 internal states (u^T K(lx) v) -- NOT 256 patterns.")
