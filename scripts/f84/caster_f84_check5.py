"""F84 final diagnostic: extract the *implied per-pattern weight table* of the appendix's
aggregated formula (by delta-P probes) and compare it with Fig. 1D under both readings.
This pins down exactly HOW the appendix's table and its formula disagree."""
import numpy as np
from itertools import product

A, G, C, T = 0, 1, 2, 3
R, Y = (A, G), (C, T)
pi = np.array([0.1, 0.2, 0.3, 0.4])
pA, pG, pC, pT = pi
pR, pY = pA + pG, pC + pT


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


def w_agg(sigma, split=(0, 1, 2, 3)):
    P = {s: (1.0 if s == sigma else 0.0) for s in product(range(4), repeat=4)}
    return Ew_aggregated(P, split)


def w_pinned(s):
    a, b, c, d = s
    if a in R and b in R and c in Y and d in Y:
        if a != b and c != d:
            return 4 * pA * pG * pC * pT
        if a == b and c != d:
            return -2 * (pA ** 2 + pG ** 2) * pC * pT
        if a != b and c == d:
            return -2 * pA * pG * (pC ** 2 + pT ** 2)
        return (pA ** 2 + pG ** 2) * (pC ** 2 + pT ** 2)
    return 0.0


def w_unordered(s):
    a, b, c, d = s
    if (a == b and a in R and c == d and c in Y) or (a == b and a in Y and c == d and c in R):
        return 4 * pA * pG * pC * pT
    if ({a, b} == {A, G} and c == d and c in Y) or ({c, d} == {A, G} and a == b and a in Y):
        return -2 * pA * pG * (pC ** 2 + pT ** 2)
    if (a == b and a in R and {c, d} == {C, T}) or (c == d and c in R and {a, b} == {C, T}):
        return -2 * (pA ** 2 + pG ** 2) * pC * pT
    if {a, b} == {A, G} and {c, d} == {C, T}:
        return (pA ** 2 + pG ** 2) * (pC ** 2 + pT ** 2)
    return 0.0


print(f"pi={pi},  pR={pR}, pY={pY}")
print(f"4 pA pG pC pT = {4*pA*pG*pC*pT:.10f}   pR^2 pY^2 = {pR**2*pY**2:.10f}"
      f"   ratio = {pR**2*pY**2/(4*pA*pG*pC*pT):.10f}   pR*pY = {pR*pY:.10f}")
print()
print(f"{'pattern':>22} {'agg':>14} {'pinned':>14} {'unordered':>14}  agg/4={'-':>12}")
nz = 0
for s in product(range(4), repeat=4):
    a = w_agg(s); pn = w_pinned(s); un = w_unordered(s)
    if abs(a) < 1e-12 and abs(pn) < 1e-12 and abs(un) < 1e-12:
        continue
    nz += 1
    print(f"{str(s):>22} {a:>14.8f} {pn:>14.8f} {un:>14.8f}  {a/4:>14.8f}")
print(f"\nnonzero patterns (any reading): {nz}")
# global check: is the aggregated implied table a scalar multiple of either reading?
agg = np.array([w_agg(s) for s in product(range(4), repeat=4)])
for name, f in (("pinned", w_pinned), ("unordered", w_unordered)):
    ref = np.array([f(s) for s in product(range(4), repeat=4)])
    nzm = (np.abs(ref) > 1e-12)
    if nzm.any():
        ratios = agg[nzm] / ref[nzm]
        print(f"agg / {name}: ratios = {np.round(ratios, 6)}")
