"""Dump the F84 weight table IMPLIED by the appendix's aggregated E[w] formula (sm.tex 1559-1562),
for all 256 point patterns, as a reference artifact to diff against the agent's Lean `wF84` later.

Method: the aggregated formula is linear in the pattern-probability vector (P(sigma)),
so feeding a delta P at sigma extracts the implied weight of sigma.
Reading choice: coefficients AS PRINTED (that is the only self-consistent one;
its difference equals 4x the printed constant -- see CASTER_F84_FINDING.md).
"""
import json
import numpy as np
from itertools import product

A, G, C, T = 0, 1, 2, 3
R, Y = (A, G), (C, T)
pi = np.array([0.1, 0.2, 0.3, 0.4])
pR, pY = pi[A] + pi[G], pi[C] + pi[T]


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


rows = []
nz = 0
for s in product(range(4), repeat=4):
    P = {t: (1.0 if t == s else 0.0) for t in product(range(4), repeat=4)}
    w = Ew_aggregated(P, (0, 1, 2, 3))
    if abs(w) > 1e-12:
        nz += 1
    rows.append({"pattern": "".join("AGCT"[x] for x in s), "w": round(w, 12)})

print(f"pi = {list(pi)}  squarefree coefficients: 4pApGpCpC = {4*pi[0]*pi[1]*pi[2]*pi[3]:.10f}"
      f"   pR^2 pY^2 = {pR**2*pY**2:.10f}")
print(f"nonzero patterns: {nz} / 256")
print("table (nonzero only):")
for r in rows:
    if r["w"] != 0.0:
        print(f"  {r['pattern']}  {r['w']:+.10f}")
with open(r"C:\Users\ASTER\AppData\Local\Temp\caster_f84_reference_table.json", "w") as f:
    json.dump({"pi": list(pi), "table": rows}, f, indent=1)
print("\nsaved -> caster_f84_reference_table.json")
