"""Decisive side-by-side: my Ew_of vs a VERBATIM copy of caster_f84_iface.py's Ew_collapsed."""
import numpy as np
from itertools import product

A, G, C, T = 0, 1, 2, 3
R, Y = (A, G), (C, T)


def _build(pi, kappa):
    pR, pY = pi[A] + pi[G], pi[C] + pi[T]
    lam = (pR * pY) / ((1 - sum(x * x for x in pi)) * pR * pY
                       + 2 * kappa * (pi[A] * pi[G] * pY + pi[C] * pi[T] * pR))
    B = np.zeros((4, 4))
    for i in range(4):
        for j in range(4):
            same = (i in R and j in R) or (i in Y and j in Y)
            pc = pR if j in R else pY
            B[i, j] = pi[j] / pc if same else 0.0
    return B, lam


def _K(B, pi, kappa, lam, t):
    Pi = np.tile(pi, (4, 1))
    return Pi + np.exp(-lam * t) * (B - Pi) + np.exp(-lam * (1 + kappa) * t) * (np.eye(4) - B)


def _Ew_collapsed(pi, B, kappa, lam, la, lb, lx, lc, ld, split):
    """VERBATIM from scripts/f84/caster_f84_iface.py"""
    Ka, Kb, Kx, Kc, Kd = (_K(B, pi, kappa, lam, t) for t in (la, lb, lx, lc, ld))
    P = {s: sum(pi[p] * Ka[p, s[0]] * Kb[p, s[1]] * Kx[p, q] * Kc[q, s[2]] * Kd[q, s[3]]
                for p in range(4) for q in range(4))
         for s in product(range(4), repeat=4)}

    def Pc(i, j, k, l):
        s = [0] * 4
        s[split[0]], s[split[1]], s[split[2]], s[split[3]] = i, j, k, l
        return P[tuple(s)]
    pR, pY = pi[A] + pi[G], pi[C] + pi[T]
    sqR, sqY = pi[A] ** 2 + pi[G] ** 2, pi[C] ** 2 + pi[T] ** 2
    mon = lambda U, V: sum(Pc(i, i, j, j) for i in U for j in V)
    pureMon = lambda U, V: sum(Pc(i, j, k, k) for i in U for j in U for k in V)
    monPure = lambda U, V: sum(Pc(i, i, k, l) for i in U for k in V for l in V)
    pureAll = lambda U, V: sum(Pc(i, j, k, l) for i in U for j in U for k in V for l in V)
    return (pR ** 2 * pY ** 2 / 4 * (mon(R, Y) + mon(Y, R))
            - pY ** 2 * sqR / 4 * (pureMon(R, Y) + monPure(Y, R))
            - pR ** 2 * sqY / 4 * (monPure(R, Y) + pureMon(Y, R))
            + sqR * sqY / 4 * (pureAll(R, Y) + pureAll(Y, R)))


pi = np.array([0.31, 0.24, 0.20, 0.25])
kappa = 0.9
B, lam = _build(pi, kappa)
la, lb, lx, lc, ld = 0.4, 0.7, 0.3, 0.5, 0.9
pA, pG, pC, pT = pi
pR, pY = pA + pG, pC + pT
Cval = 2 * pA * pC * pG * pT * pR * pY * np.exp(-lam * (1 + kappa) * (la + lb + lc + ld)) * (1 - np.exp(-lam * lx))
print("pi =", pi, "kappa =", kappa, "lam =", lam)
print("C (printed constant) =", Cval)
print()
print("VERBATIM iface.py Ew_collapsed (divide-by-4 coefficients):")
for name, split in (("ab|cd", (0, 1, 2, 3)), ("ac|bd", (0, 2, 1, 3)), ("ad|bc", (0, 3, 1, 2))):
    print(f"   {name}: Ew = {_Ew_collapsed(pi, B, kappa, lam, la, lb, lx, lc, ld, split): .10e}")
e_ab = _Ew_collapsed(pi, B, kappa, lam, la, lb, lx, lc, ld, (0, 1, 2, 3))
e_ac = _Ew_collapsed(pi, B, kappa, lam, la, lb, lx, lc, ld, (0, 2, 1, 3))
e_ad = _Ew_collapsed(pi, B, kappa, lam, la, lb, lx, lc, ld, (0, 3, 1, 2))
print(f"   (ab-ac)/C = {(e_ab - e_ac) / Cval}")
print(f"   (ab-ad)/C = {(e_ab - e_ad) / Cval}")
print(f"   (ac-ad)/C = {(e_ac - e_ad) / Cval}")
print()
# now the same object via my `ev` indexing, printed per family, split (0,2,1,3)
Ka, Kb, Kx, Kc, Kd = (_K(B, pi, kappa, lam, t) for t in (la, lb, lx, lc, ld))
P = {s: sum(pi[p] * Ka[p, s[0]] * Kb[p, s[1]] * Kx[p, q] * Kc[q, s[2]] * Kd[q, s[3]]
            for p in range(4) for q in range(4))
     for s in product(range(4), repeat=4)}


def fam(split):
    def Pc(i, j, k, l):
        s = [0] * 4
        s[split[0]], s[split[1]], s[split[2]], s[split[3]] = i, j, k, l
        return P[tuple(s)]
    sqR, sqY = pi[A] ** 2 + pi[G] ** 2, pi[C] ** 2 + pi[T] ** 2
    out = {}
    out['pR2pY2 mon(R,Y)'] = pR ** 2 * pY ** 2 / 4 * sum(Pc(i, i, j, j) for i in R for j in Y)
    out['pR2pY2 mon(Y,R)'] = pR ** 2 * pY ** 2 / 4 * sum(Pc(i, i, j, j) for i in Y for j in R)
    out['-pY2qR pureMon(R,Y)'] = -pY ** 2 * sqR / 4 * sum(Pc(i, j, k, k) for i in R for j in R for k in Y)
    out['-pY2qR monPure(Y,R)'] = -pY ** 2 * sqR / 4 * sum(Pc(i, i, k, l) for i in Y for k in R for l in R)
    out['-pR2qY monPure(R,Y)'] = -pR ** 2 * sqY / 4 * sum(Pc(i, i, k, l) for i in R for k in Y for l in Y)
    out['-pR2qY pureMon(Y,R)'] = -pR ** 2 * sqY / 4 * sum(Pc(i, j, k, k) for i in Y for j in Y for k in R)
    out['qRqY pureAll(R,Y)'] = sqR * sqY / 4 * sum(Pc(i, j, k, l) for i in R for j in R for k in Y for l in Y)
    out['qRqY pureAll(Y,R)'] = sqR * sqY / 4 * sum(Pc(i, j, k, l) for i in Y for j in Y for k in R for l in R)
    return out


for split, name in (((0, 2, 1, 3), "ac|bd"), ((0, 3, 1, 2), "ad|bc")):
    print(f"--- families for split {split} ({name}) ---")
    f = fam(split)
    for k, v in f.items():
        print(f"   {k:22s} = {v: .8e}")
    print(f"   {'SUM':22s} = {sum(f.values()): .8e}    (should equal C = {Cval:.8e})")
