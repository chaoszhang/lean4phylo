"""Check the Lean interface convention of `Phylo/Stat/CASTERF84Events.lean` (commit 36ce9be).

The Lean file asserts the correspondence
    EwF84    = Ew(la, lb, lx, lc, ld)      (topology ab|cd)
    EwF84_ac = Ew(la, lc, lx, lb, ld)      (topology ac|bd)
    EwF84_ad = Ew(la, ld, lx, lb, lc)      (topology ad|bc)
where `Ew` is the collapsed aggregated form applied with the *topology's* side grouping.

Python's `Ew_collapsed(P, split)` places the pattern's four labels at positions `split`:
    EwF84    <-> split (0,1,2,3)   ,  EwF84_ac <-> split (0,2,1,3) ,  EwF84_ad <-> split (0,3,1,2)
(the same convention: side 1 = leaves at split[0],split[1]).
Two consequences follow, and both must hold for the convention to be right:
    (i)  (E(0,1,2,3) - E(0,2,1,3)) / C = 1     with C the printed constant (the ÷4-normalised table)
    (ii) E(0,2,1,3) = E(0,3,1,2)               ("the two wrong topologies have equal weight")
"""
import numpy as np
from itertools import product

A, G, C, T = 0, 1, 2, 3
R, Y = (A, G), (C, T)


def build(pi, kappa):
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


def K(B, pi, kappa, lam, t):
    Pi = np.tile(pi, (4, 1))
    return Pi + np.exp(-lam * t) * (B - Pi) + np.exp(-lam * (1 + kappa) * t) * (np.eye(4) - B)


def Ew_collapsed(pi, B, kappa, lam, la, lb, lx, lc, ld, split):
    Ka, Kb, Kx, Kc, Kd = (K(B, pi, kappa, lam, la), K(B, pi, kappa, lam, lb),
                          K(B, pi, kappa, lam, lx), K(B, pi, kappa, lam, lc),
                          K(B, pi, kappa, lam, ld))
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
    # ÷4-normalised coefficients (the Lean file's convention)
    return (pR ** 2 * pY ** 2 / 4 * (mon(R, Y) + mon(Y, R))
            - pY ** 2 * sqR / 4 * (pureMon(R, Y) + monPure(Y, R))
            - pR ** 2 * sqY / 4 * (monPure(R, Y) + pureMon(Y, R))
            + sqR * sqY / 4 * (pureAll(R, Y) + pureAll(Y, R)))


rng = np.random.default_rng(31337)
w_i = w_ii = 0.0
for _ in range(200):
    raw = rng.random(4) + 0.15
    pi = raw / raw.sum()
    kappa = float(rng.random() * 3)
    B, lam = build(pi, kappa)
    la, lb, lx, lc, ld = (float(x) for x in (rng.random(5) + 0.1))
    e_ab = Ew_collapsed(pi, B, kappa, lam, la, lb, lx, lc, ld, (0, 1, 2, 3))
    e_ac = Ew_collapsed(pi, B, kappa, lam, la, lb, lx, lc, ld, (0, 2, 1, 3))
    e_ad = Ew_collapsed(pi, B, kappa, lam, la, lb, lx, lc, ld, (0, 3, 1, 2))
    pA, pG, pC, pT = pi
    pR, pY = pA + pG, pC + pT
    claim = (2 * pA * pC * pG * pT * pR * pY
             * np.exp(-lam * (1 + kappa) * (la + lb + lc + ld)) * (1 - np.exp(-lam * lx)))
    w_i = max(w_i, abs((e_ab - e_ac) / claim - 1))
    w_ii = max(w_ii, abs(e_ac - e_ad) / max(1e-12, abs(e_ac)))
print("(i)  (EwF84 - EwF84_ac)/C  vs 1        : max |ratio - 1| =", w_i)
print("(ii) EwF84_ac = EwF84_ad              : max rel. diff  =", w_ii)
print()
print("=> the Lean interface convention (EwF84<->(0,1,2,3), EwF84_ac<->(0,2,1,3),")
print("   EwF84_ad<->(0,3,1,2)) reproduces the printed constant under the /4 normalisation",
      "and the two wrong topologies.")
