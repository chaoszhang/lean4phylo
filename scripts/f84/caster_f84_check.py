"""DECISIVE F84 check, done directly from the appendix's explicit data:
  Q_ij = lam * pi_j * (1 + kappa/pi_R * [i,j in R] + kappa/pi_Y * [i,j in Y])   (i != j)
  lam  = pi_R pi_Y / ((1 - sum pi^2) pi_R pi_Y + 2 kappa (pi_A pi_G pi_Y + pi_C pi_T pi_R))
  P(sigma) = sum_{i,j} pi_i K(la,i,sa) K(lb,i,sb) K(lx,i,j) K(lc,j,sc) K(ld,j,sd),  K = exp(Q t)
Weight table readings for topology ab|cd:
  (a) LITERAL Fig.1D:  +4pApGpCpC for {sa,sb}={A,G} & {sc,sd}={C,T}; etc.  (8 patterns)
  (b) MATCHING/aggregated: the appendix's own E[w] formula (coefficient pi_R^2 pi_Y^2).
Compare E[w(ab|cd)] - E[w(ac|bd)] with 2 pA pC pG pT pR pY e^{-lam(1+kappa)L_T}(1-e^{-lam l_x}).
"""
import numpy as np
from itertools import product

A, G, C, T = 0, 1, 2, 3
R, Y = (A, G), (C, T)


def build_Q(pi, kappa):
    pR, pY = pi[A] + pi[G], pi[C] + pi[T]
    lam = (pR * pY) / ((1 - sum(x * x for x in pi)) * pR * pY
                       + 2 * kappa * (pi[A] * pi[G] * pY + pi[C] * pi[T] * pR))
    Q = np.zeros((4, 4))
    for i in range(4):
        for j in range(4):
            if i == j:
                continue
            f = 1.0
            if i in R and j in R:
                f += kappa / pR
            if i in Y and j in Y:
                f += kappa / pY
            Q[i, j] = lam * pi[j] * f
    for i in range(4):
        Q[i, i] = -sum(Q[i, j] for j in range(4) if j != i)
    return Q, lam


def expm(Q, t):
    """exp(Q t) by scaling and squaring with a Taylor series (no scipy)."""
    nrm = np.abs(Q).sum(axis=1).max() * abs(t)
    s = max(0, int(np.ceil(np.log2(nrm + 1e-300))) + 4)
    M = Q * t / (2 ** s)
    E = np.eye(4)
    term = np.eye(4)
    for k in range(1, 30):
        term = term @ M / k
        E = E + term
        if np.abs(term).max() < 1e-18:
            break
    for _ in range(s):
        E = E @ E
    return E


def patternProbs(pi, Q, la, lb, lx, lc, ld):
    Ka, Kb, Kx, Kc, Kd = (expm(Q, la), expm(Q, lb), expm(Q, lx), expm(Q, lc), expm(Q, ld))
    out = {}
    for s in product(range(4), repeat=4):
        tot = 0.0
        for i in range(4):
            for j in range(4):
                tot += (pi[i] * Ka[i, s[0]] * Kb[i, s[1]] * Kx[i, j]
                        * Kc[j, s[2]] * Kd[j, s[3]])
        out[s] = tot
    return out


def w_literal(pi, s, split):
    """Fig. 1D read as a COMPLETE pointwise table (the F84 agent's reading (a))."""
    pA, pG, pC, pT = pi
    sa, sb, sc, sd = (s[i] for i in split)
    inR = {A, G}
    inY = {C, T}
    if sa in inR and sb in inR and sa != sb and sc in inY and sd in inY and sc != sd:
        return 4 * pA * pG * pC * pT
    if {sa, sb} == {A, G} and sc == sd and sc in inY:
        return -2 * pA * pG * (pC ** 2 + pT ** 2)
    if {sc, sd} == {C, T} and sa == sb and sa in inR:
        return -2 * (pA ** 2 + pG ** 2) * pC * pT
    if {sa, sb} == {A, G} and {sc, sd} == {C, T}:
        return (pA ** 2 + pG ** 2) * (pC ** 2 + pT ** 2)
    return 0.0


def w_matching(pi, s, split):
    """The appendix's own E[w] formula, read per pattern with coefficient pi_R^2 pi_Y^2
    (plus the class-aggregated terms).  split = (0,1,2,3) => ab|cd."""
    pA, pG, pC, pT = pi
    pR, pY = pA + pG, pC + pT
    a, b, c, d = (s[i] for i in split)
    inR = lambda x: x in R
    inY = lambda x: x in Y
    w = 0.0
    if a in R and b in R and a != b and c in Y and d in Y and c != d:
        w += pR ** 2 * pY ** 2
    if c in R and d in R and c != d and a in Y and b in Y and a != b:
        w += pR ** 2 * pY ** 2
    if a in R and c in Y and b in R and d in Y:
        w += pR ** 2 * pY ** 2
    if c in R and a in Y and d in R and b in Y:
        w += pR ** 2 * pY ** 2
    return w


def score(pi, Q, ls, split, wfun):
    P = patternProbs(pi, Q, ls[0], ls[1], ls[2], ls[3], ls[4])
    tot = 0.0
    for s, p in P.items():
        tot += wfun(pi, s, split) * p
    return tot


np.random.seed(3)
print(f"{'pi':>28} {'read':>9} {'diff':>16} {'claim':>16} {'ratio':>10}")
for trial in range(6):
    raw = np.random.rand(4) + 0.15
    pi = raw / raw.sum()
    kappa = float(np.random.choice([0.0, 0.5, 1.0, 2.0]))
    la, lb, lx, lc, ld = (float(x) for x in (np.random.rand(5) + 0.1))
    Q, lam = build_Q(pi, kappa)
    pA, pG, pC, pT = pi
    pR, pY = pA + pG, pC + pT
    claim = (2 * pA * pC * pG * pT * pR * pY
             * np.exp(-lam * (1 + kappa) * (la + lb + lc + ld))
             * (1 - np.exp(-lam * lx)))
    d_lit = (score(pi, Q, (la, lb, lx, lc, ld), (0, 1, 2, 3), w_literal)
             - score(pi, Q, (la, lb, lx, lc, ld), (0, 2, 1, 3), w_literal))
    d_mat = (score(pi, Q, (la, lb, lx, lc, ld), (0, 1, 2, 3), w_matching)
             - score(pi, Q, (la, lb, lx, lc, ld), (0, 2, 1, 3), w_matching))
    print(f"{np.round(pi,4)} k={kappa:<4} literal {d_lit:+16.10f} {claim:+16.10f} {d_lit/claim:>10.5f}")
    print(f"{'':>28} matching {d_mat:+16.10f} {claim:+16.10f} {d_mat/claim:>10.5f}")
