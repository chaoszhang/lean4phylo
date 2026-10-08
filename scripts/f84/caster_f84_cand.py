"""Which F84 weight table is the intended one?  Test candidate tables for a CONSTANT ratio
of (E[w(ab|cd)] - E[w(ac|bd)]) to the printed constant 2 pA pC pG pT pR pY e^{-lam(1+kap)L}(1-e^{-lam lx}).

Candidates:
  AGG  : the appendix's aggregated formula as printed (my earlier finding: ratio == 4 exactly)
  SYM  : "within-side structure" rows applied symmetrically in BOTH orientations (32 patterns)
  SYM/4: SYM divided by 4
  LIT  : Fig. 1D literal (16 patterns, no mirrors)   [known: drifts]
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
    nrm = np.abs(Q).sum(axis=1).max() * abs(t)
    s = max(0, int(np.ceil(np.log2(nrm + 1e-300))) + 4)
    M = Q * t / (2 ** s)
    E = np.eye(4); term = np.eye(4)
    for k in range(1, 40):
        term = term @ M / k; E = E + term
        if np.abs(term).max() < 1e-20:
            break
    for _ in range(s):
        E = E @ E
    return E


def P4(pi, Q, la, lb, lx, lc, ld):
    Ka, Kb, Kx, Kc, Kd = (expm(Q, la), expm(Q, lb), expm(Q, lx), expm(Q, lc), expm(Q, ld))
    return {s: sum(pi[i] * Ka[i, s[0]] * Kb[i, s[1]] * Kx[i, j] * Kc[j, s[2]] * Kd[j, s[3]]
                   for i in range(4) for j in range(4))
            for s in product(range(4), repeat=4)}


def rows(pi):
    pA, pG, pC, pT = pi
    return (4 * pA * pG * pC * pT, -2 * pA * pG * (pC ** 2 + pT ** 2),
            -2 * (pA ** 2 + pG ** 2) * pC * pT, (pA ** 2 + pG ** 2) * (pC ** 2 + pT ** 2))


def w_sym(pi, s, split=(0, 1, 2, 3)):
    a, b, c, d = (s[i] for i in split)
    if not ((a in R and b in R and c in Y and d in Y) or (a in Y and b in Y and c in R and d in R)):
        return 0.0
    r = rows(pi)
    if a == b and c == d:
        return r[0]
    if a == b and c != d:
        return r[1]
    if a != b and c == d:
        return r[2]
    return r[3]


def w_lit(pi, s, split=(0, 1, 2, 3)):
    a, b, c, d = (s[i] for i in split)
    if not (a in R and b in R and c in Y and d in Y):
        return 0.0
    r = rows(pi)
    if a == b and c == d:
        return r[0]
    if a == b and c != d:
        return r[1]
    if a != b and c == d:
        return r[2]
    return r[3]


def Ew_aggregated(pi, P, split):
    pR, pY = pi[A] + pi[G], pi[C] + pi[T]
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


np.random.seed(41)
names = ["AGG (as printed)", "SYM", "SYM/4", "LIT (no mirrors)"]
acc = {k: [] for k in names}
for _ in range(7):
    raw = np.random.rand(4) + 0.15
    pi = raw / raw.sum()
    kappa = float(np.random.choice([0.0, 0.5, 1.0, 2.0]))
    la, lb, lx, lc, ld = (float(x) for x in (np.random.rand(5) + 0.1))
    Q, lam = build_Q(pi, kappa)
    P = P4(pi, Q, la, lb, lx, lc, ld)
    pA, pG, pC, pT = pi
    pR, pY = pA + pG, pC + pT
    claim = (2 * pA * pC * pG * pT * pR * pY
             * np.exp(-lam * (1 + kappa) * (la + lb + lc + ld)) * (1 - np.exp(-lam * lx)))
    d = {}
    d["AGG (as printed)"] = Ew_aggregated(pi, P, (0, 1, 2, 3)) - Ew_aggregated(pi, P, (0, 2, 1, 3))
    for nm, wf in (("SYM", w_sym), ("SYM/4", w_sym), ("LIT (no mirrors)", w_lit)):
        dab = sum(wf(pi, s, (0, 1, 2, 3)) * P[s] for s in P)
        dac = sum(wf(pi, s, (0, 2, 1, 3)) * P[s] for s in P)
        d[nm] = (dab - dac) / (4.0 if nm == "SYM/4" else 1.0)
    for k in names:
        acc[k].append(d[k] / claim)

for k in names:
    v = np.array(acc[k])
    tag = "CONSTANT ✓" if np.abs(v - v.mean()).max() < 1e-9 else "drifts"
    print(f"{k:>18}: ratios={np.round(v, 4)}  mean={v.mean():.6f}  spread={np.abs(v - v.mean()).max():.2e}  {tag}")
