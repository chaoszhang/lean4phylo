"""Pin down the F84 table: test the LITERAL Fig.1D assignment (rows as printed) with the
16 pinned patterns, and a few nearby variants.  Target ratio 1 (i.e. the printed constant)."""
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


def r1(pi):
    pA, pG, pC, pT = pi
    return 4 * pA * pG * pC * pT


def r2(pi):
    pA, pG, pC, pT = pi
    return -2 * pA * pG * (pC ** 2 + pT ** 2)


def r3(pi):
    pA, pG, pC, pT = pi
    return -2 * (pA ** 2 + pG ** 2) * pC * pT


def r4(pi):
    pA, pG, pC, pT = pi
    return (pA ** 2 + pG ** 2) * (pC ** 2 + pT ** 2)


def mk(assign):
    def w(pi, s, split=(0, 1, 2, 3)):
        a, b, c, d = (s[i] for i in split)
        if not (a in R and b in R and c in Y and d in Y):
            return 0.0
        return assign(pi, a == b, c == d)
    return w


CANDS = {
    # literal Fig.1D: AA|CC->r1 ; AG|CC->r2 ; AA|CT->r3 ; AG|CT->r4
    "FIG1D literal (a=b,c=d)->r1; (a!=b,c=d)->r2; (a=b,c!=d)->r3; else r4":
        mk(lambda pi, ab, cd: r1(pi) if (ab and cd) else r2(pi) if cd else r3(pi) if ab else r4(pi)),
    # rows 2/3 swapped  (= what I tested last time, ratio 2)
    "rows 2/3 swapped":
        mk(lambda pi, ab, cd: r1(pi) if (ab and cd) else r3(pi) if cd else r2(pi) if ab else r4(pi)),
    # rows 1/4 swapped
    "rows 1/4 swapped":
        mk(lambda pi, ab, cd: r4(pi) if (ab and cd) else r2(pi) if cd else r3(pi) if ab else r1(pi)),
    # all four swapped
    "rows 1<->4 and 2<->3":
        mk(lambda pi, ab, cd: r4(pi) if (ab and cd) else r3(pi) if cd else r2(pi) if ab else r1(pi)),
}

np.random.seed(53)
acc = {k: [] for k in CANDS}
for _ in range(6):
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
    for k, wf in CANDS.items():
        dab = sum(wf(pi, s, (0, 1, 2, 3)) * P[s] for s in P)
        dac = sum(wf(pi, s, (0, 2, 1, 3)) * P[s] for s in P)
        acc[k].append((dab - dac) / claim)

for k, v in acc.items():
    v = np.array(v)
    const = np.abs(v - v.mean()).max() < 1e-9
    print(f"{'CONSTANT' if const else 'drifts  '} mean={v.mean():+.6f} spread={np.abs(v - v.mean()).max():.2e}")
    print(f"    {k}")
