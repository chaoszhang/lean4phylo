"""F84, take 3 — implement the appendix's OWN aggregated E[w] formula literally
(sm.tex 1559-1562) and see whether it yields the printed constant
2 pi_A pi_C pi_G pi_T pi_R pi_Y e^{-lam(1+kappa)L_T}(1-e^{-lam l_x}).

Also validates expm() against the known JC69 kernel (pi uniform, kappa=0, lam=4/3).
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
    E = np.eye(4)
    term = np.eye(4)
    for k in range(1, 40):
        term = term @ M / k
        E = E + term
        if np.abs(term).max() < 1e-20:
            break
    for _ in range(s):
        E = E @ E
    return E


# ---------- sanity: JC69 kernel ----------
pi4 = np.full(4, 0.25)
Qjc, lamjc = build_Q(pi4, 0.0)
Qjc = Qjc * (4.0 / 3.0) / lamjc          # normalise so that off-diagonals are 1/3
E4 = lambda t: np.exp(-(4.0 / 3.0) * t)
for t in (0.0, 0.3, 1.1):
    M = expm(Qjc, t)
    worst = 0.0
    for i in range(4):
        for j in range(4):
            want = 0.25 + 0.75 * E4(t) if i == j else 0.25 - 0.25 * E4(t)
            worst = max(worst, abs(M[i, j] - want))
    print(f"JC69 kernel check t={t}: max|exp(Qt) - closed form| = {worst:.2e}")


def P4(pi, Q, la, lb, lx, lc, ld):
    Ka, Kb, Kx, Kc, Kd = (expm(Q, la), expm(Q, lb), expm(Q, lx), expm(Q, lc), expm(Q, ld))
    out = {}
    for s in product(range(4), repeat=4):
        out[s] = sum(pi[i] * Ka[i, s[0]] * Kb[i, s[1]] * Kx[i, j]
                     * Kc[j, s[2]] * Kd[j, s[3]] for i in range(4) for j in range(4))
    return out


def Ew_aggregated(pi, P, split):
    """Appendix sm.tex 1559-1562, literally: four lines, each inside the double sum."""
    pR = pi[A] + pi[G]
    pY = pi[C] + pi[T]
    tot = 0.0
    for chi in R:
        for psi in Y:
            pX, pPsi = pi[chi], pi[psi]

            def Pr(*letters):          # aggregate P over the class names given
                acc = 0.0
                for i in letters[0]:
                    for j in letters[1]:
                        acc += P[tuple(split_inv((i, j, letters[2], letters[3]), split))]
                return acc
            # simpler: index patterns directly in the canonical order
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


def split_inv(*a):
    return None


np.random.seed(9)
print()
worst = 0.0
for trial in range(6):
    raw = np.random.rand(4) + 0.15
    pi = raw / raw.sum()
    kappa = float(np.random.choice([0.0, 0.5, 1.0, 2.0]))
    la, lb, lx, lc, ld = (float(x) for x in (np.random.rand(5) + 0.1))
    Q, lam = build_Q(pi, kappa)
    P = P4(pi, Q, la, lb, lx, lc, ld)
    pA, pG, pC, pT = pi
    pR, pY = pA + pG, pC + pT
    claim = (2 * pA * pC * pG * pT * pR * pY
             * np.exp(-lam * (1 + kappa) * (la + lb + lc + ld))
             * (1 - np.exp(-lam * lx)))
    d = (Ew_aggregated(pi, P, (0, 1, 2, 3)) - Ew_aggregated(pi, P, (0, 2, 1, 3)))
    ratio = d / claim
    worst = max(worst, abs(ratio - 1))
    print(f"pi={np.round(pi,4)} k={kappa:<4} agg diff={d:+.10e} claim={claim:+.10e} ratio={ratio:.6f}")
print("\nworst |ratio-1| =", worst)
