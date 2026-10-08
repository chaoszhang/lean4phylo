"""DECISIVE F84 check (v2) — with the four Fig.1D rows transcribed correctly under the
appendix's own "matching" semantics (footnote 1), and mirrors included.

  Q_ij = lam pi_j (1 + kappa/pi_R [i,j in R] + kappa/pi_Y [i,j in Y])   (i != j)
  lam  = pi_R pi_Y / ((1 - sum pi^2) pi_R pi_Y + 2 kappa (pi_A pi_G pi_Y + pi_C pi_T pi_R))
  P(sigma) = sum_{i,j} pi_i K(la,i,sa)K(lb,i,sb)K(lx,i,j)K(lc,j,sc)K(ld,j,sd)

Row decomposition (a = sa, b = sb, c = sc, d = sd; R={A,G}, Y={C,T}):
  row1  +4pApGpCpC   : (a=b in R and c=d in Y) or (a=b in Y and c=d in R)
  row2  -2pApG(pC^2+pT^2) : ({a,b}={A,G} and c=d in Y) or ({c,d}={A,G} and a=b in Y)
  row3  -2(pA^2+pG^2)pCpC  : (a=b in R and {c,d}={C,T}) or (c=d in R and {a,b}={C,T})
  row4  +(pA^2+pG^2)(pC^2+pT^2) : {a,b}={A,G} and {c,d}={C,T}
Sanity target: diff = 2 pA pC pG pT pR pY e^{-lam(1+kappa)L_T}(1-e^{-lam l_x}).
"""
import numpy as np
from itertools import product

A, G, C, T = 0, 1, 2, 3
R, Y = {A, G}, {C, T}


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


def patterns(pi, Q, la, lb, lx, lc, ld):
    Ka, Kb, Kx, Kc, Kd = (expm(Q, la), expm(Q, lb), expm(Q, lx), expm(Q, lc), expm(Q, ld))
    out = {}
    for s in product(range(4), repeat=4):
        out[s] = sum(pi[i] * Ka[i, s[0]] * Kb[i, s[1]] * Kx[i, j]
                     * Kc[j, s[2]] * Kd[j, s[3]] for i in range(4) for j in range(4))
    return out


def wF84(pi, s, split):
    pA, pG, pC, pT = pi
    a, b, c, d = (s[i] for i in split)
    if (a == b and a in R and c == d and c in Y) or (a == b and a in Y and c == d and c in R):
        return 4 * pA * pG * pC * pT
    if ({a, b} == {A, G} and c == d and c in Y) or ({c, d} == {A, G} and a == b and a in Y):
        return -2 * pA * pG * (pC ** 2 + pT ** 2)
    if (a == b and a in R and {c, d} == {C, T}) or (c == d and c in R and {a, b} == {C, T}):
        return -2 * (pA ** 2 + pG ** 2) * pC * pT
    if {a, b} == {A, G} and {c, d} == {C, T}:
        return (pA ** 2 + pG ** 2) * (pC ** 2 + pT ** 2)
    return 0.0


def score(pi, Q, ls, split):
    P = patterns(pi, Q, *ls)
    return sum(wF84(pi, s, split) * p for s, p in P.items())


# --- sanity: Q's stationarity / reversibility / spectrum ---
pi0 = np.array([0.1, 0.2, 0.3, 0.4])
for kappa in (0.0, 1.0, 3.0):
    Q, lam = build_Q(pi0, kappa)
    assert abs(Q.sum(axis=1)).max() < 1e-13, "row sums"
    assert abs(pi0 @ Q).max() < 1e-13, "pi Q = 0"
    assert abs((pi0[:, None] * Q) - (pi0[:, None] * Q).T).max() < 1e-13, "detailed balance"
    ev = np.linalg.eigvals(Q).real
    print(f"kappa={kappa}: lam={lam:.6f}  eigenvalues={np.round(np.sort(ev), 6)}")

print()
np.random.seed(5)
worst = 0.0
for trial in range(8):
    raw = np.random.rand(4) + 0.15
    pi = raw / raw.sum()
    kappa = float(np.random.choice([0.0, 0.3, 1.0, 2.5]))
    ls = tuple(float(x) for x in (np.random.rand(5) + 0.1))
    la, lb, lx, lc, ld = ls
    Q, lam = build_Q(pi, kappa)
    pA, pG, pC, pT = pi
    pR, pY = pA + pG, pC + pT
    claim = (2 * pA * pC * pG * pT * pR * pY
             * np.exp(-lam * (1 + kappa) * (la + lb + lc + ld))
             * (1 - np.exp(-lam * lx)))
    d = score(pi, Q, ls, (0, 1, 2, 3)) - score(pi, Q, ls, (0, 2, 1, 3))
    ratio = d / claim
    worst = max(worst, abs(ratio - 1))
    print(f"pi={np.round(pi,4)} k={kappa:<4} diff={d:+.12e} claim={claim:+.12e} ratio={ratio:.9f}")
print("\nworst |ratio - 1| =", worst)
