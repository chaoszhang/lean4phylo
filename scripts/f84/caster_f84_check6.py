"""F84 take 6: which choice of the four line-coefficients makes the appendix's own
aggregated formula reproduce its printed constant?  (Fixes the typo for the author.)
Printed: line1 = pR^2 pY^2 , line2 = pX^2 pY^2 , line3 = pR^2 pPsi^2 , line4 = pX^2 pPsi^2
(note the asymmetry of line 3 vs line 2 -- a likely typo)."""
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


def Ew(pi, P, split, coef):
    """coef = (c1, c2, c3, c4) where each c is a function (chi, psi) -> coefficient."""
    c1, c2, c3, c4 = coef
    tot = 0.0
    for chi in R:
        for psi in Y:
            def Pc(i, j, k, l):
                s = [0] * 4
                s[split[0]], s[split[1]], s[split[2]], s[split[3]] = i, j, k, l
                return P[tuple(s)]
            agg = lambda U, V: sum(Pc(i, j, k, l) for i in U for j in U for k in V for l in V)
            tot += c1(chi, psi) * (Pc(chi, chi, psi, psi) + Pc(psi, psi, chi, chi))
            tot -= c2(chi, psi) * (agg(R, (psi,)) + agg((psi,), R))
            tot -= c3(chi, psi) * (agg((chi,), Y) + agg(Y, (chi,)))
            tot += c4(chi, psi) * (agg(R, Y) + agg(Y, R))
    return tot


def coefs(pi):
    pR, pY = pi[A] + pi[G], pi[C] + pi[T]
    f = lambda a, b: a ** 2 * b ** 2
    return {
        "printed  (RY,XY,RPsi,XPsi)": lambda chi, psi: (f(pR, pY), f(pi[chi], pY), f(pR, pi[psi]), f(pi[chi], pi[psi])),
        "sym      (RY,XPsi,RY,XPsi)": lambda chi, psi: (f(pR, pY), f(pi[chi], pi[psi]), f(pR, pY), f(pi[chi], pi[psi])),
        "sym2     (RY,XPsi,RPsi,XPsi)": lambda chi, psi: (f(pR, pY), f(pi[chi], pi[psi]), f(pR, pi[psi]), f(pi[chi], pi[psi])),
        "line3:=XY  (RY,XY,XY,XPsi)": lambda chi, psi: (f(pR, pY), f(pi[chi], pY), f(pi[chi], pY), f(pi[chi], pi[psi])),
        "all X Psi   (XY,XPsi,XPsi,XPsi)": lambda chi, psi: (f(pi[chi], pY), f(pi[chi], pi[psi]), f(pi[chi], pi[psi]), f(pi[chi], pi[psi])),
        "all RY      (RY,RY,RY,RY)": lambda chi, psi: (f(pR, pY), f(pR, pY), f(pR, pY), f(pR, pY)),
        "quarter of printed": lambda chi, psi: (f(pR, pY) / 4, f(pi[chi], pY) / 4, f(pR, pi[psi]) / 4, f(pi[chi], pi[psi]) / 4),
    }


np.random.seed(23)
names = list(coefs(np.array([.25] * 4)).keys())
acc = {k: [] for k in names}
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
             * np.exp(-lam * (1 + kappa) * (la + lb + lc + ld)) * (1 - np.exp(-lam * lx)))
    cs = coefs(pi)
    for k in names:
        wf = cs[k]
        c = (lambda chi, psi, wf=wf: wf(chi, psi)[0],
             lambda chi, psi, wf=wf: wf(chi, psi)[1],
             lambda chi, psi, wf=wf: wf(chi, psi)[2],
             lambda chi, psi, wf=wf: wf(chi, psi)[3])
        d = Ew(pi, P, (0, 1, 2, 3), c) - Ew(pi, P, (0, 2, 1, 3), c)
        acc[k].append(d / claim)

print(f"{'variant':>34} {'ratios':>54} {'spread':>10}")
for k in names:
    v = np.array(acc[k])
    print(f"{k:>34} {str(np.round(v, 5)):>54} {np.abs(v - v.mean()).max():>10.2e}")
