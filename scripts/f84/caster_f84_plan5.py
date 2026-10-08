"""Independent verification of agent A's §5 plan (the gR/gY class-block route).

Claims to check (numerically, random F84 parameters):
 (A) 4*Ew_lean = Σ_pΣ_q π_p * Kx(p,q) * (gR(p)*gY(q) + gY(p)*gR(q))
 (B) p ∉ R → gR(p) = 0 ;  q ∉ Y → gY(q) = 0
 (C) Σ_{p∈R} π_p gR(p) = piR*(piR^2 - sqR)*rm(t1)*rm(t2)
 (E) 4*Ew_lean = 2*(1-sm lx)*piR*piY*(piR^2-sqR)*(piY^2-sqY)*rm(t1)rm(t2)rm(t3)rm(t4)
 where  S(U,p,t)   = Σ_{i∈U} K(t)[p][i]
        D(U,p,q,t,t') = Σ_{i∈U} K(t)[p][i]*K(t')[q][i]
        gR(p) = piR^2*D(R,p,p,t1,t2) - sqR*S(R,p,t1)*S(R,p,t2)      (R = {A,G})
        gY(q) = piY^2*D(Y,q,q,t3,t4) - sqY*S(Y,q,t3)*S(Y,q,t4)      (Y = {C,T})
 `Ew_lean` = the committed `CASTERF84Events.Ew` (coefficients 照印, then /4).
"""
import numpy as np
from itertools import product

A, G, C, T = 0, 1, 2, 3
R, Y = (A, G), (C, T)
rng = np.random.default_rng(20260111)


def setup(pi, kappa):
    pR, pY = pi[A] + pi[G], pi[C] + pi[T]
    lam = (pR * pY) / ((1 - sum(x * x for x in pi)) * pR * pY
                       + 2 * kappa * (pi[A] * pi[G] * pY + pi[C] * pi[T] * pR))
    B = np.zeros((4, 4))
    for i in range(4):
        for j in range(4):
            same = (i in R and j in R) or (i in Y and j in Y)
            pc = pR if j in R else pY
            B[i, j] = pi[j] / pc if same else 0.0
    return B, lam, pR, pY


def K(B, pi, kappa, lam, t):
    Pi = np.tile(pi, (4, 1))
    return Pi + np.exp(-lam * t) * (B - Pi) + np.exp(-lam * (1 + kappa) * t) * (np.eye(4) - B)


def patt4(pi, B, kappa, lam, t1, t2, tx, t3, t4):
    K1, K2, Kx, K3, K4 = (K(B, pi, kappa, lam, t) for t in (t1, t2, tx, t3, t4))
    P = np.zeros((4, 4, 4, 4))
    for p in range(4):
        for q in range(4):
            P += pi[p] * np.einsum('i,j,k,l->ijkl', K1[p], K2[p], Kx[p, q] * K3[q], K4[q])
    return P


def Ew_lean(pi, B, kappa, lam, t1, t2, tx, t3, t4):
    P = patt4(pi, B, kappa, lam, t1, t2, tx, t3, t4)
    mon = lambda U, V: sum(P[i, i, j, j] for i in U for j in V)
    pm = lambda U, V: sum(P[i, j, k, k] for i in U for j in U for k in V)
    mp = lambda U, V: sum(P[i, i, k, l] for i in U for k in V for l in V)
    pa = lambda U, V: sum(P[i, j, k, l] for i in U for j in U for k in V for l in V)
    pR, pY = pi[A] + pi[G], pi[C] + pi[T]
    sqR, sqY = pi[A] ** 2 + pi[G] ** 2, pi[C] ** 2 + pi[T] ** 2
    return (pR ** 2 * pY ** 2 * (mon(R, Y) + mon(Y, R))
            - pY ** 2 * sqR * (pm(R, Y) + mp(Y, R))
            - pR ** 2 * sqY * (mp(R, Y) + pm(Y, R))
            + sqR * sqY * (pa(R, Y) + pa(Y, R))) / 4


wA = wB = wC = wE = 0.0
worst = None
for _ in range(120):
    raw = rng.random(4) + 0.2
    pi = raw / raw.sum()
    kappa = float(rng.random() * 3)
    B, lam, pR, pY = setup(pi, kappa)
    t1, t2, lx, t3, t4 = (float(x) for x in (rng.random(5) + 0.1))
    K1, K2, Kx, K3, K4 = (K(B, pi, kappa, lam, t) for t in (t1, t2, lx, t3, t4))
    S = lambda U, p, Kv: sum(Kv[p, i] for i in U)
    D = lambda U, p, q, Kv1, Kv2: sum(Kv1[p, i] * Kv2[q, i] for i in U)
    gR = lambda p: pR ** 2 * D(R, p, p, K1, K2) - (pi[A] ** 2 + pi[G] ** 2) * S(R, p, K1) * S(R, p, K2)
    gY = lambda q: pY ** 2 * D(Y, q, q, K3, K4) - (pi[C] ** 2 + pi[T] ** 2) * S(Y, q, K3) * S(Y, q, K4)
    ew4 = 4 * Ew_lean(pi, B, kappa, lam, t1, t2, lx, t3, t4)

    # (A)
    rhsA = sum(pi[p] * Kx[p, q] * (gR(p) * gY(q) + gY(p) * gR(q))
               for p in range(4) for q in range(4))
    wA = max(wA, abs(rhsA - ew4) / max(1e-300, abs(ew4)))
    # (B)
    wB = max(wB, abs(gR(C)), abs(gR(T)), abs(gY(A)), abs(gY(G)))
    # (C)
    lhsC = sum(pi[p] * gR(p) for p in R)
    rhsC = pR * (pR ** 2 - (pi[A] ** 2 + pi[G] ** 2)) * np.exp(-lam * (1 + kappa) * t1) * np.exp(-lam * (1 + kappa) * t2)
    wC = max(wC, abs(lhsC - rhsC) / max(1e-300, abs(rhsC)))
    # (E)
    rhsE = (2 * (1 - np.exp(-lam * lx)) * pR * pY
            * (pR ** 2 - (pi[A] ** 2 + pi[G] ** 2)) * (pY ** 2 - (pi[C] ** 2 + pi[T] ** 2))
            * np.exp(-lam * (1 + kappa) * (t1 + t2 + t3 + t4)))
    wE = max(wE, abs(rhsE - ew4) / max(1e-300, abs(ew4)))
    if worst is None:
        worst = (pR, pY, pi.copy(), gR(A), lhsC, rhsC)

print("(A) 4*Ew = Σπ_p Kx (gR gY + gY gR)      : max rel =", wA)
print("(B) p∉R → gR p = 0 ; q∉Y → gY q = 0     : max abs =", wB)
print("(C) Σ_{p∈R} π_p gR p = piR(piR²-sqR)rm t1 rm t2 : max rel =", wC)
print("(E) 4*Ew = 2(1-sm lx)piR piY(piR²-sqR)(piY²-sqY)∏rm : max rel =", wE)
print()
print("worst example: pR =", worst[0], " pY =", worst[1], " pi =", worst[2])
print("  gR(A) =", worst[3], "  Σ_{R}π gR =", worst[4], "  rhsC =", worst[5])
