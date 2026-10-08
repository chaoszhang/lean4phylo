"""Independent verification of the `EwA_zero` / `EwB_zero` route (A-grouping factorisation).

Route (analogous to the diagonal `gR`/`gY` one):
    GA_c(p,q) := pi_c^2 * D_c(p,q;s,t) - sq_c * S_c(p,s) * S_c(q,t)
      with c=R using (s,t) = (t1,t3) and c=Y using (s,t) = (t2,t4).
Claim (i)   4*EwA = 2 * ΣpΣq π_p * Kx_{pq} * GA_R(p,q) * GA_Y(p,q)
Claim (ii)  GA_R(p,q) = 0 whenever p ∉ R and q ∉ R
Claim (iii) p ∈ R, q ∉ R  =>  GA_R(p,q) = piR * rm(t1) * (1 - sm(t3)) * (piR*π_p - sqR)
Claim (iv)  Σ_{p∈R} π_p * (piR*π_p - sqR) = 0     (the final cancellation)
"""
import numpy as np

A, G, C, T = 0, 1, 2, 3
R, Y = (A, G), (C, T)
rng = np.random.default_rng(20260112)


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


def EwA_lean(pi, B, kappa, lam, la, lb, lx, lc, ld):
    """EwA = Ew evaluated with the A grouping (pattern positions (0,2),(1,3)), /4."""
    Ka, Kb, Kx, Kc, Kd = (K(B, pi, kappa, lam, t) for t in (la, lb, lx, lc, ld))
    P = np.zeros((4, 4, 4, 4))
    for p in range(4):
        for q in range(4):
            P += pi[p] * np.einsum('i,j,k,l->ijkl', Ka[p], Kb[p], Kx[p, q] * Kc[q], Kd[q])
    Pc = lambda i, j, k, l: P[i, k, j, l]
    mon = lambda U, V: sum(Pc(i, i, j, j) for i in U for j in V)
    pm = lambda U, V: sum(Pc(i, j, k, k) for i in U for j in U for k in V)
    mp = lambda U, V: sum(Pc(i, i, k, l) for i in U for k in V for l in V)
    pa = lambda U, V: sum(Pc(i, j, k, l) for i in U for j in U for k in V for l in V)
    pR, pY = pi[A] + pi[G], pi[C] + pi[T]
    sqR, sqY = pi[A] ** 2 + pi[G] ** 2, pi[C] ** 2 + pi[T] ** 2
    return (pR ** 2 * pY ** 2 * (mon(R, Y) + mon(Y, R))
            - pY ** 2 * sqR * (pm(R, Y) + mp(Y, R))
            - pR ** 2 * sqY * (mp(R, Y) + pm(R, R) * 0 + pm(Y, R))
            + sqR * sqY * (pa(R, Y) + pa(Y, R))) / 4


wi = wii = wiii = wiv = 0.0
for _ in range(100):
    raw = rng.random(4) + 0.2
    pi = raw / raw.sum()
    kappa = float(rng.random() * 3)
    B, lam, pR, pY = setup(pi, kappa)
    la, lb, lx, lc, ld = (float(x) for x in (rng.random(5) + 0.1))
    K1, K2, Kx, K3, K4 = (K(B, pi, kappa, lam, t) for t in (la, lb, lx, lc, ld))
    S = lambda U, p, Kv: sum(Kv[p, i] for i in U)
    D = lambda U, p, q, Kv1, Kv2: sum(Kv1[p, i] * Kv2[q, i] for i in U)
    sqR, sqY = pi[A] ** 2 + pi[G] ** 2, pi[C] ** 2 + pi[T] ** 2
    GAR = lambda p, q: pR ** 2 * D(R, p, q, K1, K3) - sqR * S(R, p, K1) * S(R, q, K3)
    GAY = lambda p, q: pY ** 2 * D(Y, p, q, K2, K4) - sqY * S(Y, p, K2) * S(Y, q, K4)
    # ★ 修正：A-分组的「镜像」不是交换结点，而是交换**两对长度**：
    #   (R,Y) 组 = G_R(t1,t3)·G_Y(t2,t4)；(Y,R) 组 = G_Y(t1,t3)·G_R(t2,t4)
    EY = lambda p, q: pY ** 2 * D(Y, p, q, K1, K3) - sqY * S(Y, p, K1) * S(Y, q, K3)
    ER = lambda p, q: pR ** 2 * D(R, p, q, K2, K4) - sqR * S(R, p, K2) * S(R, q, K4)

    rhs = sum(pi[p] * Kx[p, q] * (GAR(p, q) * GAY(p, q) + EY(p, q) * ER(p, q))
              for p in range(4) for q in range(4))
    lhs = 4 * EwA_lean(pi, B, kappa, lam, la, lb, lx, lc, ld)
    wi = max(wi, abs(rhs - lhs) / max(1e-300, abs(lhs)))

    # (ii) both nodes outside R
    for p in Y:
        for q in Y:
            wii = max(wii, abs(GAR(p, q)))
    # (iii) p in R, q outside R
    for p in R:
        for q in Y:
            pred = pR * np.exp(-lam * (1 + kappa) * la) * (1 - np.exp(-lam * lc)) * (pR * pi[p] - sqR)
            wiii = max(wiii, abs(GAR(p, q) - pred) / max(1e-300, abs(pred)))
    # (iv)
    wiv = max(wiv, abs(sum(pi[p] * (pR * pi[p] - sqR) for p in R)))

print("(i)   4*EwA = 2 ΣpΣq π_p Kx GA_R GA_Y        : max rel =", wi)
print("(ii)  p,q ∉ R => GA_R(p,q) = 0              : max abs =", wii)
print("(iii) p∈R,q∉R => GA_R = piR rm(t1)(1-sm(t3))(piR π_p - sqR) : max rel =", wiii)
print("(iv)  Σ_{p∈R} π_p (piR π_p - sqR) = 0       : max abs =", wiv)
