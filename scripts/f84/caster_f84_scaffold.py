"""Derive + verify the scaffolding identities for F84's derivation (hand-off to the formalization agent).

Kernel (F84 exact solution):  K(t) = Pi + e^{-lam t}(B - Pi) + e^{-lam(1+kap)t}(I - B)
  B_ij = 1[class(i)=class(j)] * pi_j / p_class(j),  Pi_ij = pi_j,  R={A,G}, Y={C,T}

Claim (class-sum identity):
  S_U(p,t) := sum_{i in U} K(t)_{p i}  =  pi_U + e^{-lam t} * (1[p in U] - pi_U)      for U in {R,Y}
i.e. the within-class factor e^{-lam(1+kap)t} CANCELS for class sums -- this is what makes the
collapsed side-wise events tractable.
Also: sum_{i in U} pi_i = pi_U ;  sum_{i in U} B_{p i} = 1[p in U] ;  sum_{i in U} I_{p i} = 1[p in U].
"""
import numpy as np

A, G, C, T = 0, 1, 2, 3
R, Y = {A, G}, {C, T}


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
    return B, lam, pR, pY


def Kmat(B, pi, kappa, lam, t):
    sm, rm = np.exp(-lam * t), np.exp(-lam * (1 + kappa) * t)
    Pi = np.tile(pi, (4, 1))
    return Pi + sm * (B - Pi) + rm * (np.eye(4) - B)


rng = np.random.default_rng(101)
worst_S = 0.0
for _ in range(200):
    raw = rng.random(4) + 0.15
    pi = raw / raw.sum()
    kappa = float(rng.random() * 3)
    B, lam, pR, pY = build(pi, kappa)
    t = float(rng.random() * 2)
    K = Kmat(B, pi, kappa, lam, t)
    for U, pU in ((R, pR), (Y, pY)):
        for p in range(4):
            lhs = sum(K[p, i] for i in U)
            rhs = pU + np.exp(-lam * t) * ((1.0 if p in U else 0.0) - pU)
            worst_S = max(worst_S, abs(lhs - rhs))
print("S_U(p,t) = pi_U + e^{-lam t}(1[p in U] - pi_U):  worst |lhs-rhs| =", worst_S)

# also: row sums of K are 1, and sum over a class of the *second* factor
worst_row = 0.0
for _ in range(50):
    raw = rng.random(4) + 0.15
    pi = raw / raw.sum()
    kappa = float(rng.random() * 3)
    B, lam, pR, pY = build(pi, kappa)
    K = Kmat(B, pi, kappa, lam, 0.7)
    worst_row = max(worst_row, np.abs(K.sum(axis=1) - 1).max())
print("K row sums = 1:  worst =", worst_row)

# and the 'monomorphic' quantities M_U(p) = sum_{i in U} K(la)_{p i} K(lb)_{p i} -- no closed form claimed,
# but they are exactly the rank-one-ish quantities the agent must compute.
print()
print("=> the class-sum identity is exact, so every 'pure U' side contributes")
print("   S_U(p,l) = pi_U + e^{-lam l}(1[p in U] - pi_U)  (a 2-valued function of p) -- very cheap in Lean.")
