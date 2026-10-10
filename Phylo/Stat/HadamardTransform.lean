/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.JukesCantor

/-!
# `Phylo.Stat.HadamardTransform` —— I3：Evans–Speed / Hadamard 变换

## 文献依据（篇名 + 行号；行号指 `references/md/` 下的文本文件）

* **S. N. Evans, T. P. Speed, *Invariants of some probability models used in phylogenetic
  inference*（1993）, `references/md/EvansSpeed1993_InvariantsProbabilityModels.md`（共 1113 行）**：
  * **283–350 行（§3 "Some discrete Fourier analysis"）**：有限交换群的对偶群、特征标、
    **Fourier 变换** `f̂(χ) = Σ_g f(g) χ(g)` 与 **Fourier 逆公式**；**326–345 行**：
    `f ⋆ g` 的 Fourier 变换 `= f̂ · ĝ`（**卷积 ↦ 乘法**）；
  * **376–420 行（§4, Lemma 4.1–4.3）**：K3P / K2P / **JC** 的 `f̂(χ)` 取值 ——
    JC 的 `f̂` 只在单位特征标处为 `1`，其余为 `e^{−4t/3}`（正是本文件 `HadP_diag` 的内容）；
  * **421–460 行（§5 "Another description of the models"）**：把模型写成**加性随机效应**
    `Y = D Z`；**431–440 行**「Identify the four bases {A,G,C,T} with the elements of the
    **Klein four-group** `Z₂ ⊕ Z₂`」；
  * **532–650 行（§6, Theorem 6.1 / 6.2）**：由 Fourier 坐标构造全部不变量的一般方法。
* **B. Sturmfels, S. Sullivant, *Toric ideals of phylogenetic invariants*,
  `references/md/SturmfelsSullivant2005_ToricIdealsPhyloInvariants.md`（共 2831 行）**：
  * **480–500 行（Lemma 4）**：`(b)` **Fourier 变换把卷积变成乘法**（= 本文件 `HadK_conv`）；
    `(c)` 常函数 `1` 的 Fourier 变换是 `|G|·δ_1`（= 本文件 `H_row_sum`/`H_col_sum`）；
  * **507–520 行**：group based model 是 **toric** variety（Fourier 坐标下是单项式参数化）；
  * **628–654 行（Theorem 6, Evans–Speed）**：`q(χ) = π̂(∑χ) · ∏_v f̂^{(v)}(∑_{l∈Λ(v)}χ_l)`
    —— 本文件的缺口 `evansSpeed_general_gap`。
* **M. Casanellas, J. Fernández-Sánchez (2011) §5.5「Jukes–Cantor model」**
  （`references/md/CasanellasFernandezSanchez2011_RelevantInvariants.md`，**2980–3180 行**）：
  `S4` 的等变矩阵 = 「对角 `a`、非对角 `b`」 = JC 转移矩阵；**3179–3227 行**列出 JC 的
  12 条不变量。
* **Alvarez-Gonzalez et al. (2024)**（`references/md/AlvarezGonzalezEtAl2024_HadamardConjugationClosestTreeProofs.md`）：
  补件 —— 「Hadamard 共轭」这一术语在现代系统发育文献中的用法（本文件只作旁证）。

## 本文件做的事

库内 `Phylo.JukesCantor` 已有 **Fourier 坐标** `q t i j = 1 − 4·pDiff t i j / 3`
（`q_eq_exp_pathLen : q t i j = e (pathLen t i j)`），但那里它只是「JC 修正项」。
本文件把它**升格为 Hadamard 变换的代数陈述**：

1. **显式 `4 × 4` Hadamard 矩阵** `H`（Klein 四元群 `Z₂×Z₂` 的特征标表；行/列按
   `A,C,G,T = 0,1,2,3` 排列，与 `Phylo.LakeInvariants` 的编码一致）：
   `H_symm`（对称）、`H_mul_self`（`H * H = 4 • 1`）、`H_row_sum` / `H_col_sum`
   （每行/列和 `= 4·[指标 = 0]`）、`H_det_sq`（`(det H)² = 256`；Python 精确算出 `det H = 16`）；
2. **反例检查（★B）** `Hbad_sq_ne_four`：只把 `H` 的 `(1,1)` 处 `−1` 改成 `1`，
   `H² = 4·1` **就不成立** —— 「Hadamard 条件」不是写法上的想当然；
3. **Hadamard 共轭** `HadK d = H · K(d) · H`（`K d = Phylo.JC.kernel d`）的**闭式**
   `HadK_apply`：`(HadK d) u v = if u = v then (if u = 0 then 4 else 4·e d) else 0`
   —— **JC 的 Hadamard 共轭完全对角**，非平凡对角元 `4·e d`；
4. ★★★ **Fourier 把卷积变成乘法**（ES §3 326–345 行；SS2005 Lemma 4(b)）：
   `HadK_conv : HadK s * HadK u = 4 • HadK (s + u)`（原始形式，含 `4 = |G|`）；
   归一化形式 `HadP_conv : HadP s * HadP u = HadP (s + u)`；
   迭代版 `chainProd_eq`：**`n+1` 段路径**时 `chainProd n d = HadP (∑ k, d k)`；
5. ★★★ **`q` 就是非平凡 Hadamard 系数**：`HadP_apply` / `HadP_diag` / `q_eq_hadamard` ——
   归一化共轭 `HadP d = H · P(d) · H`（`P d = (1/4)·K d`，均匀根分布）满足
   `HadP (pathLen t i j) u u = JC.q t i j`（`u ≠ 0`）；
6. **缺口** `evansSpeed_general_gap`：一般 `m` 片叶（含**分支顶点**）的 Evans–Speed
   Theorem 6。

## 反例检查（★B）

* **`H² = 4I` 真的对「我写的」`H` 成立吗？** 已证（`H_mul_self`，4 个对角元各自是
  `1+1+1+1 = 4`）；并且 `Hbad_sq_ne_four` 证明**并非**任何 ±1 矩阵都满足。
* **`HadK` 在 `(0,0)` 处的 `4` 是否只靠「`4·off + e = 1`」？** 是 —— 展开后是
  `16·off(d) + 4·e(d) = 4·(4·off(d) + e(d))`，等价于 `Phylo.JukesCantor` 的
  `four_off_add`（该文件头记录了「写成 `1/4 + [a=b]·c` 是**错的**」这一勘误，本文件沿用
  正确的 `trans`）。
* **`HadK_conv` 的因子 `4` 是 `|G|` 而不是笔误？** Python 脚本
  `scripts/msc/w11b_i3_i6_i7_check.py` 用 `Z[x]`（`x = e^{−4t/3}`）精确算出
  `H κ(t) H = diag(4, 4x, 4x, 4x)`，故 `Hκ(s)H · Hκ(u)H = 16·diag(1, x^{s+u}, …) = 4·Hκ(s+u)H`。
* **`H * H` 会不会被误当成逐点乘法？** `H : Matrix (Fin 4) (Fin 4) ℝ`；
  `Fin 4 → Fin 4 → ℝ` 上另有逐点的 `Pi.instMul`，故本文件的证明一律**不展开**
  `Kmat`/`Pm`，只用 `Kmat_apply` 逐项重写。

## 诚实边界

* 本文件**只做 2 分类群（单条边）与「`n+1` 条边串联」**的 Hadamard/Fourier 陈述 ——
  即 `Fin 4` 上能显式算清的**全部**内容。
* **未做**：一般 `m` 片叶、含**分支顶点**的 Evans–Speed Theorem 6 ——
  见 `evansSpeed_general_gap`。缺的是「`G^m` 上的 `m` 重 Fourier 变换 +
  `m` 重重指标」与一般树 GMM 层（= `InvariantsRank.TreeMarkovFactorGap` 的同一欠账）。
* **未做**：Casanellas §5.5 的 `T^{fe}(ψ)` 分块、`S0,…,S4` 的秩条件
  （那条路线属 `Phylo.JukesCantor` / `Phylo.LakeInvariants`）。
* 本文件**不引入**新的 Mathlib import（只用 `Phylo.JukesCantor` 自带的依赖）。
* 无 `sorry`、无 `axiom`、无 `native_decide`。
-/

noncomputable section

namespace Phylo.Stat.HadamardTransform

open Matrix

/-! ## 1. ★★★ 显式 `4 × 4` Hadamard 矩阵（Klein 四元群的特征标表） -/

/-- ★★★ **Klein 四元群 `Z₂ × Z₂` 的特征标表**（`4 × 4` Hadamard 矩阵）。

行/列都按 `A = (0,0) ↦ 0`、`C = (1,0) ↦ 1`、`G = (0,1) ↦ 2`、`T = (1,1) ↦ 3` 排列
（与 `Phylo.LakeInvariants` 的编码一致）；`H u g = (−1)^{u₁g₁+u₂g₂}`。 -/
def H : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![1, 1, 1, 1], ![1, -1, 1, -1], ![1, 1, -1, -1], ![1, -1, -1, 1]]

@[simp] theorem H_00 : H 0 0 = 1 := rfl
@[simp] theorem H_01 : H 0 1 = 1 := rfl
@[simp] theorem H_02 : H 0 2 = 1 := rfl
@[simp] theorem H_03 : H 0 3 = 1 := rfl
@[simp] theorem H_10 : H 1 0 = 1 := rfl
@[simp] theorem H_11 : H 1 1 = -1 := rfl
@[simp] theorem H_12 : H 1 2 = 1 := rfl
@[simp] theorem H_13 : H 1 3 = -1 := rfl
@[simp] theorem H_20 : H 2 0 = 1 := rfl
@[simp] theorem H_21 : H 2 1 = 1 := rfl
@[simp] theorem H_22 : H 2 2 = -1 := rfl
@[simp] theorem H_23 : H 2 3 = -1 := rfl
@[simp] theorem H_30 : H 3 0 = 1 := rfl
@[simp] theorem H_31 : H 3 1 = -1 := rfl
@[simp] theorem H_32 : H 3 2 = -1 := rfl
@[simp] theorem H_33 : H 3 3 = 1 := rfl

/-- ★ `H` **对称**（Klein 四元群上 `u₁g₁ + u₂g₂` 对 `u, g` 对称）。 -/
theorem H_symm : Hᵀ = H := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

/-- ★★ **`H * H = 4 • 1`**（Hadamard 矩阵的定义性质；`4 = |G|`）。 -/
theorem H_mul_self : H * H = 4 • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.smul_apply] <;>
    norm_num

/-- ★★ **每行之和** `∑_g H u g = 4 · [u = 0]`（ES §3 Lemma 4(c) / SS2005 Lemma 4(c)）。 -/
theorem H_row_sum (u : Fin 4) :
    (∑ g : Fin 4, H u g) = if u = 0 then 4 else 0 := by
  fin_cases u <;> norm_num [Fin.sum_univ_four]

/-- ★★ **每列之和** `∑_u H u g = 4 · [g = 0]`（`H` 对称，故与行和同值）。 -/
theorem H_col_sum (g : Fin 4) :
    (∑ u : Fin 4, H u g) = if g = 0 then 4 else 0 := by
  fin_cases g <;> norm_num [Fin.sum_univ_four]

/-- ★ **`H * H` 的对角形式**（`H_mul_self` 的等价写法，便于取行列式）。 -/
theorem H_mul_self_diagonal : H * H = Matrix.diagonal fun _ : Fin 4 => (4 : ℝ) := by
  rw [H_mul_self]
  ext i j
  rw [Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
  by_cases h : i = j <;> simp [h]

/-- ★ **`(det H)² = 256`**（等价地 `|det H| = 16`；Python 脚本精确算出 `det H = 16`）。 -/
theorem H_det_sq : H.det * H.det = 256 := by
  rw [← Matrix.det_mul, H_mul_self_diagonal, Matrix.det_diagonal]
  norm_num

/-! ### 1.1 ★B 反例检查：Hadamard 条件不是想当然 -/

/-- **故意写错的「Hadamard 矩阵」**：把 `H` 在 `(1,1)` 处的 `−1` 改成 `1`。 -/
def Hbad : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => H i j + if (i, j) = (1, 1) then 2 else 0

/-- ★★ **反例检查**：`Hbad * Hbad ≠ 4 • 1`。
（具体地 `(Hbad * Hbad) 1 2 = 2 ≠ 0`。）—— 这说明 `H_mul_self` **不是**任意 ±1 矩阵的
平凡性质，`H` 的符号排布是**真的**条件。 -/
theorem Hbad_sq_ne_four : Hbad * Hbad ≠ 4 • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  intro h
  have h12 := congrFun (congrFun h 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.smul_apply, Hbad, Matrix.of_apply] at h12

/-! ## 2. Hadamard 共轭与「Fourier 把卷积变成乘法」 -/

/-- **JC 转移矩阵作为矩阵**（与 `Phylo.JC.kernel` 逐项相同）。 -/
def Kmat (d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := JC.kernel d

@[simp] theorem Kmat_apply (d : ℝ) (i j : Fin 4) : Kmat d i j = JC.kernel d i j := rfl

/-- **均匀根分布下的二分类群分布**：`P d = (1/4) • K d`。 -/
def Pm (d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := (1 / 4 : ℝ) • Kmat d

/-- ★★ **Hadamard 共轭**（Klein 四元群上）：`HadK d = H · K(d) · H`。 -/
def HadK (d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := H * Kmat d * H

/-- ★★ **归一化的 Hadamard 共轭**（对分布 `P d = (1/4)·K d`）：`HadP d = H · P(d) · H`。 -/
def HadP (d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := H * Pm d * H

/-- ★★★ **JC 的 Hadamard 共轭闭式**：

`(HadK d) u v = if u = v then (if u = 0 then 4 else 4 · e d) else 0`，

即 **`HadK d` 是对角矩阵**：平凡特征标处为 `4`（`= |G|`）、三个非平凡特征标处为 `4·e d`。

（展开后 `(HadK d) u v = 16·off(d)·[u=0][v=0] + 4·e(d)·[u=v]`，其中用到
`4·off(d) + e(d) = 1`，即 `Phylo.JC.four_off_add`。） -/
theorem HadK_apply (d : ℝ) (u v : Fin 4) :
    HadK d u v = if u = v then (if u = 0 then 4 else 4 * JC.e d) else 0 := by
  show (H * Kmat d * H) u v = _
  fin_cases u <;> fin_cases v <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_four, Kmat_apply, JC.kernel_apply, JC.ind,
      JC.off] <;>
    norm_num <;> ring

/-- ★★★ **Fourier/Hadamard 变换把卷积变成乘法**（ES 1993 §3, 326–345 行；
SS2005 **Lemma 4(b)**, 480–500 行）：

`HadK s * HadK u = 4 • HadK (s + u)`。

左端 = 两条边上「Hadamard 变换的乘积」，右端 = **合起来的边**（长度 `s + u`）；
`4 = |G|` 就是 Fourier 逆变换的归一化因子。结合 `Phylo.JC.kernel_conv`
（`K s * K u = K (s+u)`），这正是「**卷积 ↦ 乘法**」在 JC / Klein 四元群上的显式形式。 -/
theorem HadK_conv (s u : ℝ) : HadK s * HadK u = 4 • HadK (s + u) := by
  have hκ : Kmat (s + u) = Kmat s * Kmat u := by
    ext i j
    show JC.kernel (s + u) i j = (Kmat s * Kmat u) i j
    rw [Matrix.mul_apply]
    exact (JC.kernel_conv s u i j).symm
  have key : (H * Kmat s * H) * (H * Kmat u * H)
      = 4 • (H * (Kmat s * Kmat u) * H) := by
    calc (H * Kmat s * H) * (H * Kmat u * H)
        = H * Kmat s * (H * H) * Kmat u * H := by noncomm_ring
      _ = H * Kmat s * (4 • (1 : Matrix (Fin 4) (Fin 4) ℝ)) * Kmat u * H := by
            rw [H_mul_self]
      _ = 4 • (H * (Kmat s * Kmat u) * H) := by
            rw [mul_smul_comm, mul_one, smul_mul_assoc, smul_mul_assoc,
              show (H * Kmat s * Kmat u) * H = H * (Kmat s * Kmat u) * H from by noncomm_ring]
  show (H * Kmat s * H) * (H * Kmat u * H) = 4 • (H * Kmat (s + u) * H)
  rw [hκ, key]

/-! ## 3. ★★★ `q` 就是非平凡的 Hadamard 系数 -/

/-- ★ **`HadP d = (1/4) • HadK d`**（因为 `P d = (1/4) • K d`）。 -/
theorem HadP_eq_smul (d : ℝ) : HadP d = (1 / 4 : ℝ) • HadK d := by
  rw [HadP, Pm, HadK, mul_smul_comm, smul_mul_assoc]

/-- ★★★ **归一化 Hadamard 共轭的闭式**：
`(HadP d) u v = if u = v then (if u = 0 then 1 else JC.e d) else 0`。

这就是 ES 1993 §4 Lemma 4.3 里「JC 的 `f̂(χ)` 在单位特征标处为 `1`、
在非平凡特征标处为 `e^{−4d/3}`」这句话的显式陈述。 -/
theorem HadP_apply (d : ℝ) (u v : Fin 4) :
    HadP d u v = if u = v then (if u = 0 then 1 else JC.e d) else 0 := by
  rw [HadP_eq_smul, Matrix.smul_apply, HadK_apply]
  split_ifs with h1 h2
  · norm_num
  · ring
  · ring

/-- ★★ **非平凡对角元**：`HadP d u u = JC.e d`（`u ≠ 0`）。 -/
theorem HadP_diag (d : ℝ) (u : Fin 4) (hu : u ≠ 0) : HadP d u u = JC.e d := by
  rw [HadP_apply]
  simp [hu]

/-- ★★★ **`Phylo.JukesCantor` 的 Fourier 坐标 `q` = 非平凡 Hadamard 系数**：

`(HadP (pathLen t i j)) u u = JC.q t i j`（`u ≠ 0`）。

即：`q t i j = 1 − 4·pDiff t i j / 3` **不是**人为的修正项，而是
**JC 二分类群分布的 Hadamard 共轭在非平凡特征标处的取值**。 -/
theorem q_eq_hadamard (t : Fin 5 → ℝ) (i j : Fin 4) (u : Fin 4) (hu : u ≠ 0) :
    HadP (JC.pathLen t i j) u u = JC.q t i j := by
  rw [HadP_diag _ _ hu, JC.q_eq_exp_pathLen]

/-- ★★★ **归一化形式**（对 `HadP`，无 `4` 因子）：`HadP s * HadP u = HadP (s + u)`。

这是「**Fourier 变换把卷积变成乘法**」最干净的形式（常数 `4 = |G|` 已被归一化吸收）。 -/
theorem HadP_conv (s u : ℝ) : HadP s * HadP u = HadP (s + u) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_four, HadP_apply] <;>
    norm_num <;>
    try rw [JC.e_mul]

/-- ★★ **`n+1` 段路径的有序乘积**（矩阵乘法只构成 `Monoid` 而非 `CommMonoid`，
故用显式递归定义而不是 `Finset.prod`）。 -/
def chainProd : (n : ℕ) → (Fin (n + 1) → ℝ) → Matrix (Fin 4) (Fin 4) ℝ
  | 0, d => HadP (d 0)
  | n + 1, d => chainProd n (fun k => d (Fin.castSucc k)) * HadP (d (Fin.last (n + 1)))

/-- ★★ **`n+1` 段路径的 Hadamard 变换**：`chainProd n d = HadP (∑ k, d k)`。

即：**`n+1` 段路径的卷积在 Fourier/Hadamard 坐标下就是逐段的乘积**，而乘积恰好又只是
「总长度」的变换 —— 这是 JC 路径可加性（`Phylo.JC.pathLen_identity` 那一族恒等式）的
Fourier 版本。 -/
theorem chainProd_eq (n : ℕ) :
    ∀ d : Fin (n + 1) → ℝ, chainProd n d = HadP (∑ k, d k) := by
  induction n with
  | zero =>
    intro d
    show HadP (d 0) = HadP (∑ k : Fin 1, d k)
    rw [Fin.sum_univ_one]
  | succ m ih =>
    intro d
    show chainProd m (fun k => d (Fin.castSucc k)) * HadP (d (Fin.last (m + 1)))
      = HadP (∑ k : Fin (m + 2), d k)
    rw [ih (fun k => d (Fin.castSucc k)), HadP_conv]
    conv_rhs => rw [Fin.sum_univ_castSucc]

/-! ## 4. 诚实边界（显式缺口） -/

/-- **缺口（I3 的核心）**：**一般 Evans–Speed 定理**（Sturmfels–Sullivant 2005,
**Theorem 6, 628–654 行**；Evans–Speed 1993 §6, 532–650 行）。

设立：有限交换群 `G`（加法）、特征标 `χ i : G → ℝ`（`χ 0 = 1`、`χ (a+b) = χ a · χ b`）；
`m` 片叶的 **claw tree** `K₁,ₘ`：根分布 `π`、第 `i` 片叶的边分布 `f i`，联合分布
`p g = ∑_h π h · ∏_i f i (g i − h)`，Fourier 坐标 `q χ = ∑_g p g · ∏_i χ i (g i)`。

**断言（公式 (10)、(11)）**：

`q χ = (∑_h π h · ∏_i χ i h) · ∏_i (∑_a f i a · χ i a)`

（右端即 `π̂(∏χ) · ∏_i f̂_i(χ_i)`）。

**本文件已证** `G` 上「无分支」的全部内容（`HadK_apply`/`HadK_conv`/`chainProd_eq`/
`HadP_diag`：`Fin 4` 上显式算清的 Hadamard 共轭与「卷积 ↦ 乘法」）。
**未证** `m ≥ 2` 的**分支**情形，需要的器材是：

* `Fin m → G` 上「逐点平移」的等价 `g ↦ g + h` 与 `Finset.prod_univ_sum` 型的
  「乘积 ↦ 多重和」重排（`m` 重重指标）；
* 一般树 GMM 的 site-pattern 概率（库内 `Phylo.JC.patternProb` 只有 4 叶固定拓扑）——
  与 `Phylo.Stat.InvariantsRank.TreeMarkovFactorGap` 是同一欠账。

因此如实落缺口，不把 `m = 1` 的情形冒充成一般定理。 -/
def evansSpeed_general_gap (m : ℕ) : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (π : G → ℝ) (f : Fin m → G → ℝ) (χ : Fin m → G → ℝ),
    (∀ i, χ i 0 = 1) →
    (∀ i a b, χ i (a + b) = χ i a * χ i b) →
    (∑ g : Fin m → G, (∑ h : G, π h * ∏ i, f i (g i - h)) * ∏ i, χ i (g i))
      = (∑ h : G, π h * ∏ i, χ i h) * ∏ i, (∑ a : G, f i a * χ i a)

/-- 缺口的**假设非空真**：特征标假设（`χ 0 = 1`、`χ (a+b) = χ a · χ b`）**可满足且非平凡**
（在 `ℤ` 上取 `χ a = (−1)^a`）。故 `evansSpeed_general_gap` 的假设不是空条件。 -/
theorem evansSpeed_gap_hypotheses_satisfiable :
    ∃ χ : Fin 1 → ℤ → ℝ,
      (∀ i, χ i 0 = 1) ∧ (∀ i a b, χ i (a + b) = χ i a * χ i b) := by
  refine ⟨fun _ a => (-1 : ℝ) ^ a, ?_, ?_⟩
  · intro i
    show (-1 : ℝ) ^ (0 : ℤ) = 1
    exact zpow_zero (-1 : ℝ)
  · intro i a b
    show (-1 : ℝ) ^ (a + b) = (-1 : ℝ) ^ a * (-1 : ℝ) ^ b
    exact zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0) a b

end Phylo.Stat.HadamardTransform
