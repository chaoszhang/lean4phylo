/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# `Phylo.Algorithm.NJ` —— 邻接法（Neighbor Joining）的代数层

`CONCEPTS.md` §5 的 M5：NJ（Saitou–Nei 1987 / Studier–Keppler 1988）。

**NJ 正确性定理**：可加距离矩阵下，最小化 Q-判据的那对 taxa 必是真树的一颗樱桃。

本文件给**纯度量表述**的完整代数骨架（不用加权树对象）：

* `Dissimilarity` / `FourPoint`（四点条件）· `Q`（Q-判据）· `ell` / `z` / `rho`（路径距离泛函）
* **★ `Q_eq_neg_two_ell`**：`Q = -2·(δ + ℓ)` —— 把「最小化 Q」翻译成「最大化 `z = δ + ℓ`」
* **★ `two_mul_z`**：`2z(i,j) = S(i) + S(j) + (2-n)·δ(i,j)` —— 把所有 `z` 不等式化成线性不等式
* **★ `z_hinge`**：`z(a,b)+z(i,j) − (z(a,i)+z(b,j)) = ((2-n)/2)·(P − Q₁)` —— 门控恒等式
* **★ `four_point_z_iff`**：`n ≥ 4` 时「四点和 `P` 最小」⟺「`z` 的和最大」

## ⚠️ 形式化缺口（本文件的诚实边界）

`nj_cherry` 依赖 **`MaxZCherryCore`**。

> ✦ **定性（重要，勿误传）**：这**不是学术开放问题**。NJ 的正确性**早已被证明**：
> **Studier–Keppler (1988)** 给出首个正确证明（并指出 Saitou–Nei 1987 原始证明有误），
> **Weller (2023)** 用 *leaf-status* 给出极简重证，Mihaescu–Levy–Pachter (2009) 亦有。
> 本库把它留作缺口，**只是形式化路径的选择问题**，不是数学未解。

**缺口究竟在哪**：

> 「`z` 的最大性是**全局**的（涉及所有行和 `S`），而 quartet 分裂是**局部**的。」
> 上述标准证明都显式使用「实现树 + 中心节点 + 沿路径 leaf-status 单调 + 子树内必存在樱桃」
> —— 即需要 **Buneman 存在性（四点条件 ⟹ 存在实现树）** 这个**本库尚未形式化**的前置。
> 在**不引入树对象**的纯度量设定下，我们尚未找到可直接形式化的干净论证。

故本文件把 `MaxZCherryCore` 作为**显式假设**（**不使用 `sorry`** —— 这样库里依然零 `sorry`），
`nj_cherry` 表述为「**假设硬核 ⟹ NJ 樱桃引理**」，是诚实且可用的形式。

**解锁路径（明确、已知可行）**：形式化 **Buneman 存在性**（四点条件 ⟹ 存在实现树，
见 `HANDOVER.md` 的 T3），即可照抄 Weller 的 leaf-status 论证。
`Phylo/Dendrogram.lean` 的「超度量 ⟹ 镶嵌族 ⟹ 树」管线已经铺好，是**现成的模板**。
**解锁 Buneman，即解锁 NJ 硬核。**
-/

open Finset
open scoped BigOperators

noncomputable section

namespace NJ

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- 相异度矩阵：对称、零对角。**不**要求三角不等式。 -/
structure Dissimilarity (X : Type*) where
  val : X → X → ℝ
  symm : ∀ i j, val i j = val j i
  diag : ∀ i, val i i = 0

namespace Dissimilarity

variable (δ : Dissimilarity X)

/-- **四点条件**（Buneman，等价于「可加」）：任意四点的三对和中，最大者至少出现两次。 -/
def FourPoint : Prop :=
  ∀ i j k l : X,
    δ.val i j + δ.val k l ≤ δ.val i k + δ.val j l ∨
    δ.val i j + δ.val k l ≤ δ.val i l + δ.val j k

/-- **樱桃判据**（纯用 δ 表述，不引用树）：对任意 `k,l` 异于 `a,b`，
`δ(a,b)+δ(k,l)` 同时 ≤ 两个「交叉和」。 -/
def IsCherry (a b : X) : Prop :=
  a ≠ b ∧
  ∀ k l : X, k ≠ a → k ≠ b → l ≠ a → l ≠ b →
      δ.val a b + δ.val k l ≤ δ.val a k + δ.val b l ∧
      δ.val a b + δ.val k l ≤ δ.val a l + δ.val b k

/-- 行和 `S(i) = Σ_k δ(i,k)`。 -/
def S (i : X) : ℝ := ∑ k, δ.val i k

/-- **Q-判据**（Studier–Keppler）：`Q(i,j) = (n-2)δ(i,j) − S(i) − S(j)`。 -/
def Q (i j : X) : ℝ :=
  ((Fintype.card X : ℝ) - 2) * δ.val i j - (∑ k, δ.val i k) - (∑ k, δ.val j k)

/-- **路径距离泛函** `ℓ(i,j) = ½ Σ_k (δ(i,k) + δ(j,k) − δ(i,j))`。 -/
def ell (i j : X) : ℝ :=
  (∑ k, (δ.val i k + δ.val j k - δ.val i j)) / 2

/-- **待最大化泛函** `z(i,j) = δ(i,j) + ℓ(i,j)`。由 `Q_eq_neg_two_ell`，最大化 z ⟺ 最小化 Q。 -/
def z (i j : X) : ℝ := δ.val i j + δ.ell i j

/-- **点到路径的形式距离** `ρ(x;i,j) = (δ(x,i)+δ(x,j)−δ(i,j))/2`。

树度量中即 x 到 i-j 路径的距离；`rho_nonneg` 表明四点条件下它非负。 -/
def rho (x i j : X) : ℝ := (δ.val x i + δ.val x j - δ.val i j) / 2

/-! ## 基础引理 -/

omit [Fintype X] [DecidableEq X] in
/-- **四点条件 ⟹ 三角不等式**（取两点重合的实例）。 -/
theorem triangle (hfp : δ.FourPoint) (a k l : X) :
    δ.val k l ≤ δ.val a k + δ.val a l := by
  have h := hfp a a k l
  rw [δ.diag a, zero_add] at h
  rcases h with h | h <;> linarith

omit [Fintype X] [DecidableEq X] in
/-- 不存在「`δ(i,j)+δ(k,l)` 严格大于另两个和」的情形。 -/
theorem fourpoint_not_unique_max (hfp : δ.FourPoint) (i j k l : X) :
    ¬ (δ.val i k + δ.val j l < δ.val i j + δ.val k l ∧
       δ.val i l + δ.val j k < δ.val i j + δ.val k l) := by
  intro h
  rcases hfp i j k l with h' | h' <;> linarith [h.1, h.2]

omit [Fintype X] [DecidableEq X] in
/-- **四点条件的实质**：若某项严格最小，则另两项相等。 -/
theorem fourpoint_eq_of_lt (hfp : δ.FourPoint) (i j k l : X)
    (h : (δ.val i j + δ.val k l < δ.val i k + δ.val j l) ∧
         (δ.val i j + δ.val k l < δ.val i l + δ.val j k)) :
    δ.val i k + δ.val j l = δ.val i l + δ.val j k := by
  have hA : δ.val i k + δ.val j l ≤ δ.val i l + δ.val j k := by
    rcases hfp i k j l with h' | h'
    · linarith [h.1]
    · linarith [δ.symm k j]
  have hB : δ.val i l + δ.val j k ≤ δ.val i k + δ.val j l := by
    rcases hfp i l j k with h' | h'
    · linarith [h.2, δ.symm l k]
    · linarith [δ.symm l j]
  linarith

omit [Fintype X] [DecidableEq X] in
/-- `ρ(x;i,j) ≥ 0`（由 `triangle`）。 -/
theorem rho_nonneg (hfp : δ.FourPoint) (x i j : X) : 0 ≤ δ.rho x i j := by
  have h := triangle δ hfp x i j
  simp only [rho]
  linarith

omit [DecidableEq X] in
/-- `ℓ(i,j) = Σ_x ρ(x;i,j)` —— 代数定义与几何定义的对齐。 -/
theorem ell_eq_sum_rho (i j : X) : δ.ell i j = ∑ k, δ.rho k i j := by
  simp only [ell, rho]
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun k _ => by rw [δ.symm k i, δ.symm k j]

omit [DecidableEq X] in
/-- `δ` 在 `ell` 中可交换。 -/
theorem ell_comm (i j : X) : δ.ell i j = δ.ell j i := by
  simp only [ell]
  rw [δ.symm i j]
  exact congrArg (· / 2) (Finset.sum_congr rfl fun k _ => by rw [add_comm])

omit [DecidableEq X] in
/-- **`z` 对称**。 -/
theorem z_comm (i j : X) : δ.z i j = δ.z j i := by
  simp only [z]
  rw [δ.symm i j, ell_comm δ i j]

/-! ## 引理 1：纯代数恒等式 -/

omit [DecidableEq X] in
/-- `Q(i,j) = -2·z(i,j)`。 -/
theorem Q_eq_neg_two_ell (i j : X) :
    δ.Q i j = -2 * (δ.val i j + δ.ell i j) := by
  simp only [Q, ell]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
  simp only [nsmul_eq_mul]
  ring

omit [DecidableEq X] in
/-- `Q(i,j) = -2·z(i,j)`。 -/
theorem Q_eq_neg_two_z (i j : X) : δ.Q i j = -2 * δ.z i j :=
  Q_eq_neg_two_ell δ i j

omit [DecidableEq X] in
/-- **核心恒等式**：`2z(i,j) = S(i) + S(j) + (2-n)·δ(i,j)`。 -/
theorem two_mul_z (i j : X) :
    2 * δ.z i j = δ.S i + δ.S j + (2 - (Fintype.card X : ℝ)) * δ.val i j := by
  have hsum : (∑ k, (δ.val i k + δ.val j k - δ.val i j))
      = δ.S i + δ.S j - (Fintype.card X : ℝ) * δ.val i j := by
    simp only [S]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
    simp only [nsmul_eq_mul]
  simp only [z, ell, hsum]
  ring

omit [DecidableEq X] in
/-- ★★ **Weller 2023 Observation 2**（`Weller2023_..md:143`；此处限制在**标签**上，2026-10-08 补登记）：

路径的叶状态等于两端**叶状态**（行和 `S`）的平均减去 `|X|·δ(i,j)/2`：
`ℓ(i,j) = ½ (S(i) + S(j) − |X| · δ(i,j))`。

✦ **接口说明**（`HANDOVER.md` §4.2 T0.3 的对齐表）：`δ.S i` **就是** Weller 的叶状态
`ℓ_T(i) = Σ_{x∈L(T)} d(i,x)`（`x = i` 那一项为 `0`，故「对叶求和」与「对标签求和」一致）；
`δ.ell i j` **就是** `ℓ_T(p) = Σ_{x∈L(T)} d(x,p)`（`p` = `i`-`j` 路径）。

（原式此前只以 `two_mul_z` **证明内部**的步骤 `hsum` 形式存在 —— 本定理把它**提出并命名**，
以便 T0.3 的转录显式引用；两处各留一份同型证明，换取不动既有证明。） -/
theorem ell_eq_S (i j : X) :
    δ.ell i j = (δ.S i + δ.S j - (Fintype.card X : ℝ) * δ.val i j) / 2 := by
  have hsum : (∑ k, (δ.val i k + δ.val j k - δ.val i j))
      = δ.S i + δ.S j - (Fintype.card X : ℝ) * δ.val i j := by
    simp only [S]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
    simp only [nsmul_eq_mul]
  simp only [ell, hsum]

omit [DecidableEq X] in
/-- ★★ **`z` 的闭形式**（Weller 2023 的 eq (3)，`Weller2023_..md:304–324`；限制在标签上）：

`z(i,j) = ½ (S(i) + S(j) − (|X|−2)·δ(i,j))`。

即 `two_mul_z` 两边同除 `2`；单列出来是为了让 T0.3 的转录能直接引用「**叶状态形式**」
（Weller 的 `z` 是「路径叶状态 + 路径长度」，本式把它换成纯 `S`/`δ` 的组合）。 -/
theorem z_eq_S (i j : X) :
    δ.z i j = (δ.S i + δ.S j - ((Fintype.card X : ℝ) - 2) * δ.val i j) / 2 := by
  have h := two_mul_z δ i j
  rw [show δ.z i j = 2 * δ.z i j / 2 by ring, h]
  ring

omit [DecidableEq X] in
/-- **门控恒等式**：`z(a,b)+z(i,j) − (z(a,i)+z(b,j)) = ((2−n)/2)·(P − Q₁)`，其中
`P = δ(a,b)+δ(i,j)`、`Q₁ = δ(a,i)+δ(b,j)`。

因 `n ≥ 4` 时 `(2−n)/2 < 0`，故 `P ≤ Q₁` **等价于** `z(a,b)+z(i,j) ≥ z(a,i)+z(b,j)`
—— 这是把「z 的最大性」翻译成「四点和的不等式」的桥梁。 -/
theorem z_hinge (i j a b : X) :
    δ.z a b + δ.z i j - (δ.z a i + δ.z b j)
      = ((2 - (Fintype.card X : ℝ)) / 2)
          * (δ.val a b + δ.val i j - (δ.val a i + δ.val b j)) := by
  have h1 := two_mul_z δ a b
  have h2 := two_mul_z δ i j
  have h3 := two_mul_z δ a i
  have h4 := two_mul_z δ b j
  linarith

/-! ## 引理 2：★ 四点上的「z-分裂等价」 -/

omit [DecidableEq X] in
/-- ★ **四点上的 z-分裂等价**（`n ≥ 4`）：

「四点和 `P = δ(a,b)+δ(i,j)` 同时 ≤ 两个交叉和」**⟺**「配对 `{a,b},{i,j}` 使 `z` 的和最大」。

这是 `z_hinge` 的直接推论（系数 `(2−n)/2 < 0` 使不等号反向），
也是「z 最大性」与「quartet 分裂」之间的**精确字典** —— NJ 硬核证明的代数骨架。 -/
theorem four_point_z_iff (hcard : 4 ≤ Fintype.card X) (a b i j : X) :
    (δ.val a b + δ.val i j ≤ δ.val a i + δ.val b j ∧
     δ.val a b + δ.val i j ≤ δ.val a j + δ.val b i) ↔
    (δ.z a i + δ.z b j ≤ δ.z a b + δ.z i j ∧
     δ.z a j + δ.z b i ≤ δ.z a b + δ.z i j) := by
  have hc : (2 - (Fintype.card X : ℝ)) / 2 < 0 := by
    have h4 : (4 : ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast hcard
    linarith
  have h1 := z_hinge δ i j a b
  have h2 := z_hinge δ j i a b
  have hs : δ.z j i = δ.z i j := z_comm δ j i
  have hs' : δ.val j i = δ.val i j := δ.symm j i
  rw [hs, hs'] at h2
  constructor
  · rintro ⟨hP1, hP2⟩
    constructor
    · have hmul : 0 ≤ ((2 - (Fintype.card X : ℝ)) / 2)
          * (δ.val a b + δ.val i j - (δ.val a i + δ.val b j)) :=
        mul_nonneg_of_nonpos_of_nonpos hc.le (by linarith)
      linarith
    · have hmul : 0 ≤ ((2 - (Fintype.card X : ℝ)) / 2)
          * (δ.val a b + δ.val i j - (δ.val a j + δ.val b i)) :=
        mul_nonneg_of_nonpos_of_nonpos hc.le (by linarith)
      linarith
  · rintro ⟨hz1, hz2⟩
    constructor
    · by_contra h
      push_neg at h
      have hmul : ((2 - (Fintype.card X : ℝ)) / 2)
          * (δ.val a b + δ.val i j - (δ.val a i + δ.val b j)) < 0 :=
        mul_neg_of_neg_of_pos hc (by linarith)
      linarith
    · by_contra h
      push_neg at h
      have hmul : ((2 - (Fintype.card X : ℝ)) / 2)
          * (δ.val a b + δ.val i j - (δ.val a j + δ.val b i)) < 0 :=
        mul_neg_of_neg_of_pos hc (by linarith)
      linarith

/-! ## 引理 3：★ 硬核命题（**形式化缺口**，作为显式假设）

⚠️ **这是「已证定理的形式化缺口」，不是数学开放问题** —— NJ 正确性见
Studier–Keppler (1988)、Weller (2023)、Mihaescu–Levy–Pachter (2009)；
缺口在于本库尚未形式化其前置「**Buneman 存在性**」（四点条件 ⟹ 存在实现树）。 -/

/-- **★ 硬核命题 `MaxZCherryCore`**（NJ 定理的纯度量表述）。

✦ **经典已证，本库尚未形式化**（Studier–Keppler 1988；Weller 2023）—— 非开放问题。

若 `(a,b)` **全局**最大化 `z`，则对任意互异且都异于 `a,b` 的 `i,j`，
四点和 `P` 同时 ≤ 两个交叉和 —— 即所有含 `a,b` 的 quartet 都按 `ab|ij` 分裂。

**为什么难**：`z` 的最大性是全局的（涉及所有行和 `S`），而 quartet 分裂是局部的；
标准证明需 **Buneman 存在性**（四点条件 ⟹ 存在实现树）+ Weller 2023 的 *leaf-status* 论证。
纯度量路线**尚缺干净证明**（数值上随机 4000 棵正权树无界点）。

本库把它作为**显式假设**而非 `sorry` —— 保持零 `sorry`，并让依赖关系清晰可见。 -/
def MaxZCherryCore : Prop :=
  δ.FourPoint →
    ∀ a b : X, a ≠ b → (∀ i j : X, i ≠ j → δ.z i j ≤ δ.z a b) →
      ∀ i j : X, i ≠ j → i ≠ a → i ≠ b → j ≠ a → j ≠ b →
        δ.val a b + δ.val i j ≤ δ.val a i + δ.val b j ∧
        δ.val a b + δ.val i j ≤ δ.val a j + δ.val b i

/-- **后承 1**（由硬核 + `z_hinge`/`four_point_z_iff`）：最大 z 对给出四点分裂。 -/
theorem max_z_gives_split (hcore : δ.MaxZCherryCore) (hcard : 4 ≤ Fintype.card X)
    (hfp : δ.FourPoint) (a b : X) (hab : a ≠ b)
    (hmax : ∀ i j : X, i ≠ j → δ.z i j ≤ δ.z a b) :
    ∀ i j : X, i ≠ j → i ≠ a → i ≠ b → j ≠ a → j ≠ b →
      δ.val a b + δ.val i j ≤ δ.val a i + δ.val b j ∧
      δ.val a b + δ.val i j ≤ δ.val a j + δ.val b i :=
  hcore hfp a b hab hmax

/-- **★ NJ 樱桃引理**（假设硬核）：若 `δ` 满足四点条件、`(a,b)` 最大化 `z`，则 `(a,b)` 是樱桃。

（退化情形 `k = l` 由三角不等式处理；非退化情形归约到 `MaxZCherryCore`。） -/
theorem max_at_cherry (hcore : δ.MaxZCherryCore)
    (hfp : δ.FourPoint)
    (a b : X) (hab : a ≠ b)
    (hmax : ∀ i j : X, i ≠ j → δ.val i j + δ.ell i j ≤ δ.val a b + δ.ell a b) :
    δ.IsCherry a b := by
  refine ⟨hab, ?_⟩
  intro k l hka hkb hla hlb
  rcases eq_or_ne k l with hkl | hkl
  · subst hkl
    have htri : δ.val a b ≤ δ.val k a + δ.val k b := triangle δ hfp k a b
    have hkk : δ.val k k = 0 := δ.diag k
    have hka' : δ.val k a = δ.val a k := δ.symm k a
    have hkb' : δ.val k b = δ.val b k := δ.symm k b
    constructor <;> linarith
  · exact hcore hfp a b hab hmax k l hkl hka hkb hla hlb

/-- **★ NJ 主定理**（假设硬核）：若 `δ` 满足四点条件，且 `(a,b)` **最小化 Q**，则 `(a,b)` 是樱桃。

证明：由 `Q_eq_neg_two_ell`，`Q` 最小 ⟺ `δ+ℓ` 最大，再用 `max_at_cherry`。 -/
theorem nj_cherry (hcore : δ.MaxZCherryCore)
    (hfp : δ.FourPoint)
    (a b : X) (hab : a ≠ b)
    (hmin : ∀ i j : X, i ≠ j → δ.Q a b ≤ δ.Q i j) :
    δ.IsCherry a b := by
  apply max_at_cherry δ hcore hfp a b hab
  intro i j hij
  have h1 : δ.Q a b ≤ δ.Q i j := hmin i j hij
  rw [Q_eq_neg_two_ell δ, Q_eq_neg_two_ell δ] at h1
  linarith

end Dissimilarity

end NJ
