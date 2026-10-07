/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Algorithm.NJ
import Phylo.Buneman

/-!
# `Phylo.DissimilarityPerturb` —— 「非对角项统一加 `ε`」的扰动预备件（T0.3 收尾）

**动机（T0.3 步骤 C 的收尾）**：T0.2 给出的实现树**可能含零权内部边**，而 Weller 的树层 Thm 2
需要**正边权**。收缩零权边代价高；本文件提供那条更省的**扰动路线**的代数件：

> 令 `δ_ε(x,y) = δ(x,y) + ε`（`x ≠ y`）、`δ_ε(x,x) = 0`（`addConst δ ε`）。则

1. ★★★ `z_addConst`：**`z_ε = z + (|X|/2)·ε`** —— 平移一个**与 `i,j` 无关**的常数
   ⇒ **`z` 的最大化集合不变**（这是整条路线的命门）；
2. ★★ `fourSum_addConst`：目标四点和不等式**两边同样加 `2ε`** ⇒ 对 `δ_ε` 证出即对 `δ` 成立；
3. ★★ `fourPoint_addConst` / ★★ `positiveDefinite_addConst`：两个前提条件**被保持**
   ⇒ 构造出的实现树各边可望全正，Weller 的 Thm 2 即可使用。

## ⚠️ 两处对原派单陈述的**必要修正**（原陈述为假，附反例）

* `fourPoint_addConst` **需要 `0 ≤ ε`**。反例（`ε < 0`）：取三点 `x,k,l` 上的路径度量
  `δ(x,k) = δ(x,l) = 1`、`δ(k,l) = 2`（树度量 ⇒ `FourPoint` ✓）；取 `ε = -1/2`，则实例
  `(x,x,k,l)` 给出 `δ_ε(x,x) + δ_ε(k,l) = 3/2 > 1 = δ_ε(x,k) + δ_ε(x,l)`，两个析取支都不成立。
* `positiveDefinite_addConst` **需要 `δ` 的非负性** `∀ x y, 0 ≤ δ.val x y`。
  反例：`X` 至少两点、`δ ≡ -1`（非对角）满足 `PositiveDefinite`（非对角值 ≠ 0），
  但 `ε = 1` 时 `δ_ε(x,y) = 0`（`x ≠ y`）⇒ `PositiveDefinite` 失败。

（树可实现的 `δ` 天然满足这两条前提，故对 T0.3 的用途无碍。）

## 状态

* ✅ `addConst` + `addConst_val_ne` / `addConst_val_self` / `addConst_val_eq`
* ✅ ★★★ `z_addConst`（附 `S_addConst`）
* ✅ ★★ `fourSum_addConst`
* ✅ ★★ `fourPoint_addConst`（+ `0 ≤ ε`）
* ✅ ★★ `positiveDefinite_addConst`（+ 非负性）
* ✅ **§6 ADR 2016 式 (2)(3)(5)**：★★ `fourSum_sub_eq_of_pendant` + ★★ `fourPoint_of_pendant`
  —— **USTAR 的配对可加修正** `δ(x,y) = δr(x,y) + u x + u y`（`x ≠ y`）：四个标签互异时
  三对和的**差额逐项不变** ⇒ 四点条件保持（`u x = 1 − w x` 即 ADR 的 `2 − (w_x + w_y)`）；
* ✅ **§7 阴性结论**：★★★ `not_fourPoint_of_pendant_naive` —— 若不额外假设 `δ` 的**三角不等式**，
  上述朴素传递是**假命题**（`Fin 4` 显式见证；形制同 `Phylo/BunemanShrinkPD.lean`）
  （**零 `sorry` / 零 `axiom`**）
-/

universe u

namespace NJ

namespace Dissimilarity

open Finset
open scoped BigOperators

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## 1. 指示函数与「加常数」 -/

omit [Fintype X] in
/-- **「两标签不同」的指示函数**（实数版）：`x ≠ y` 记 `1`，否则记 `0`。 -/
noncomputable def distinctInd (x y : X) : ℝ := if x = y then 0 else 1

omit [Fintype X] in
theorem distinctInd_self (x : X) : distinctInd x x = 0 := by simp [distinctInd]

omit [Fintype X] in
theorem distinctInd_of_ne {x y : X} (h : x ≠ y) : distinctInd x y = 1 := by
  simp [distinctInd, h]

omit [Fintype X] in
theorem distinctInd_comm (x y : X) : distinctInd x y = distinctInd y x := by
  by_cases h : x = y
  · subst h; simp [distinctInd]
  · have h' : y ≠ x := fun hh => h hh.symm
    simp [distinctInd, h, h']

omit [Fintype X] in
theorem distinctInd_nonneg (x y : X) : 0 ≤ distinctInd x y := by
  by_cases h : x = y <;> simp [distinctInd, h]

omit [Fintype X] in
theorem distinctInd_le_one (x y : X) : distinctInd x y ≤ 1 := by
  by_cases h : x = y <;> simp [distinctInd, h]

omit [Fintype X] in
/-- 两项指示函数之和 `≤ 1` ⟺ 至少一对相等（用于「坏情形」的定位）。 -/
theorem distinctInd_add_le_one_iff {p q r s : X} :
    distinctInd p q + distinctInd r s ≤ 1 ↔ p = q ∨ r = s := by
  constructor
  · intro h
    by_cases h1 : p = q
    · exact Or.inl h1
    · refine Or.inr ?_
      have h2 : distinctInd p q = 1 := distinctInd_of_ne h1
      have h3 : distinctInd r s ≤ 0 := by linarith
      have h4 : distinctInd r s = 0 := le_antisymm h3 (distinctInd_nonneg r s)
      by_contra hrs
      rw [distinctInd_of_ne hrs] at h4
      norm_num at h4
  · rintro (h | h)
    · subst h
      rw [distinctInd_self]
      have := distinctInd_le_one r s
      linarith
    · subst h
      rw [distinctInd_self]
      have := distinctInd_le_one p q
      linarith

omit [Fintype X] in
/-- **计数引理（第一支）**：指示函数和满足第一对不等式，或退化为 `i = k ∨ j = l`。 -/
theorem distinctInd_le_or_eq_left (i j k l : X) :
    distinctInd i j + distinctInd k l ≤ distinctInd i k + distinctInd j l ∨ i = k ∨ j = l := by
  by_cases h1 : i = k
  · exact Or.inr (Or.inl h1)
  · by_cases h2 : j = l
    · exact Or.inr (Or.inr h2)
    · refine Or.inl ?_
      have e1 : distinctInd i k = 1 := distinctInd_of_ne h1
      have e2 : distinctInd j l = 1 := distinctInd_of_ne h2
      have a := distinctInd_le_one i j
      have b := distinctInd_le_one k l
      linarith

omit [Fintype X] in
/-- **计数引理（第二支）**：指示函数和满足第二对不等式，或退化为 `i = l ∨ j = k`。 -/
theorem distinctInd_le_or_eq_right (i j k l : X) :
    distinctInd i j + distinctInd k l ≤ distinctInd i l + distinctInd j k ∨ i = l ∨ j = k := by
  by_cases h1 : i = l
  · exact Or.inr (Or.inl h1)
  · by_cases h2 : j = k
    · exact Or.inr (Or.inr h2)
    · refine Or.inl ?_
      have e1 : distinctInd i l = 1 := distinctInd_of_ne h1
      have e2 : distinctInd j k = 1 := distinctInd_of_ne h2
      have a := distinctInd_le_one i j
      have b := distinctInd_le_one k l
      linarith

omit [Fintype X] in
/-- **非对角项统一加 `ε`**（对角仍为 `0`）：`δ_ε(x,y) = δ(x,y) + ε`（`x ≠ y`）。 -/
noncomputable def addConst (δ : Dissimilarity X) (ε : ℝ) : Dissimilarity X where
  val := fun x y => if x = y then 0 else δ.val x y + ε
  symm := by
    intro x y
    by_cases h : x = y
    · subst h; simp
    · simp [h, Ne.symm h, δ.symm x y]
  diag := by
    intro x
    simp

omit [Fintype X] in
theorem addConst_val_ne (δ : Dissimilarity X) (ε : ℝ) {x y : X} (h : x ≠ y) :
    (δ.addConst ε).val x y = δ.val x y + ε := by
  simp [addConst, h]

omit [Fintype X] in
theorem addConst_val_self (δ : Dissimilarity X) (ε : ℝ) (x : X) :
    (δ.addConst ε).val x x = 0 := by
  simp [addConst]

omit [Fintype X] in
/-- **统一展开式**：`δ_ε(x,y) = δ(x,y) + ε·[x ≠ y]`（两种情形合一，供计数用）。 -/
theorem addConst_val_eq (δ : Dissimilarity X) (ε : ℝ) (x y : X) :
    (δ.addConst ε).val x y = δ.val x y + ε * distinctInd x y := by
  by_cases h : x = y
  · subst h
    rw [addConst_val_self, distinctInd_self, δ.diag, mul_zero, add_zero]
  · rw [addConst_val_ne δ ε h, distinctInd_of_ne h, mul_one]

/-! ## 2. `S` 的平移与 ★★★ `z` 的平移 -/

omit [Fintype X] in
/-- 两个只差一点的函数，其和只差该点之差。 -/
theorem sum_eq_sum_add_sub {s : Finset X} {f g : X → ℝ} {a : X} (ha : a ∈ s)
    (h : ∀ x ∈ s, x ≠ a → f x = g x) : s.sum f = s.sum g + (f a - g a) := by
  have h1 := Finset.sum_erase_add s f ha
  have h2 := Finset.sum_erase_add s g ha
  have h3 : (s.erase a).sum f = (s.erase a).sum g := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    exact h x (Finset.mem_of_mem_erase hx) (Finset.mem_erase.mp hx).1
  rw [← h1, ← h2, h3]
  ring

/-- ★★ **`S` 的平移**：`S_ε(u) = S(u) + (|X| − 1)·ε`。 -/
theorem S_addConst (δ : Dissimilarity X) (ε : ℝ) (u : X) :
    (δ.addConst ε).S u = δ.S u + ((Fintype.card X : ℝ) - 1) * ε := by
  have hd : ∀ k ∈ (Finset.univ : Finset X), k ≠ u →
      (δ.addConst ε).val u k = δ.val u k + ε :=
    fun k _ hk => addConst_val_ne δ ε (Ne.symm hk)
  have h1 : (∑ k : X, (δ.addConst ε).val u k) = (∑ k : X, (δ.val u k + ε)) - ε := by
    have h := sum_eq_sum_add_sub (s := (Finset.univ : Finset X))
      (f := fun k => (δ.addConst ε).val u k) (g := fun k => δ.val u k + ε)
      (a := u) (Finset.mem_univ u) hd
    rw [addConst_val_self δ ε u, δ.diag u, zero_add, zero_sub] at h
    exact h
  have h2 : (∑ k : X, (δ.val u k + ε))
      = (∑ k : X, δ.val u k) + (Fintype.card X : ℝ) * ε := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  show (∑ k : X, (δ.addConst ε).val u k)
      = (∑ k : X, δ.val u k) + ((Fintype.card X : ℝ) - 1) * ε
  rw [h1, h2]
  ring

/-- ★★★ **关键**：`z` 被平移了一个**与 `i j` 无关**的常数 `(|X|/2)·ε`
⇒ 最大化集合（以及「哪一对的 `z` 最大」）在扰动下**不变**。 -/
theorem z_addConst (δ : Dissimilarity X) {ε : ℝ} {i j : X} (hij : i ≠ j) :
    (δ.addConst ε).z i j = δ.z i j + (Fintype.card X : ℝ) / 2 * ε := by
  rw [z_eq_S (δ.addConst ε) i j, z_eq_S δ i j, S_addConst δ ε i, S_addConst δ ε j,
    addConst_val_ne δ ε hij]
  ring

/-! ## 3. 四点和：两边同步平移 `2ε` -/

omit [Fintype X] in
/-- 三个「配对和」的同步平移（内部引理，六条互异假设都被用到）。 -/
private theorem fourSum_addConst_all (δ : Dissimilarity X) (ε : ℝ) {a b i j : X}
    (hab : a ≠ b) (hij : i ≠ j) (hia : i ≠ a) (hib : i ≠ b) (hja : j ≠ a) (hjb : j ≠ b) :
    ((δ.addConst ε).val a b + (δ.addConst ε).val i j = δ.val a b + δ.val i j + 2 * ε) ∧
    ((δ.addConst ε).val a i + (δ.addConst ε).val b j = δ.val a i + δ.val b j + 2 * ε) ∧
    ((δ.addConst ε).val a j + (δ.addConst ε).val b i = δ.val a j + δ.val b i + 2 * ε) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [addConst_val_ne δ ε hab, addConst_val_ne δ ε hij]; ring
  · rw [addConst_val_ne δ ε hia.symm, addConst_val_ne δ ε hjb.symm]; ring
  · rw [addConst_val_ne δ ε hja.symm, addConst_val_ne δ ε hib.symm]; ring

omit [Fintype X] in
/-- ★★ **目标不等式两边同样加 `2ε`** ⇒ 等价（条件：六个配对都非对角）。

（配 `fourPoint_addConst` 使用：对 `δ_ε` 证出的四点和不等式逐一翻译回 `δ`。） -/
theorem fourSum_addConst (δ : Dissimilarity X) (ε : ℝ) {a b i j : X}
    (hab : a ≠ b) (hij : i ≠ j) (hia : i ≠ a) (hib : i ≠ b) (hja : j ≠ a) (hjb : j ≠ b) :
    (δ.addConst ε).val a b + (δ.addConst ε).val i j = δ.val a b + δ.val i j + 2 * ε :=
  (fourSum_addConst_all δ ε hab hij hia hib hja hjb).1

/-! ## 4. 四点条件的保持 -/

omit [Fintype X] in
/-- ★★ **四点条件保持**（`0 ≤ ε`）。

把每个配对写成 `δ(x,y) + ε·[x ≠ y]`，则两边之差 = `δ` 侧之差 + `ε·(计数差)`；
计数差为负时必是「`i = k ∨ j = l`（或对称）」的退化情形，此时**另一支**的 δ-不等式
由对称性成立、且计数差非负。 -/
theorem fourPoint_addConst (δ : Dissimilarity X) {ε : ℝ} (hε : 0 ≤ ε) (h : δ.FourPoint) :
    (δ.addConst ε).FourPoint := by
  intro i j k l
  have e1 : (δ.addConst ε).val i j + (δ.addConst ε).val k l
      = δ.val i j + δ.val k l + ε * (distinctInd i j + distinctInd k l) := by
    rw [addConst_val_eq, addConst_val_eq]; ring
  have e2 : (δ.addConst ε).val i k + (δ.addConst ε).val j l
      = δ.val i k + δ.val j l + ε * (distinctInd i k + distinctInd j l) := by
    rw [addConst_val_eq, addConst_val_eq]; ring
  have e3 : (δ.addConst ε).val i l + (δ.addConst ε).val j k
      = δ.val i l + δ.val j k + ε * (distinctInd i l + distinctInd j k) := by
    rw [addConst_val_eq, addConst_val_eq]; ring
  rw [e1, e2, e3]
  rcases h i j k l with hA | hB
  · by_cases hk : distinctInd i j + distinctInd k l ≤ distinctInd i k + distinctInd j l
    · exact Or.inl (by
        have := mul_le_mul_of_nonneg_left hk hε
        linarith)
    · -- 坏情形：`i = k ∨ j = l`；改用第二支（δ 侧由对称性成立）
      rcases (distinctInd_le_or_eq_left i j k l) with hle | hik | hjl
      · exact absurd hle hk
      · have hB' : δ.val i j + δ.val k l ≤ δ.val i l + δ.val j k := by
          subst hik; linarith [δ.symm j i]
        have hK1' : distinctInd i j + distinctInd k l ≤ distinctInd i l + distinctInd j k := by
          subst hik
          have := distinctInd_comm i j
          linarith
        exact Or.inr (by
          have := mul_le_mul_of_nonneg_left hK1' hε
          linarith)
      · have hB' : δ.val i j + δ.val k l ≤ δ.val i l + δ.val j k := by
          subst hjl; linarith [δ.symm k j]
        have hK1' : distinctInd i j + distinctInd k l ≤ distinctInd i l + distinctInd j k := by
          subst hjl
          have := distinctInd_comm k j
          linarith
        exact Or.inr (by
          have := mul_le_mul_of_nonneg_left hK1' hε
          linarith)
  · by_cases hk : distinctInd i j + distinctInd k l ≤ distinctInd i l + distinctInd j k
    · exact Or.inr (by
        have := mul_le_mul_of_nonneg_left hk hε
        linarith)
    · rcases (distinctInd_le_or_eq_right i j k l) with hle | hil | hjk
      · exact absurd hle hk
      · have hA' : δ.val i j + δ.val k l ≤ δ.val i k + δ.val j l := by
          subst hil; linarith [δ.symm k i, δ.symm j i]
        have hK1' : distinctInd i j + distinctInd k l ≤ distinctInd i k + distinctInd j l := by
          subst hil
          have a := distinctInd_comm k i
          have b := distinctInd_comm j i
          linarith
        exact Or.inl (by
          have := mul_le_mul_of_nonneg_left hK1' hε
          linarith)
      · have hA' : δ.val i j + δ.val k l ≤ δ.val i k + δ.val j l := by
          subst hjk; exact le_refl _
        have hK1' : distinctInd i j + distinctInd k l ≤ distinctInd i k + distinctInd j l := by
          subst hjk; exact le_refl _
        exact Or.inl (by
          have := mul_le_mul_of_nonneg_left hK1' hε
          linarith)

/-! ## 5. 正定性的保持 -/

omit [Fintype X] in
/-- 正定保持的核心（`δ` 非负 + `ε > 0`；`δ` 自身的正定性在此**不被需要**）。 -/
private theorem positiveDefinite_addConst_aux (δ : Dissimilarity X) {ε : ℝ} (hε : 0 < ε)
    (hnn : ∀ x y : X, 0 ≤ δ.val x y) (_h : δ.PositiveDefinite) :
    (δ.addConst ε).PositiveDefinite := by
  intro x y hxy
  by_cases hx : x = y
  · exact hx
  · exfalso
    rw [addConst_val_ne δ ε hx] at hxy
    have := hnn x y
    linarith

omit [Fintype X] in
/-- ★★ **正定保持**（`ε > 0`，且 `δ` 的取值非负）。

⚠️ 需要**非负性**（原派单没有它，且原陈述为假）：`δ ≡ -1`（非对角）满足 `PositiveDefinite`，
但 `ε = 1` 会把非对角项压到 `0` ⇒ `PositiveDefinite` 失败。树可实现的 `δ` 天然非负。
`h : δ.PositiveDefinite` 在有了非负性后是**冗余**的，保留只为签名兼容（转发的辅助引理里被忽略）。 -/
theorem positiveDefinite_addConst (δ : Dissimilarity X) {ε : ℝ} (hε : 0 < ε)
    (hnn : ∀ x y : X, 0 ≤ δ.val x y) (h : δ.PositiveDefinite) :
    (δ.addConst ε).PositiveDefinite :=
  positiveDefinite_addConst_aux δ hε hnn h

/-! ## 6. USTAR 的**挂边修正**（ADR 2016 式 (2)(3)(5)）

ADR 2016（`AllmanDegnanRhodes2016_NJst_StatisticalConsistency.md`）把 NJst 的相异度
`D = E_σ(D_T)`（**USTAR**）与 STAR 相异度 `D^r = E_σ(D^r_{T^r})` 用

`D(x,y) = D^r(x,y) + 2 − (w_x + w_y)`　　　（式 (2)(3)，`:682–689`、`:704–714`）

联系起来（`w_x = E_σ(w_x)` 是根被抑制后 `x` 的挂边长度的期望；上式对 `x ≠ y`）。
本节把这个**配对可加修正**抽成纯代数：取 `u x = 1 − w x`，即 `δ(x,y) = δr(x,y) + u x + u y`。

ADR 随后（`:716–735`）说明：**四个标签互异**时，三对和
`{a,b}|{c,d}`、`{a,c}|{b,d}`、`{a,d}|{b,c}` 各覆盖四个标签恰好一次，故**同加**
`u a + u b + u c + u d` ⇒ 四点条件（式 (4)）**保持**为式 (5)。这正是 ★★ `fourSum_sub_eq_of_pendant`
+ ★★ `fourPoint_of_pendant` 的内容。

⚠️ **重复下标的情形是另一回事**（ADR `:737–746` 也是另行处理）：那时不能用上述「同加常数」，
必须回到「每个 `D_T` 都是树度量」（⇒ 三角不等式）。故 ★★ `fourPoint_of_pendant` 显式要求
`δ` 的**三角不等式** `htri` —— 见 §7 的 ★★★ 阴性结论。 -/

omit [Fintype X] [DecidableEq X] in
/-- **配对可加修正**：`δ(x,y) = δr(x,y) + u x + u y`（`x ≠ y`）。

取 `u x = 1 − w x` 即 ADR 2016 的 `D(x,y) = D^r(x,y) + 2 − (w_x + w_y)`。 -/
def IsPendantCorrected (δ δr : Dissimilarity X) (u : X → ℝ) : Prop :=
  ∀ x y : X, x ≠ y → δ.val x y = δr.val x y + u x + u y

omit [Fintype X] [DecidableEq X] in
/-- ★★ **式 (5) 的差额恒等式**：配对可加修正使四点**三对和的差额逐项不变**（四个标签互异）。

右端 `(a,b)` 与 `(c,d)` 覆盖四个标签恰好一次，故「三对和」中的每一对都加上同一个
`u a + u b + u c + u d` —— 正是 ADR「only added `2 − E(w_a+w_b+w_c+w_d)` to the three sums」
（`:726–735`）的代数内容。 -/
theorem fourSum_sub_eq_of_pendant {δ δr : Dissimilarity X} {u : X → ℝ}
    (h : IsPendantCorrected δ δr u) {a b c d : X}
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (hbd : b ≠ d) :
    (δ.val a b + δ.val c d) - (δ.val a c + δ.val b d)
      = (δr.val a b + δr.val c d) - (δr.val a c + δr.val b d) := by
  rw [h a b hab, h c d hcd, h a c hac, h b d hbd]
  ring

omit [Fintype X] [DecidableEq X] in
/-- ★★ **重复下标（互异数 `≤ 3`）的四点条件**：只要 `δ` 满足**三角不等式**即自动成立
（四个下标里必有一对相等，此时恰有一个析取支由对称性或 `diag` 立即成立）。

⚠️ 这一条**不能**由挂边修正的代数得到（见 ★★★ `not_fourPoint_of_pendant_naive`）；
ADR 在 `:737–746` 用「每个 `D_T` 都是树度量」另行处理这一情形。 -/
theorem fourPoint_of_triangle_of_not_pairwise {δ : Dissimilarity X}
    (htri : ∀ a k l : X, δ.val k l ≤ δ.val a k + δ.val a l) {i j k l : X}
    (h : ¬ (i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l)) :
    (δ.val i j + δ.val k l ≤ δ.val i k + δ.val j l) ∨
    (δ.val i j + δ.val k l ≤ δ.val i l + δ.val j k) := by
  by_cases hij : i = j
  · left; rw [hij, δ.diag j, zero_add]; exact htri j k l
  by_cases hik : i = k
  · right; rw [hik]; linarith [δ.symm k j]
  by_cases hil : i = l
  · left; rw [hil]; linarith [δ.symm l j, δ.symm k l]
  by_cases hjk : j = k
  · left; rw [hjk]
  by_cases hjl : j = l
  · right; rw [hjl]; linarith [δ.symm k l]
  by_cases hkl : k = l
  · left; rw [hkl, δ.diag l, add_zero]; linarith [htri l i j, δ.symm i l, δ.symm j l]
  · exact absurd ⟨hij, hik, hil, hjk, hjl, hkl⟩ h

omit [Fintype X] [DecidableEq X] in
/-- ★★ **式 (4)(5)：配对可加修正保持四点条件**（ADR 2016 Thm 4.2 证明的代数核心）。

* 四个标签**互异**：三对和同加 `u a + u b + u c + u d` ⇒ 用 ★★ `fourSum_sub_eq_of_pendant`
  把 `δr.FourPoint`（式 (4)）搬到 `δ`（式 (5)）；
* 有**重复**下标：用 `htri`（`δ` 的三角不等式）经 ★★ `fourPoint_of_triangle_of_not_pairwise`。

⚠️ **`htri` 不可省**（★★★ `not_fourPoint_of_pendant_naive`），且它不是纯代数结论：
库内由**实现树**（`Phylogram.dist_triangle`）或由「期望保不等式」给出。 -/
theorem fourPoint_of_pendant {δ δr : Dissimilarity X} {u : X → ℝ}
    (h : IsPendantCorrected δ δr u) (hr : δr.FourPoint)
    (htri : ∀ a k l : X, δ.val k l ≤ δ.val a k + δ.val a l) : δ.FourPoint := by
  intro i j k l
  by_cases h4 : i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l
  · rcases h4 with ⟨hij, hik, hil, hjk, hjl, hkl⟩
    rcases hr i j k l with h' | h'
    · left
      have hsub := fourSum_sub_eq_of_pendant h hij hkl hik hjl
      linarith
    · right
      have hsub := fourSum_sub_eq_of_pendant h hij (fun hh => hkl hh.symm) hil hjk
      linarith [δ.symm l k, δr.symm l k]
  · exact fourPoint_of_triangle_of_not_pairwise htri h4

/-! ## 7. ★★★ 阴性结论：**朴素**的挂边传递是**假命题**

「`δ = δr + u x + u y` 且 `δr.FourPoint` ⇒ `δ.FourPoint`」若**不**额外假设 `δ` 的三角不等式，
则**为假**。本节的机器可查见证（形制同 `Phylo/BunemanShrinkPD.lean`）：

* `δr` = `Fin 4` 上非对角恒为 `2` 的常数相异度（`FourPoint` ✓，三对和都等于 `4`）；
* `u 0 = −10`、`u k = +10`（`k ≠ 0`）⇒ `δ(0,k) = 2`、`δ(k,l) = 22`（`k,l ≠ 0`，互异）。
  **注意 `δ` 的非对角项全为正** ⇒ 「非负性」也不够；
* 取四点 `(0,0,1,2)`：`δ(0,0) + δ(1,2) = 22 > 4 = δ(0,1) + δ(0,2) = δ(0,2) + δ(1,0)`
  ⇒ `FourPoint` 两个析取支**都不成立**。

⇒ 这正是 `fourPoint_of_pendant` 里 `htri` 不可省的原因（ADR 在 `:737–746` 另行处理该情形）。 -/

/-- 常数相异度的值函数（`Fin 4`，非对角恒为 `2`）。 -/
def constTwoVal : Fin 4 → Fin 4 → ℝ
  | 0, 0 => 0 | 1, 1 => 0 | 2, 2 => 0 | 3, 3 => 0 | _, _ => 2

/-- 常数相异度 `δr`（非对角恒为 `2`）。 -/
def constTwo : Dissimilarity (Fin 4) where
  val := constTwoVal
  symm := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  diag := by intro i; fin_cases i <;> rfl

/-- 常数相异度满足四点条件（三对和都等于 `4` ⇒ 两个析取支都成立）。 -/
theorem constTwo_fourPoint : constTwo.FourPoint := by
  intro i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [constTwo, constTwoVal] <;> norm_num

/-- 「坏修正」函数：`u 0 = −10`、其余 `+10`。 -/
def badUVal : Fin 4 → ℝ
  | 0 => -10 | _ => 10

/-- 被修正的相异度 `δ = δr + u x + u y`：非对角为 `2`（一端是 `0`）或 `22`（两端都非 `0`）。 -/
def badPendantVal : Fin 4 → Fin 4 → ℝ
  | 0, 0 => 0 | 1, 1 => 0 | 2, 2 => 0 | 3, 3 => 0
  | 0, _ => 2 | _, 0 => 2
  | _, _ => 22

/-- 被修正的相异度 `δ`（见 `badPendantVal`）。 -/
def badPendant : Dissimilarity (Fin 4) where
  val := badPendantVal
  symm := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  diag := by intro i; fin_cases i <;> rfl

/-- `badPendant` 与 `constTwo` 确实相差一个**配对可加修正**（`u = badUVal`）。 -/
theorem badPendant_isPendantCorrected : IsPendantCorrected badPendant constTwo badUVal := by
  intro x y h
  fin_cases x <;> fin_cases y <;>
    first
      | exact absurd rfl h
      | (simp only [badPendant, constTwo, badPendantVal, constTwoVal, badUVal]; norm_num)

/-- ★★★ **阴性结论**：「`δr.FourPoint` + 配对可加修正 ⇒ `δ.FourPoint`」**是假命题**
（缺少 `δ` 的三角不等式时）。见证与数值见本节开头。 -/
theorem not_fourPoint_of_pendant_naive :
    ¬ (∀ (δ δr : Dissimilarity (Fin 4)) (u : Fin 4 → ℝ),
        IsPendantCorrected δ δr u → δr.FourPoint → δ.FourPoint) := by
  intro h
  have hbad : badPendant.FourPoint :=
    h badPendant constTwo badUVal badPendant_isPendantCorrected constTwo_fourPoint
  have h0 := hbad 0 0 1 2
  simp only [badPendant, badPendantVal] at h0
  norm_num at h0

end Dissimilarity

end NJ
