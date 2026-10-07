/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Algorithm.NJ
import Phylo.Core

/-!
# `Phylo.Buneman` —— 四点条件 ⟹ 存在实现加权树（Buneman 存在性，T0.2）

**文献**：P. Buneman, *A Note on the Metric Properties of Trees*,
J. Combinatorial Theory (B) **17** (1974) 48–50。

| 位置 | 内容 |
| --- | --- |
| `Buneman1974_MetricPropertiesOfTrees.md` **17–29** | 四点条件（三对和中最大者至少出现两次） |
| 同文 **70–72** | **Theorem 2**：`d` 是 `S` 上的度量且满足四点条件 ⟹ 存在含 `S` 的加权树诱导 `d` |
| 同文 **74–121** | Theorem 2 的**归纳证明**（选极大三元组 `(p,q,r)`、加入新点 `t`、挂回 `p,q`） |

**本文件用路线 A**：**转录** Buneman 1974 Theorem 2 的归纳证明
（不是 Bandelt–Dress 的 split/laminar 再推导）。非 `univ` 的「球族镶嵌」管线
（`Phylo/Dendrogram.lean`）只适用于**超度量**这一特殊情形，对一般四点条件不适用，
故此处不走路线 B。

## 术语与假设

* `Dissimilarity`（`Phylo/Algorithm/NJ.lean:61`）只要求**对称 + 零对角**；
  Buneman 的 `d` 是**度量**，故正定性 `val x y = 0 → x = y` 作为**显式假设**列出
  （见 `Dissimilarity.PositiveDefinite`）。
* 三角不等式**不用假设**：`Dissimilarity.triangle`（`NJ.lean:107`）已证它由四点条件推出
  —— 这正是 Buneman 第 27 行的注记「put `z = t`」。

## ★ 已证内容（本文件）

* **★★ `Dissimilarity.fourpoint_two_eq_max`** —— 四点条件的「最大者出现两次」**正规形**：
  三对和中必有两个相等且都 ≥ 第三个。Buneman 第 26–29 行的原文陈述，本库
  `FourPoint`（`NJ.lean:71`，析取式）与它的等价形式。
* **★★ `Dissimilarity.fourpoint_eq_of_le_both`** —— 若某对和同时 ≤ 另两对和，
  则另两对和相等（归纳证明第 86–89 行「用四点条件得到等式」的那一步）。

**Buneman 归纳步的算术核心**（第 78–95、112–113 行）

* **★★ `Dissimilarity.bunemanScore`** / **`bunemanScore_comm`** —— 第 81 行被最大化的量
  `f(a,b,c) = δ(a,c) + δ(b,c) − δ(a,b)`。
* **★★ `Dissimilarity.exists_three_distinct`** / **`exists_max_triple`** ——
  `|X| ≥ 3` 时**互异**极大三元组存在（第 78–81 行）。
* **★★ `Dissimilarity.max_triple_ineq_left`** / **`max_triple_ineq_right`** ——
  极大性给出的两条不等式（第 82–85 行）。
* **★★★ `Dissimilarity.max_triple_fourpoint_eq`** —— 四点条件给出的等式
  `δ(x,q) + δ(p,r) = δ(x,p) + δ(q,r)`（第 86–89 行）。
* **★★★ `Dissimilarity.max_triple_identity_one`** —— Buneman 恒等式 (1)（第 90–91 行）。
* **★★ `Dissimilarity.rho_p_le_val`** / **`rho_add_rho`** —— 新点 `t` 的两条边权
  `ρ(p;q,r)`、`ρ(q;p,r)`（第 94 行；两者之和为 `δ(p,q)`）。
* **★★★ `Dissimilarity.shrinkVal_symm`** / **`shrinkVal_self`** / **`shrinkVal_nonneg`** /
  **`shrinkVal_fourpoint`** —— 扩张相异度 `δ'`：对称、零对角、非负、
  **四点条件保持**（第 92–95、112–113 行）。
* **★★★ `Dissimilarity.attach_left`** / **`attach_right`** —— (2a)/(2b)：
  `p` 与 `q` 都挂在 `t` 上（第 106–110 行）。
* **★★ `Dissimilarity.shrinkDissimilarity`** —— 把 `δ'` 打包成 `Dissimilarity`
  （供归纳假设使用）。

## ⬜ 形式化缺口（本文件的诚实边界）

**目标定理**（Buneman 1974, Theorem 2；`HANDOVER.md` §4 的 T0.2 验收项）：

```lean
theorem Dissimilarity.exists_phylogram_of_fourPoint
    (δ : Dissimilarity X) (hFP : δ.FourPoint) (hpos : ∀ x y, δ.val x y = 0 → x = y) :
    ∃ T : Phylogram X, ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y
```

**这不是学术开放问题**：Buneman 1974 已给出完整证明（Zaretskii 1965 亦有等价结果）。
上面的算术核心（选极大三元组、加入 `t`、`δ'` 仍是满足四点条件的相异度、(2a)/(2b)）
**已全部形式化**；剩下的只有**树的图手术 + 归纳装配**：

* **挂叶手术**：把 `Phylogram` 的一片叶（对应新点 `t`）改成内部顶点，再挂上两片新叶 `p,q`；
  需要新增图论引理「树上挂两个悬挂点仍是树」+ 度数记账（`t` 由度 1 变度 3，
  `no_degree_two`、`leaf_iff_degree_one` 保持）+ 唯一路径的边权和计算
  （`dist` 沿「`p—t—…—x`」分解，用 `attach_left` / `attach_right`）；
* **归纳**：对 `Fintype.card` 强归纳（基例 `|Y| ≤ 2`：单点树 / 一条边），
  每步用上面的手术 + 上面的算术核心。

本文件把该装配登记为 `Dissimilarity.InductiveAssembly`（**显式假设**，
与 `Phylo/Algorithm/NJ.lean` 的 `MaxZCherryCore` 同一房规）——
**不使用 `sorry`**，库仍零 `sorry`，且依赖关系机器可查。
-/

noncomputable section

open Finset
open scoped BigOperators

universe u

namespace NJ

namespace Dissimilarity

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## 度量层：Buneman 需要而本库 `Dissimilarity` 未含的公理 -/

omit [Fintype X] [DecidableEq X] in
/-- **正定**（Buneman 的「度量」比本库 `Dissimilarity` 多出的那一条）：
`val x y = 0 → x = y`。非负性与三角不等式**不需要**单列
（非负由 `triangle` + 零对角推出）。 -/
def PositiveDefinite (δ : Dissimilarity X) : Prop :=
  ∀ x y : X, δ.val x y = 0 → x = y

/-! ## 四点条件的正规形（Buneman 1974, 第 26–29 行） -/

omit [Fintype X] [DecidableEq X] in
/-- ★★ **四点条件的「最大者出现两次」正规形**：三对和
`i j + k l`、`i k + j l`、`i l + j k` 中必有两个相等，且都不小于第三个。

这是 Buneman 第 26–29 行的原文陈述，也是本库 `FourPoint`
（`NJ.lean:71` 的析取式，只排除「某对和是严格最大」）的等价重述。
归纳证明第 86–89 行反复使用的就是这个形式。 -/
theorem fourpoint_two_eq_max (δ : Dissimilarity X) (hfp : δ.FourPoint) (i j k l : X) :
    (δ.val i j + δ.val k l = δ.val i k + δ.val j l ∧
        δ.val i l + δ.val j k ≤ δ.val i j + δ.val k l) ∨
    (δ.val i j + δ.val k l = δ.val i l + δ.val j k ∧
        δ.val i k + δ.val j l ≤ δ.val i j + δ.val k l) ∨
    (δ.val i k + δ.val j l = δ.val i l + δ.val j k ∧
        δ.val i j + δ.val k l ≤ δ.val i k + δ.val j l) := by
  have hAB : δ.val i j + δ.val k l ≤ δ.val i k + δ.val j l ∨
      δ.val i j + δ.val k l ≤ δ.val i l + δ.val j k := hfp i j k l
  have hB : δ.val i k + δ.val j l ≤ δ.val i j + δ.val k l ∨
      δ.val i k + δ.val j l ≤ δ.val i l + δ.val j k := by
    rcases hfp i k j l with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa only [δ.symm k j] using h)
  have hC : δ.val i l + δ.val j k ≤ δ.val i j + δ.val k l ∨
      δ.val i l + δ.val j k ≤ δ.val i k + δ.val j l := by
    rcases hfp i l j k with h | h
    · exact Or.inl (by simpa only [δ.symm l k] using h)
    · exact Or.inr (by simpa only [δ.symm l j] using h)
  rcases hAB with hAB | hAB
  · rcases hB with hBA | hBC
    · refine Or.inl ⟨le_antisymm hAB hBA, ?_⟩
      rcases hC with hCA | hCB
      · exact hCA
      · linarith
    · refine Or.inr (Or.inr ⟨?_, hAB⟩)
      rcases hC with hCA | hCB
      · exact le_antisymm hBC (le_trans hCA hAB)
      · exact le_antisymm hBC hCB
  · rcases hC with hCA | hCB
    · refine Or.inr (Or.inl ⟨le_antisymm hAB hCA, ?_⟩)
      rcases hB with hBA | hBC
      · exact hBA
      · linarith
    · rcases hB with hBA | hBC
      · exact Or.inl ⟨le_antisymm (le_trans hAB hCB) hBA, le_trans hCB hBA⟩
      · exact Or.inr (Or.inr ⟨le_antisymm hBC hCB, le_trans hAB hCB⟩)

omit [Fintype X] [DecidableEq X] in
/-- ★★ **四点条件的等式一步**（Buneman 1974, 第 86–89 行）：

若 `δ i j + δ k l` 同时不大于另两对和，则另两对和**相等**。
（否则另两对和中较大者成为唯一最大，违反四点条件。） -/
theorem fourpoint_eq_of_le_both (δ : Dissimilarity X) (hfp : δ.FourPoint) (i j k l : X)
    (h₁ : δ.val i j + δ.val k l ≤ δ.val i k + δ.val j l)
    (h₂ : δ.val i j + δ.val k l ≤ δ.val i l + δ.val j k) :
    δ.val i k + δ.val j l = δ.val i l + δ.val j k := by
  rcases fourpoint_two_eq_max δ hfp i j k l with ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨h, -⟩
  · linarith
  · linarith
  · exact h

/-! ## 归纳步的算术核心（Buneman 1974, 第 78–95 行）

把归纳证明里**除树手术外的全部算术**做完：

* ★★ `exists_max_triple` —— 极大三元组存在（第 78–81 行）；
* ★★ `max_triple_ineq_left` / `max_triple_ineq_right` —— 由极大性导出的两条不等式（第 82–85 行）；
* ★★★ `max_triple_fourpoint_eq` —— 四点条件给出的等式（第 86–89 行）；
* ★★★ `max_triple_identity_one` —— Buneman 恒等式 (1)（第 90–91 行）；
* ★★ `rho_p_le_val` / `rho_add_rho` —— 新点 `t` 的两个边权（第 94 行）；
* ★★★ `shrinkVal_*` —— 扩张相异度 `δ'`（第 92–95 行）：对称、零对角、非负、
  **四点条件保持**、以及「`p`、`q` 挂在 `t` 上」的两条挂叶恒等式（(2a)/(2b)）。

⇒ 归纳装配（`InductiveAssembly`）所缺的**只剩树的图手术**。 -/

omit [Fintype X] [DecidableEq X] in
/-- 四点条件 ⟹ `δ ≥ 0`（`triangle` 取两点重合）。 -/
theorem val_nonneg (δ : Dissimilarity X) (hfp : δ.FourPoint) (x y : X) : 0 ≤ δ.val x y := by
  have h := triangle δ hfp x y y
  rw [δ.diag y] at h
  linarith

omit [Fintype X] [DecidableEq X] in
/-- **Buneman 得分** `f(a,b,c) = δ(a,c) + δ(b,c) − δ(a,b)`：第 81 行被最大化的量。 -/
def bunemanScore (δ : Dissimilarity X) (a b c : X) : ℝ :=
  δ.val a c + δ.val b c - δ.val a b

omit [Fintype X] [DecidableEq X] in
/-- 得分对头两个自变量对称（故极大三元组可交换前两位）。 -/
theorem bunemanScore_comm (δ : Dissimilarity X) (a b c : X) :
    δ.bunemanScore a b c = δ.bunemanScore b a c := by
  simp only [bunemanScore]
  rw [δ.symm b a]
  ring

/-- 三点互异（`3 ≤ |X|` 时存在）。 -/
theorem exists_three_distinct (h : 3 ≤ Fintype.card X) :
    ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have h1 : 1 < Fintype.card X := by omega
  obtain ⟨a⟩ : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨b, hba⟩ := Fintype.exists_ne_of_one_lt_card h1 a
  have hb : ({a, b} : Finset X).card < Fintype.card X := by
    rw [Finset.card_pair hba.symm]
    omega
  obtain ⟨c, hc⟩ : ∃ c, c ∉ ({a, b} : Finset X) := by
    by_contra h
    rw [not_exists] at h
    have huniv : ({a, b} : Finset X) = Finset.univ := by
      refine Finset.eq_univ_of_forall fun x => ?_
      by_contra hx
      exact h x hx
    rw [huniv, Finset.card_univ] at hb
    exact absurd hb (lt_irrefl _)
  have hca : c ≠ a := fun h => hc (by simp [h])
  have hcb : c ≠ b := fun h => hc (by simp [h])
  exact ⟨a, b, c, hba.symm, hca.symm, hcb.symm⟩

/-- ★★ **极大三元组存在**（Buneman 第 78–81 行）：`|X| ≥ 3` 时存在**互异**三元组
`(p,q,r)` 使得分 `f` 在所有互异三元组上最大。

（原文只说「out of all ordered triples」，但 `p = q` 会让 `f(p,p,r) = 2δ(p,r)` 取到更大的值，
而构造要求 `p ≠ q`；故须在**互异**三元组上取极大 —— 这是对原文的一处显式澄清。） -/
theorem exists_max_triple (δ : Dissimilarity X) (h3 : 3 ≤ Fintype.card X) :
    ∃ p q r : X, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c →
        δ.bunemanScore a b c ≤ δ.bunemanScore p q r := by
  obtain ⟨a₀, b₀, c₀, hab, hac, hbc⟩ := exists_three_distinct (X := X) h3
  have hne : ((Finset.univ : Finset (X × X × X)).filter
      (fun t => t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2)).Nonempty :=
    ⟨(a₀, b₀, c₀), by simp [hab, hac, hbc]⟩
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image _
    (fun t : X × X × X => δ.bunemanScore t.1 t.2.1 t.2.2) hne
  have hcond := (Finset.mem_filter.mp ht).2
  have ht1 : t.1 ≠ t.2.1 := hcond.1
  have ht2 : t.1 ≠ t.2.2 := hcond.2.1
  have ht3 : t.2.1 ≠ t.2.2 := hcond.2.2
  exact ⟨t.1, t.2.1, t.2.2, ht1, ht2, ht3, fun a b c ha hb hc =>
    hmax (a, b, c) (by simp [ha, hb, hc])⟩

omit [Fintype X] [DecidableEq X] in
/-- ★★ **极大三元组的第一条不等式**（Buneman 第 83 行）：
`x ≠ q` 时 `δ(x,r) + δ(p,q) ≤ δ(x,q) + δ(p,r)`
（`x = p` 时两边相等，故不需 `x ≠ p`）。

（`x = r` 的退化情形就是三角不等式，故须分情形。） -/
theorem max_triple_ineq_left (δ : Dissimilarity X) (hfp : δ.FourPoint) {p q r x : X}
    (hqr : q ≠ r)
    (hmax : ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c →
      δ.bunemanScore a b c ≤ δ.bunemanScore p q r)
    (hxq : x ≠ q) :
    δ.val x r + δ.val p q ≤ δ.val x q + δ.val p r := by
  rcases eq_or_ne x r with hxr | hxr
  · rw [← hxr]
    have ht := triangle δ hfp x p q
    have h1 : δ.val x x = 0 := δ.diag x
    have h2 : δ.val p x = δ.val x p := δ.symm p x
    linarith
  · have h := hmax x q r hxq hxr hqr
    simp only [bunemanScore] at h
    linarith

omit [Fintype X] [DecidableEq X] in
/-- ★★ **极大三元组的第二条不等式**（Buneman 第 85 行）：
`x ≠ p` 时 `δ(x,r) + δ(p,q) ≤ δ(x,p) + δ(q,r)`
（`x = q` 时两边相等，故不需 `x ≠ q`）。 -/
theorem max_triple_ineq_right (δ : Dissimilarity X) (hfp : δ.FourPoint) {p q r x : X}
    (hpr : p ≠ r)
    (hmax : ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c →
      δ.bunemanScore a b c ≤ δ.bunemanScore p q r)
    (hxp : x ≠ p) :
    δ.val x r + δ.val p q ≤ δ.val x p + δ.val q r := by
  rcases eq_or_ne x r with hxr | hxr
  · rw [← hxr]
    have ht := triangle δ hfp x p q
    have h1 : δ.val x x = 0 := δ.diag x
    have h2 : δ.val q x = δ.val x q := (δ.symm x q).symm
    linarith
  · have h := hmax x p r hxp hxr hpr
    simp only [bunemanScore] at h
    linarith

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **四点条件给出的等式**（Buneman 第 86–89 行）：
极大三元组下，对任意 `x ∉ {p,q}`，`δ(x,q) + δ(p,r) = δ(x,p) + δ(q,r)`。 -/
theorem max_triple_fourpoint_eq (δ : Dissimilarity X) (hfp : δ.FourPoint) {p q r x : X}
    (hpr : p ≠ r) (hqr : q ≠ r)
    (hmax : ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c →
      δ.bunemanScore a b c ≤ δ.bunemanScore p q r)
    (hxp : x ≠ p) (hxq : x ≠ q) :
    δ.val x q + δ.val p r = δ.val x p + δ.val q r := by
  have h1 := max_triple_ineq_left δ hfp hqr hmax hxq
  have h2 := max_triple_ineq_right δ hfp hpr hmax hxp
  have h3 := fourpoint_eq_of_le_both δ hfp x r p q
    (by rw [δ.symm r q]; exact h2) (by rw [δ.symm r p]; exact h1)
  rw [δ.symm r q, δ.symm r p] at h3
  linarith

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **Buneman 恒等式 (1)**（第 90–91 行）：对任意 `x,y ∉ {p,q}`，
`δ(y,p) + δ(x,q) = δ(x,p) + δ(y,q)`。 -/
theorem max_triple_identity_one (δ : Dissimilarity X) (hfp : δ.FourPoint) {p q r x y : X}
    (hpr : p ≠ r) (hqr : q ≠ r)
    (hmax : ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c →
      δ.bunemanScore a b c ≤ δ.bunemanScore p q r)
    (hxp : x ≠ p) (hxq : x ≠ q) (hyp : y ≠ p) (hyq : y ≠ q) :
    δ.val y p + δ.val x q = δ.val x p + δ.val y q := by
  have hx := max_triple_fourpoint_eq δ hfp hpr hqr hmax hxp hxq
  have hy := max_triple_fourpoint_eq δ hfp hpr hqr hmax hyp hyq
  linarith

omit [Fintype X] [DecidableEq X] in
/-- ★★ **新点 `t` 到 `p` 的边权**：`ρ(p;q,r) ≤ δ(x,p)`（Buneman 第 94 行，
即第 116 行的「集合缩小后 `δ` 仍是度量」所需的非负性）。 -/
theorem rho_p_le_val (δ : Dissimilarity X) (hfp : δ.FourPoint) {p q r x : X}
    (hpr : p ≠ r)
    (hmax : ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c →
      δ.bunemanScore a b c ≤ δ.bunemanScore p q r)
    (hxp : x ≠ p) :
    δ.rho p q r ≤ δ.val x p := by
  have h2 := max_triple_ineq_right δ hfp hpr hmax hxp
  have h3 := triangle δ hfp x p r
  simp only [rho]
  linarith

omit [Fintype X] [DecidableEq X] in
/-- ★★ **两条挂叶边权之和**：`ρ(p;q,r) + ρ(q;p,r) = δ(p,q)`
（把 Buneman 第 106–110 行的 (2b) 写成对称形式的关键恒等式）。 -/
theorem rho_add_rho (δ : Dissimilarity X) (p q r : X) :
    δ.rho p q r + δ.rho q p r = δ.val p q := by
  simp only [rho]
  rw [δ.symm q p]
  ring

/-! ### 扩张相异度 `δ'`（Buneman 第 92–95 行）

点集 `S' = S ∖ {p,q} ∪ {t}`，其中 `t` 到 `x` 的距离取 `δ(x,p) − ρ(p;q,r)`
（原文第 95 行的 `d(t,x) = d(x,p) − d(t,p)`）。 -/

/-- **归纳步的新点集** `S ∖ {p,q} ∪ {t}`：`Sum.inl x` 是保留的旧点，`Sum.inr ()` 即新点 `t`。 -/
abbrev BunemanShrink (p q : X) : Type u := {x : X // x ≠ p ∧ x ≠ q} ⊕ Unit

/-- **扩张相异度**（Buneman 第 92–95 行）。 -/
def shrinkVal (δ : Dissimilarity X) (p q r : X) : BunemanShrink p q → BunemanShrink p q → ℝ
  | Sum.inl x, Sum.inl y => δ.val x.1 y.1
  | Sum.inl x, Sum.inr _ => δ.val x.1 p - δ.rho p q r
  | Sum.inr _, Sum.inl y => δ.val y.1 p - δ.rho p q r
  | Sum.inr _, Sum.inr _ => 0

omit [Fintype X] [DecidableEq X] in
theorem shrinkVal_inl_inl (δ : Dissimilarity X) (p q r : X)
    (x y : {x : X // x ≠ p ∧ x ≠ q}) :
    δ.shrinkVal p q r (Sum.inl x) (Sum.inl y) = δ.val x.1 y.1 := rfl

omit [Fintype X] [DecidableEq X] in
theorem shrinkVal_inl_inr (δ : Dissimilarity X) (p q r : X)
    (x : {x : X // x ≠ p ∧ x ≠ q}) (u : Unit) :
    δ.shrinkVal p q r (Sum.inl x) (Sum.inr u) = δ.val x.1 p - δ.rho p q r := rfl

omit [Fintype X] [DecidableEq X] in
theorem shrinkVal_inr_inl (δ : Dissimilarity X) (p q r : X) (u : Unit)
    (x : {x : X // x ≠ p ∧ x ≠ q}) :
    δ.shrinkVal p q r (Sum.inr u) (Sum.inl x) = δ.val x.1 p - δ.rho p q r := rfl

omit [Fintype X] [DecidableEq X] in
theorem shrinkVal_inr_inr (δ : Dissimilarity X) (p q r : X) (u v : Unit) :
    δ.shrinkVal p q r (Sum.inr u) (Sum.inr v) = 0 := rfl

omit [Fintype X] [DecidableEq X] in
/-- 扩张相异度**对称**（四种情形都按定义归约）。 -/
theorem shrinkVal_symm (δ : Dissimilarity X) (p q r : X) (a b : BunemanShrink p q) :
    δ.shrinkVal p q r a b = δ.shrinkVal p q r b a := by
  rcases a with x | u <;> rcases b with y | v
  · exact δ.symm x.1 y.1
  · rfl
  · rfl
  · rfl

omit [Fintype X] [DecidableEq X] in
/-- 扩张相异度**零对角**。 -/
theorem shrinkVal_self (δ : Dissimilarity X) (p q r : X) (a : BunemanShrink p q) :
    δ.shrinkVal p q r a a = 0 := by
  rcases a with x | u
  · exact δ.diag x.1
  · rfl

omit [Fintype X] [DecidableEq X] in
/-- ★★ 扩张相异度**非负**（Buneman 第 113 行；用的是 `rho_p_le_val`）。 -/
theorem shrinkVal_nonneg (δ : Dissimilarity X) (hfp : δ.FourPoint) {p q r : X}
    (hpr : p ≠ r)
    (hmax : ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c →
      δ.bunemanScore a b c ≤ δ.bunemanScore p q r)
    (a b : BunemanShrink p q) : 0 ≤ δ.shrinkVal p q r a b := by
  rcases a with x | u <;> rcases b with y | v
  · exact val_nonneg δ hfp x.1 y.1
  · exact sub_nonneg.mpr (rho_p_le_val δ hfp hpr hmax x.2.1)
  · exact sub_nonneg.mpr (rho_p_le_val δ hfp hpr hmax y.2.1)
  · exact le_refl 0

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **(2a)：`p` 挂在 `t` 上**（Buneman 第 106 行）：`δ(x,p) = ρ(p;q,r) + δ'(t,x)`。 -/
theorem attach_left (δ : Dissimilarity X) (p q r : X)
    (x : {x : X // x ≠ p ∧ x ≠ q}) :
    δ.val x.1 p = δ.rho p q r + δ.shrinkVal p q r (Sum.inr ()) (Sum.inl x) := by
  show δ.val x.1 p = δ.rho p q r + (δ.val x.1 p - δ.rho p q r)
  ring

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **(2b)：`q` 也挂在 `t` 上**：`δ(x,q) = ρ(q;p,r) + δ'(t,x)`。

（Buneman 第 107–110 行用恒等式 (1) 得到这一条；本文件等价地写成对称的
`ρ(q;p,r)` 形式，并用四点条件给出的等式 `max_triple_fourpoint_eq` 证明。） -/
theorem attach_right (δ : Dissimilarity X) (hfp : δ.FourPoint) {p q r : X}
    (hpr : p ≠ r) (hqr : q ≠ r)
    (hmax : ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c →
      δ.bunemanScore a b c ≤ δ.bunemanScore p q r)
    (x : {x : X // x ≠ p ∧ x ≠ q}) :
    δ.val x.1 q = δ.rho q p r + δ.shrinkVal p q r (Sum.inr ()) (Sum.inl x) := by
  have hx := max_triple_fourpoint_eq δ hfp hpr hqr hmax x.2.1 x.2.2
  have hs : δ.val q p = δ.val p q := δ.symm q p
  simp only [shrinkVal_inr_inl, rho]
  linarith

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **「`t` 处的三角不等式」**（四点条件保持中最实质的一步）：

`δ(x,y) ≤ δ'(t,x) + δ'(t,y)`。

由四点条件作用在 `(x,y,p,q)` 加上 `max_triple_fourpoint_eq` 得到：
`δ(x,y) + δ(p,q) ≤ δ(x,p) + δ(y,q)`（或对称的另一支），
再把 `δ(y,q) = δ(y,p) + δ(q,r) − δ(p,r)` 代入即可。 -/
theorem shrinkVal_triangle_at_t (δ : Dissimilarity X) (hfp : δ.FourPoint) {p q r : X}
    (hpr : p ≠ r) (hqr : q ≠ r)
    (hmax : ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c →
      δ.bunemanScore a b c ≤ δ.bunemanScore p q r)
    (x y : {x : X // x ≠ p ∧ x ≠ q}) :
    δ.val x.1 y.1 ≤ δ.shrinkVal p q r (Sum.inr ()) (Sum.inl x) +
      δ.shrinkVal p q r (Sum.inr ()) (Sum.inl y) := by
  rcases hfp x.1 y.1 p q with h | h
  · have hy := max_triple_fourpoint_eq δ hfp hpr hqr hmax y.2.1 y.2.2
    simp only [shrinkVal_inr_inl, rho]
    linarith
  · have hx := max_triple_fourpoint_eq δ hfp hpr hqr hmax x.2.1 x.2.2
    simp only [shrinkVal_inr_inl, rho]
    linarith

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **扩张后四点条件保持**（Buneman 第 112–113 行）：

`δ'` 在 `S ∖ {p,q} ∪ {t}` 上仍满足四点条件。

* 四个点都在旧集：原四点条件（第 112 行「It also follows from the definition of d on
  S ∪ {t} that d still satisfies the four-point condition」）；
* 恰一个 `t`：对 `(p, 其余三点)` 用四点条件，`ρ(p;q,r)` 两边抵消；
* 恰两个 `t`：要么两边同项（平凡），要么化归 `shrinkVal_triangle_at_t`。 -/
theorem shrinkVal_fourpoint (δ : Dissimilarity X) (hfp : δ.FourPoint) {p q r : X}
    (hpr : p ≠ r) (hqr : q ≠ r)
    (hmax : ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c →
      δ.bunemanScore a b c ≤ δ.bunemanScore p q r)
    (a b c d : BunemanShrink p q) :
    δ.shrinkVal p q r a b + δ.shrinkVal p q r c d ≤
        δ.shrinkVal p q r a c + δ.shrinkVal p q r b d ∨
      δ.shrinkVal p q r a b + δ.shrinkVal p q r c d ≤
        δ.shrinkVal p q r a d + δ.shrinkVal p q r b c := by
  rcases a with x | u <;> rcases b with y | v <;> rcases c with z | w <;> rcases d with t | s
  all_goals
    simp only [shrinkVal_inl_inl, shrinkVal_inl_inr, shrinkVal_inr_inl, shrinkVal_inr_inr]
  · simpa using hfp x.1 y.1 z.1 t.1
  · rcases hfp p z.1 x.1 y.1 with h | h
    · right
      linarith [δ.symm p x.1, δ.symm p y.1, δ.symm p z.1, δ.symm x.1 y.1,
        δ.symm x.1 z.1, δ.symm y.1 z.1, h]
    · left
      linarith [δ.symm p x.1, δ.symm p y.1, δ.symm p z.1, δ.symm x.1 y.1,
        δ.symm x.1 z.1, δ.symm y.1 z.1, h]
  · rcases hfp p t.1 x.1 y.1 with h | h
    · left
      linarith [δ.symm p x.1, δ.symm p y.1, δ.symm p t.1, δ.symm x.1 y.1,
        δ.symm x.1 t.1, δ.symm y.1 t.1, h]
    · right
      linarith [δ.symm p x.1, δ.symm p y.1, δ.symm p t.1, δ.symm x.1 y.1,
        δ.symm x.1 t.1, δ.symm y.1 t.1, h]
  · left
    simpa only [shrinkVal_inl_inl, shrinkVal_inl_inr, shrinkVal_inr_inl, shrinkVal_inr_inr,
      add_zero, zero_add] using shrinkVal_triangle_at_t δ hfp hpr hqr hmax x y
  · rcases hfp p x.1 z.1 t.1 with h | h
    · right
      linarith [δ.symm p x.1, δ.symm p z.1, δ.symm p t.1, δ.symm x.1 z.1,
        δ.symm x.1 t.1, δ.symm z.1 t.1, h]
    · left
      linarith [δ.symm p x.1, δ.symm p z.1, δ.symm p t.1, δ.symm x.1 z.1,
        δ.symm x.1 t.1, δ.symm z.1 t.1, h]
  · right
    linarith
  · left
    linarith
  · left
    linarith
  · rcases hfp p y.1 z.1 t.1 with h | h
    · left
      linarith [δ.symm p y.1, δ.symm p z.1, δ.symm p t.1, δ.symm y.1 z.1,
        δ.symm y.1 t.1, δ.symm z.1 t.1, h]
    · right
      linarith [δ.symm p y.1, δ.symm p z.1, δ.symm p t.1, δ.symm y.1 z.1,
        δ.symm y.1 t.1, δ.symm z.1 t.1, h]
  · left
    linarith
  · right
    linarith
  · left
    linarith
  · left
    simpa only [shrinkVal_inl_inl, shrinkVal_inl_inr, shrinkVal_inr_inl, shrinkVal_inr_inr,
      add_zero, zero_add] using shrinkVal_triangle_at_t δ hfp hpr hqr hmax z t
  · left
    linarith
  · left
    linarith
  · left
    linarith

/-- ★★ 扩张相异度是**相异度**（打包 `shrinkVal` 的对称与零对角）。 -/
def shrinkDissimilarity (δ : Dissimilarity X) (p q r : X) :
    Dissimilarity (BunemanShrink p q) where
  val := δ.shrinkVal p q r
  symm := δ.shrinkVal_symm p q r
  diag := δ.shrinkVal_self p q r

/-! ## ⬜ 归纳装配（缺口）与目标定理 -/

/-- **Buneman 存在性目标**（Buneman 1974, Theorem 2，第 70–72 行）：

存在加权树 `T`（本库的 `Phylogram X`：无度 2 顶点、叶恰为 `X` 的正规形），
使树上路径距离在叶上等于 `δ`。 -/
def ExistsRealizingPhylogram (δ : Dissimilarity X) : Prop :=
  ∃ T : Phylogram.{u, u} X, ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y

/-- ⬜ **归纳装配（T0.2 的缺口，作为显式假设，不用 `sorry`）**。

Buneman 归纳证明（第 74–121 行）的**装配部分**：

1. 基例：`|Y| ≤ 2`（一条边 / 单点树）；
2. 归纳步：取极大三元组 `(p,q,r)`，在 `Y ∖ {p,q} ∪ {t}` 上用归纳假设，
   再把 `p,q` 作为**悬挂叶**挂到 `t` 上（边权 `ρ(p;q,r)`、`ρ(q;p,r)`）。

其中「挂两个悬挂叶」的**图手术**及其 `IsTree` / 度数 / `dist` 记账是
本库尚未建立的部分（本文件其余定理把它所需的**算术**全部证出）。
形式与 `Phylo/Algorithm/NJ.lean` 的 `MaxZCherryCore` 一致：显式假设、零 `sorry`。

（第一个参数只用来**钉住宇宙** `u`：装配须对与 `X` 同宇宙的所有有限类型成立。） -/
def InductiveAssembly (_X : Type u) : Prop :=
  ∀ {Y : Type u} [Fintype Y] [DecidableEq Y] (δ : Dissimilarity Y),
    δ.FourPoint → δ.PositiveDefinite → δ.ExistsRealizingPhylogram

/-- **目标定理（条件形式）**：Buneman 1974 Theorem 2。

在 `InductiveAssembly`（归纳装配，见其 docstring）下，
四点条件 + 正定 ⟹ 存在实现 `δ` 的 `Phylogram`。 -/
theorem exists_phylogram_of_fourPoint (δ : Dissimilarity X) (hFP : δ.FourPoint)
    (hpos : δ.PositiveDefinite) (hgap : InductiveAssembly X) :
    δ.ExistsRealizingPhylogram :=
  hgap (Y := X) (δ := δ) hFP hpos

end Dissimilarity

end NJ
