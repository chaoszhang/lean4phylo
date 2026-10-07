/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.BunemanGraft

/-!
# `Phylo.InductiveAssembly` —— Buneman 归纳装配（TASK 4）

**文献**：P. Buneman, *A Note on the Metric Properties of Trees*,
J. Combinatorial Theory (B) **17** (1974) 48–50，
`references/md/Buneman1974_MetricPropertiesOfTrees.md` 第 74–121 行（Theorem 2 的归纳证明）。

**转录 vs 改编**：**改编**。`Phylo/Buneman.lean`（已登记）给出归纳步的全部算术；
`Phylo/BunemanGraft.lean`（已登记）给出挂叶的图手术、`IsTree`、度数记账与 `dist` 记账；
本文件负责**装配**（基例 + 强归纳），并由此**收口 T0.2**：
`NJ.Dissimilarity.InductiveAssembly` 不再是假设，而是**定理**。

## ⚠ 两条**属于目标本身**的障碍（先说清楚，避免在假命题上自旋）

### （A）`|Y| = 1` **不存在任何 `Phylogram`**

`Cladogram.leaf_iff_degree_one` 要求「度 `1` 的顶点」**恰是**标签的像，于是标签数
`|Y|` **等于**树的度 `1` 顶点数。而非空有限树只有两种可能：

* 只有 1 个顶点 —— 度为 `0`，**没有**度 `1` 顶点；
* 至少 2 个顶点 —— 至少有 **2** 个度 `1` 顶点（`SimpleGraph.IsTree.exists_ne_and_degree_eq_one`）。

故 `|Y| = 1` 时 `Phylogram Y` 是**空类型**（★★★ `Phylo.not_nonempty_phylogram_of_subsingleton`）。
**推论**：

* **修正前**的 `Dissimilarity.InductiveAssembly`（对**所有** `Y : Type u` 量化，含单点类型）
  **是假命题** —— ★★★ `Phylo.not_inductiveAssembly_without_card_hypothesis`
  （`Phylo/Buneman.lean` 的现行版本已补上 `Fintype.card Y ≠ 1` 前提）；
* 形如 `Fintype.card Y ≤ 3 → δ.ExistsRealizingPhylogram` 的基例**也是假命题**（含 `|Y| = 1`）；
  正确的基例必须**排除** `|Y| = 1`（注意 `|Y| = 0` 是合法的，故不是 `2 ≤ card`）。

### （B）只有 `PositiveDefinite` 而没有 `FourPoint` 时，**边权非负性无法满足**

`Phylogram.w_nonneg` 要求每条边权 `≥ 0`。`|Y| = 3` 的星形（中心 + 3 叶）边权必为

`w_x = (δ(x,y) + δ(x,z) − δ(y,z)) / 2`，`w_y`、`w_z` 同理；

其非负**等价于**三角不等式。而 `Dissimilarity`（对称 + 零对角）与 `PositiveDefinite`
**都不蕴含**三角不等式：`δ(y,z) = 21`、`δ(x,y) = δ(x,z) = 10` 给出 `w_x = −1/2 < 0`。
三角不等式由**四点条件**推出（`Dissimilarity.triangle`，`Phylo/Algorithm/NJ.lean:107`），
故基例必须假设 **`δ.FourPoint`**。

> **（B'）`PositiveDefinite` 其实完全用不到。** 归纳构造（选极大三元组 → 缩小 →
> 挂叶）从不使用正定性；`δ.rho_nonneg` 只需要四点条件。故本文件的强归纳只假设
> `Fintype.card Y ≠ 1` + `δ.FourPoint`（★★★ `Phylo.exists_realizingPhylogram_of_card_ne_one`），
> `PositiveDefinite` 只在收口（★★★ `Phylo.inductiveAssembly`、★ `Phylo.exists_phylogram_of_fourPoint'`）
> 里作为**被忽略的形参**出现。这比「先证缩小时的 `shrinkVal` 正定引理」省一条引理。

## ★ 已证内容（本文件）

**障碍的证据（用于修正目标）**

* **★★★ `Phylo.not_nonempty_phylogram_of_subsingleton`** —— 单点标签类型上没有 `Phylogram`。
* **★★★ `Phylo.not_inductiveAssembly_without_card_hypothesis`** ——
  **修正前**的装配陈述（对所有有限 `Y` 量化）是假命题（取单点 `Y`）。

**基例**

* **★★★ `Phylo.twoLeafPhylogram`** —— `Fintype.card Y = 2` 时的**单边树**：
  `V := Y`、`graph := ⊤`（两个顶点一条边）、`leaf` 是恒等嵌入、边权恒为 `c`。
* **★★★ `Phylo.twoLeafPhylogram_dist`** —— 该树的距离：同一标签给 `0`，不同标签给 `c`。
* **★★★ `Phylo.exists_realizingPhylogram_of_card_eq_two`** —— **基例 `|Y| = 2`**：
  `δ.FourPoint → Fintype.card Y = 2 → δ.ExistsRealizingPhylogram`（取 `c := δ.val a b`，
  非负性用 `Dissimilarity.val_nonneg`）。
* **★★★ `Phylo.exists_realizingPhylogram_of_isEmpty`** —— **基例 `|Y| = 0`**：
  单顶点无边树（`V := PUnit`、`graph := ⊥`、`w ≡ 0`；标签嵌入用 `Function.Embedding.ofIsEmpty`，
  距离量化是空量化）。
* **★★ `Phylo.degree_top_eq_one_of_card_eq_two`** —— 两个标签时 `⊤` 的度为 `1`。
* **★★★ `Phylo.card_bunemanShrink`** —— **缩小后的标签数**：
  `p ≠ q → Fintype.card (BunemanShrink p q) = Fintype.card Y - 1`
  （`Fintype.card_sum` + `Fintype.card_subtype` + `Finset.filter_ne'` ×2 + `Finset.card_erase_of_mem`）。

**归纳步与收口（T0.2 完成）**

* **★★★ `Phylo.exists_realizingPhylogram_of_card_ne_one`** —— **主定理（强形式）**：
  `Fintype.card Y ≠ 1 → δ.FourPoint → δ.ExistsRealizingPhylogram`。
  对 `Fintype.card Y` 做 `Nat.strong_induction_on`；`n = 0` 用
  ★★★ `exists_realizingPhylogram_of_isEmpty`，`n = 2` 用
  ★★★ `exists_realizingPhylogram_of_card_eq_two`，`n ≥ 3` 用
  ★★ `Dissimilarity.exists_max_triple` + ★★ `Dissimilarity.shrinkDissimilarity` +
  ★★★ `Phylo.graftPhylogram` + ★★★ `Phylo.graftPhylogram_dist_leaf_{old,p,q,pq}`。
* **★★★ `Phylo.inductiveAssembly`** —— **T0.2 收口**：
  `NJ.Dissimilarity.InductiveAssembly X` 成立（`PositiveDefinite` 形参被忽略）。
* **★ `Phylo.exists_phylogram_of_fourPoint'`** —— `NJ.Dissimilarity.exists_phylogram_of_fourPoint`
  的**无 `hgap` 版本**：四点条件 + 正定 + `|Y| ≠ 1` ⟹ 存在实现 `δ` 的 `Phylogram`。

## 归纳路线（本文件实际落地，与旧版 ⬜ 指导的三处出入）

1. **只需要两个基例**：`|Y| = 0`（★ `exists_realizingPhylogram_of_isEmpty`）与
   `|Y| = 2`（★ `exists_realizingPhylogram_of_card_eq_two`）。
   **`|Y| = 3` 不需要单独造三点星形** —— 它由归纳步本身覆盖（取极大三元组、缩小到
   `BunemanShrink p q`（`|·| = 2`）、挂回 `p,q`）。旧版指导里的
   ⬜ `exists_realizingPhylogram_of_card_eq_three` 与 ⬜ `…_of_card_eq_two_or_three`
   因此**不再需要**，已删除（不是未证，是不必证）。
2. **`PositiveDefinite` 不进归纳陈述**（见上面 (B')），省掉一条 `shrinkVal` 正定引理。
3. **缩小后的 `FourPoint` 与「`p,q` 挂在 `t` 上」都是现成的**
   （★★★ `Dissimilarity.shrinkVal_fourpoint`、★★★ `Dissimilarity.attach_left` /
   `attach_right`，及 ★★ `Dissimilarity.rho_add_rho`），
   本文件只做「把 `graftPhylogram_dist_leaf_*` 的树距离逐点换回 `δ.val`」的 8 情形分类。

## ⬜ 待办

* 无。本文件的目标（T0.2：`InductiveAssembly` 由假设升级为定理）已**全部落地**，
  零 `sorry`、零 `axiom`、零 warning。
-/

noncomputable section

open SimpleGraph

universe u

namespace Phylo

attribute [local instance] Classical.propDecidable

section Refute

/-- ★★★ **标签类型是单点时不存在任何 `Phylogram`。**

`Cladogram.leaf_iff_degree_one` 要求「度 `1` 的顶点」**恰是**标签的像，于是
`|Y| = #(度 1 顶点)`；而非空有限树要么只有 1 个顶点（度 `0`，**没有**度 `1` 顶点），
要么有 **≥ 2** 个度 `1` 顶点（`SimpleGraph.IsTree.exists_ne_and_degree_eq_one`）。
故 `|Y| = 1` 时 `Phylogram Y` 是**空类型**。 -/
theorem not_nonempty_phylogram_of_subsingleton {Y : Type u} [Fintype Y] [Nonempty Y]
    [Subsingleton Y] : ¬ Nonempty (Phylogram.{u, u} Y) := by
  rintro ⟨T⟩
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  have hdeg : T.graph.degree (T.leaf y₀) = 1 :=
    (T.leaf_iff_degree_one (T.leaf y₀)).mp ⟨y₀, rfl⟩
  rcases subsingleton_or_nontrivial T.V with hsub | hnt
  · have hempty : T.graph.neighborFinset (T.leaf y₀) = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr fun w hw => ?_
      exact T.graph.notMem_neighborFinset_self (T.leaf y₀)
        (hsub.elim w (T.leaf y₀) ▸ hw)
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hempty] at hdeg
    exact absurd hdeg (by simp)
  · obtain ⟨a, b, hab, ha, hb⟩ :=
      @SimpleGraph.IsTree.exists_ne_and_degree_eq_one T.V T.graph hnt _ _ T.isTree
    obtain ⟨y, rfl⟩ := (T.leaf_iff_degree_one a).mpr ha
    obtain ⟨z, rfl⟩ := (T.leaf_iff_degree_one b).mpr hb
    exact hab (congrArg T.leaf (Subsingleton.elim y z))

/-- ★★★ **修正前的 `Dissimilarity.InductiveAssembly` 陈述是假命题。**

这是本库**第 4 起陈述层假命题**，也是唯一一起**目标本身为假**的事故：旧陈述
`∀ {Y} [Fintype Y] [DecidableEq Y] (δ), δ.FourPoint → δ.PositiveDefinite → δ.ExistsRealizingPhylogram`
对**所有**有限类型量化（含单点类型），而单点类型上没有 `Phylogram`
（★★★ `Phylo.not_nonempty_phylogram_of_subsingleton`），故后件恒假。

**反例**：取 `|Y| = 1`、`δ := 常数 0`。前件逐项满足 ——
`Dissimilarity`（对称 `rfl` + 零对角 `rfl`）、`δ.FourPoint`（`0 + 0 ≤ 0 + 0`）、
`δ.PositiveDefinite`（单点类型里 `Subsingleton.elim`）—— 而后件要求 `∃ T : Phylogram Y`，恒假。

保留此定理作为**修正的依据**：`Phylo/Buneman.lean` 现行
`InductiveAssembly` 已补上 `Fintype.card Y ≠ 1` 前提，故它**不再是**假命题
（并由 ★★★ `Phylo.inductiveAssembly` 证明）。 -/
theorem not_inductiveAssembly_without_card_hypothesis (Y : Type u) [Fintype Y]
    [DecidableEq Y] [Nonempty Y] [Subsingleton Y] :
    ¬ (∀ {Z : Type u} [Fintype Z] [DecidableEq Z] (δ : NJ.Dissimilarity Z),
        δ.FourPoint → δ.PositiveDefinite → δ.ExistsRealizingPhylogram) := by
  intro h
  let δ : NJ.Dissimilarity Y :=
    { val := fun _ _ => 0, symm := fun _ _ => rfl, diag := fun _ => rfl }
  have hfp : δ.FourPoint := fun _ _ _ _ => Or.inl (by simp [δ])
  have hpos : δ.PositiveDefinite := fun y z _ => Subsingleton.elim y z
  obtain ⟨T, -⟩ := h (Z := Y) (δ := δ) hfp hpos
  exact not_nonempty_phylogram_of_subsingleton (Y := Y) ⟨T⟩

end Refute

section TwoLeaf

variable {Y : Type u} [Fintype Y] [DecidableEq Y]

/-- ★★ 两个标签时完全图的度为 `1`。 -/
theorem degree_top_eq_one_of_card_eq_two (hcard : Fintype.card Y = 2) (v : Y) :
    (⊤ : SimpleGraph Y).degree v = 1 := by
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_top, Finset.card_compl,
    Finset.card_singleton, hcard]

/-- ★★★ **两个标签的树**：`V := Y`、`graph := ⊤`（两个顶点一条边）、`leaf` 是恒等嵌入、
所有边权取常数 `c`。 -/
noncomputable def twoLeafPhylogram (hcard : Fintype.card Y = 2) (c : ℝ) (hc : 0 ≤ c) :
    Phylogram Y where
  V := Y
  fintypeV := inferInstance
  decEqV := inferInstance
  graph := ⊤
  decAdj := inferInstance
  isTree := by
    refine SimpleGraph.IsTree.mk ?_ ?_
    · rw [SimpleGraph.connected_top_iff]
      exact Fintype.card_pos_iff.mp (by omega)
    · refine SimpleGraph.IsAcyclic.of_card_le_two ?_
      rw [ENat.card_eq_coe_fintype_card, hcard]
      norm_num
  leaf := Function.Embedding.refl Y
  leaf_iff_degree_one := by
    intro v
    rw [degree_top_eq_one_of_card_eq_two hcard v]
    simp
  no_degree_two := by
    intro v
    rw [degree_top_eq_one_of_card_eq_two hcard v]
    norm_num
  w := fun _ => c
  w_nonneg := fun _ => hc

-- 与 `Phylo/BunemanGraft.lean` 里 `graftCladogram`／`graftPhylogram` 同理：
-- `Cladogram.V` 是结构字段，`(twoLeafPhylogram …).V` 必须在 `reducible` 透明层归约，
-- 才能与「顶点集就是 `Y`」的陈述自由互转。
attribute [reducible] twoLeafPhylogram

/-- ★★★ **单边树的距离**：同一标签给 `0`，两个不同标签给 `c`。 -/
theorem twoLeafPhylogram_dist (hcard : Fintype.card Y = 2) (c : ℝ) (hc : 0 ≤ c) (x y : Y) :
    (twoLeafPhylogram hcard c hc).dist ((twoLeafPhylogram hcard c hc).leaf x)
        ((twoLeafPhylogram hcard c hc).leaf y)
      = if x = y then 0 else c := by
  classical
  by_cases hxy : x = y
  · subst hxy
    rw [ite_eq_left rfl]
    exact Phylogram.dist_self (twoLeafPhylogram hcard c hc)
      ((twoLeafPhylogram hcard c hc).leaf x)
  · rw [ite_eq_right hxy]
    have hpath : (SimpleGraph.Walk.cons ((SimpleGraph.top_adj x y).mpr hxy)
        (SimpleGraph.Walk.nil : (twoLeafPhylogram hcard c hc).graph.Walk y y)).IsPath := by
      rw [SimpleGraph.Walk.cons_isPath_iff]
      refine ⟨?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_nil]
        exact List.nodup_singleton y
      · rw [SimpleGraph.Walk.support_nil]
        simpa using hxy
    have hw : (twoLeafPhylogram hcard c hc).wExt s(x, y) = c := by
      rw [Phylogram.wExt,
        dite_eq_left ((SimpleGraph.mem_edgeSet _).mpr ((SimpleGraph.top_adj x y).mpr hxy))]
    calc (twoLeafPhylogram hcard c hc).dist ((twoLeafPhylogram hcard c hc).leaf x)
            ((twoLeafPhylogram hcard c hc).leaf y)
        = (twoLeafPhylogram hcard c hc).walkDist (SimpleGraph.Walk.cons
            ((SimpleGraph.top_adj x y).mpr hxy)
            (SimpleGraph.Walk.nil : (twoLeafPhylogram hcard c hc).graph.Walk y y)) :=
          Phylogram.dist_eq_walkDist_of_isPath _ _ hpath
      _ = (twoLeafPhylogram hcard c hc).wExt s(x, y)
            + (twoLeafPhylogram hcard c hc).walkDist
              (SimpleGraph.Walk.nil : (twoLeafPhylogram hcard c hc).graph.Walk y y) :=
          Phylogram.walkDist_cons _ _ _
      _ = (twoLeafPhylogram hcard c hc).wExt s(x, y) + 0 := by
          rw [Phylogram.walkDist_nil]
      _ = c := by rw [hw, add_zero]

/-- ★★★ **基例 `|Y| = 2`**：一条边，权 `δ(a,b)`，其中 `Y = {a,b}`。 -/
theorem exists_realizingPhylogram_of_card_eq_two (δ : NJ.Dissimilarity Y) (hfp : δ.FourPoint)
    (hcard : Fintype.card Y = 2) : δ.ExistsRealizingPhylogram := by
  classical
  obtain ⟨a, b, hab, huniv⟩ := Finset.card_eq_two (s := (Finset.univ : Finset Y)).mp (by
    rw [Finset.card_univ]; exact hcard)
  refine ⟨twoLeafPhylogram hcard (δ.val a b) (δ.val_nonneg hfp a b), ?_⟩
  intro x y
  rw [twoLeafPhylogram_dist]
  by_cases hxy : x = y
  · rw [ite_eq_left hxy, hxy, δ.diag]
  · rw [ite_eq_right hxy]
    have hx : x = a ∨ x = b := by
      have hmem : x ∈ (Finset.univ : Finset Y) := Finset.mem_univ x
      rw [huniv] at hmem
      simpa using hmem
    have hy : y = a ∨ y = b := by
      have hmem : y ∈ (Finset.univ : Finset Y) := Finset.mem_univ y
      rw [huniv] at hmem
      simpa using hmem
    rcases hx with hxa | hxb <;> rcases hy with hya | hyb
    · exact absurd (hxa.trans hya.symm) hxy
    · rw [hxa, hyb]
    · rw [hxb, hya, δ.symm b a]
    · exact absurd (hxb.trans hyb.symm) hxy

end TwoLeaf

section Assembly

open NJ.Dissimilarity

variable {Y : Type u} [Fintype Y] [DecidableEq Y]

/-- ★★★ **缩小后的标签数**：`|Y ∖ {p,q} ∪ {t}| = |Y| − 1`（`p ≠ q` 时）。

`BunemanShrink p q = {x // x ≠ p ∧ x ≠ q} ⊕ Unit`，故计数是
`|{x // x ≠ p ∧ x ≠ q}| + 1`；再用 `Fintype.card_subtype` 与
`Finset.filter_ne'`（两次）把子类型化到 `(univ.erase p).erase q`，
`Finset.card_erase_of_mem` 给出 `(|Y| − 1) − 1 = |Y| − 2`。 -/
theorem card_bunemanShrink {p q : Y} (hpq : p ≠ q) :
    Fintype.card (BunemanShrink p q) = Fintype.card Y - 1 := by
  classical
  have hsum : Fintype.card (BunemanShrink p q)
      = Fintype.card {x : Y // x ≠ p ∧ x ≠ q} + 1 := by
    rw [Fintype.card_sum, Fintype.card_unit]
  rw [hsum]
  have hsub : Fintype.card {x : Y // x ≠ p ∧ x ≠ q} = Fintype.card Y - 2 := by
    rw [Fintype.card_subtype]
    have hf : (Finset.univ.filter fun x : Y => x ≠ p ∧ x ≠ q)
        = (Finset.univ.erase p).erase q := by
      rw [← Finset.filter_filter, Finset.filter_ne', Finset.filter_ne']
    rw [hf,
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hpq.symm, Finset.mem_univ q⟩),
      Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ]
    omega
  rw [hsub]
  have h2 : 1 < Fintype.card Y := Fintype.one_lt_card_iff.mpr ⟨p, q, hpq⟩
  omega

omit [Fintype Y] [DecidableEq Y] in
/-- ★★★ **基例 `|Y| = 0`**：单顶点无边树。

`V := PUnit`（与 `Y` 无关，故不用搬运），`graph := ⊥`，`leaf := Function.Embedding.ofIsEmpty`，
边权恒 `0`。`leaf_iff_degree_one` 两侧都是 `False`：左边 `∃ x : Y, …` 因 `IsEmpty Y` 为空，
右边 `⊥.degree v = 0 ≠ 1`。距离量化 `∀ x y : Y, …` 是空量化。 -/
theorem exists_realizingPhylogram_of_isEmpty (δ : NJ.Dissimilarity Y) [IsEmpty Y] :
    δ.ExistsRealizingPhylogram := by
  refine ⟨{
    V := PUnit, fintypeV := inferInstance, decEqV := inferInstance
    graph := ⊥, decAdj := inferInstance
    isTree := ?_, leaf := Function.Embedding.ofIsEmpty
    leaf_iff_degree_one := ?_, no_degree_two := ?_
    w := fun _ => 0, w_nonneg := fun _ => le_refl 0 }, ?_⟩
  · rw [SimpleGraph.isTree_iff]
    constructor
    · rw [SimpleGraph.connected_iff]
      exact ⟨fun a _ => SimpleGraph.Reachable.refl a, ⟨PUnit.unit⟩⟩
    · rw [SimpleGraph.IsAcyclic]
      intro v c hc
      cases c with
      | nil => simp at hc
      | cons h _ => exact absurd h (by simp)
  · intro v
    have h : (⊥ : SimpleGraph PUnit).degree v = 0 := by simp [SimpleGraph.degree]
    rw [h]
    simp
  · intro v
    have h : (⊥ : SimpleGraph PUnit).degree v = 0 := by simp [SimpleGraph.degree]
    rw [h]
    norm_num
  · intro x
    exact isEmptyElim x

/-- ★★★ **主定理（强形式，无 `PositiveDefinite`）**：

`Fintype.card Y ≠ 1` + 四点条件 ⟹ 存在实现 `δ` 的 `Phylogram`。

证明是对 `n = Fintype.card Y` 的 `Nat.strong_induction_on`：

* `n = 0`：★★★ `exists_realizingPhylogram_of_isEmpty`（单顶点树）；
* `n = 2`：★★★ `exists_realizingPhylogram_of_card_eq_two`（单边树）；
* `n ≥ 3`：★★ `Dissimilarity.exists_max_triple` 取互异极大三元组 `(p,q,r)`
  （Buneman 第 78–81 行），在 `BunemanShrink p q = Y ∖ {p,q} ∪ {t}` 上用
  `δ' := δ.shrinkDissimilarity p q r`（Buneman 第 92–95 行）作归纳假设
  （★★★ `card_bunemanShrink` 给出 `|·| = |Y| − 1 < |Y|`，
  ★★★ `Dissimilarity.shrinkVal_fourpoint` 保住四点条件），
  再用 ★★★ `Phylo.graftPhylogram` 把 `p,q` 挂到 `t` 上（Buneman 第 119–121 行）。

八个 `x,y` 情形分别落到 ★★★ `Phylo.graftPhylogram_dist_leaf_old` / `_p` / `_q` / `_pq`，
再用 `Dissimilarity.shrinkVal_inl_inl`、★★★ `Dissimilarity.attach_left` / `attach_right`、
★★ `Dissimilarity.rho_add_rho` 把树距离换回 `δ.val`。 -/
theorem exists_realizingPhylogram_of_card_ne_one {Y : Type u} [Fintype Y] [DecidableEq Y]
    (δ : NJ.Dissimilarity Y) (hcard : Fintype.card Y ≠ 1) (hfp : δ.FourPoint) :
    δ.ExistsRealizingPhylogram := by
  classical
  have key : ∀ n : ℕ, ∀ {Z : Type u} [Fintype Z] [DecidableEq Z] (δ : NJ.Dissimilarity Z),
      Fintype.card Z = n → Fintype.card Z ≠ 1 → δ.FourPoint →
      δ.ExistsRealizingPhylogram := by
    intro n
    refine Nat.strong_induction_on (p := fun k => ∀ {Z : Type u} [Fintype Z] [DecidableEq Z]
        (δ : NJ.Dissimilarity Z), Fintype.card Z = k → Fintype.card Z ≠ 1 → δ.FourPoint →
        δ.ExistsRealizingPhylogram) n ?_
    intro m ih Z _instZ _decZ δ hcardZ hn1 hfpZ
    rcases eq_or_ne m 0 with hm0 | hm0
    · have hempty : IsEmpty Z := Fintype.card_eq_zero_iff.mp (hcardZ.trans hm0)
      exact exists_realizingPhylogram_of_isEmpty δ
    rcases eq_or_ne m 2 with hm2 | hm2
    · exact exists_realizingPhylogram_of_card_eq_two δ hfpZ (hcardZ.trans hm2)
    · have h3 : 3 ≤ Fintype.card Z := by omega
      obtain ⟨p, q, r, hpq, hpr, hqr, hmax⟩ := δ.exists_max_triple h3
      have hfp' : (δ.shrinkDissimilarity p q r).FourPoint := by
        intro a b c d
        exact shrinkVal_fourpoint δ hfpZ hpr hqr hmax a b c d
      have hcardShrink : Fintype.card (BunemanShrink p q) = Fintype.card Z - 1 :=
        card_bunemanShrink hpq
      have hlt : Fintype.card (BunemanShrink p q) < m := by omega
      have hne1 : Fintype.card (BunemanShrink p q) ≠ 1 := by omega
      obtain ⟨T', hT'⟩ := ih (Fintype.card (BunemanShrink p q)) hlt
        (δ.shrinkDissimilarity p q r) rfl hne1 hfp'
      have hT'' : ∀ a b : BunemanShrink p q,
          T'.dist (T'.leaf a) (T'.leaf b) = δ.shrinkVal p q r a b :=
        fun a b => (hT' a b).trans rfl
      refine ⟨graftPhylogram δ hfpZ p q r hpq T', ?_⟩
      intro x y
      by_cases hxp : x = p
      · subst x
        by_cases hyp : y = p
        · subst y
          rw [Phylogram.dist_self, δ.diag]
        · by_cases hyq : y = q
          · subst y
            rw [graftPhylogram_dist_leaf_pq δ hfpZ p q r hpq T', rho_add_rho δ p q r]
          · rw [graftPhylogram_dist_leaf_p δ hfpZ p q r hpq T' hyp hyq,
              hT'' (Sum.inr ()) (Sum.inl ⟨y, hyp, hyq⟩),
              ← attach_left δ p q r ⟨y, hyp, hyq⟩, δ.symm y p]
      · by_cases hxq : x = q
        · subst x
          by_cases hyp : y = p
          · subst y
            rw [Phylogram.dist_comm, graftPhylogram_dist_leaf_pq δ hfpZ p q r hpq T',
              rho_add_rho δ p q r, δ.symm q p]
          · by_cases hyq : y = q
            · subst y
              rw [Phylogram.dist_self, δ.diag]
            · rw [graftPhylogram_dist_leaf_q δ hfpZ p q r hpq T' hyp hyq,
                hT'' (Sum.inr ()) (Sum.inl ⟨y, hyp, hyq⟩),
                ← attach_right δ hfpZ hpr hqr hmax ⟨y, hyp, hyq⟩, δ.symm y q]
        · by_cases hyp : y = p
          · subst y
            rw [Phylogram.dist_comm, graftPhylogram_dist_leaf_p δ hfpZ p q r hpq T' hxp hxq,
              hT'' (Sum.inr ()) (Sum.inl ⟨x, hxp, hxq⟩),
              ← attach_left δ p q r ⟨x, hxp, hxq⟩]
          · by_cases hyq : y = q
            · subst y
              rw [Phylogram.dist_comm, graftPhylogram_dist_leaf_q δ hfpZ p q r hpq T' hxp hxq,
                hT'' (Sum.inr ()) (Sum.inl ⟨x, hxp, hxq⟩),
                ← attach_right δ hfpZ hpr hqr hmax ⟨x, hxp, hxq⟩]
            · rw [graftPhylogram_dist_leaf_old δ hfpZ p q r hpq T' hxp hxq hyp hyq,
                hT'' (Sum.inl ⟨x, hxp, hxq⟩) (Sum.inl ⟨y, hyp, hyq⟩),
                shrinkVal_inl_inl]
  exact key (Fintype.card Y) δ rfl hcard hfp

/-- ★★★ **Buneman 归纳装配（T0.2 收口）**：`NJ.Dissimilarity.InductiveAssembly X` 成立。

`InductiveAssembly` 的陈述是
`∀ {Y} [Fintype Y] [DecidableEq Y] (δ), Fintype.card Y ≠ 1 → δ.FourPoint → δ.PositiveDefinite →
δ.ExistsRealizingPhylogram`；这里直接由 ★★★ `exists_realizingPhylogram_of_card_ne_one`
给出，`PositiveDefinite` 前提**不被使用**（见文件头 (B')）。 -/
theorem inductiveAssembly (X : Type u) : NJ.Dissimilarity.InductiveAssembly X :=
  fun δ hcard hfp _ => exists_realizingPhylogram_of_card_ne_one δ hcard hfp

/-- ★ **`NJ.Dissimilarity.exists_phylogram_of_fourPoint` 的「删掉 `hgap`」版本**：
四点条件 + 正定 + `|Y| ≠ 1` ⟹ `∃ T : Phylogram Y` 实现 `δ`。
（原定理需要一个显式的归纳装配假设 `hgap`；本文件用 ★★★ `inductiveAssembly` 把它补齐。） -/
theorem exists_phylogram_of_fourPoint' {Y : Type u} [Fintype Y] [DecidableEq Y]
    (δ : NJ.Dissimilarity Y) (hcard : Fintype.card Y ≠ 1)
    (hfp : δ.FourPoint) (hpos : δ.PositiveDefinite) : δ.ExistsRealizingPhylogram :=
  NJ.Dissimilarity.exists_phylogram_of_fourPoint δ hcard hfp hpos (inductiveAssembly Y)

end Assembly

end Phylo
