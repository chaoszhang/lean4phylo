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
本文件负责**装配**（基例 + 强归纳）。

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
故基例必须假设 **`δ.FourPoint`**（`PositiveDefinite` 在 `|Y| = 2, 3` 时其实是多余的）。

## ★ 已证内容（本文件）

**障碍的证据（用于修正目标）**

* **★★★ `Phylo.not_nonempty_phylogram_of_subsingleton`** —— 单点标签类型上没有 `Phylogram`。
* **★★★ `Phylo.not_inductiveAssembly_without_card_hypothesis`** ——
  **修正前**的装配陈述（对所有有限 `Y` 量化）是假命题（取单点 `Y`）。

**基例（修正后）**

* **★★★ `Phylo.twoLeafPhylogram`** —— `Fintype.card Y = 2` 时的**单边树**：
  `V := Y`、`graph := ⊤`（两个顶点一条边）、`leaf` 是恒等嵌入、边权恒为 `c`。
* **★★★ `Phylo.twoLeafPhylogram_dist`** —— 该树的距离：同一标签给 `0`，不同标签给 `c`。
* **★★★ `Phylo.exists_realizingPhylogram_of_card_eq_two`** —— **基例 `|Y| = 2`**：
  `δ.FourPoint → Fintype.card Y = 2 → δ.ExistsRealizingPhylogram`（取 `c := δ.val a b`，
  非负性用 `Dissimilarity.val_nonneg`）。
* **★★ `Phylo.degree_top_eq_one_of_card_eq_two`** —— 两个标签时 `⊤` 的度为 `1`。

## ⬜ 待办（本文件**尚未**落地的）

* **⬜ `Phylo.exists_realizingPhylogram_of_card_eq_three`** —— **基例 `|Y| = 3`**：三点星形
  （中心度 3、三片叶度 1），边权 `w_x = (δ(x,y)+δ(x,z)−δ(y,z))/2`（非负用
  `Dissimilarity.triangle`）。可行路线：把它写成
  `Phylo.graftPhylogram` 作用在 `BunemanShrink p q`（2 个标签，用 ★★★
  `Phylo.twoLeafPhylogram`）上的结果，再用已登记的
  ★★★ `Phylo.graftPhylogram_dist_leaf_p/_q/_pq` + `Dissimilarity.attach_left`／
  `attach_right`／`rho_add_rho` 读出三条距离。
* **⬜ `Phylo.exists_realizingPhylogram_of_card_eq_two_or_three`** —— 上面两条的合并陈述。
* **⬜ 归纳步 / ★★★ `Phylo.inductiveAssembly`** —— 对**修正后**的装配陈述
  `∀ Y, Fintype.card Y ≠ 1 → δ.FourPoint → δ.PositiveDefinite → δ.ExistsRealizingPhylogram`
  做 `Fintype.card Y` 的强归纳（步长用 `exists_max_triple` + `shrinkDissimilarity` +
  已登记的 `Phylo.graftPhylogram_dist_leaf_*`）。
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
`InductiveAssembly` 已补上 `Fintype.card Y ≠ 1` 前提，故它**不再是**假命题。 -/
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

end Phylo
