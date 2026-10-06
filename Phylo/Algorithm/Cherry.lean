/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Phylo.Core

/-!
# `Phylo.Algorithm.Cherry` —— 樱桃（cherry）与「每棵树都有 cherry」

`CONCEPTS.md` §5 的 M5 算法层地基。**cherry** `{a,b}` 指两个叶共享一个公共邻居 ——
这是 NJ / UPGMA / 贪心归约类算法的**基本归约单元**（「每棵树都有 cherry」是它们的起点）。

## 主定理 `exists_isCherry`

**任何**（`|V| ≥ 3` 的）**Cladogram 都有 cherry**。证明走**纯组合计数**（不用距离）：

* **上界 `ℓ ≤ i`**（`card_leafFinset_le_internalFinset`）：无 cherry ⟹「叶 ↦ 其唯一邻居」是
  **单射**，且落点都是**内部顶点**；
* **下界 `i + 2 ≤ ℓ`**（`internalFinset_card_add_two_le_leafFinset_card`）：握手引理
  `2|E| = Σ deg` + 树的 `|E| = n - 1` +「内部顶点度 ≥ 3」+ `n = ℓ + i`；
* 两者矛盾。

（`|V| = 2` 时确有反例：单边 `u—w`，两叶相邻而不共邻居 —— 故假设 `3 ≤ |V|` 不可去。）
-/

namespace Cladogram

open SimpleGraph

variable {X : Type*} [Fintype X] [DecidableEq X] (T : Cladogram X)

/-- **樱桃（cherry）**：叶 `a`、`b` **共享一个公共邻居** `v`。 -/
def IsCherry (a b : X) : Prop :=
  a ≠ b ∧ ∃ v : T.V, T.graph.Adj (T.leaf a) v ∧ T.graph.Adj (T.leaf b) v

/-- 樱桃关系**对称**。 -/
theorem isCherry_symm {a b : X} (h : T.IsCherry a b) : T.IsCherry b a :=
  ⟨h.1.symm, by obtain ⟨v, h1, h2⟩ := h.2; exact ⟨v, h2, h1⟩⟩

theorem isCherry_comm (a b : X) : T.IsCherry a b ↔ T.IsCherry b a :=
  ⟨isCherry_symm T, isCherry_symm T⟩

/-! ### 叶集与内部顶点集 -/

/-- 叶顶点集。 -/
noncomputable def leafFinset : Finset T.V := by
  classical
  exact Finset.univ.filter T.IsLeaf

/-- 内部顶点集。 -/
noncomputable def internalFinset : Finset T.V := by
  classical
  exact Finset.univ.filter fun v => ¬ T.IsLeaf v

theorem mem_leafFinset {v : T.V} : v ∈ T.leafFinset ↔ T.IsLeaf v := by
  classical
  rw [leafFinset, Finset.mem_filter]
  simp

theorem mem_internalFinset {v : T.V} : v ∈ T.internalFinset ↔ ¬ T.IsLeaf v := by
  classical
  rw [internalFinset, Finset.mem_filter]
  simp

/-- 叶与内部顶点**划分**顶点集：`ℓ + i = |V|`。 -/
theorem leafFinset_card_add_internalFinset_card :
    T.leafFinset.card + T.internalFinset.card = Fintype.card T.V := by
  classical
  rw [leafFinset, internalFinset]
  simpa [Finset.card_univ] using
    (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset T.V)) T.IsLeaf)

/-! ### 「内部顶点度 ≥ 3」 -/

/-- **内部顶点的度 ≥ 3**（`|V| ≥ 2`）。

度 ≠ 1（否则是叶）、度 ≠ 2（`no_degree_two`）、度 ≠ 0（树连通 + 无孤立点）。 -/
theorem three_le_degree_of_not_isLeaf (hV : 2 ≤ Fintype.card T.V) {v : T.V}
    (hv : ¬ T.IsLeaf v) : 3 ≤ T.graph.degree v := by
  haveI : Nontrivial T.V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hne1 : T.graph.degree v ≠ 1 := fun h => hv ((T.isLeaf_iff_degree_eq_one v).mpr h)
  have hne2 : T.graph.degree v ≠ 2 := T.no_degree_two v
  have hne0 : T.graph.degree v ≠ 0 := by
    intro h0
    obtain ⟨w, hw⟩ := exists_ne v
    have hpos := SimpleGraph.Reachable.degree_pos_left (G := T.graph) (u := v) (v := w) hw.symm
      (T.isTree.connected v w)
    omega
  omega

/-! ### 「叶的邻居是内部顶点」 -/

/-- **两个度 1 的相邻顶点 ⟹ 树只有这两个顶点**（故 `|V| ≥ 3` 时不存在叶–叶边）。 -/
theorem eq_or_eq_of_adj_of_degree_eq_one {v w : T.V} (hv : T.graph.degree v = 1)
    (hw : T.graph.degree w = 1) (hadj : T.graph.Adj v w) (z : T.V) : z = v ∨ z = w := by
  have hv1 : T.graph.neighborFinset v = {w} := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp
      (by rw [card_neighborFinset_eq_degree T.graph v, hv])
    have hwa : w ∈ T.graph.neighborFinset v := (mem_neighborFinset T.graph v w).mpr hadj
    rw [ha] at hwa
    rw [ha, Finset.mem_singleton.mp hwa]
  have hw1 : T.graph.neighborFinset w = {v} := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp
      (by rw [card_neighborFinset_eq_degree T.graph w, hw])
    have hva : v ∈ T.graph.neighborFinset w := (mem_neighborFinset T.graph w v).mpr hadj.symm
    rw [ha] at hva
    rw [ha, Finset.mem_singleton.mp hva]
  obtain ⟨p⟩ := T.isTree.connected z v
  refine Walk.recOn (motive := fun a b _ => b = v → (a = v ∨ a = w)) p ?_ ?_ rfl
  · intro a ha
    exact Or.inl ha
  · intro a b c hadj' q ih hc
    rcases ih hc with hb | hb
    · rw [hb] at hadj'
      exact Or.inr (Finset.mem_singleton.mp
        (by rw [← hv1]; exact (mem_neighborFinset T.graph v a).mpr hadj'.symm))
    · rw [hb] at hadj'
      exact Or.inl (Finset.mem_singleton.mp
        (by rw [← hw1]; exact (mem_neighborFinset T.graph w a).mpr hadj'.symm))

/-- **叶的邻居是内部顶点**（`|V| ≥ 3`）：否则两叶相邻 ⟹ 树只有 2 个顶点。 -/
theorem not_isLeaf_of_adj_of_isLeaf (hV : 3 ≤ Fintype.card T.V) {v w : T.V}
    (hv : T.IsLeaf v) (hadj : T.graph.Adj v w) : ¬ T.IsLeaf w := by
  intro hw
  have hv1 : T.graph.degree v = 1 := (T.isLeaf_iff_degree_eq_one v).mp hv
  have hw1 : T.graph.degree w = 1 := (T.isLeaf_iff_degree_eq_one w).mp hw
  have h2 := T.eq_or_eq_of_adj_of_degree_eq_one hv1 hw1 hadj
  have hsub : (Finset.univ : Finset T.V) ⊆ {v, w} := fun z _ => by
    rcases h2 z with h | h <;> simp [h]
  have hcard2 : Fintype.card T.V ≤ 2 := by
    calc Fintype.card T.V = (Finset.univ : Finset T.V).card := Finset.card_univ.symm
      _ ≤ ({v, w} : Finset T.V).card := Finset.card_le_card hsub
      _ = 2 := Finset.card_pair hadj.ne
  omega

/-! ### 上界：无 cherry ⟹ `ℓ ≤ i` -/

/-- 叶的**唯一邻居**（非叶时取自身，仅作占位）。 -/
noncomputable def leafNb (v : T.V) : T.V :=
  if h : T.graph.degree v = 1 then (degree_eq_one_iff_existsUnique_adj.mp h).choose else v

theorem adj_leafNb {v : T.V} (h : T.graph.degree v = 1) : T.graph.Adj v (T.leafNb v) := by
  rw [leafNb, dif_pos h]
  exact (degree_eq_one_iff_existsUnique_adj.mp h).choose_spec.1

/-- **无 cherry ⟹ `ℓ ≤ i`**：`叶 ↦ 唯一邻居` 是单射，且落点均为内部顶点。 -/
theorem card_leafFinset_le_internalFinset (hV : 3 ≤ Fintype.card T.V)
    (hnocherry : ∀ a b : X, ¬ T.IsCherry a b) :
    T.leafFinset.card ≤ T.internalFinset.card := by
  refine Finset.card_le_card_of_injOn T.leafNb ?_ ?_
  · intro v hv
    simp only [Finset.mem_coe] at hv ⊢
    rw [mem_internalFinset]
    exact T.not_isLeaf_of_adj_of_isLeaf hV ((mem_leafFinset T).mp hv)
      (T.adj_leafNb ((T.isLeaf_iff_degree_eq_one v).mp ((mem_leafFinset T).mp hv)))
  · intro v hv u hu heq
    simp only [Finset.mem_coe] at hv hu
    have hv' : T.IsLeaf v := (mem_leafFinset T).mp hv
    have hu' : T.IsLeaf u := (mem_leafFinset T).mp hu
    have hv1 : T.graph.degree v = 1 := (T.isLeaf_iff_degree_eq_one v).mp hv'
    have hu1 : T.graph.degree u = 1 := (T.isLeaf_iff_degree_eq_one u).mp hu'
    by_contra hne
    obtain ⟨a, ha⟩ := hv'
    obtain ⟨b, hb⟩ := hu'
    have hab : a ≠ b := fun hab => hne (by rw [← ha, ← hb, hab])
    refine hnocherry a b ⟨hab, T.leafNb v, ?_, ?_⟩
    · rw [ha]; exact T.adj_leafNb hv1
    · rw [hb, heq]; exact T.adj_leafNb hu1

/-! ### 下界：`i + 2 ≤ ℓ` -/

/-- **下界 `i + 2 ≤ ℓ`**（握手引理 + 树的边数 + 内部顶点度 ≥ 3）。 -/
theorem internalFinset_card_add_two_le_leafFinset_card (hV : 3 ≤ Fintype.card T.V) :
    T.internalFinset.card + 2 ≤ T.leafFinset.card := by
  classical
  have hsplit : T.leafFinset.sum (fun v => T.graph.degree v)
      + T.internalFinset.sum (fun v => T.graph.degree v) = ∑ v, T.graph.degree v := by
    simpa [leafFinset, internalFinset] using
      (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset T.V) T.IsLeaf
        (fun v => T.graph.degree v))
  have hL : T.leafFinset.sum (fun v => T.graph.degree v) = T.leafFinset.card := by
    rw [show T.leafFinset.sum (fun v => T.graph.degree v) = T.leafFinset.sum (fun _ => 1) from
      Finset.sum_congr rfl fun v hv => ((mem_leafFinset T).mp hv).degree_eq_one]
    simp
  have hI : 3 * T.internalFinset.card ≤ T.internalFinset.sum (fun v => T.graph.degree v) := by
    have h := Finset.card_nsmul_le_sum T.internalFinset (fun v => T.graph.degree v) 3
      (fun v hv => T.three_le_degree_of_not_isLeaf (by omega) ((mem_internalFinset T).mp hv))
    simpa [mul_comm] using h
  have hdeg : ∑ v, T.graph.degree v = 2 * T.graph.edgeFinset.card :=
    T.graph.sum_degrees_eq_twice_card_edges
  have hE : T.graph.edgeFinset.card = Fintype.card T.V - 1 := by
    have := T.isTree.card_edgeFinset
    omega
  have hcard := T.leafFinset_card_add_internalFinset_card
  have h1 : T.leafFinset.card + 3 * T.internalFinset.card ≤ 2 * T.graph.edgeFinset.card := by
    rw [← hdeg, ← hsplit]
    exact add_le_add hL.ge hI
  rw [hE, ← hcard] at h1
  omega

/-! ### 主定理 -/

/-- ★ **每棵树都有 cherry**（`|V| ≥ 3`）。

NJ / UPGMA 等贪心归约算法的起点：总能找到一对共享邻居的叶并归约掉。 -/
theorem exists_isCherry (hV : 3 ≤ Fintype.card T.V) : ∃ a b : X, T.IsCherry a b := by
  by_contra h
  push_neg at h
  have hle := T.card_leafFinset_le_internalFinset hV h
  have hge := T.internalFinset_card_add_two_le_leafFinset_card hV
  omega

end Cladogram
