/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Aho

/-!
# `Phylo.Consensus` —— 多数共识（majority-rule consensus）与贪婪共识

给定一族（同一叶集上的）树，一个 split 的**支持度** = 含它的树的个数。

**核心组合事实（鸽笼原理）**：若 `s`、`t` 都在**严格多数**（> n/2）的树中出现，
则它们必在**同一棵**树中出现 —— 因为两个支持集的大小之和 > n，必相交。
而树的 split 系统两两相容（`pairwiseCompatible`，`Phylo/Split.lean:894`，root 命名空间），

⇒ **多数 split 两两相容**（`majority_compatible`）。

再由 **Aho–Buneman**（`Phylo.Aho`）立得：

⇒ **多数共识树存在**（`majority_consensus_exists`）。

这是 Margush–McMorris（1981）多数共识的经典论证，也解释了为什么
「贪婪共识（greedy consensus）」总能在多数 split 上成功：它们从不冲突。
-/

open Phylo

universe u

/-! ## 支持度与多数相容 -/

/-- `s` 在树族 `T` 中的**支持度**（含 `s` 的树的个数）。 -/
noncomputable def supportCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Type*} [Fintype X] [DecidableEq X] (T : ι → Cladogram X) (s : Split X) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => (T i).IsSplitOf s).card

/-- `s` 是**严格多数** split：出现在多于一-半的树里。 -/
def IsMajority {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Type*} [Fintype X] [DecidableEq X] (T : ι → Cladogram X) (s : Split X) : Prop :=
  2 * supportCount T s > Fintype.card ι

/-- ★★ **严格多数的 split 两两相容**（鸽笼原理）。

`s`、`t` 的支持集大小都 `> n/2`，故两者之和 `> n`，必交于一棵树 `T i`；
`T i` 的两个 split 相容（`pairwiseCompatible`）⟹ `s` 与 `t` 相容。

**这是多数共识的全部组合内容** —— 其余由 Aho–Buneman 承担。 -/
theorem majority_compatible {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Type*} [Fintype X] [DecidableEq X] (T : ι → Cladogram X) (s t : Split X)
    (hs : IsMajority T s) (ht : IsMajority T t) : Split.Compatible s t := by
  classical
  by_contra hc
  have hdisj : Disjoint (Finset.univ.filter fun i => (T i).IsSplitOf s)
      (Finset.univ.filter fun i => (T i).IsSplitOf t) := by
    rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨i, hi⟩
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hi
    exact hc (pairwiseCompatible (T i) s hi.1.2 t hi.2.2)
  have hcard : (Finset.univ.filter (fun i => (T i).IsSplitOf s)
      ∪ Finset.univ.filter (fun i => (T i).IsSplitOf t)).card
      = (Finset.univ.filter fun i => (T i).IsSplitOf s).card
        + (Finset.univ.filter fun i => (T i).IsSplitOf t).card :=
    Finset.card_union_of_disjoint hdisj
  have hle : (Finset.univ.filter (fun i => (T i).IsSplitOf s)
      ∪ Finset.univ.filter (fun i => (T i).IsSplitOf t)).card ≤ Fintype.card ι := by
    have h := Finset.card_le_card (Finset.subset_univ
      (Finset.univ.filter (fun i => (T i).IsSplitOf s)
        ∪ Finset.univ.filter fun i => (T i).IsSplitOf t))
    rwa [Finset.card_univ] at h
  have hs' : 2 * (Finset.univ.filter fun i => (T i).IsSplitOf s).card > Fintype.card ι := hs
  have ht' : 2 * (Finset.univ.filter fun i => (T i).IsSplitOf t).card > Fintype.card ι := ht
  omega

/-! ## 多数共识树 -/

/-- **（非平凡）多数 split 集**：严格多数、且两侧各 `≥ 2` 个叶。 -/
noncomputable def majoritySplits {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Type*} [Fintype X] [DecidableEq X] (T : ι → Cladogram X) : Finset (Split X) := by
  classical
  exact Finset.univ.filter fun s : Split X =>
    IsMajority T s ∧ 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card

theorem mem_majoritySplits {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Type*} [Fintype X] [DecidableEq X] {T : ι → Cladogram X} {s : Split X} :
    s ∈ majoritySplits T ↔ IsMajority T s ∧ 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card := by
  classical
  simp [majoritySplits]

set_option maxHeartbeats 800000 in
/-- ★★★ **多数共识树存在**（Margush–McMorris 1981 + Aho–Buneman）。

对任一树族 `T`，存在一棵树展示**所有严格多数的非平凡 split**。

**证明**：多数 split 两两相容（`majority_compatible`），
再由 `compatible_exists_rootedTree` 建出树。 -/
theorem majority_consensus_exists {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Type u} [Fintype X] [DecidableEq X] (T : ι → Cladogram X)
    (h2 : 2 ≤ Fintype.card X) :
    ∃ Tr : RootedTree.{u, u} X, ∀ s ∈ majoritySplits T, Tr.DisplaysSplit s := by
  classical
  have : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  refine compatible_exists_rootedTree (majoritySplits T) (Classical.arbitrary X) ?_ ?_ h2
  · intro s hs t ht
    rw [mem_majoritySplits] at hs ht
    exact majority_compatible T s t hs.1 ht.1
  · intro s hs
    rw [mem_majoritySplits] at hs
    exact ⟨hs.2.1, hs.2.2⟩

/-! ## 推论：全体一致的 split -/

/-- **全体一致（unanimous）的 split 必是多数 split**（`ι` 非空时）。 -/
theorem isMajority_of_forall {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {X : Type*} [Fintype X] [DecidableEq X] (T : ι → Cladogram X) {s : Split X}
    (h : ∀ i, (T i).IsSplitOf s) : IsMajority T s := by
  classical
  have hfilter : (Finset.univ.filter fun i => (T i).IsSplitOf s) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => h i
  have hc : supportCount T s = Fintype.card ι := by
    simp only [supportCount]
    rw [hfilter, Finset.card_univ]
  have hpos : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ‹Nonempty ι›
  show 2 * supportCount T s > Fintype.card ι
  rw [hc]
  omega
