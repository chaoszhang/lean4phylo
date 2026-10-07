/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Laminar

/-!
# `Phylo.Aho` —— Aho / Buneman：**相容的 split 系统必被一棵树展示**

**定理**（Aho–Sagiv–Szymanski 1981；Buneman 1971；Semple–Steel Thm 3.1.4）
一个 split 系统 `fam` 能被某棵（无根）树展示 **⟺** `fam` **两两相容**。

* **(⟹)** 即 `pairwiseCompatible`（`Phylo/Split.lean:894`，root 命名空间；本库已证：树的 split 系统两两相容）。
* **(⟸)** 本文件给出**构造**：这是 Aho 树构造算法（Aho's tree-building algorithm）的正确性。

**构造思路**（与库内「相容 ⟹ 存在树」同一路线）：
1. 固定 `ρ`，取每个 split 的**规范 cluster**（避开 `ρ` 的一侧）——
   相容性使它们**两两镶嵌**（`laminar_of_compatible_clusters`）；
2. 正规化（删单元素簇、加 `univ` 作根），仍镶嵌；
3. 用 `toRootedTreeOfCard` 把镶嵌族变成一棵 `RootedTree`；
4. `leafSide_parentEdge_of_card` 说明族里每个非 `univ` 的 `B` 都是某条边的叶侧。

**本文件证**：`∃ T, ∀ s ∈ fam, T` 展示 `s`（无根意义，允许 `s.swap`）。
-/

open Phylo

universe u

namespace RootedTree

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- 边 `e` 的 `u` 侧叶集（与 `Cladogram.sideLeaves` 同一定义）。 -/
noncomputable def sideLeaves (T : RootedTree X) (e : Sym2 T.V) (u : T.V) : Finset X := by
  classical
  exact Finset.univ.filter fun x => (T.graph.deleteEdges {e}).Reachable (T.leaf x) u

/-- `T` **展示** split `s`：`s` 的 `A` 侧恰是某条边的叶侧。 -/
def IsSplitOf (T : RootedTree X) (s : Split X) : Prop :=
  ∃ (a b : T.V) (_ : T.graph.Adj a b) (u : T.V), s.sideA = T.sideLeaves s(a, b) u

/-- `T` **展示** `s`（**允许换向**：无根意义下 `s` 与 `s.swap` 是同一个 split）。 -/
def DisplaysSplit (T : RootedTree X) (s : Split X) : Prop := T.IsSplitOf s ∨ T.IsSplitOf s.swap

end RootedTree

/-- `toRootedTreeOfCard` 的 `sideLeaves` 就是 `leafSide`（同一式子，定义相等）。 -/
@[simp] theorem toRootedTreeOfCard_sideLeaves {α : Type*} [Fintype α] [DecidableEq α]
    {F : Finset (Finset α)} (hl : LaminarFamily F)
    (huniv : (Finset.univ : Finset α) ∈ F)
    (hcard : ∀ B ∈ F, B = Finset.univ ∨ 2 ≤ B.card)
    (h2 : 2 ≤ Fintype.card α) (e : Sym2 (LaminarVertex F)) (u : LaminarVertex F) :
    (toRootedTreeOfCard hl huniv hcard h2).sideLeaves e u = leafSide F e u :=
  rfl

set_option maxHeartbeats 800000 in
/-- ★★★ **Aho–Buneman（构造方向）**：**两两相容**的 split 系统必被一棵树展示。

* `fam : Finset (Split X)` 两两相容；
* 每个 `s ∈ fam` **非平凡**（两侧都 `≥ 2` 个叶）——平凡 split 由任何足够大的树的
  「叶边」自动展示，为省去该情形的枝节，这里排除之；
* `2 ≤ |X|`。

⇒ 存在 `RootedTree X` 展示 `fam` 的每个成员（允许 `swap`）。 -/
theorem compatible_exists_rootedTree {X : Type u} [Fintype X] [DecidableEq X]
    (fam : Finset (Split X)) (ρ : X)
    (h : ∀ s ∈ fam, ∀ t ∈ fam, Split.Compatible s t)
    (hnt : ∀ s ∈ fam, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card)
    (h2 : 2 ≤ Fintype.card X) :
    ∃ T : RootedTree.{u, u} X, ∀ s ∈ fam, T.DisplaysSplit s := by
  classical
  set F : Finset (Finset X) := fam.image (fun s => s.cluster ρ) with hF
  have hmemF : ∀ A : Finset X, A ∈ F ↔ ∃ s ∈ fam, s.cluster ρ = A := by
    intro A
    rw [hF, Finset.mem_image]
  have hl : LaminarFamily F := by
    intro A hA B hB
    obtain ⟨s, hs, rfl⟩ := (hmemF A).mp hA
    obtain ⟨t, ht, rfl⟩ := (hmemF B).mp hB
    exact laminar_of_compatible_clusters (h s hs t ht) rfl rfl
  have hl' : LaminarFamily (normFinset F) := laminarFamily_normFinset hl
  have huniv' : (Finset.univ : Finset X) ∈ normFinset F := univ_mem_normFinset
  have hcard' : ∀ B ∈ normFinset F, B = Finset.univ ∨ 2 ≤ B.card := by
    intro B hB
    rcases (mem_normFinset.mp hB) with hh | hh
    · exact Or.inl hh
    · exact Or.inr hh.2
  have hne' : ∀ B ∈ normFinset F, B.Nonempty := nonempty_of_mem_of_hcard hcard' h2
  refine ⟨toRootedTreeOfCard hl' huniv' hcard' h2, fun s hs => ?_⟩
  have hBmem : s.cluster ρ ∈ F := (hmemF _).mpr ⟨s, hs, rfl⟩
  have hBcard : 2 ≤ (s.cluster ρ).card := by
    rcases s.cluster_eq_sideA_or_compl ρ with h1 | h1
    · rw [h1]; exact (hnt s hs).1
    · rw [h1, ← Split.sideB_eq_compl]; exact (hnt s hs).2
  have hBne : s.cluster ρ ≠ Finset.univ := fun hh =>
    s.notMem_cluster ρ (hh ▸ Finset.mem_univ ρ)
  have hBmem' : s.cluster ρ ∈ normFinset F :=
    mem_normFinset.mpr (Or.inr ⟨hBmem, hBcard⟩)
  have hleaf : leafSide (normFinset F)
      (parentEdge hl' hne' huniv' (s.cluster ρ) hBmem' hBne)
      (Sum.inl (⟨s.cluster ρ, hBmem'⟩ : ↥(normFinset F))) = s.cluster ρ :=
    leafSide_parentEdge_of_card hl' huniv' hcard' h2 hBmem' hBne
  have hadj : (treeGraph (normFinset F)).Adj
      (Sum.inl (⟨s.cluster ρ, hBmem'⟩ : ↥(normFinset F)))
      (Sum.inl (parentV hl' hne' huniv' (⟨s.cluster ρ, hBmem'⟩ : ↥(normFinset F)) hBne)) :=
    (treeGraph_adj_inl_inl (normFinset F) ⟨s.cluster ρ, hBmem'⟩
      (parentV hl' hne' huniv' ⟨s.cluster ρ, hBmem'⟩ hBne)).mpr
      (Or.inl (isParentOf_parentOf (A := s.cluster ρ) hl' hne' huniv' hBmem' hBne))
  rcases s.cluster_eq_sideA_or_compl ρ with hcl | hcl
  · refine Or.inl ⟨Sum.inl (⟨s.cluster ρ, hBmem'⟩ : ↥(normFinset F)),
      Sum.inl (parentV hl' hne' huniv' (⟨s.cluster ρ, hBmem'⟩ : ↥(normFinset F)) hBne),
      hadj,
      Sum.inl (⟨s.cluster ρ, hBmem'⟩ : ↥(normFinset F)), ?_⟩
    show s.sideA = leafSide (normFinset F)
      s(Sum.inl (⟨s.cluster ρ, hBmem'⟩ : ↥(normFinset F)),
        Sum.inl (parentV hl' hne' huniv' (⟨s.cluster ρ, hBmem'⟩ : ↥(normFinset F)) hBne))
      (Sum.inl (⟨s.cluster ρ, hBmem'⟩ : ↥(normFinset F)))
    rw [← hcl]
    exact hleaf.symm
  · refine Or.inr ⟨Sum.inl (⟨s.cluster ρ, hBmem'⟩ : ↥(normFinset F)),
      Sum.inl (parentV hl' hne' huniv' (⟨s.cluster ρ, hBmem'⟩ : ↥(normFinset F)) hBne),
      hadj,
      Sum.inl (⟨s.cluster ρ, hBmem'⟩ : ↥(normFinset F)), ?_⟩
    show s.swap.sideA = leafSide (normFinset F)
      s(Sum.inl (⟨s.cluster ρ, hBmem'⟩ : ↥(normFinset F)),
        Sum.inl (parentV hl' hne' huniv' (⟨s.cluster ρ, hBmem'⟩ : ↥(normFinset F)) hBne))
      (Sum.inl (⟨s.cluster ρ, hBmem'⟩ : ↥(normFinset F)))
    rw [Split.swap_sideA, Split.sideB_eq_compl, ← hcl]
    exact hleaf.symm
