/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Aho
import Phylo.Algorithm.UPGMA

/-!
# `Phylo.Dendrogram` —— 超度量 ⟹ 镶嵌球族 ⟹ 树（UPGMA 的结构定理）

**UPGMA**（Sokal–Michener 1958；Sneath–Sokal）输入一个**超度量**相异度 `δ`
（分子钟假设），逐层合并最相似的类。本文件给出它成立的**组合骨架**：

1. **★ 球传递性**（`Dissimilarity.ball_trans`，已在 `Phylo.Algorithm.UPGMA`）；
2. ★★ **两球相交 ⟹ 嵌套**（`ball_subset_of_mem_of_le`）；
3. ★★★ **球族两两「嵌套或相离」**（`ball_subset_or_disjoint`）⟹ **镶嵌族**；
4. ★★★ **树存在**（`exists_rootedTree_displays_balls`）：
   任一有限球族都被一棵 `RootedTree` 的边侧实现（用 `Phylo.Laminar` 的建树管线）。

⇒ 超度量的**分层聚类**（dendrogram）确实对应一棵树：这正是 UPGMA 的正确性内核。

⬜ 反向（「树实现 ⟹ 该树诱导的叶距离 = 原超度量」，即 dendrogram 的**唯一性/忠实性**）
不在本文件；它需要「叶距离由树结构决定」的引理。
-/

noncomputable section

open Phylo

universe u

namespace NJ

namespace Dissimilarity

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- `r`-**球**（以 `x` 为心）：`{y | δ x y ≤ r}`。 -/
def ball (δ : Dissimilarity X) (x : X) (r : ℝ) : Finset X :=
  Finset.univ.filter fun y => δ.val x y ≤ r

theorem mem_ball {δ : Dissimilarity X} {x y : X} {r : ℝ} :
    y ∈ δ.ball x r ↔ δ.val x y ≤ r := by
  simp [ball]

/-- ★★ **相交 ⟹ 嵌套（同序）**：超度量下，若 `z` 同时落在 `r`-球 `ball x r` 与
`r'`-球 `ball y r'` 内且 `r ≤ r'`，则整个 `ball x r` 含于 `ball y r'`。

（两步超度量不等式：先 `δ z w ≤ max (δ z x) (δ x w) ≤ r'`，再 `δ y w ≤ max (δ y z) (δ z w) ≤ r'`。） -/
theorem ball_subset_of_mem_of_le (δ : Dissimilarity X) (h : δ.Ultrametric)
    {x y z : X} {r r' : ℝ} (hxz : δ.val x z ≤ r) (hyz : δ.val y z ≤ r')
    (hle : r ≤ r') : δ.ball x r ⊆ δ.ball y r' := by
  intro w hw
  rw [mem_ball] at hw ⊢
  have hzw : δ.val z w ≤ r' := by
    refine le_trans (h z x w) (max_le ?_ ?_)
    · rw [δ.symm z x]; exact le_trans hxz hle
    · exact le_trans hw hle
  exact le_trans (h y z w) (max_le hyz hzw)

/-- ★★★ **球族「嵌套或相离」** —— 超度量下球族是**镶嵌族**。

这是 UPGMA 分层聚类的全部组合内容：相交则小半径的球含于大半径的球。 -/
theorem ball_subset_or_disjoint (δ : Dissimilarity X) (h : δ.Ultrametric)
    {x y : X} {r r' : ℝ} (hz : (δ.ball x r ∩ δ.ball y r').Nonempty) :
    δ.ball x r ⊆ δ.ball y r' ∨ δ.ball y r' ⊆ δ.ball x r := by
  obtain ⟨z, hz⟩ := hz
  obtain ⟨hzx, hzy⟩ := Finset.mem_inter.mp hz
  rw [mem_ball] at hzx hzy
  rcases le_total r r' with hle | hle
  · exact Or.inl (ball_subset_of_mem_of_le δ h hzx hzy hle)
  · exact Or.inr (ball_subset_of_mem_of_le δ h hzy hzx hle)

/-- ★★★ **超度量的有限球族是镶嵌族**。 -/
theorem laminarFamily_ballImage (δ : Dissimilarity X) (h : δ.Ultrametric)
    (S : Finset (X × ℝ)) : LaminarFamily (S.image fun p => δ.ball p.1 p.2) := by
  intro A hA B hB
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hA
  obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hB
  rw [← hp, ← hq]
  by_cases hint : ((δ.ball p.1 p.2) ∩ (δ.ball q.1 q.2)).Nonempty
  · rcases ball_subset_or_disjoint δ h hint with hsub | hsub
    · exact Or.inl hsub
    · exact Or.inr (Or.inl hsub)
  · refine Or.inr (Or.inr ?_)
    rwa [Finset.disjoint_iff_inter_eq_empty, ← Finset.not_nonempty_iff_eq_empty]

set_option maxHeartbeats 800000 in
/-- ★★★ **UPGMA / dendrogram 结构定理**：超度量的有限球族被一棵树实现。

具体地：对任一有限半径-中心集合 `S`，存在 `RootedTree X`，其对每个**非平凡**球
（`2 ≤ |ball|` 且 `≠ univ`）都有一条边，其叶侧恰为该球。

（构造：球族镶嵌 ⟹ 正规化（删单元素、加根）⟹ `toRootedTreeOfCard` 建树
⟹ `leafSide_parentEdge_of_card` 给出「球 = 边侧」。） -/
theorem exists_rootedTree_displays_balls (δ : Dissimilarity X) (h : δ.Ultrametric)
    (S : Finset (X × ℝ)) (h2 : 2 ≤ Fintype.card X) :
    ∃ T : RootedTree.{u, u} X, ∀ p ∈ S,
      2 ≤ (δ.ball p.1 p.2).card → (δ.ball p.1 p.2) ≠ Finset.univ →
        ∃ e : Sym2 T.V, ∃ u : T.V, T.sideLeaves e u = δ.ball p.1 p.2 := by
  classical
  set F : Finset (Finset X) := S.image (fun p => δ.ball p.1 p.2) with hF
  have hl : LaminarFamily F := laminarFamily_ballImage δ h S
  have hl' : LaminarFamily (normFinset F) := laminarFamily_normFinset hl
  have huniv' : (Finset.univ : Finset X) ∈ normFinset F := univ_mem_normFinset
  have hcard' : ∀ B ∈ normFinset F, B = Finset.univ ∨ 2 ≤ B.card := by
    intro B hB
    rcases (mem_normFinset.mp hB) with hh | hh
    · exact Or.inl hh
    · exact Or.inr hh.2
  refine ⟨toRootedTreeOfCard hl' huniv' hcard' h2, fun p hp hcard hne => ?_⟩
  have hBF : δ.ball p.1 p.2 ∈ F := Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hBmem' : δ.ball p.1 p.2 ∈ normFinset F :=
    mem_normFinset.mpr (Or.inr ⟨hBF, hcard⟩)
  refine ⟨parentEdge hl' (nonempty_of_mem_of_hcard hcard' h2) huniv' _ hBmem' hne,
    Sum.inl (⟨_, hBmem'⟩ : ↥(normFinset F)), ?_⟩
  rw [toRootedTreeOfCard_sideLeaves]
  exact leafSide_parentEdge_of_card hl' huniv' hcard' h2 hBmem' hne

end Dissimilarity

end NJ
