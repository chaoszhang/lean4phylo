/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Algorithm.Cherry

/-!
# `Phylo.Algorithm.BinaryCount` —— 二叉树的**计数公式**

无根二叉（binary）树的经典计数：设 `ℓ` = 叶数、`i` = 内部顶点数，则

```
ℓ = i + 2,     |V| = 2ℓ - 2,     |E| = 2ℓ - 3
```

**证明**（握手引理）：`Σ deg = 2|E| = 2(|V| - 1)`；二叉树里 `deg = 1`（叶）或 `3`（内部），
故 `ℓ + 3i = 2(ℓ + i - 1)`，即 `ℓ = i + 2`。

（推论「非平凡 split 数 = `ℓ - 3`」同理 —— 内部边双端都是内部顶点，
`3i = 2·E_ii + ℓ`，故 `E_ii = (3i - ℓ)/2 = ℓ - 3`。） -/

namespace Cladogram

variable {X : Type*} [Fintype X] [DecidableEq X] (T : Cladogram X)

/-- ★★ **二叉树：`ℓ = i + 2`**（叶数 = 内部顶点数 + 2）。 -/
theorem IsBinary.leafFinset_card_eq (h : T.IsBinary) :
    T.leafFinset.card = T.internalFinset.card + 2 := by
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
  have hI : T.internalFinset.sum (fun v => T.graph.degree v) = 3 * T.internalFinset.card := by
    rw [show T.internalFinset.sum (fun v => T.graph.degree v)
        = T.internalFinset.sum (fun _ => 3) from
      Finset.sum_congr rfl fun v hv => h.degree_eq_three ((mem_internalFinset T).mp hv)]
    simp [mul_comm]
  have hdeg : ∑ v, T.graph.degree v = 2 * T.graph.edgeFinset.card :=
    T.graph.sum_degrees_eq_twice_card_edges
  have hE : T.graph.edgeFinset.card = Fintype.card T.V - 1 := by
    have := T.isTree.card_edgeFinset
    omega
  have hcard := T.leafFinset_card_add_internalFinset_card
  have hwedge : T.leafFinset.card + 3 * T.internalFinset.card = 2 * T.graph.edgeFinset.card := by
    rw [← hdeg, ← hsplit, hL, hI]
  have hV : Fintype.card T.V = T.leafFinset.card + T.internalFinset.card := hcard.symm
  -- 消去减法：`|E| + 1 = |V|` ⟹ `2|E| + 2 = 2|V|`
  have hE1 : T.graph.edgeFinset.card + 1 = Fintype.card T.V := by
    have := T.isTree.card_edgeFinset
    omega
  have hE2 : 2 * T.graph.edgeFinset.card + 2 = 2 * Fintype.card T.V := by omega
  omega

/-- ★ **二叉树至少有两个叶**（由 `ℓ = i + 2`）。 -/
theorem IsBinary.two_le_leafFinset_card (h : T.IsBinary) : 2 ≤ T.leafFinset.card := by
  have := h.leafFinset_card_eq
  omega

/-- ★★ **二叉树的顶点数**：`|V| = 2ℓ - 2`。 -/
theorem IsBinary.card_V (h : T.IsBinary) :
    Fintype.card T.V = 2 * T.leafFinset.card - 2 := by
  have h1 := h.leafFinset_card_eq
  have h2 := T.leafFinset_card_add_internalFinset_card
  omega

/-- ★★ **二叉树的边数**：`|E| = 2ℓ - 3`。 -/
theorem IsBinary.card_edgeFinset (h : T.IsBinary) :
    T.graph.edgeFinset.card = 2 * T.leafFinset.card - 3 := by
  have hE : T.graph.edgeFinset.card = Fintype.card T.V - 1 := by
    have := T.isTree.card_edgeFinset
    omega
  have hV := h.card_V
  omega

/-- ★★ **叶数相同的二叉树有相同的顶点数与边数**。 -/
theorem IsBinary.card_eq_of_leaf_card_eq {T' : Cladogram X} (h : T.IsBinary) (h' : T'.IsBinary)
    (hℓ : T.leafFinset.card = T'.leafFinset.card) :
    Fintype.card T.V = Fintype.card T'.V ∧
      T.graph.edgeFinset.card = T'.graph.edgeFinset.card := by
  have hV₁ := h.card_V
  have hV₂ := h'.card_V
  have hE₁ := h.card_edgeFinset
  have hE₂ := h'.card_edgeFinset
  refine ⟨by omega, by omega⟩

end Cladogram
