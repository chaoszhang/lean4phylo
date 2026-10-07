/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.SplitsMaximal

/-!
# `Phylo.SplitsDetermineTreeBase` —— 退化基数：`|X| ≤ 2` 时任意两棵 cladogram 同构

`Phylo/SplitsDetermineTree.lean` 的目标主定理「树由 split 系统决定」（T0.1）在
**退化基数** `|X| ≤ 2` 时需要单独处理 —— 那里 split 系统太小，承载不了结构信息。
本文件给出那一小块：★★ **`Fintype.card X ≤ 2` 时任意两棵 `Cladogram X` 同构**。

## 路线

1. **计数引理** ★★ `card_V_le_two_mul_card`：`2 ≤ |V| ⟹ |V| ≤ 2|X| − 2`。
   握手引理 `Σ deg = 2|E| = 2(|V| − 1)`；叶各贡献 `1`，非叶各贡献 `≥ 3`
   （`no_degree_two` + ★ `three_le_degree_of_not_isLeaf`）；代入 `|V| = |X| + i`
   得 `i + 2 ≤ |X|`。
2. **情形 `|X| = 0`**：若有 `2 ≤ |V|`，计数引理给 `|V| ≤ 2·0 − 2 = 0` —— 矛盾，
   故 `|V| = 1`（树连通 ⟹ 顶点集非空）。唯一顶点互映；`leaf_compat` 由唯一性即得。
3. **情形 `|X| = 1`**：**不存在** `Cladogram X`（导出 `False`）。叶 `T.leaf x₀` 度 `1`
   故有邻居 `w ≠ T.leaf x₀` ⟹ `2 ≤ |V|`；计数引理给 `|V| ≤ 2·1 − 2 = 0` —— 矛盾。
4. **情形 `|X| = 2`**：`|leafFinset| = 2 ≤ |V|`（叶集含于顶点集）与 `|V| ≤ 2·2 − 2 = 2`
   得 `|V| = 2`，于是 `leafFinset = univ`（★★ `isLeaf_of_card_eq_two`：**每个顶点都是叶**）。
   故 `T.leaf : X ↪ V` 是**双射**，`Equiv` 取「`T.leaf` 之逆接 `T'.leaf`」，
   `leaf_compat` 由构造即得；邻接对应由 ★★ `adj_leaf_of_card_eq_two`
   （度 `1` 顶点的唯一邻居只能是另一个顶点）给出。

全部定理均已证出；无未证目标、无新公理、不改任何既有文件。
-/

universe u v

open SimpleGraph

namespace Cladogram

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## 计数引理 -/

/-- ★★ **计数引理**：`2 ≤ |V| ⟹ |V| ≤ 2|X| − 2`。

`Σ_v deg v = 2|E| = 2(|V| − 1)`；叶各贡献 `1`（共 `|X|`），非叶各贡献 `≥ 3`；
把 `|V| = |X| + i` 代入即得 `i + 2 ≤ |X|`，即 `|V| ≤ 2|X| − 2`。 -/
theorem card_V_le_two_mul_card (T : Cladogram.{u, v} X)
    (hV : 2 ≤ Fintype.card T.V) :
    Fintype.card T.V ≤ 2 * Fintype.card X - 2 := by
  classical
  have hsplit : T.leafFinset.sum (fun v => T.graph.degree v)
      + T.internalFinset.sum (fun v => T.graph.degree v) = ∑ v, T.graph.degree v := by
    simpa [leafFinset, internalFinset] using
      (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset T.V) T.IsLeaf
        (fun v => T.graph.degree v))
  have hL : T.leafFinset.sum (fun v => T.graph.degree v) = T.leafFinset.card := by
    rw [show T.leafFinset.sum (fun v => T.graph.degree v)
        = T.leafFinset.sum (fun _ => 1) from
      Finset.sum_congr rfl fun v hv => ((mem_leafFinset T).mp hv).degree_eq_one]
    simp
  have hI : 3 * T.internalFinset.card ≤ T.internalFinset.sum (fun v => T.graph.degree v) := by
    calc 3 * T.internalFinset.card = T.internalFinset.sum (fun _ => (3 : ℕ)) := by
          simp [Finset.sum_const, mul_comm]
      _ ≤ T.internalFinset.sum (fun v => T.graph.degree v) :=
          Finset.sum_le_sum fun v hv =>
            T.three_le_degree_of_not_isLeaf hV ((mem_internalFinset T).mp hv)
  have hdeg : ∑ v, T.graph.degree v = 2 * T.graph.edgeFinset.card :=
    T.graph.sum_degrees_eq_twice_card_edges
  have hE : T.graph.edgeFinset.card = Fintype.card T.V - 1 := by
    have h := T.isTree.card_edgeFinset
    omega
  have hcardX : T.leafFinset.card = Fintype.card X := T.card_leafFinset
  have hpart : T.leafFinset.card + T.internalFinset.card = Fintype.card T.V :=
    T.leafFinset_card_add_internalFinset_card
  omega

/-- ★★ **`|X| = 2` 且 `|V| = 2` 时每个顶点都是叶**（叶数 `= |X| = 2 = |V|` 穷尽顶点集）。 -/
theorem isLeaf_of_card_eq_two (T : Cladogram.{u, v} X) (hX : Fintype.card X = 2)
    (hV : Fintype.card T.V = 2) (v : T.V) : T.IsLeaf v := by
  classical
  have huniv : T.leafFinset = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [T.card_leafFinset, hX, hV]
  exact (mem_leafFinset T).mp (by rw [huniv]; exact Finset.mem_univ v)

/-- ★★ **`|X| = 2`、每个顶点都是叶时，不同标签的叶必相邻**
（两顶点图 + 树连通：度 `1` 顶点的唯一邻居只能在另一个顶点处）。 -/
theorem adj_leaf_of_card_eq_two (T : Cladogram.{u, v} X) (hX : Fintype.card X = 2)
    (hleaf : ∀ v : T.V, T.IsLeaf v) {x y : X} (hxy : x ≠ y) :
    T.graph.Adj (T.leaf x) (T.leaf y) := by
  classical
  have hdeg : T.graph.degree (T.leaf x) = 1 :=
    (T.leaf_iff_degree_one (T.leaf x)).mp ⟨x, rfl⟩
  have hpos : 0 < (T.graph.neighborFinset (T.leaf x)).card := by
    rw [card_neighborFinset_eq_degree T.graph (T.leaf x), hdeg]
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  have hadj : T.graph.Adj (T.leaf x) w :=
    (mem_neighborFinset T.graph (T.leaf x) w).mp hw
  obtain ⟨z, hz⟩ := hleaf w
  have hzx : z ≠ x := by
    intro hzx
    rw [hzx] at hz
    rw [hz] at hadj
    exact hadj.ne rfl
  have huniv : ({x, y} : Finset X) = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_pair hxy, hX]
  have hmem : z ∈ ({x, y} : Finset X) := by rw [huniv]; exact Finset.mem_univ z
  rw [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hzy : z = y := by
    rcases hmem with h | h
    · exact absurd h hzx
    · exact h
  rw [hzy] at hz
  rwa [← hz] at hadj

/-! ## 三种情形 -/

/-- ★★ **情形 `|X| = 0`**：`|V| = 1`，唯一顶点互映。 -/
theorem iso_of_card_eq_zero (T T' : Cladogram.{u, v} X) (hX : Fintype.card X = 0) :
    Nonempty (Iso T T') := by
  classical
  have hcardV : Fintype.card T.V = 1 := by
    have hpos : 0 < Fintype.card T.V :=
      Fintype.card_pos_iff.mpr T.isTree.connected.nonempty
    by_contra hne
    have h2 : 2 ≤ Fintype.card T.V := by omega
    have hle := T.card_V_le_two_mul_card h2
    omega
  have hcardV' : Fintype.card T'.V = 1 := by
    have hpos : 0 < Fintype.card T'.V :=
      Fintype.card_pos_iff.mpr T'.isTree.connected.nonempty
    by_contra hne
    have h2 : 2 ≤ Fintype.card T'.V := by omega
    have hle := T'.card_V_le_two_mul_card h2
    omega
  obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hcardV
  obtain ⟨x', hx'⟩ := Fintype.card_eq_one_iff.mp hcardV'
  let e : T.V ≃ T'.V :=
    { toFun := fun _ => x'
      invFun := fun _ => x
      left_inv := fun v => (hx v).symm
      right_inv := fun w => (hx' w).symm }
  have he : ∀ v : T.V, e v = x' := fun _ => rfl
  refine ⟨{ gIso := RelIso.mk e ?_, leaf_compat := ?_ }⟩
  · exact fun {a b} =>
      ⟨fun h => (h.ne ((hx' (e a)).trans (hx' (e b)).symm)).elim,
       fun h => (h.ne ((hx a).trans (hx b).symm)).elim⟩
  · intro y
    show e (T.leaf y) = T'.leaf y
    rw [he]
    exact (hx' (T'.leaf y)).symm

/-- ★★ **情形 `|X| = 1`**：**不存在** `Cladogram X`。

叶 `T.leaf x₀` 度为 `1` 故有邻居 `w ≠ T.leaf x₀`，于是 `2 ≤ |V|`；计数引理给
`|V| ≤ 2·1 − 2 = 0` —— 矛盾。 -/
theorem false_of_card_eq_one (T : Cladogram.{u, v} X) (hX : Fintype.card X = 1) : False := by
  classical
  obtain ⟨x₀, -⟩ := Fintype.card_eq_one_iff.mp hX
  have hdeg : T.graph.degree (T.leaf x₀) = 1 :=
    (T.leaf_iff_degree_one (T.leaf x₀)).mp ⟨x₀, rfl⟩
  have hpos : 0 < (T.graph.neighborFinset (T.leaf x₀)).card := by
    rw [card_neighborFinset_eq_degree T.graph (T.leaf x₀), hdeg]
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  have hadj : T.graph.Adj (T.leaf x₀) w :=
    (mem_neighborFinset T.graph (T.leaf x₀) w).mp hw
  have h2 : 2 ≤ Fintype.card T.V := by
    have hlt := Fintype.one_lt_card_iff.mpr ⟨w, T.leaf x₀, hadj.ne.symm⟩
    omega
  have hle := T.card_V_le_two_mul_card h2
  omega

/-- ★★ **情形 `|X| = 2`**：两棵树都恰有 `2` 个顶点、都是叶、且由一条边相连。

`Equiv` 取 `(T.leaf)⁻¹` 接 `T'.leaf`（两边都是 `X ≃ V` 的逆），`leaf_compat` 由构造即得；
邻接对应由 ★★ `adj_leaf_of_card_eq_two` 给出（`x = y` 时两边都是无自环的假命题）。 -/
theorem iso_of_card_eq_two (T T' : Cladogram.{u, v} X) (hX : Fintype.card X = 2) :
    Nonempty (Iso T T') := by
  classical
  have hV2 : 2 ≤ Fintype.card T.V := by
    have h := Finset.card_le_card (Finset.subset_univ T.leafFinset)
    rw [Finset.card_univ, T.card_leafFinset, hX] at h
    exact h
  have hV : Fintype.card T.V = 2 := by
    have hle := T.card_V_le_two_mul_card hV2
    omega
  have hV2' : 2 ≤ Fintype.card T'.V := by
    have h := Finset.card_le_card (Finset.subset_univ T'.leafFinset)
    rw [Finset.card_univ, T'.card_leafFinset, hX] at h
    exact h
  have hV' : Fintype.card T'.V = 2 := by
    have hle := T'.card_V_le_two_mul_card hV2'
    omega
  have hleaf : ∀ v : T.V, T.IsLeaf v := T.isLeaf_of_card_eq_two hX hV
  have hleaf' : ∀ v : T'.V, T'.IsLeaf v := T'.isLeaf_of_card_eq_two hX hV'
  have hbij : Function.Bijective (T.leaf : X → T.V) :=
    (Fintype.bijective_iff_injective_and_card (T.leaf : X → T.V)).mpr
      ⟨T.leaf.injective, by rw [hX, hV]⟩
  let e : X ≃ T.V := Equiv.ofBijective (T.leaf : X → T.V) hbij
  have he : ∀ x : X, e x = T.leaf x := fun _ => rfl
  have hbij' : Function.Bijective (T'.leaf : X → T'.V) :=
    (Fintype.bijective_iff_injective_and_card (T'.leaf : X → T'.V)).mpr
      ⟨T'.leaf.injective, by rw [hX, hV']⟩
  let e' : X ≃ T'.V := Equiv.ofBijective (T'.leaf : X → T'.V) hbij'
  have he' : ∀ x : X, e' x = T'.leaf x := fun _ => rfl
  let f : T.V ≃ T'.V := e.symm.trans e'
  have hleaff : ∀ x : X, f (T.leaf x) = T'.leaf x := by
    intro x
    show e' (e.symm (T.leaf x)) = T'.leaf x
    rw [← he x, Equiv.symm_apply_apply, he' x]
  have hadj : ∀ a b : T.V, T'.graph.Adj (f a) (f b) ↔ T.graph.Adj a b := by
    intro a b
    obtain ⟨x, rfl⟩ := hleaf a
    obtain ⟨y, rfl⟩ := hleaf b
    rw [hleaff x, hleaff y]
    by_cases hxy : x = y
    · rw [hxy]
      exact ⟨fun h => (h.ne rfl).elim, fun h => (h.ne rfl).elim⟩
    · exact ⟨fun _ => T.adj_leaf_of_card_eq_two hX hleaf hxy,
             fun _ => T'.adj_leaf_of_card_eq_two hX hleaf' hxy⟩
  exact ⟨{ gIso := RelIso.mk f (fun {a b} => hadj a b), leaf_compat := hleaff }⟩

/-- ★★ **退化基数**：`|X| ≤ 2` 时任意两棵 cladogram 同构。 -/
theorem iso_of_card_le_two {T T' : Cladogram.{u, v} X}
    (hcard : Fintype.card X ≤ 2) : Nonempty (Iso T T') := by
  have hthree : Fintype.card X = 0 ∨ Fintype.card X = 1 ∨ Fintype.card X = 2 := by omega
  rcases hthree with h0 | h1 | h2
  · exact T.iso_of_card_eq_zero T' h0
  · exact (T.false_of_card_eq_one h1).elim
  · exact T.iso_of_card_eq_two T' h2

end Cladogram
