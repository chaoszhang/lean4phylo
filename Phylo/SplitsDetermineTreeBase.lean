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

/-! ## 情形 `|X| = 3`（W47：`Phylo/Stat/NJRun.lean` 的基例）

`|X| = 3` 时**任意** cladogram 都是三叉星：`|V| = 4`、恰有一个内部点 `c`、且
`Adj a b ↔ a = c ∨ b = c`。⇒ 三标签拓扑**唯一**。 -/

/-- ★★ **`|X| = 3` ⇒ `|V| = 4`**。上界用 `card_V_le_two_mul_card`；
`|V| = 3` 被排除：那样叶集穷尽顶点集 ⇒ 所有点度 `1` ⇒ 度数和 `3 ≠ 4 = 2(|V|−1)`。 -/
theorem card_V_eq_four_of_card_eq_three (T : Cladogram.{u, v} X) (hX : Fintype.card X = 3) :
    Fintype.card T.V = 4 := by
  classical
  have h3 : 3 ≤ Fintype.card T.V := by
    have h := Fintype.card_le_of_injective T.leaf T.leaf.injective
    omega
  have hle : Fintype.card T.V ≤ 4 := by
    have h := T.card_V_le_two_mul_card (by omega)
    omega
  have hne : Fintype.card T.V ≠ 3 := by
    intro hV3
    have huniv : T.leafFinset = Finset.univ := by
      refine Finset.eq_univ_of_card _ ?_
      rw [T.card_leafFinset, hX, hV3]
    have hleaf : ∀ v : T.V, T.IsLeaf v := fun v =>
      (mem_leafFinset T).mp (by rw [huniv]; exact Finset.mem_univ v)
    have hsum : ∑ v, T.graph.degree v = 3 := by
      rw [show (∑ v, T.graph.degree v) = ∑ _v : T.V, 1 from
        Finset.sum_congr rfl fun v _ => (hleaf v).degree_eq_one]
      simp [hV3]
    have hdeg : ∑ v, T.graph.degree v = 2 * T.graph.edgeFinset.card :=
      T.graph.sum_degrees_eq_twice_card_edges
    have hE : T.graph.edgeFinset.card = Fintype.card T.V - 1 := by
      have h := T.isTree.card_edgeFinset
      omega
    omega
  omega

/-- ★★ **`|X| = 3` ⇒ 恰有一个内部顶点**。 -/
theorem existsUnique_not_isLeaf_of_card_eq_three (T : Cladogram.{u, v} X)
    (hX : Fintype.card X = 3) : ∃! c : T.V, ¬ T.IsLeaf c := by
  classical
  have hV := T.card_V_eq_four_of_card_eq_three hX
  have hI : T.internalFinset.card = 1 := by
    have h := T.leafFinset_card_add_internalFinset_card
    rw [T.card_leafFinset, hX] at h
    omega
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hI
  refine ⟨c, (mem_internalFinset T).mp (by rw [hc]; exact Finset.mem_singleton_self c), ?_⟩
  intro v hv
  have hmem : v ∈ T.internalFinset := (mem_internalFinset T).mpr hv
  rw [hc] at hmem
  exact Finset.mem_singleton.mp hmem

/-- ★★★ **`|X| = 3` 时的邻接刻画**：`Adj a b ↔ a ≠ b ∧ (a = c ∨ b = c)`。

（`c` 的度：度数和 `6 = 3·1 + deg c` ⇒ `deg c = 3`；于是 `neighborFinset c` 与 `univ.erase c`
都是三元且前者含于后者 ⇒ 相等。反过来，若边两端都不是 `c`，则它们都是叶、各有度 `1`，
而 `c` 又与之相邻 ⇒ `deg a ≥ 2`，矛盾。★ 互异前提 `a ≠ b` **不可省**：
`a = b = c` 时右端真而左端假。） -/
theorem adj_iff_eq_center_of_card_eq_three (T : Cladogram.{u, v} X)
    (hX : Fintype.card X = 3) {c : T.V} (hc : ¬ T.IsLeaf c) :
    ∀ a b : T.V, T.graph.Adj a b ↔ (a ≠ b ∧ (a = c ∨ b = c)) := by
  classical
  have hV := T.card_V_eq_four_of_card_eq_three hX
  have hun : ∀ y : T.V, ¬ T.IsLeaf y → y = c := by
    intro y hy
    obtain ⟨d, _hd, huniq⟩ := T.existsUnique_not_isLeaf_of_card_eq_three hX
    rw [huniq y hy, huniq c hc]
  have hsum : ∑ v, T.graph.degree v = 2 * T.graph.edgeFinset.card :=
    T.graph.sum_degrees_eq_twice_card_edges
  have hE : T.graph.edgeFinset.card = Fintype.card T.V - 1 := by
    have h := T.isTree.card_edgeFinset
    omega
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
  have hcardL : T.leafFinset.card = 3 := by rw [T.card_leafFinset, hX]
  have hIeq : T.internalFinset = {c} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr
      ⟨(mem_internalFinset T).mpr hc, ?_⟩
    intro v hv
    by_contra hvc
    exact hvc (hun v ((mem_internalFinset T).mp hv))
  have hdegc : T.graph.degree c = 3 := by
    have hI : T.internalFinset.sum (fun v => T.graph.degree v) = T.graph.degree c := by
      rw [hIeq, Finset.sum_singleton]
    have htot : ∑ v, T.graph.degree v = 6 := by
      rw [hsum, hE, hV]
    have hl3 : T.leafFinset.sum (fun v => T.graph.degree v) = 3 := by
      rw [hL, hcardL]
    omega
  have hnb : T.graph.neighborFinset c = Finset.univ.erase c := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro v hv
      have hadj := (mem_neighborFinset T.graph c v).mp hv
      exact Finset.mem_erase.mpr ⟨hadj.ne.symm, Finset.mem_univ v⟩
    · rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, hV,
        card_neighborFinset_eq_degree T.graph c, hdegc]
  intro a b
  constructor
  · rintro hab
    refine ⟨hab.ne, ?_⟩
    by_cases ha : a = c
    · exact Or.inl ha
    by_cases hb : b = c
    · exact Or.inr hb
    exfalso
    have haleaf : T.IsLeaf a := by
      by_contra hcon
      exact ha (hun a hcon)
    have hca : T.graph.Adj c a := by
      rw [← mem_neighborFinset, hnb]
      exact Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩
    have hsub : ({b, c} : Finset T.V) ⊆ T.graph.neighborFinset a := by
      intro v hv
      rw [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with hv1 | hv2
      · rw [hv1]; exact (mem_neighborFinset T.graph a b).mpr hab
      · rw [hv2]; exact (mem_neighborFinset T.graph a c).mpr hca.symm
    have h2 : 2 ≤ (T.graph.neighborFinset a).card := by
      have h := Finset.card_le_card hsub
      rwa [Finset.card_pair hb] at h
    have h1 : T.graph.degree a = 1 := haleaf.degree_eq_one
    rw [card_neighborFinset_eq_degree] at h2
    omega
  · rintro ⟨hne, h | h⟩
    · rw [h]
      rw [← mem_neighborFinset, hnb]
      exact Finset.mem_erase.mpr ⟨fun hbc => hne (h.trans hbc.symm), Finset.mem_univ b⟩
    · rw [h]
      rw [SimpleGraph.adj_comm, ← mem_neighborFinset, hnb]
      exact Finset.mem_erase.mpr ⟨fun hac => hne (hac.trans h.symm), Finset.mem_univ a⟩

/-- ★★★ **`|X| = 3` 时任意两棵 cladogram 同构**（三叶树 = 三叉星 ⇒ 拓扑唯一）。 -/
theorem iso_of_card_eq_three (T T' : Cladogram.{u, v} X) (hX : Fintype.card X = 3) :
    Nonempty (Iso T T') := by
  classical
  obtain ⟨c, hc, hunT⟩ := T.existsUnique_not_isLeaf_of_card_eq_three hX
  obtain ⟨c', hc', hunT'⟩ := T'.existsUnique_not_isLeaf_of_card_eq_three hX
  have hadjT := T.adj_iff_eq_center_of_card_eq_three hX hc
  have hadjT' := T'.adj_iff_eq_center_of_card_eq_three hX hc'
  have hleafT : ∀ v : T.V, v ≠ c → T.IsLeaf v := fun v hv =>
    Classical.byContradiction fun hcon => hv (hunT v hcon)
  have hleafT' : ∀ w : T'.V, w ≠ c' → T'.IsLeaf w := fun w hw =>
    Classical.byContradiction fun hcon => hw (hunT' w hcon)
  -- 顶点映射：`c ↦ c'`，叶按标号
  let g : T.V → T'.V := fun v =>
    if hv : v = c then c' else T'.leaf (Classical.choose (hleafT v hv))
  have hgc : g c = c' := by
    show (if hv : c = c then c' else _) = c'
    rw [dite_eq_left rfl]
  have hgne : ∀ (v : T.V) (hv : v ≠ c),
      g v = T'.leaf (Classical.choose (hleafT v hv)) := by
    intro v hv
    show (if hv' : v = c then c' else _) = _
    rw [dite_eq_right hv]
  have hcleaf : ∀ (y : X), T'.leaf y ≠ c' := fun y h => hc' ⟨y, h⟩
  have hinj : Function.Injective g := by
    intro a b hab
    by_cases ha : a = c
    · rw [ha] at hab ⊢
      rw [hgc] at hab
      by_cases hb : b = c
      · exact hb.symm
      · rw [hgne b hb] at hab
        exact absurd hab.symm (hcleaf _)
    · by_cases hb : b = c
      · rw [hb] at hab ⊢
        rw [hgne a ha, hgc] at hab
        exact absurd hab (hcleaf _)
      · rw [hgne a ha, hgne b hb] at hab
        have hy : Classical.choose (hleafT a ha) = Classical.choose (hleafT b hb) :=
          T'.leaf.injective hab
        have h1 : T.leaf (Classical.choose (hleafT a ha)) = a :=
          Classical.choose_spec (hleafT a ha)
        have h2 : T.leaf (Classical.choose (hleafT b hb)) = b :=
          Classical.choose_spec (hleafT b hb)
        rw [← h1, ← h2, hy]
  have hsurj : Function.Surjective g := by
    intro w
    by_cases hw : w = c'
    · exact ⟨c, by rw [hw]; exact hgc⟩
    · obtain ⟨y, hy⟩ := hleafT' w hw
      have hcy : T.leaf y ≠ c := by
        intro h
        exact hc (h ▸ ⟨y, rfl⟩)
      refine ⟨T.leaf y, ?_⟩
      rw [hgne (T.leaf y) hcy]
      have hspec : Classical.choose (hleafT (T.leaf y) hcy) = y :=
        T.leaf.injective (Classical.choose_spec (hleafT (T.leaf y) hcy))
      rw [hspec]
      exact hy
  let f : T.V ≃ T'.V := Equiv.ofBijective g ⟨hinj, hsurj⟩
  have hf : ∀ v : T.V, f v = g v := fun _ => rfl
  have hkey : ∀ v : T.V, f v = c' ↔ v = c := by
    intro v
    rw [hf]
    constructor
    · intro h
      by_contra hv
      rw [hgne v hv] at h
      exact hcleaf _ h
    · intro h
      rw [h]; exact hgc
  refine ⟨{ gIso := RelIso.mk f (fun {a b} => ?_), leaf_compat := ?_ }⟩
  · show T'.graph.Adj (f a) (f b) ↔ T.graph.Adj a b
    rw [hadjT' (f a) (f b), hadjT a b, hkey a, hkey b]
    exact ⟨fun h => ⟨fun hab => h.1 (by rw [hab]), h.2⟩,
           fun h => ⟨fun hab => h.1 (f.injective hab), h.2⟩⟩
  · intro x
    have hcx : T.leaf x ≠ c := fun h => hc (h ▸ ⟨x, rfl⟩)
    show f (T.leaf x) = T'.leaf x
    rw [hf, hgne (T.leaf x) hcx]
    have hspec : Classical.choose (hleafT (T.leaf x) hcx) = x :=
      T.leaf.injective (Classical.choose_spec (hleafT (T.leaf x) hcx))
    rw [hspec]

end Cladogram
