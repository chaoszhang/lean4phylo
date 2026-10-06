/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Quartet

/-!
# `Phylo.Binary` —— 不兼容 split、quartet 差异、与 binary 树的专门描述

**背景（老师 2026-10-07 定的路线）**。`QuartetDecidesTree`（binary 树由 quartet 系统决定）
走**逆否**，拆成三步：

```
T ≇ T'   ⟹   Σ(T) ≠ Σ(T')   ⟹   ∃ 不兼容的 split 对   ⟹   ∃ 同一 4-叶集上两个不同的 quartet
```

这一步判断的价值在于：把「quartet 系统决定树」这个**整体**命题，换成
「split 系统决定树」+「split 的两两（不）兼容」+「不兼容 ⟹ quartet 不同」——
后两块都是**纯组合**的，不需要任何分析/测度内容。

本文件提供：
* `Split.Incompatible`（定义 + 四交刻画 + 对称 + 排中）；
* ★★ `exists_four_of_incompatible` —— 不兼容 ⟹ 存在 4 个互异叶；
* ★★★ `exists_restrict_ne_of_incompatible` —— 不兼容 ⟹ 同一 4-叶集上两个**不同**的 split
  （= 两个不同的 quartet）。**这就是老师路线的最后一步**；
* ★★ binary 树的专门描述（`IsBinary` 的度/邻居推论 + `BinaryCladogram`）。

⬜ **路线第 1、2 步**（「不同构 ⟹ Σ 不同」、「Σ 不同 ⟹ 存在不兼容对」）不在本文件，
见 `Phylo/Stat/QuartetDecides.lean` 的 `QuartetDecidesRoute`：它们等价于
**binary 树 split 系统是极大相容族**（⟺ Buneman 存在性）。
-/

universe u v

namespace Split

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## 不兼容的 split -/

/-- 两个 split **不兼容**：不能被同一棵树展示。

（`Compatible s t` 是「某一对分侧不交」，其否定即「两侧的四个交**全**非空」。） -/
def Incompatible (s t : Split α) : Prop := ¬ s.Compatible t

/-- **不兼容的展开**：四个交都非空。 -/
theorem incompatible_iff {s t : Split α} :
    s.Incompatible t ↔
      (s.sideA ∩ t.sideA).Nonempty ∧ (s.sideA ∩ t.sideB).Nonempty ∧
      (s.sideB ∩ t.sideA).Nonempty ∧ (s.sideB ∩ t.sideB).Nonempty := by
  simp only [Incompatible, Compatible, Finset.disjoint_iff_inter_eq_empty,
    Finset.nonempty_iff_ne_empty, not_or]

/-- 不兼容关系**对称**。 -/
theorem incompatible_comm {s t : Split α} : s.Incompatible t ↔ t.Incompatible s :=
  not_congr (compatible_comm s t)

/-- **排中**：两个 split 要么相容、要么不兼容。 -/
theorem compatible_or_incompatible (s t : Split α) : s.Compatible t ∨ s.Incompatible t :=
  Classical.em _

/-! ## 不兼容 ⟹ 四叶构造 -/

/-- ★★ **不兼容 ⟹ 四叶构造**。

`s`、`t` 不兼容时四个交都非空，各取一点：
`a ∈ A₁∩B₁`、`b ∈ A₁∩B₂`、`c ∈ A₂∩B₁`、`d ∈ A₂∩B₂`。
则 `{a,b} ⊆ s.sideA`、`{c,d} ⊆ s.sideB`、`{a,c} ⊆ t.sideA`、`{b,d} ⊆ t.sideB`，
且四点**两两互异**（`a,b` 分居 `s` 两侧；`a,c` 分居 `t` 两侧；其余同理）。

几何意义：在 `S = {a,b,c,d}` 上，`s` 给出 quartet `ab|cd`，`t` 给出 `ac|bd` —— **不同**。 -/
theorem exists_four_of_incompatible {s t : Split α} (h : s.Incompatible t) :
    ∃ a b c d : α,
      ({a, b} : Finset α) ⊆ s.sideA ∧ ({c, d} : Finset α) ⊆ s.sideB ∧
      ({a, c} : Finset α) ⊆ t.sideA ∧ ({b, d} : Finset α) ⊆ t.sideB ∧
      ({a, b, c, d} : Finset α).card = 4 := by
  rw [incompatible_iff] at h
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩ := h
  obtain ⟨ha1, ha2⟩ := Finset.mem_inter.mp ha
  obtain ⟨hb1, hb2⟩ := Finset.mem_inter.mp hb
  obtain ⟨hc1, hc2⟩ := Finset.mem_inter.mp hc
  obtain ⟨hd1, hd2⟩ := Finset.mem_inter.mp hd
  have hs_ne : ∀ {x y : α}, x ∈ s.sideA → y ∈ s.sideB → x ≠ y :=
    fun hx hy heq => (Finset.disjoint_left.mp s.disjoint_sides) (heq ▸ hx) hy
  have ht_ne : ∀ {x y : α}, x ∈ t.sideA → y ∈ t.sideB → x ≠ y :=
    fun hx hy heq => (Finset.disjoint_left.mp t.disjoint_sides) (heq ▸ hx) hy
  have hab : a ≠ b := ht_ne ha2 hb2
  have hac : a ≠ c := hs_ne ha1 hc1
  have had : a ≠ d := ht_ne ha2 hd2
  have hbc : b ≠ c := hs_ne hb1 hc1
  have hbd : b ≠ d := hs_ne hb1 hd1
  have hcd : c ≠ d := ht_ne hc2 hd2
  refine ⟨a, b, c, d, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha1
    · rw [Finset.mem_singleton] at hx; rw [hx]; exact hb1
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hc1
    · rw [Finset.mem_singleton] at hx; rw [hx]; exact hd1
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha2
    · rw [Finset.mem_singleton] at hx; rw [hx]; exact hc2
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hb2
    · rw [Finset.mem_singleton] at hx; rw [hx]; exact hd2
  · have h1 : a ∉ ({b, c, d} : Finset α) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, hac, had⟩
    have h2 : b ∉ ({c, d} : Finset α) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hbc, hbd⟩
    have h3 : c ∉ ({d} : Finset α) := by
      simp only [Finset.mem_singleton]
      exact hcd
    rw [show ({a, b, c, d} : Finset α) = insert a (insert b (insert c ({d} : Finset α)))
        from rfl,
      Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_singleton]

/-! ## 不兼容 ⟹ 同一 4-叶集上两个不同的 quartet -/

/-- ★★★ **不兼容 ⟹ 同一 4-叶集上两个不同的 split**（即两个不同的 quartet）。

取 `S := {a,b,c,d}`（来自 `exists_four_of_incompatible`）与两侧的**限制**：
`r₁ := s.restrict S` 把 `{a,b}` 与 `{c,d}` 分开，`r₂ := t.restrict S` 把 `{a,c}` 与 `{b,d}` 分开。
因 `b` 在 `r₁` 的 `A` 侧而**不**在 `r₂` 的 `A` 侧（`b ∈ t.sideB`），故 `r₁ ≠ r₂`。

**这是老师 2026-10-07 路线的最后一步**：「不兼容的 split 对 ⟹ 不兼容的 quartet」。 -/
theorem exists_restrict_ne_of_incompatible {s t : Split α} (h : s.Incompatible t) :
    ∃ (S : Finset α) (_ : S.card = 4)
      (hA₁ : (s.restrictSide S 0).Nonempty) (hB₁ : (s.restrictSide S 1).Nonempty)
      (hA₂ : (t.restrictSide S 0).Nonempty) (hB₂ : (t.restrictSide S 1).Nonempty),
      s.restrict S hA₁ hB₁ ≠ t.restrict S hA₂ hB₂ := by
  obtain ⟨a, b, c, d, hab_s, hcd_s, hac_t, hbd_t, hcard⟩ := exists_four_of_incompatible h
  have ha_s : a ∈ s.sideA := hab_s (by simp)
  have hb_s : b ∈ s.sideA := hab_s (by simp)
  have hc_s : c ∈ s.sideB := hcd_s (by simp)
  have ha_t : a ∈ t.sideA := hac_t (by simp)
  have hb_t : b ∈ t.sideB := hbd_t (by simp)
  have haS : a ∈ ({a, b, c, d} : Finset α) := by simp
  have hbS : b ∈ ({a, b, c, d} : Finset α) := by simp
  have hcS : c ∈ ({a, b, c, d} : Finset α) := by simp
  have hA₁ : (s.restrictSide ({a, b, c, d} : Finset α) 0).Nonempty :=
    ⟨⟨a, haS⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      by simpa [Split.sideA] using ha_s⟩⟩
  have hB₁ : (s.restrictSide ({a, b, c, d} : Finset α) 1).Nonempty :=
    ⟨⟨c, hcS⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      by simpa [Split.sideB] using hc_s⟩⟩
  have hA₂ : (t.restrictSide ({a, b, c, d} : Finset α) 0).Nonempty :=
    ⟨⟨a, haS⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      by simpa [Split.sideA] using ha_t⟩⟩
  have hB₂ : (t.restrictSide ({a, b, c, d} : Finset α) 1).Nonempty :=
    ⟨⟨b, hbS⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      by simpa [Split.sideB] using hb_t⟩⟩
  refine ⟨({a, b, c, d} : Finset α), hcard, hA₁, hB₁, hA₂, hB₂, ?_⟩
  intro heq
  have hmem1 : (⟨b, hbS⟩ : ↥({a, b, c, d} : Finset α))
      ∈ (s.restrict _ hA₁ hB₁).sideA := by
    show (⟨b, hbS⟩ : ↥({a, b, c, d} : Finset α))
      ∈ s.restrictSide ({a, b, c, d} : Finset α) 0
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      by simpa [Split.sideA] using hb_s⟩
  have hmem2 : (⟨b, hbS⟩ : ↥({a, b, c, d} : Finset α))
      ∉ (t.restrict _ hA₂ hB₂).sideA := by
    show (⟨b, hbS⟩ : ↥({a, b, c, d} : Finset α))
      ∉ t.restrictSide ({a, b, c, d} : Finset α) 0
    intro hbt
    have hbt' : b ∈ t.sideA := by
      simpa [Split.sideA] using (Finset.mem_filter.mp hbt).2
    exact (Finset.disjoint_left.mp t.disjoint_sides) hbt'
      (by simpa [Split.sideB] using hb_t)
  rw [heq] at hmem1
  exact hmem2 hmem1

end Split

/-! ## binary 树的专门描述

`CONCEPTS.md` §3.3（老师 2026-10-06 定）：**无根树取「内部节点 `degree = 3`」**。
`QuadetDecidesTree` 必须限定在 binary 上（polytomy refine 成 binary 不改 quartet 系统），
故把 binary 的推论单独成层。 -/

namespace Cladogram

variable {X : Type*} {T : Cladogram X}

/-- ★ **二叉树中非叶顶点的邻居恰 3 个**。 -/
theorem IsBinary.card_neighborFinset (h : T.IsBinary) {v : T.V} (hv : ¬ T.IsLeaf v) :
    (T.graph.neighborFinset v).card = 3 := by
  rw [SimpleGraph.card_neighborFinset_eq_degree, h.degree_eq_three hv]

/-- ★★ **二叉树中非叶顶点至少有两个不同的邻居**。

（binary 性最常用的形式：从内部顶点往两个方向各走一步。） -/
theorem IsBinary.exists_two_adj (h : T.IsBinary) {v : T.V} (hv : ¬ T.IsLeaf v) :
    ∃ c d : T.V, c ≠ d ∧ T.graph.Adj v c ∧ T.graph.Adj v d := by
  have h3 : 1 < (T.graph.neighborFinset v).card := by
    rw [h.card_neighborFinset hv]; norm_num
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp h3
  exact ⟨c, d, hcd, (SimpleGraph.mem_neighborFinset T.graph v c).mp hc,
    (SimpleGraph.mem_neighborFinset T.graph v d).mp hd⟩

/-- **二叉树自动无度 2**（`Cladogram.no_degree_two` 对 binary 是冗余的）。 -/
theorem IsBinary.degree_ne_two (h : T.IsBinary) (v : T.V) : T.graph.degree v ≠ 2 := by
  rcases h.degree_eq_one_or_three v with h1 | h3 <;> omega

end Cladogram

/-- **二叉 cladogram**（无根）：`Cladogram` + 内部顶点度**恰为** 3。

（`Cladogram` 的 `no_degree_two` 只排除度 2、允许 polytomy；本结构把它加强为 binary，
用于 `QuartetDecidesTree` 一类**必须** binary 的定理。） -/
structure BinaryCladogram (X : Type*) extends Cladogram X where
  isBinary : toCladogram.IsBinary

namespace BinaryCladogram

variable {X : Type*} (T : BinaryCladogram X)

/-- 二叉树中非叶顶点的邻居恰 3 个。 -/
theorem card_neighborFinset {v : T.toCladogram.V} (hv : ¬ T.toCladogram.IsLeaf v) :
    (T.toCladogram.graph.neighborFinset v).card = 3 :=
  T.isBinary.card_neighborFinset hv

/-- 二叉树中非叶顶点至少有两个不同的邻居。 -/
theorem exists_two_adj {v : T.toCladogram.V} (hv : ¬ T.toCladogram.IsLeaf v) :
    ∃ c d : T.toCladogram.V, c ≠ d ∧ T.toCladogram.graph.Adj v c ∧
      T.toCladogram.graph.Adj v d :=
  T.isBinary.exists_two_adj hv

/-- 二叉树无度 2。 -/
theorem degree_ne_two (v : T.toCladogram.V) : T.toCladogram.graph.degree v ≠ 2 :=
  T.isBinary.degree_ne_two v

end BinaryCladogram
