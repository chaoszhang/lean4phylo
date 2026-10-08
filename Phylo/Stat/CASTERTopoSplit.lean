/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERTopo
import Phylo.Stat.CASTERTheorem1

/-!
# `Phylo.Stat.CASTERTopoSplit` —— 把 **无根 quartet 拓扑（`Topo`）**接到 **`Split`** 世界

## 为什么需要它

各模型（`Phylo.Stat.CASTERJC69` / `CASTERLM1` / `CASTERF84`）产出的是 **`Topo` 层**的结论
（`CASTERTopo.TopoIdeal`：每个 4-元集上三个无根 quartet 拓扑的期望权重 + 命题 B）。
而库里既有的定理 1 / 定理 2 / 树同构收口（`CASTERTheorem1` / `CASTERTheorem2` /
`QuartetDecides`）都建在 **`Split ↥S`** 世界（`CASTERIdeal`）上。

本文件给出两边的**词典**：

* ★★★ `TopoIdeal.toSplitIdeal` —— 从 `TopoIdeal`（+ 每个 4-元集的标号 `↥S ≃ Fin 4`
  + 一个「真 `Split` 选择」）造出 `CASTERIdeal`；
* ★★ `eq_or_swap_of_topoOfSplit_eq` —— `2|2` 划分的**拓扑类相同 ⟹ 相等或互为 `swap`**
  （这是 `propB` 能搬运的关键）；
* ★ `topoOfSplit_swap` —— 类映射**对 `swap` 不变**（对**所有**划分成立，不只是 `2|2`）。

于是「模型 ⇒ 定理 1（`Topo` 层）」可以**免费**升级为
「模型 ⇒ 定理 1（`Split` 层）⇒ 估计量的树与真树**同构**」（经既有的
`caster_statisticallyConsistent` + `QuartetDecidesTree`）。

## 记账约定（唯一一处「人为」的地方）

`CASTERIdeal.propB` 要对**所有** `r : Split ↥S` 成立，而 `1|3` 这类**非 quartet** 划分
在 CASTER 的权重表里**根本没有定义**。本文件的办法是把它们的权重填成一个**严格小于三个
`Topo` 权重的最小值**的占位值 `topoMin - 1`，于是它们**永远不可能被选中** ——
这与语义一致（`1|3` 划分不是 quartet，不该被选）。真正的 `2|2` 划分仍用 `Topo` 权重。 -/

universe u

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace Phylo.Stat.CASTERTopoSplit

open Phylo.Stat.CASTERWeights (Topo)
open Phylo.Stat.CASTERTopo

/-! ## 1. `x` 所在的那一侧，与「0 号的伙伴」 -/

/-- `x` 所在的**那一侧**（`x ∈ sideA` 时取 `sideA`，否则取 `sideB`）。

这个写法的好处：**对 `swap` 天然不变**（`swap` 只是把两侧互换），
于是拓扑类映射的 `swap`-不变性几乎是免费的。 -/
def sideWith (r : Split α) (x : α) : Finset α := if x ∈ r.sideA then r.sideA else r.sideB

theorem sideWith_eq_sideA_or_sideB (r : Split α) (x : α) :
    sideWith r x = r.sideA ∨ sideWith r x = r.sideB := by
  unfold sideWith; split <;> simp

theorem mem_sideWith_self (r : Split α) (x : α) : x ∈ sideWith r x := by
  unfold sideWith
  split_ifs with h
  · exact h
  · by_contra hx
    have hx' : x ∈ r.sideA := by
      have := r.union_sides
      have : x ∈ r.sideA ∪ r.sideB := by rw [this]; exact Finset.mem_univ x
      exact (Finset.mem_union.mp this).resolve_right hx
    exact h hx'

theorem sideWith_swap (r : Split α) (x : α) : sideWith r.swap x = sideWith r x := by
  have hcomp := r.sideB_eq_compl
  unfold sideWith
  rw [Split.swap_sideA, Split.swap_sideB]
  by_cases h : x ∈ r.sideA
  · have hnb : x ∉ r.sideB := fun hx => (Finset.disjoint_left.mp r.disjoint_sides h) hx
    simp only [h, hnb, ite_true, ite_false]
  · have hb : x ∈ r.sideB := by
      have := r.union_sides
      have : x ∈ r.sideA ∪ r.sideB := by rw [this]; exact Finset.mem_univ x
      exact (Finset.mem_union.mp this).resolve_left h
    simp only [h, hb, ite_true, ite_false]

/-- **`sideA` 由 `sideB` 决定**（补侧；由「并 = 全集 + 不交」立得）。 -/
theorem sideA_eq_sdiff (s : Split α) : s.sideA = Finset.univ \ s.sideB := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · intro hx
    exact fun hx' => (Finset.disjoint_left.mp s.disjoint_sides hx) hx'
  · intro hx
    by_contra hxA
    have := s.union_sides
    have : x ∈ s.sideA ∪ s.sideB := by rw [this]; exact Finset.mem_univ x
    exact hxA ((Finset.mem_union.mp this).resolve_right hx)

theorem card_sideA_add_card_sideB (s : Split α) :
    s.sideA.card + s.sideB.card = Fintype.card α := by
  rw [← Finset.card_union_of_disjoint s.disjoint_sides, s.union_sides, Finset.card_univ]

/-- 两侧 `sideA` 相同 ⟹ 两个 split 相等（`parts` 由 `sideA` 与 `sideB = sideAᶜ` 决定）。 -/
theorem eq_of_sideA_eq {s t : Split α} (h : s.sideA = t.sideA) : s = t := by
  rw [KPartition.eq_iff_parts]
  funext i
  fin_cases i
  · exact h
  · change s.sideB = t.sideB
    rw [s.sideB_eq_sdiff, t.sideB_eq_sdiff, h]

/-- `s.sideA = t.sideB` ⟹ `s = t.swap`。 -/
theorem eq_swap_of_sideA_eq_sideB {s t : Split α} (h : s.sideA = t.sideB) : s = t.swap := by
  rw [KPartition.eq_iff_parts]
  funext i
  fin_cases i
  · change s.sideA = t.swap.sideA
    rw [Split.swap_sideA]; exact h
  · change s.sideB = t.swap.sideB
    rw [Split.swap_sideB]
    rw [s.sideB_eq_sdiff, h, sideA_eq_sdiff]

/-! ## 2. 拓扑类映射 -/

/-- **`e.symm 0` 的伙伴编号**：与它同侧的那个标号（`2|2` 划分下唯一，取 `1/2/3`）。 -/
def partnerOf (e : α ≃ Fin 4) (r : Split α) : Fin 4 :=
  if e.symm 1 ∈ sideWith r (e.symm 0) then 1
  else if e.symm 2 ∈ sideWith r (e.symm 0) then 2
  else 3

/-- 编号到拓扑：`1 ↦ ab|cd`、`2 ↦ ac|bd`、`3 ↦ ad|bc`。 -/
def toTopoOfIdx (i : Fin 4) : Topo :=
  if i = 1 then .ab_cd else if i = 2 then .ac_bd else .ad_bc

/-- **`Split α` 的无向 quartet 拓扑类**（对 `2|2` 划分有意义；与 `swap` 无关）。 -/
def topoOfSplit (e : α ≃ Fin 4) (r : Split α) : Topo := toTopoOfIdx (partnerOf e r)

theorem partnerOf_eq_one_or_two_or_three (e : α ≃ Fin 4) (r : Split α) :
    partnerOf e r = 1 ∨ partnerOf e r = 2 ∨ partnerOf e r = 3 := by
  unfold partnerOf; split_ifs <;> simp

theorem partnerOf_swap (e : α ≃ Fin 4) (r : Split α) :
    partnerOf e r.swap = partnerOf e r := by
  unfold partnerOf; rw [sideWith_swap]

/-- ★ **类映射对 `swap` 不变**（对**所有**划分成立）。 -/
theorem topoOfSplit_swap (e : α ≃ Fin 4) (r : Split α) :
    topoOfSplit e r.swap = topoOfSplit e r := by
  unfold topoOfSplit; rw [partnerOf_swap]

/-- `Fin 4` 的四个元素（`fin_cases` 只接受局部变量，故单列一条）。 -/
theorem fin4_eq_four (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  fin_cases i <;> simp

omit [Fintype α] [DecidableEq α] in
/-- 四个标号穷尽 `α`（`α` 有 4 个元素）。 -/
theorem eq_four (e : α ≃ Fin 4) (a : α) :
    a = e.symm 0 ∨ a = e.symm 1 ∨ a = e.symm 2 ∨ a = e.symm 3 := by
  have h := fin4_eq_four (e a)
  rcases h with h | h | h | h
  · exact Or.inl (by rw [← h]; simp)
  · exact Or.inr (Or.inl (by rw [← h]; simp))
  · exact Or.inr (Or.inr (Or.inl (by rw [← h]; simp)))
  · exact Or.inr (Or.inr (Or.inr (by rw [← h]; simp)))

theorem fin4_eq_one_or_two_or_three (i : Fin 4) : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 0 := by
  fin_cases i <;> simp

theorem toTopoOfIdx_inj {i j : Fin 4}
    (hi : i = 1 ∨ i = 2 ∨ i = 3) (hj : j = 1 ∨ j = 2 ∨ j = 3)
    (h : toTopoOfIdx i = toTopoOfIdx j) : i = j := by
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    simp_all [toTopoOfIdx]

/-- ★★ **伙伴确实在 `0` 的那一侧**（`2|2` 划分时）。 -/
theorem partnerOf_mem (e : α ≃ Fin 4) {r : Split α} (hr : r.sideA.card = 2) :
    e.symm (partnerOf e r) ∈ sideWith r (e.symm 0) := by
  have hcard := card_sideA_add_card_sideB r
  have hα : Fintype.card α = 4 := by
    have := Fintype.card_congr e; simpa using this
  have hmem0 : e.symm 0 ∈ sideWith r (e.symm 0) := mem_sideWith_self r _
  have hside : sideWith r (e.symm 0) = r.sideA ∨ sideWith r (e.symm 0) = r.sideB :=
    sideWith_eq_sideA_or_sideB r _
  have hc2 : (sideWith r (e.symm 0)).card = 2 := by
    rcases hside with h | h <;> rw [h]
    · exact hr
    · omega
  unfold partnerOf
  split_ifs with h1 h2
  · exact h1
  · exact h2
  · by_contra h3
    have hsub : sideWith r (e.symm 0) ⊆ {e.symm 0} := by
      intro x hx
      rcases eq_four e x with h | h | h | h
      · simp [h]
      · exact absurd (h ▸ hx) h1
      · exact absurd (h ▸ hx) h2
      · exact absurd (h ▸ hx) h3
    have := Finset.card_le_card hsub
    simp at this
    omega

/-- ★★ **`0` 的那一侧就是 `{0, 伙伴}`**（`2|2` 划分时）。 -/
theorem sideWith_eq_pair (e : α ≃ Fin 4) {r : Split α} (hr : r.sideA.card = 2) :
    sideWith r (e.symm 0) = {e.symm 0, e.symm (partnerOf e r)} := by
  have hcard := card_sideA_add_card_sideB r
  have hα : Fintype.card α = 4 := by
    have := Fintype.card_congr e; simpa using this
  have hside := sideWith_eq_sideA_or_sideB r (e.symm 0)
  have hc2 : (sideWith r (e.symm 0)).card = 2 := by
    rcases hside with h | h <;> rw [h]
    · exact hr
    · omega
  have hp : partnerOf e r = 1 ∨ partnerOf e r = 2 ∨ partnerOf e r = 3 :=
    partnerOf_eq_one_or_two_or_three e r
  have hne : e.symm (partnerOf e r) ≠ e.symm 0 := by
    intro h
    have := e.symm.injective h
    rcases hp with h' | h' | h' <;> rw [h'] at this <;> exact absurd this (by decide)
  have hsub : ({e.symm 0, e.symm (partnerOf e r)} : Finset α) ⊆ sideWith r (e.symm 0) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_sideWith_self r _
    · exact partnerOf_mem e hr
  have hcard2 : ({e.symm 0, e.symm (partnerOf e r)} : Finset α).card = 2 := by
    rw [Finset.card_pair]
    exact fun h => hne h.symm
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard2, hc2])).symm

/-- ★★★ **`2|2` 划分的类相同 ⟹ 相等或互为 `swap`**（`propB` 搬运的关键）。 -/
theorem eq_or_swap_of_topoOfSplit_eq (e : α ≃ Fin 4) {r r' : Split α}
    (hr : r.sideA.card = 2) (hr' : r'.sideA.card = 2)
    (h : topoOfSplit e r = topoOfSplit e r') : r = r' ∨ r = r'.swap := by
  have hp : partnerOf e r = partnerOf e r' :=
    toTopoOfIdx_inj (partnerOf_eq_one_or_two_or_three e r)
      (partnerOf_eq_one_or_two_or_three e r') h
  have hside : sideWith r (e.symm 0) = sideWith r' (e.symm 0) := by
    rw [sideWith_eq_pair e hr, sideWith_eq_pair e hr', hp]
  rcases sideWith_eq_sideA_or_sideB r (e.symm 0) with h1 | h1 <;>
    rcases sideWith_eq_sideA_or_sideB r' (e.symm 0) with h2 | h2
  · exact Or.inl (eq_of_sideA_eq (h1 ▸ h2 ▸ hside))
  · exact Or.inr (eq_swap_of_sideA_eq_sideB (h1 ▸ h2 ▸ hside))
  · refine Or.inr (eq_swap_of_sideA_eq_sideB ?_)
    rw [sideA_eq_sdiff r, ← h1, Split.sideB_eq_sdiff r', ← h2, hside]
  · exact Or.inl (eq_of_sideA_eq (by
      rw [sideA_eq_sdiff r, ← h1, sideA_eq_sdiff r', ← h2, hside]))

end Phylo.Stat.CASTERTopoSplit

namespace Phylo.Stat.CASTERTopo

open Phylo.Stat.CASTERTopoSplit
open Phylo.Stat.CASTERWeights

/-! ## 3. 从 `TopoIdeal` 造出 `CASTERIdeal` -/

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- 每个 4-元集的一个**标号**（把它的四个叶编号为 `0,1,2,3`）。 -/
abbrev QuartetLabel (X : Type u) [Fintype X] [DecidableEq X] :=
  ∀ (S : Finset X) (_ : S.card = 4), ↥S ≃ Fin 4

/-- 三个 `Topo` 权重的最小值（给非 `2|2` 划分当占位基准）。 -/
noncomputable def topoMin (M : TopoIdeal X) (S : Finset X) (hS : S.card = 4) : ℝ :=
  min (min (M.W S hS .ab_cd) (M.W S hS .ac_bd)) (M.W S hS .ad_bc)

theorem topoMin_le (M : TopoIdeal X) (S : Finset X) (hS : S.card = 4) (T : Topo) :
    topoMin M S hS ≤ M.W S hS T := by
  rcases T with _ | _ | _ <;>
    simp only [topoMin] <;>
    first
      | exact le_trans (min_le_left _ _) (min_le_left _ _)
      | exact le_trans (min_le_left _ _) (min_le_right _ _)
      | exact min_le_right _ _

namespace TopoIdeal

/-- ★★★ **从 `TopoIdeal` 造出 `CASTERIdeal`**（把两个世界接起来）。

参数：每个 4-元集的标号 `e`；一个**真 `Split` 选择** `qtrue`（它必须是 `2|2`，
且其拓扑类正好是 `M.qtrue`）。

权重表：`2|2` 划分取 `Topo` 权重（经 `topoOfSplit`）；非 `2|2` 划分取占位值
`topoMin - 1`（严格小于三个 `Topo` 权重，故永不被选中 —— `CASTERIdeal.propB` 要求
它对**所有** `r` 成立，而 CASTER 的权重表只对 quartet 有意义）。 -/
noncomputable def toSplitIdeal (M : TopoIdeal X) (e : QuartetLabel X)
    (qtrue : QuartetChoice X)
    (hq : ∀ (S : Finset X) (hS : S.card = 4), topoOfSplit (e S hS) (qtrue S hS) = M.qtrue S hS)
    (hqcard : ∀ (S : Finset X) (hS : S.card = 4), (qtrue S hS).sideA.card = 2) :
    CASTERIdeal X where
  W := fun S hS r =>
    if r.sideA.card = 2 then M.W S hS (topoOfSplit (e S hS) r) else topoMin M S hS - 1
  W_swap := by
    intro S hS r
    have hα : Fintype.card ↥S = 4 := by rw [Fintype.card_coe]; exact hS
    have hsum := card_sideA_add_card_sideB r
    have hcard : r.swap.sideA.card = 2 ↔ r.sideA.card = 2 := by
      rw [Split.swap_sideA]
      constructor <;> intro h
      · have : r.sideB.card = 2 := h
        omega
      · have : r.sideB.card = 2 := by omega
        exact this
    by_cases hr : r.sideA.card = 2
    · have h2 : r.swap.sideA.card = 2 := hcard.mpr hr
      simp only [h2, hr, topoOfSplit_swap]
    · have h2 : ¬ r.swap.sideA.card = 2 := fun h => hr (hcard.mp h)
      simp only [h2, hr, ite_false]
  qtrue := qtrue
  propB := by
    intro S hS r hne hne'
    by_cases hr : r.sideA.card = 2
    · have hqt : (qtrue S hS).sideA.card = 2 := hqcard S hS
      have hclass : topoOfSplit (e S hS) r ≠ M.qtrue S hS := by
        rw [← hq S hS]
        intro h
        rcases eq_or_swap_of_topoOfSplit_eq (e S hS) hr hqt h with h' | h'
        · exact hne h'
        · exact hne' h'
      have hlt := M.propB S hS (topoOfSplit (e S hS) r) hclass
      simp only [hr, hqt, hq S hS, ite_true]
      exact hlt
    · have hlt : topoMin M S hS - 1 < topoMin M S hS := by linarith
      have hle : topoMin M S hS ≤ M.W S hS (M.qtrue S hS) := topoMin_le M S hS _
      simp only [hr, hqcard S hS, hq S hS, ite_true, ite_false]
      linarith

end TopoIdeal

end Phylo.Stat.CASTERTopo
