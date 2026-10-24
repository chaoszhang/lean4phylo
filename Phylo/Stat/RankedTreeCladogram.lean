/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CoalescentHistoryCount
import Phylo.CladogramBuild
import Mathlib.Combinatorics.SimpleGraph.Star

/-!
# `Phylo.Stat.RankedTreeCladogram` —— M3 `tree` 槽：`RankedTree n → Cladogram (Fin n)`

## 0. 为什么需要这件器材

`YHKClanLawGap`（`Phylo/Stat/ReciprocalMonophyly.lean:924`）的形状是

```
∃ (Ω : Type) (_ : Fintype Ω) (prob : Ω → ℝ) (_ : ∀ ω, 0 ≤ prob ω)
  (_ : ∑ ω, prob ω = 1) (tree : Ω → Cladogram (Fin n)),
  ∀ A : Finset (Fin n), A.Nonempty → A.card < n → … = clanProb n A.card
```

`Ω := RankedTree n`、`prob := 1 / H n` 与归一化 `sum_rankedTree_uniform`
（`Phylo/Stat/CoalescentHistoryCount.lean` §6）都**已就绪**；缺的只是 `tree`。
没有它，「`A` 是不是 clan」这句话**根本不可陈述**。

## 1. 造法（复用 §11.7 的器材，不从图论重建）

1. 合并史 `ω` 的每一步并出一个块；所有**非单点、非全集**块（`2 ≤ |C| ≤ n−2`）
   记作 `blockFamily n ω`；
2. 每块 `C` 给一条**无根 split** `C | (univ ∖ C)`（`splitOf`），并补上换向
   ⇒ `splitFamily n ω`；
3. 块族是镶嵌族（★★ `RankedGeneTree.laminarFamily_cladesOf`）⇒ split 族两两相容
   （`compatible_swapClosure` 把换向也一并处理）；
4. ★★★ `Cladogram.ofCompatibleSplits` 把族造成树，★★★
   `Cladogram.isSplitOf_ofCompatibleSplits` 给「族的成员（＋平凡 split）**恰是**树的
   split」的**完全刻画**。

⚠️ `Cladogram` 是**无根**载体，`IsClade` 在它上面**就是学界的 clan**
（`Phylo/InternalEdge.lean:589` 的术语提示）⇒ 一条 split 的**两侧**都是 clan。
故本文件的关键引理是「`A` **或** `Aᶜ` 是 `ω` 的非单点块」，
而不是「`A` 是 `ω` 的 clade」—— 前者恰是 ZDS Lemma 6.1 的包含-排除
`p_n(a) + p_n(n−a) − p̂_n(a,n−a)` 所需形状。

## 2. 交付清单

| 条目 | 状态 |
|---|---|
| `blockFamily` / `baseSplits` / `splitFamily`（合并史 ↦ split 族） | ★ 本文件 |
| `rankedTreeCladogramOfThree`（`3 ≤ n`）、`rankedTreeCladogram`（`2 ≤ n`） | ★★ 本文件 |
| `isClade_rankedTreeCladogramOfThree_iff`（**关键刻画**） | ★★★ 本文件 |

★ **`Cladogram (Fin 1)` 是空类型**（单顶点树的度是 `0`，不满足「度 1 ⟺ 叶」），
故 `n = 1` 那一档**不存在**（§5.2 有论证）；本文件因此把 `tree` 槽实现在 `2 ≤ n` 上。
-/

namespace Phylo.Stat.RankedTreeCladogram

/-! ## 3. 合并史的**非单点块** -/

/-- `ω` 的**非单点、非全集块**：clade 集中基数落在 `[2, n−2]` 的那些。

单点块与全集块不是**非平凡** split（`n−1` 元块的补是单点，同样平凡），
故它们不进入 split 族；但它们在 `IsClade` 的刻画里以「平凡支」出现。 -/
def blockFamily (n : ℕ) (ω : RankedGeneTree.RankedTree n) : Finset (Finset (Fin n)) :=
  (RankedGeneTree.cladesOf n ω.1).filter (fun C => 2 ≤ C.card ∧ C.card ≤ n - 2)

theorem mem_blockFamily {n : ℕ} {ω : RankedGeneTree.RankedTree n} {C : Finset (Fin n)} :
    C ∈ blockFamily n ω ↔
      C ∈ RankedGeneTree.cladesOf n ω.1 ∧ 2 ≤ C.card ∧ C.card ≤ n - 2 :=
  Finset.mem_filter

theorem two_le_card_of_mem_blockFamily {n : ℕ} {ω : RankedGeneTree.RankedTree n}
    {C : Finset (Fin n)} (h : C ∈ blockFamily n ω) : 2 ≤ C.card :=
  (mem_blockFamily.mp h).2.1

theorem card_le_of_mem_blockFamily {n : ℕ} {ω : RankedGeneTree.RankedTree n}
    {C : Finset (Fin n)} (h : C ∈ blockFamily n ω) : C.card ≤ n - 2 :=
  (mem_blockFamily.mp h).2.2

theorem mem_cladesOf_of_mem_blockFamily {n : ℕ} {ω : RankedGeneTree.RankedTree n}
    {C : Finset (Fin n)} (h : C ∈ blockFamily n ω) :
    C ∈ RankedGeneTree.cladesOf n ω.1 :=
  (mem_blockFamily.mp h).1

theorem nonempty_of_mem_blockFamily {n : ℕ} {ω : RankedGeneTree.RankedTree n}
    {C : Finset (Fin n)} (h : C ∈ blockFamily n ω) : C.Nonempty :=
  Finset.card_pos.mp (by have h2 := two_le_card_of_mem_blockFamily h; omega)

/-- 补集的基数（`Fin n` 上的通用形式）。 -/
theorem card_compl_eq (n : ℕ) (C : Finset (Fin n)) : (Cᶜ).card = n - C.card := by
  rw [Finset.card_compl, Fintype.card_fin]

theorem compl_nonempty_of_mem_blockFamily {n : ℕ} {ω : RankedGeneTree.RankedTree n}
    {C : Finset (Fin n)} (h : C ∈ blockFamily n ω) : (Cᶜ).Nonempty := by
  rw [← Finset.card_pos, card_compl_eq n C]
  have h1 := two_le_card_of_mem_blockFamily h
  have h2 := card_le_of_mem_blockFamily h
  omega

/-! ## 4. 块 ↦ 无根 split 族 -/

/-- 单块 `C` 给出的 split `C | Cᶜ`（`C ∈ blockFamily n ω` 保证两侧非空）。 -/
noncomputable def blockSplit (n : ℕ) (ω : RankedGeneTree.RankedTree n)
    (C : {C : Finset (Fin n) // C ∈ blockFamily n ω}) : Split (Fin n) :=
  splitOf C.1 (nonempty_of_mem_blockFamily C.2) (compl_nonempty_of_mem_blockFamily C.2)

@[simp] theorem blockSplit_sideA (n : ℕ) (ω : RankedGeneTree.RankedTree n)
    (C : {C : Finset (Fin n) // C ∈ blockFamily n ω}) :
    (blockSplit n ω C).sideA = C.1 := by
  simp [blockSplit]

/-- 每个非单点块给**一条**定向 split（尚未补换向）。 -/
noncomputable def baseSplits (n : ℕ) (ω : RankedGeneTree.RankedTree n) :
    Finset (Split (Fin n)) :=
  (blockFamily n ω).attach.biUnion (fun C => {blockSplit n ω C})

/-- `baseSplits` 的成员都来自某个非单点块。 -/
theorem sideA_mem_blockFamily_of_mem_baseSplits {n : ℕ} {ω : RankedGeneTree.RankedTree n}
    {s : Split (Fin n)} (h : s ∈ baseSplits n ω) : s.sideA ∈ blockFamily n ω := by
  rw [baseSplits, Finset.mem_biUnion] at h
  obtain ⟨C, -, hC⟩ := h
  rw [Finset.mem_singleton] at hC
  rw [hC, blockSplit_sideA]
  exact C.2

/-- 每个非单点块都给出 `baseSplits` 中的一条 split（其一侧恰为该块）。 -/
theorem exists_mem_baseSplits_of_mem_blockFamily {n : ℕ} {ω : RankedGeneTree.RankedTree n}
    {A : Finset (Fin n)} (h : A ∈ blockFamily n ω) :
    ∃ s : Split (Fin n), s ∈ baseSplits n ω ∧ s.sideA = A := by
  refine ⟨blockSplit n ω ⟨A, h⟩, ?_, blockSplit_sideA n ω ⟨A, h⟩⟩
  rw [baseSplits, Finset.mem_biUnion]
  exact ⟨⟨A, h⟩, Finset.mem_attach _ _, Finset.mem_singleton_self _⟩

/-- ★★ **`baseSplits` 两两相容**：块族是镶嵌族（`laminarFamily_cladesOf`）。 -/
theorem compatible_baseSplits {n : ℕ} {ω : RankedGeneTree.RankedTree n} :
    ∀ s ∈ baseSplits n ω, ∀ t ∈ baseSplits n ω, Split.Compatible s t := by
  intro s hs t ht
  have hs' := mem_cladesOf_of_mem_blockFamily (sideA_mem_blockFamily_of_mem_baseSplits hs)
  have ht' := mem_cladesOf_of_mem_blockFamily (sideA_mem_blockFamily_of_mem_baseSplits ht)
  have hlam := RankedGeneTree.laminarFamily_cladesOf (n := n) ω.1
  rcases hlam s.sideA hs' t.sideA ht' with hsub | hsub | hdisj
  · exact Split.compatible_of_subset_left hsub
  · exact Split.compatible_of_subset_right hsub
  · exact Split.compatible_of_disjoint hdisj

/-- ★★ **`baseSplits` 非平凡**（两侧各 `≥ 2` 叶）。 -/
theorem nontrivial_baseSplits {n : ℕ} {ω : RankedGeneTree.RankedTree n} :
    ∀ s ∈ baseSplits n ω, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card := by
  intro s hs
  have hC := sideA_mem_blockFamily_of_mem_baseSplits hs
  refine ⟨two_le_card_of_mem_blockFamily hC, ?_⟩
  rw [Split.sideB_eq_compl, card_compl_eq n s.sideA]
  have h1 := two_le_card_of_mem_blockFamily hC
  have h2 := card_le_of_mem_blockFamily hC
  omega

/-- `baseSplits` **补上换向**（`ofCompatibleSplits` 的 `hswap` 要求）。 -/
noncomputable def splitFamily (n : ℕ) (ω : RankedGeneTree.RankedTree n) :
    Finset (Split (Fin n)) :=
  baseSplits n ω ∪ (baseSplits n ω).image (fun s => s.swap)

/-- ★★ `splitFamily` 两两相容（换向保持相容）。 -/
theorem splitFamily_compatible (n : ℕ) (ω : RankedGeneTree.RankedTree n) :
    ∀ s ∈ splitFamily n ω, ∀ t ∈ splitFamily n ω, Split.Compatible s t :=
  compatible_swapClosure (compatible_baseSplits (n := n) (ω := ω))

/-- ★★ `splitFamily` 非平凡（换向只对调两侧）。 -/
theorem splitFamily_nontrivial (n : ℕ) (ω : RankedGeneTree.RankedTree n) :
    ∀ s ∈ splitFamily n ω, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card :=
  nontrivial_swapClosure (nontrivial_baseSplits (n := n) (ω := ω))

/-- ★★ `splitFamily` 对换向封闭。 -/
theorem splitFamily_swap_closed (n : ℕ) (ω : RankedGeneTree.RankedTree n) :
    ∀ s ∈ splitFamily n ω, s.swap ∈ splitFamily n ω :=
  swapClosure_swap_closed (baseSplits n ω)

/-! ## 5. `tree` 槽：合并史 ↦ 无根树 -/

/-- ★★ **`3 ≤ n` 时的树**：由 `splitFamily` 经 ★★★ `Cladogram.ofCompatibleSplits` 造出。 -/
noncomputable def rankedTreeCladogramOfThree {n : ℕ} (hn : 3 ≤ n)
    (ω : RankedGeneTree.RankedTree n) : Cladogram.{0, 0} (Fin n) :=
  Cladogram.ofCompatibleSplits (splitFamily n ω) ⟨0, by omega⟩ (splitFamily_compatible n ω)
    (splitFamily_nontrivial n ω) (splitFamily_swap_closed n ω) (by simpa using hn)

/-- ★★★ **`splitFamily` 造出的树的 split 系统被完全刻画**：
`s` 是树的 split ⟺ `s` 在族里，或 `s` 平凡（单点集 / 单点集的补）。 -/
theorem isSplitOf_rankedTreeCladogramOfThree {n : ℕ} (hn : 3 ≤ n)
    (ω : RankedGeneTree.RankedTree n) (s : Split (Fin n)) :
    (rankedTreeCladogramOfThree hn ω).IsSplitOf s ↔
      s ∈ splitFamily n ω ∨ (∃ x : Fin n, s.sideA = {x}) ∨
        (∃ x : Fin n, s.sideA = {x}ᶜ) :=
  Cladogram.isSplitOf_ofCompatibleSplits (splitFamily n ω) _ _ _ _ _ s

/-! ### 5.1 `n = 2` 的边角（库内 `ofCompatibleSplits` 要求 `3 ≤ |X|`） -/

/-- `starGraph 0` 在 `Fin 2` 上处处度 `1`（两个顶点互为唯一邻居）。 -/
theorem degree_starGraph_fin_two (v : Fin 2) :
    (SimpleGraph.starGraph (0 : Fin 2)).degree v = 1 := by
  fin_cases v
  · simpa using SimpleGraph.degree_starGraph_center (r := (0 : Fin 2))
  · exact SimpleGraph.degree_starGraph_of_ne_center (by decide : (1 : Fin 2) ≠ 0)

/-- ★★ **2 叶 `Cladogram`**：`V = Fin 2`、`graph = starGraph 0`（单边 `0—1`）、`leaf = id`。 -/
noncomputable def rankedTreeCladogramTwo : Cladogram.{0, 0} (Fin 2) where
  V := Fin 2
  fintypeV := inferInstance
  decEqV := inferInstance
  graph := SimpleGraph.starGraph (0 : Fin 2)
  decAdj := inferInstance
  isTree := SimpleGraph.isTree_starGraph 0
  leaf := Function.Embedding.refl (Fin 2)
  leaf_iff_degree_one := by
    intro v
    exact ⟨fun _ => degree_starGraph_fin_two v, fun _ => ⟨v, rfl⟩⟩
  no_degree_two := by
    intro v h
    have := degree_starGraph_fin_two v
    omega

/-! ### 5.2 总计版本 `rankedTreeCladogram`（`2 ≤ n`）

★ **`n = 1` 一档不存在**：`Cladogram (Fin 1)` 是**空类型**。理由：单顶点图的度是 `0`，
而 `leaf_iff_degree_one` 要求「度 1 ⟺ 叶」；有边则两个端点度都是 `1`，其中一个是叶却
没有标签（`Fin 1` 只有一个标签）；路径长 2 的中间点度为 `2`，违反 `no_degree_two`。
任何树至少有 2 个度 1 的顶点 —— 所以 `|X| = 1` 无解。故 `tree` 槽只能在 `2 ≤ n` 上实现
（这与 `YHKClanLawGap` 的前提 `2 ≤ n` 一致）。 -/

/-- ★★★ **M3 `tree` 槽**：`RankedTree n → Cladogram (Fin n)`（`2 ≤ n`）。 -/
noncomputable def rankedTreeCladogram (n : ℕ) (hn : 2 ≤ n)
    (ω : RankedGeneTree.RankedTree n) : Cladogram.{0, 0} (Fin n) :=
  if h3 : 3 ≤ n then rankedTreeCladogramOfThree h3 ω
  else by
    have h2 : n = 2 := by omega
    subst h2
    exact rankedTreeCladogramTwo

/-- `3 ≤ n` 时总计版本就是 `rankedTreeCladogramOfThree`。 -/
theorem rankedTreeCladogram_eq_of_three {n : ℕ} (hn : 2 ≤ n) (h3 : 3 ≤ n)
    (ω : RankedGeneTree.RankedTree n) :
    rankedTreeCladogram n hn ω = rankedTreeCladogramOfThree h3 ω := by
  unfold rankedTreeCladogram
  rw [dite_eq_left h3]

end Phylo.Stat.RankedTreeCladogram
