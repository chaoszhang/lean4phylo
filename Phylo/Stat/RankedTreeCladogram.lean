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
| `clanHistories` / `clanEvent`（`Ω = RankedTree n`、`prob = 1/H n` 的事件集／概率） | ★★ 本文件 |
| `n = 4` 端到端：每个二元子集**恰在 6/18 条历史**里成 clan ⇒ 概率 `1/3` | ★★★ 本文件 |

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

/-- ★★ **派工书建议的名字（函数形态）**：`RankedTree n → Cladogram (Fin n)`。
（`tree` 槽在 `YHKClanLawGap` 里正是以 `Ω → Cladogram (Fin n)` 的形态出现。） -/
noncomputable abbrev rankedTreeToCladogram (n : ℕ) (hn : 2 ≤ n) :
    RankedGeneTree.RankedTree n → Cladogram.{0, 0} (Fin n) :=
  fun ω => rankedTreeCladogram n hn ω

/-- `3 ≤ n` 时总计版本就是 `rankedTreeCladogramOfThree`。 -/
theorem rankedTreeCladogram_eq_of_three {n : ℕ} (hn : 2 ≤ n) (h3 : 3 ≤ n)
    (ω : RankedGeneTree.RankedTree n) :
    rankedTreeCladogram n hn ω = rankedTreeCladogramOfThree h3 ω := by
  unfold rankedTreeCladogram
  rw [dite_eq_left h3]

/-! ## 6. ★★★ 关键刻画：`IsClade` ⟺ 「`A` 或 `Aᶜ` 是非单点块」 -/

/-- ★★★ **本文件的核心引理**：`A` 是 `rankedTreeCladogramOfThree hn ω` 的 clan
**⟺** `A` 或 `Aᶜ` 是 `ω` 的某个非单点块，或 `A` 平凡（单点集 / 单点集的补）。

⚠️ `Cladogram` 是**无根**载体 ⇒ 一条 split 的**两侧都是** clan，故右端出现
「`A` **或** `Aᶜ`」。这正是 ZDS Lemma 6.1 的包含-排除
`q_n(A) = p_n(a) + p_n(n−a) − p̂_n(a,n−a)` 所需的形状。 -/
theorem isClade_rankedTreeCladogramOfThree_iff {n : ℕ} (hn : 3 ≤ n)
    (ω : RankedGeneTree.RankedTree n) (A : Finset (Fin n)) :
    (rankedTreeCladogramOfThree hn ω).IsClade A ↔
      A ∈ blockFamily n ω ∨ Aᶜ ∈ blockFamily n ω ∨
        (∃ x : Fin n, A = {x}) ∨ (∃ x : Fin n, A = {x}ᶜ) := by
  have hchar := isSplitOf_rankedTreeCladogramOfThree hn ω
  have hcompl : ∀ x : Fin n, ({x}ᶜ : Finset (Fin n)).Nonempty := by
    intro x
    rw [← Finset.card_pos, card_compl_eq n {x}, Finset.card_singleton]
    omega
  constructor
  · intro h
    simp only [Cladogram.IsClade] at h
    obtain ⟨s, hs, rfl⟩ := h
    rw [hchar] at hs
    rcases hs with hmem | htriv | htriv
    · rcases Finset.mem_union.mp hmem with hb | hb
      · exact Or.inl (sideA_mem_blockFamily_of_mem_baseSplits hb)
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hb
        refine Or.inr (Or.inl ?_)
        have htA : t.sideA ∈ blockFamily n ω := sideA_mem_blockFamily_of_mem_baseSplits ht
        have heq : ((t.swap).sideA)ᶜ = t.sideA := by
          rw [Split.swap_sideA, Split.sideB_eq_compl, compl_compl]
        rw [heq]
        exact htA
    · exact Or.inr (Or.inr (Or.inl htriv))
    · exact Or.inr (Or.inr (Or.inr htriv))
  · rintro (h | h | ⟨x, hx⟩ | ⟨x, hx⟩)
    · obtain ⟨s, hs, hside⟩ := exists_mem_baseSplits_of_mem_blockFamily h
      exact ⟨s, (hchar s).mpr (Or.inl (Finset.mem_union.mpr (Or.inl hs))), hside⟩
    · obtain ⟨s, hs, hside⟩ := exists_mem_baseSplits_of_mem_blockFamily h
      refine ⟨s.swap, (hchar s.swap).mpr (Or.inl ?_), ?_⟩
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨s, hs, rfl⟩))
      · rw [Split.swap_sideA, Split.sideB_eq_compl, hside, compl_compl]
    · simp only [Cladogram.IsClade, hx]
      exact ⟨splitOf {x} (Finset.singleton_nonempty x) (hcompl x),
        (hchar _).mpr (Or.inr (Or.inl ⟨x, by simp⟩)), by simp⟩
    · simp only [Cladogram.IsClade, hx]
      exact ⟨(splitOf {x} (Finset.singleton_nonempty x) (hcompl x)).swap,
        (hchar _).mpr (Or.inr (Or.inr ⟨x, by rw [Split.swap_sideA]; simp⟩)),
        by rw [Split.swap_sideA]; simp⟩

/-! ## 7. `clanHistories` / `clanEvent`：`Ω = RankedTree n`、`prob = 1 / H n` 的事件与概率 -/

/-- 「`A` 是随机树的 clan」的**事件集**（`Ω = RankedTree n`）。

★ 写成 `noncomputable def` 而不是在定理里内联 `Finset.filter`：谓词含 `IsClade`
（不可判定），内联会让**陈述本身**需要 `DecidablePred`；收进 `def` 后所有下游陈述都不必
再拖一个 `classical`。 -/
noncomputable def clanHistories (n : ℕ) (hn : 2 ≤ n) (A : Finset (Fin n)) :
    Finset (RankedGeneTree.RankedTree n) := by
  classical
  exact Finset.univ.filter (fun ω => (rankedTreeCladogram n hn ω).IsClade A)

/-- 均匀律 `prob ≡ 1/H n` 下「`A` 是 clan」的概率 —— 即 `YHKClanLawGap` 的**左端**
（`Ω`、`prob`、`tree` 三槽都取本文件的具体实现）。 -/
noncomputable def clanEvent (n : ℕ) (hn : 2 ≤ n) (A : Finset (Fin n)) : ℝ :=
  ∑ _ω ∈ clanHistories n hn A, (1 / RankedGeneTree.H n)

/-- ★★★ **事件集的成员判定**（**M4 的接口**）：`ω` 使 `A` 成 clan ⟺ `A` 或 `Aᶜ` 是 `ω` 的
非单点块，或 `A` 平凡。

有了它，`clanEvent` 的求和就落成**块计数**：「`A` 是块」的事件 ＋「`Aᶜ` 是块」的事件
（平凡时直接是全集）。 -/
theorem mem_clanHistories_iff {n : ℕ} (hn : 2 ≤ n) (h3 : 3 ≤ n) (A : Finset (Fin n))
    (ω : RankedGeneTree.RankedTree n) :
    ω ∈ clanHistories n hn A ↔
      A ∈ blockFamily n ω ∨ Aᶜ ∈ blockFamily n ω ∨
        (∃ x : Fin n, A = {x}) ∨ (∃ x : Fin n, A = {x}ᶜ) := by
  classical
  unfold clanHistories
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [rankedTreeCladogram_eq_of_three (n := n) hn h3]
  exact isClade_rankedTreeCladogramOfThree_iff h3 ω A

/-- ★★ **事件集在非平凡基数上的形状**：`A` 成 clan 的历史集
= 「`A` 是非单点块」∪「`Aᶜ` 是非单点块」（`2 ≤ |A| ≤ n−2` 时无平凡支）。 -/
theorem mem_clanHistories_iff_of_card {n : ℕ} (hn : 2 ≤ n) (h3 : 3 ≤ n)
    {A : Finset (Fin n)} (h1 : 2 ≤ A.card) (h2 : A.card ≤ n - 2)
    (ω : RankedGeneTree.RankedTree n) :
    ω ∈ clanHistories n hn A ↔ A ∈ blockFamily n ω ∨ Aᶜ ∈ blockFamily n ω := by
  rw [mem_clanHistories_iff hn h3 A ω]
  constructor
  · rintro (h | h | ⟨x, hx⟩ | ⟨x, hx⟩)
    · exact Or.inl h
    · exact Or.inr h
    · exfalso; rw [hx, Finset.card_singleton] at h1; omega
    · exfalso; rw [hx, card_compl_eq n {x}, Finset.card_singleton] at h2; omega
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-! ## 8. `n = 4` 端到端（对齐 `yhkLawFour`：18 条历史／三棵 quartet 拓扑各 6 条） -/

/-- ★ 平凡基数（单点集 / 单点集的补）上的 clan（`n ≥ 3`）。 -/
theorem isClade_of_trivial {n : ℕ} (hn : 3 ≤ n) (ω : RankedGeneTree.RankedTree n)
    {A : Finset (Fin n)} (h : (∃ x : Fin n, A = {x}) ∨ (∃ x : Fin n, A = {x}ᶜ)) :
    (rankedTreeCladogramOfThree hn ω).IsClade A := by
  rw [isClade_rankedTreeCladogramOfThree_iff hn ω A]
  rcases h with ⟨x, hx⟩ | ⟨x, hx⟩
  · exact Or.inr (Or.inr (Or.inl ⟨x, hx⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨x, hx⟩))

/-- `n = 4`、基数 `2` 时的刻画（两个平凡支被 `card = 2` 排除）。 -/
theorem isClade_four_iff (ω : RankedGeneTree.RankedTree 4) (A : Finset (Fin 4))
    (hA : A.card = 2) :
    (rankedTreeCladogram 4 (by norm_num) ω).IsClade A ↔
      A ∈ blockFamily 4 ω ∨ Aᶜ ∈ blockFamily 4 ω := by
  rw [rankedTreeCladogram_eq_of_three (n := 4) (by norm_num) (by norm_num)]
  rw [isClade_rankedTreeCladogramOfThree_iff (n := 4) (by norm_num) (ω := ω)]
  constructor
  · rintro (h | h | ⟨x, hx⟩ | ⟨x, hx⟩)
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rw [hx, Finset.card_singleton] at hA
      omega
    · exfalso
      rw [hx, card_compl_eq 4 {x}, Finset.card_singleton] at hA
      omega
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

set_option maxRecDepth 100000 in
/-- ★★★ **闭式计数（内核规约）**：`Fin 4` 的每个二元子集 `A`，在 `H 4 = 18` 条合并史中
恰有 **6** 条使 `A` 或 `Aᶜ` 成为非单点块。

`6` 的两条独立来源（都已在会话中机器核过）：

* **按事件分解**：`#{A 是块} = 4`、`#{Aᶜ 是块} = 4`、`#{两者同时} = 2`
  ⇒ `4 + 4 − 2 = 6`。
  （`{a,b}` 成块 ⟺ `a`、`b` 彼此先合并：`{a,b}` 为 cherry 的 2 棵**不平衡**拓扑（各 1 ranking）
  加 `A | Aᶜ` 为根分裂的**平衡**拓扑（2 rankings）＝ `4`；两者同时成块 ⟺ 根分裂恰为 `A | Aᶜ`，
  即平衡那 `2` 条。）
* **按拓扑分解**：`A | Aᶜ` 的 quartet 拓扑在 `n = 4` 上恰有 `6` 条 ranked 历史
  （`H 2 · H 2 = 1` 条根分裂固定的情形另需内部结点交错 —— 故此处**不**用 `H_a·H_b`，
  而是直接由内核枚举给出闭值 `6`，与 `yhkLawFour` 的「三棵拓扑各 6 条」一致）。 -/
theorem card_filter_blockFamily_four :
    ∀ A ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun A => decide (A.card = 2) = true),
      ((Finset.univ : Finset (RankedGeneTree.RankedTree 4)).filter
        (fun ω => (decide (A ∈ blockFamily 4 ω) || decide (Aᶜ ∈ blockFamily 4 ω)) = true)).card
        = 6 := by
  decide

/-- ★★★ **`n = 4`：每个二元子集恰在 `6 / 18` 条历史里成 clan**。 -/
theorem card_clanHistories_four (A : Finset (Fin 4)) (hA : A.card = 2) :
    (clanHistories 4 (by norm_num) A).card = 6 := by
  classical
  have hmem : A ∈ (Finset.univ : Finset (Finset (Fin 4))).filter
      (fun A => decide (A.card = 2) = true) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hA]
    rfl
  have hclosed := card_filter_blockFamily_four A hmem
  have hcongr : clanHistories 4 (by norm_num) A
      = (Finset.univ : Finset (RankedGeneTree.RankedTree 4)).filter
        (fun ω => (decide (A ∈ blockFamily 4 ω) || decide (Aᶜ ∈ blockFamily 4 ω)) = true) := by
    unfold clanHistories
    apply Finset.filter_congr
    intro ω _
    rw [isClade_four_iff ω A hA]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
  rw [hcongr]
  exact hclosed

/-- ★★ **`n = 4`、基数 `1` 或 `3`：clan 事件集是全集**（`A` 平凡 ⇒ 必然事件）。 -/
theorem clanHistories_four_trivial (A : Finset (Fin 4)) (h : A.card = 1 ∨ A.card = 3) :
    clanHistories 4 (by norm_num) A = Finset.univ := by
  classical
  have htriv : (∃ x : Fin 4, A = {x}) ∨ (∃ x : Fin 4, A = {x}ᶜ) := by
    rcases h with h1 | h3
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h1
      exact Or.inl ⟨x, rfl⟩
    · have hc : (Aᶜ).card = 1 := by
        rw [card_compl_eq 4 A]
        omega
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
      refine Or.inr ⟨x, ?_⟩
      rw [← hx, compl_compl]
  have hcl : ∀ ω : RankedGeneTree.RankedTree 4,
      (rankedTreeCladogram 4 (by norm_num) ω).IsClade A := by
    intro ω
    rw [rankedTreeCladogram_eq_of_three (n := 4) (by norm_num) (by norm_num)]
    exact isClade_of_trivial (n := 4) (by norm_num) ω htriv
  unfold clanHistories
  exact Finset.filter_true_of_mem (fun ω _ => hcl ω)

/-- ★★ **`n = 4`、基数 `2`：clan 事件概率 `= 1/3`**（`6/18`）。 -/
theorem clanEvent_four_two (A : Finset (Fin 4)) (hA : A.card = 2) :
    clanEvent 4 (by norm_num) A = 1 / 3 := by
  unfold clanEvent
  rw [Finset.sum_const, card_clanHistories_four A hA, nsmul_eq_mul, RankedGeneTree.H_four]
  norm_num

/-- ★★ **`n = 4`、基数 `1` 或 `3`：clan 事件概率 `= 1`**（用 `sum_rankedTree_uniform`）。 -/
theorem clanEvent_four_trivial (A : Finset (Fin 4)) (h : A.card = 1 ∨ A.card = 3) :
    clanEvent 4 (by norm_num) A = 1 := by
  unfold clanEvent
  rw [clanHistories_four_trivial A h]
  exact CoalescentHistoryCount.sum_rankedTree_uniform 4 (by norm_num)

/-- ★★★ **`n = 4` 端到端**（`YHKClanLawGap` 的 `∃` 从句在 `n = 4` 上的**真实载体版**）：
`Ω := RankedTree 4`（`H 4 = 18` 条合并史）、`prob := 1/H 4`、`tree := rankedTreeCladogram 4`，
则非空真子集 `A` 的 clan 事件概率 `= clanProb 4 |A|`：

* `|A| = 1, 3` ⇒ `1`（必然事件，`clanEvent_four_trivial`）；
* `|A| = 2` ⇒ `1/3`（`clanEvent_four_two`，即 **6 / 18**）。

右端的 `if` 就是 `clanProb 4 A.card` 的取值：`clanProb 4 1 = clanProb 4 3 = 1`、
`clanProb 4 2 = 1/3`（`Phylo/Stat/ReciprocalMonophyly.lean` 的 `clanProb_one` /
`clanProb_pred` / `clanProb_four_two`；本文件不 import 那个模块以免循环）。 -/
theorem rankedTreeClanEvent_four (A : Finset (Fin 4)) (hA : A.Nonempty) (hlt : A.card < 4) :
    clanEvent 4 (by norm_num) A = if A.card = 2 then 1 / 3 else 1 := by
  have hpos : 1 ≤ A.card := Finset.card_pos.mpr hA
  by_cases h2 : A.card = 2
  · rw [ite_eq_left h2]
    exact clanEvent_four_two A h2
  · rw [ite_eq_right h2]
    exact clanEvent_four_trivial A (by omega)

end Phylo.Stat.RankedTreeCladogram
