/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.ReciprocalMonophyly
import Phylo.Stat.CoalescentHistoryCount

/-!
# `Phylo.Stat.CladeCount` —— (M4)：`#{ω : RankedTree n | A 是 ω 的 clade} = H n · pn n |A|`

Zhu–Degnan–Steel 2011 Lemma 4.2 的**概率层**（`YHKClanLawGap` ③ 的计数那一半），
在**均匀 `RankedTree n` 载体**上落地：

```text
# {ω : RankedTree n | A 是 ω 的 clade} = H n · pn n |A|        (1 ≤ |A| ≤ n−1)
```

配合 Lemma 6.1 的包含-排除（`clanProb_eq_inclusionExclusion`，已在库）即得缺口本体
「`A` 是 clan 的概率 `= clanProb n |A|`」。

## 载体与「clade」的库内形态

`RankedTree n`（`Phylo.Stat.RankedGeneTree:169`）= `IsMergeHistory n f` 的合并史
（`f k = (x,y)` 把两块并起来，`x`、`y` 是块代表、`x < y`）。

一条合并史给出**划分链** `Π_0 ⊂ Π_1 ⊂ ⋯ ⊂ Π_{n−1}`（`Π_L` = `gchain`/`chainMap` 的纤维）。
`A` 是这条历史的 **clade** ⟺ `A` 恰是某一层的一个块。本文件把它写成 `s`-相对形式
（`IsBlockAt`：`A = s.filter (fun z => r z = r w)`），因为计数归纳要沿「砍掉第一步」的
`s.erase y` 走 —— 而这正是 `CoalescentHistoryCount` 的 `IsMH`/`mhFinset` 已经支持的
「相对任意有限集 `s`」的载体（不必重标号）。

## 证明骨架（本文件的主线）

1. 头分解（`§3`）：按第一步的有序对 `p = (x,y)` 拆 `cladeCountS`；
2. 尾搬运（`§4`）：`f ↦ Fin.tail f` 把「`A` 是 `f` 的 clade」翻译成尾历史里
   「`A.erase y` / `A`」的 clade（`x,y ∈ A` 或 `x,y ∉ A`），混合对**永不为** clade；
3. 归纳（`§5`）：对步数 `m` 强归纳得递推
   `C(m+1,a) = C(a,2)·C(m,a−1) + C(m+1−a,2)·C(m,a)`；
4. 闭形式（`§6`）：该递推的解是 `H (m+1) · pn (m+1) a`（算术）。
-/

noncomputable section

open Classical

namespace Phylo.Stat.CladeCount

open Phylo.Stat.CoalescentHistoryCount

variable {N : ℕ}

/-! ## §1 定义：`s`-相对块、clade、计数 -/

/-- ★ `s`-相对块：代表映射 `r` 下含 `w` 的纤维（截在 `s` 上）。

（`s = univ` 时就是 `RankedGeneTree.blocksOf` 里的那个块。） -/
def blockOf (s : Finset (Fin N)) (r : Fin N → Fin N) (w : Fin N) : Finset (Fin N) :=
  s.filter (fun z => r z = r w)

/-- ★ **`A` 是第 `L` 层的一个块**（`s`-相对）。 -/
def IsBlockAt (s : Finset (Fin N)) (m : ℕ) (f : Fin m → Fin N × Fin N) (L : ℕ)
    (A : Finset (Fin N)) : Prop :=
  ∃ w ∈ A, A = blockOf s (gchain m f L) w

instance instDecidableIsBlockAt (s : Finset (Fin N)) (m : ℕ) (f : Fin m → Fin N × Fin N)
    (L : ℕ) (A : Finset (Fin N)) : Decidable (IsBlockAt s m f L A) := by
  unfold IsBlockAt
  infer_instance

/-- `f`（`s` 上 `m` 步）的、会命中 `A` 的**层号集合**（`0 ≤ L ≤ m`）。 -/
def cladeLevels (s : Finset (Fin N)) (m : ℕ) (f : Fin m → Fin N × Fin N)
    (A : Finset (Fin N)) : Finset ℕ :=
  (Finset.range (m + 1)).filter (fun L => IsBlockAt s m f L A)

/-- ★★ **`A` 是 `f` 的 clade**（`s`-相对、层号有界；空集与不合法的 `A` 自动为假）。 -/
def IsCladeH (s : Finset (Fin N)) (m : ℕ) (f : Fin m → Fin N × Fin N)
    (A : Finset (Fin N)) : Prop :=
  (cladeLevels s m f A).Nonempty

instance instDecidableIsCladeH (s : Finset (Fin N)) (m : ℕ) (f : Fin m → Fin N × Fin N)
    (A : Finset (Fin N)) : Decidable (IsCladeH s m f A) := by
  unfold IsCladeH
  infer_instance

/-- ★★ 展开式：`IsCladeH ↔ ∃ L ≤ m, A 是第 L 层的块`。 -/
theorem isCladeH_iff {s : Finset (Fin N)} {m : ℕ} {f : Fin m → Fin N × Fin N}
    {A : Finset (Fin N)} :
    IsCladeH s m f A ↔ ∃ L, L ≤ m ∧ IsBlockAt s m f L A := by
  unfold IsCladeH cladeLevels
  constructor
  · intro h
    obtain ⟨L, hL⟩ := h
    rw [Finset.mem_filter, Finset.mem_range] at hL
    exact ⟨L, by omega, hL.2⟩
  · rintro ⟨L, hL, hmem⟩
    exact ⟨L, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hmem⟩⟩

/-- ★★ **计数（显式步数版）**：`s` 上 `m` 步合并史中「`A` 是 clade」的条数。 -/
def cladeCountS (m : ℕ) (s : Finset (Fin N)) (A : Finset (Fin N)) : ℕ :=
  ((mhFinset N m s).filter (fun f => IsCladeH s m f A)).card

/-- ★★ 步数由 `|s|` 决定的版本（合法规模 `m = |s| − 1`）。 -/
def cladeCount (s : Finset (Fin N)) (A : Finset (Fin N)) : ℕ :=
  cladeCountS (s.card - 1) s A

theorem cladeCount_eq_cladeCountS (s : Finset (Fin N)) (A : Finset (Fin N)) :
    cladeCount s A = cladeCountS (s.card - 1) s A := rfl

/-- 块是 `s` 的子集。 -/
theorem blockOf_subset (s : Finset (Fin N)) (r : Fin N → Fin N) (w : Fin N) :
    blockOf s r w ⊆ s := Finset.filter_subset _ _

/-! ## §2 基例：单点集恒是 clade（第 `0` 层） -/

/-- 第 `0` 层的块就是单点集（`gchain _ _ 0 = id`）。 -/
theorem blockOf_zero (s : Finset (Fin N)) {m : ℕ} (f : Fin m → Fin N × Fin N) (w : Fin N) :
    blockOf s (gchain m f 0) w = s.filter (fun z => z = w) := by
  rw [gchain_zero]
  rfl

/-- ★ **第 `0` 层含 `w` 的块**就是 `{w}`（`w ∈ s`）。 -/
theorem blockOf_zero_singleton {s : Finset (Fin N)} {m : ℕ} (f : Fin m → Fin N × Fin N)
    {w : Fin N} (hw : w ∈ s) : blockOf s (gchain m f 0) w = {w} := by
  rw [blockOf_zero]
  ext z
  rw [Finset.mem_filter, Finset.mem_singleton]
  exact ⟨fun h => h.2, fun h => ⟨h ▸ hw, h⟩⟩

/-- ★★ **单点集恒是 clade**（任意 `s`、任意 `m`、任意 `f`）。 -/
theorem isCladeH_singleton (s : Finset (Fin N)) (m : ℕ) (f : Fin m → Fin N × Fin N)
    {w : Fin N} (hw : w ∈ s) : IsCladeH s m f {w} := by
  refine (isCladeH_iff).mpr ⟨0, Nat.zero_le m, w, Finset.mem_singleton_self w, ?_⟩
  exact (blockOf_zero_singleton f hw).symm

/-- ★★ **基例 `a = 1`**：`cladeCountS m s {w}` 就是 `s` 上的合并史总数 `Hnat |s|`。 -/
theorem cladeCountS_singleton (m : ℕ) (s : Finset (Fin N)) {w : Fin N} (hw : w ∈ s)
    (hs : s.card = m + 1) : cladeCountS m s {w} = Hnat (m + 1) := by
  unfold cladeCountS
  rw [Finset.filter_true_of_mem (fun f _ => isCladeH_singleton s m f hw),
    card_mhFinset m N s (by omega)]

/-- 第 `0` 层的块**只有**一个元素（`A ⊆ s`、`2 ≤ |A|` 时不可能）。 -/
theorem not_isBlockAt_zero {s A : Finset (Fin N)} {m : ℕ} {f : Fin m → Fin N × Fin N}
    (hAs : A ⊆ s) (hA2 : 2 ≤ A.card) : ¬ IsBlockAt s m f 0 A := by
  rintro ⟨w, hwA, hAw⟩
  have hcard : (blockOf s (gchain m f 0) w).card = 1 := by
    rw [blockOf_zero_singleton f (hAs hwA), Finset.card_singleton]
  rw [← hAw] at hcard
  omega

/-- `y ∉ B` 时 `(B ∪ {y}).erase y = B`。 -/
theorem erase_union_singleton_of_notMem {B : Finset (Fin N)} {y : Fin N} (h : y ∉ B) :
    (B ∪ {y}).erase y = B := by
  ext z
  rw [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨hzy, hz | hz⟩
    · exact hz
    · exact absurd hz hzy
  · intro hz
    exact ⟨fun hzy => h (hzy ▸ hz), Or.inl hz⟩

/-- `y ∈ A` 时 `A.erase y ∪ {y} = A`。 -/
theorem erase_union_singleton_of_mem {A : Finset (Fin N)} {y : Fin N} (h : y ∈ A) :
    A.erase y ∪ {y} = A := by
  ext z
  rw [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
  constructor
  · rintro (⟨-, hz⟩ | hz)
    · exact hz
    · exact hz ▸ h
  · intro hz
    by_cases hzy : z = y
    · exact Or.inr hzy
    · exact Or.inl ⟨hzy, hz⟩

/-! ## §3 头分解：按第一步的有序对拆开 `cladeCountS` -/

/-- ★★ **`headFiber` 两两不交**。 -/
theorem headFiber_disjoint {N m : ℕ} {s : Finset (Fin N)} {p q : PairIn N s} (hpq : p ≠ q) :
    Disjoint (headFiber (m := m) s p) (headFiber (m := m) s q) := by
  rw [Finset.disjoint_iff_ne]
  intro f hfp g hgq hfg
  simp only [headFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hfp hgq
  rw [← hfg] at hgq
  exact hpq (Subtype.ext (hfp.1.symm.trans hgq.1))

/-- ★★★ **`mhFinset` 按第一步的有序对**分解（`card_mhFinset` 证明里的 `hdecomp`）。 -/
theorem mhFinset_succ_eq_biUnion {N m : ℕ} (s : Finset (Fin N)) :
    mhFinset N (m + 1) s
      = (Finset.univ : Finset (PairIn N s)).biUnion (headFiber (m := m) s) := by
  ext f
  rw [mhFinset, Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · intro hf
    exact ⟨⟨f 0, (hf.2.1 0).1, (hf.2.1 0).2, (hf.2.2.1 0).2.2⟩, Finset.mem_univ _,
      by
        simp only [headFiber, Finset.mem_filter, Finset.mem_univ, true_and]
        exact isMH_tail hf.2⟩
  · rintro ⟨p, -, hp⟩
    simp only [headFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine ⟨Finset.mem_univ _, ?_⟩
    refine isMH_head (hg := ?_) (hx := ?_) (hy := ?_) (hxy := ?_)
    · rw [hp.1]; exact hp.2
    · rw [hp.1]; exact p.2.1
    · rw [hp.1]; exact p.2.2.1
    · rw [hp.1]; exact p.2.2.2

/-- ★★ **带滤子的头部纤维计数**：`Fin.tail` 给出「纤维 ∩ P」与「尾历史 ∩ Q」的双射。 -/
theorem card_headFiber_filter {N m : ℕ} (s : Finset (Fin N)) (p : PairIn N s)
    (P : (Fin (m + 1) → Fin N × Fin N) → Prop) [DecidablePred P]
    (Q : (Fin m → Fin N × Fin N) → Prop) [DecidablePred Q]
    (hPQ : ∀ f : Fin (m + 1) → Fin N × Fin N, f 0 = (p.1 : Fin N × Fin N) →
      IsMH (s.erase p.1.2) m (Fin.tail f) → (P f ↔ Q (Fin.tail f))) :
    ((headFiber (m := m) s p).filter P).card
      = ((mhFinset N m (s.erase p.1.2)).filter Q).card := by
  refine Finset.card_bij (fun f _ => Fin.tail f) ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_filter] at hf
    have hhead : f ∈ headFiber (m := m) s p := hf.1
    simp only [headFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hhead
    rw [Finset.mem_filter, mhFinset, Finset.mem_filter]
    exact ⟨⟨Finset.mem_univ _, hhead.2⟩, (hPQ f hhead.1 hhead.2).mp hf.2⟩
  · intro f₁ hf₁ f₂ hf₂ heq
    rw [Finset.mem_filter] at hf₁ hf₂
    have h1 : f₁ ∈ headFiber (m := m) s p := hf₁.1
    have h2 : f₂ ∈ headFiber (m := m) s p := hf₂.1
    simp only [headFiber, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    calc f₁ = Fin.cons (f₁ 0) (Fin.tail f₁) := (cons_tail f₁).symm
      _ = Fin.cons (p.1 : Fin N × Fin N) (Fin.tail f₁) := by rw [h1.1]
      _ = Fin.cons (p.1 : Fin N × Fin N) (Fin.tail f₂) := by rw [heq]
      _ = Fin.cons (f₂ 0) (Fin.tail f₂) := by rw [h2.1]
      _ = f₂ := cons_tail f₂
  · intro g hg
    rw [Finset.mem_filter] at hg
    obtain ⟨hg1, hgQ⟩ := hg
    rw [mhFinset, Finset.mem_filter] at hg1
    obtain ⟨-, hgMH⟩ := hg1
    refine ⟨Fin.cons (α := fun _ => Fin N × Fin N) p.1 g, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · simp only [headFiber, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨Fin.cons_zero (α := fun _ => Fin N × Fin N) p.1 g,
          by rw [Fin.tail_cons (α := fun _ => Fin N × Fin N) p.1 g]; exact hgMH⟩
      · have htail : Fin.tail (Fin.cons (α := fun _ => Fin N × Fin N) p.1 g) = g :=
          Fin.tail_cons (α := fun _ => Fin N × Fin N) p.1 g
        exact (hPQ _ (Fin.cons_zero (α := fun _ => Fin N × Fin N) p.1 g) (by
          rw [Fin.tail_cons]; exact hgMH)).mpr (by rw [htail]; exact hgQ)
    · exact Fin.tail_cons (α := fun _ => Fin N × Fin N) p.1 g

/-- ★★★ **`cladeCountS` 的头分解**：按第一步的有序对 `p` 求和。

（尾历史的载体是 `s.erase p.y`，步数 `m`；这正是 `IsMH` 的「相对任意有限集」。） -/
theorem cladeCountS_succ_eq_sum (m : ℕ) (s : Finset (Fin N)) (A : Finset (Fin N)) :
    cladeCountS (m + 1) s A
      = ∑ p : PairIn N s,
          ((headFiber (m := m) s p).filter (fun f => IsCladeH s (m + 1) f A)).card := by
  unfold cladeCountS
  rw [mhFinset_succ_eq_biUnion (m := m) s]
  have hunion : ((Finset.univ : Finset (PairIn N s)).biUnion (headFiber (m := m) s)).filter
        (fun f => IsCladeH s (m + 1) f A)
      = (Finset.univ : Finset (PairIn N s)).biUnion
          (fun p => (headFiber (m := m) s p).filter (fun f => IsCladeH s (m + 1) f A)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨p, hp⟩, hP⟩
      exact ⟨p, hp, hP⟩
    · rintro ⟨p, hp, hP⟩
      exact ⟨⟨p, hp⟩, hP⟩
  rw [hunion]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (PairIn N s)))
      (fun p => (headFiber (m := m) s p).filter (fun f => IsCladeH s (m + 1) f A)) := by
    intro p _ q _ hpq
    exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (headFiber_disjoint hpq))
  rw [Finset.card_biUnion hdisj]

/-! ## §4 尾搬运：把「`A` 是 `f` 的 clade」翻译到尾历史 -/

/-- ★★ **第 `L+1` 层的块（条件真）= 尾第 `L` 层的块 ∪ `{y}`**。

`y` 在 `L+1 ≥ 1` 层总与 `x` 同块（`gchain_y_eq_x`），故它只在「`x` 的块 = `w` 的块」
时挂到 `w` 的块上。 -/
theorem blockOf_succ_eq_of_eq {s : Finset (Fin N)} {m : ℕ} {f : Fin (m + 1) → Fin N × Fin N}
    {x y : Fin N} (h0 : f 0 = (x, y)) (hxy : x < y) (hys : y ∈ s) {w : Fin N} {L : ℕ}
    (hwy : w ≠ y) (hc : gchain m (Fin.tail f) L x = gchain m (Fin.tail f) L w) :
    blockOf s (gchain (m + 1) f (L + 1)) w
      = blockOf (s.erase y) (gchain m (Fin.tail f) L) w ∪ {y} := by
  have hxy' : x ≠ y := ne_of_lt hxy
  have hgw : gchain (m + 1) f (L + 1) w = gchain m (Fin.tail f) L w :=
    gchain_tail f h0 L w hwy
  have hyx : gchain (m + 1) f (L + 1) y = gchain (m + 1) f (L + 1) x :=
    gchain_y_eq_x f h0 (L + 1) (by omega)
  have hgx : gchain (m + 1) f (L + 1) x = gchain m (Fin.tail f) L x :=
    gchain_tail f h0 L x hxy'
  ext z
  rw [blockOf, Finset.mem_filter, Finset.mem_union, blockOf, Finset.mem_filter,
    Finset.mem_erase, Finset.mem_singleton]
  constructor
  · rintro ⟨hzs, hz⟩
    by_cases hzy : z = y
    · exact Or.inr hzy
    · refine Or.inl ⟨⟨hzy, hzs⟩, ?_⟩
      rw [← gchain_tail f h0 L z hzy, hz, hgw]
  · rintro (⟨⟨hzy, hzs⟩, hz⟩ | hzy)
    · exact ⟨hzs, by rw [gchain_tail f h0 L z hzy, hgw, hz]⟩
    · subst hzy
      exact ⟨hys, by rw [hyx, hgx, hc, ← hgw]⟩

/-- ★★ **第 `L+1` 层的块（条件假）= 尾第 `L` 层的块**。 -/
theorem blockOf_succ_eq_of_ne {s : Finset (Fin N)} {m : ℕ} {f : Fin (m + 1) → Fin N × Fin N}
    {x y : Fin N} (h0 : f 0 = (x, y)) (hxy : x < y) (hys : y ∈ s) {w : Fin N}
    {L : ℕ} (hwy : w ≠ y) (hc : ¬ gchain m (Fin.tail f) L x = gchain m (Fin.tail f) L w) :
    blockOf s (gchain (m + 1) f (L + 1)) w = blockOf (s.erase y) (gchain m (Fin.tail f) L) w := by
  have hxy' : x ≠ y := ne_of_lt hxy
  have hgw : gchain (m + 1) f (L + 1) w = gchain m (Fin.tail f) L w :=
    gchain_tail f h0 L w hwy
  have hyx : gchain (m + 1) f (L + 1) y = gchain (m + 1) f (L + 1) x :=
    gchain_y_eq_x f h0 (L + 1) (by omega)
  have hgx : gchain (m + 1) f (L + 1) x = gchain m (Fin.tail f) L x :=
    gchain_tail f h0 L x hxy'
  ext z
  rw [blockOf, Finset.mem_filter, blockOf, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hzs, hz⟩
    by_cases hzy : z = y
    · subst hzy
      exfalso
      apply hc
      rw [← hgx, ← hgw, ← hyx, hz]
    · exact ⟨⟨hzy, hzs⟩, by
        rw [gchain_tail f h0 L z hzy, hgw] at hz
        exact hz⟩
  · rintro ⟨⟨hzy, hzs⟩, hz⟩
    refine ⟨hzs, ?_⟩
    rw [gchain_tail f h0 L z hzy, hgw]
    exact hz

variable {s : Finset (Fin N)} {m : ℕ} {f : Fin (m + 1) → Fin N × Fin N}
  {x y : Fin N} {A : Finset (Fin N)}

/-- ★★★ **块搬运（`x, y ∉ A`）**：`A` 是 `f` 第 `L+1` 层的块 ⟺ `A` 是尾第 `L` 层的块。 -/
theorem isBlockAt_succ_none (h0 : f 0 = (x, y)) (hxy : x < y) (hxs : x ∈ s) (hys : y ∈ s)
    (hxA : x ∉ A) (hyA : y ∉ A) (L : ℕ) :
    IsBlockAt s (m + 1) f (L + 1) A ↔ IsBlockAt (s.erase y) m (Fin.tail f) L A := by
  constructor
  · rintro ⟨w, hwA, hAw⟩
    have hwy : w ≠ y := fun h => hyA (h ▸ hwA)
    by_cases hc : gchain m (Fin.tail f) L x = gchain m (Fin.tail f) L w
    · have hb := blockOf_succ_eq_of_eq h0 hxy hys hwy hc
      refine absurd ?_ hyA
      rw [hAw, hb]
      exact Finset.mem_union_right _ (Finset.mem_singleton_self y)
    · exact ⟨w, hwA, hAw.trans (blockOf_succ_eq_of_ne h0 hxy hys hwy hc)⟩
  · rintro ⟨w, hwA, hAw⟩
    have hwy : w ≠ y := fun h => hyA (h ▸ hwA)
    by_cases hc : gchain m (Fin.tail f) L x = gchain m (Fin.tail f) L w
    · exfalso
      refine hxA ?_
      rw [hAw]
      rw [blockOf, Finset.mem_filter]
      exact ⟨Finset.mem_erase.mpr ⟨ne_of_lt hxy, hxs⟩, hc⟩
    · exact ⟨w, hwA, hAw.trans (blockOf_succ_eq_of_ne h0 hxy hys hwy hc).symm⟩

/-- ★★★ **块搬运（`x, y ∈ A`）**：`A` 是 `f` 第 `L+1` 层的块 ⟺ `A.erase y` 是尾第 `L` 层的块。 -/
theorem isBlockAt_succ_both (h0 : f 0 = (x, y)) (hxy : x < y) (hys : y ∈ s)
    (hxA : x ∈ A) (hyA : y ∈ A) (L : ℕ) :
    IsBlockAt s (m + 1) f (L + 1) A ↔ IsBlockAt (s.erase y) m (Fin.tail f) L (A.erase y) := by
  have hxy' : x ≠ y := ne_of_lt hxy
  constructor
  · rintro ⟨w, hwA, hAw⟩
    have hrep : gchain (m + 1) f (L + 1) x = gchain (m + 1) f (L + 1) w := by
      have hmem : x ∈ blockOf s (gchain (m + 1) f (L + 1)) w := hAw ▸ hxA
      exact (Finset.mem_filter.mp hmem).2
    have hAx : A = blockOf s (gchain (m + 1) f (L + 1)) x := by
      rw [hAw]
      ext z
      rw [blockOf, blockOf, Finset.mem_filter, Finset.mem_filter, hrep]
    refine ⟨x, Finset.mem_erase.mpr ⟨hxy', hxA⟩, ?_⟩
    have hb := blockOf_succ_eq_of_eq (L := L) (w := x) h0 hxy hys hxy' rfl
    have hnotmem : y ∉ blockOf (s.erase y) (gchain m (Fin.tail f) L) x := by
      intro h
      exact Finset.notMem_erase y (s := s)
        (blockOf_subset (s.erase y) (gchain m (Fin.tail f) L) x h)
    rw [hAx, hb, erase_union_singleton_of_notMem hnotmem]
  · rintro ⟨w, hwA, hAw⟩
    rw [Finset.mem_erase] at hwA
    obtain ⟨hwy, hwA'⟩ := hwA
    refine ⟨w, hwA', ?_⟩
    have hxin : x ∈ blockOf (s.erase y) (gchain m (Fin.tail f) L) w := by
      rw [← hAw]
      exact Finset.mem_erase.mpr ⟨hxy', hxA⟩
    have hc : gchain m (Fin.tail f) L x = gchain m (Fin.tail f) L w :=
      (Finset.mem_filter.mp hxin).2
    rw [blockOf_succ_eq_of_eq (L := L) (w := w) h0 hxy hys hwy hc, ← hAw,
      erase_union_singleton_of_mem hyA]

/-- ★★★ **块搬运（混合对）**：`x`、`y` 一在内一在外 ⇒ `A` **绝不**是 `f` 第 `L+1` 层的块。 -/
theorem not_isBlockAt_succ_mixed (h0 : f 0 = (x, y)) (hxs : x ∈ s) (hys : y ∈ s)
    (hmix : (x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A)) (L : ℕ) :
    ¬ IsBlockAt s (m + 1) f (L + 1) A := by
  rintro ⟨w, hwA, hAw⟩
  have hryx : gchain (m + 1) f (L + 1) y = gchain (m + 1) f (L + 1) x :=
    gchain_y_eq_x f h0 (L + 1) (by omega)
  rcases hmix with ⟨hxA, hyA⟩ | ⟨hxA, hyA⟩
  · have h1 : gchain (m + 1) f (L + 1) x = gchain (m + 1) f (L + 1) w := by
      have hmem : x ∈ blockOf s (gchain (m + 1) f (L + 1)) w := hAw ▸ hxA
      exact (Finset.mem_filter.mp hmem).2
    refine hyA ?_
    rw [hAw, blockOf, Finset.mem_filter]
    exact ⟨hys, by rw [hryx, h1]⟩
  · have h1 : gchain (m + 1) f (L + 1) y = gchain (m + 1) f (L + 1) w := by
      have hmem : y ∈ blockOf s (gchain (m + 1) f (L + 1)) w := hAw ▸ hyA
      exact (Finset.mem_filter.mp hmem).2
    refine hxA ?_
    rw [hAw, blockOf, Finset.mem_filter]
    exact ⟨hxs, by rw [← hryx, h1]⟩

/-- ★★★ **clade 搬运（`x, y ∉ A`）**。 -/
theorem isCladeH_tail_none (h0 : f 0 = (x, y)) (hxy : x < y) (hxs : x ∈ s) (hys : y ∈ s)
    (hAs : A ⊆ s) (hxA : x ∉ A) (hyA : y ∉ A) (hA2 : 2 ≤ A.card) :
    IsCladeH s (m + 1) f A ↔ IsCladeH (s.erase y) m (Fin.tail f) A := by
  rw [isCladeH_iff, isCladeH_iff]
  constructor
  · rintro ⟨L, hL, hb⟩
    by_cases hL0 : L = 0
    · exact absurd (hL0 ▸ hb) (not_isBlockAt_zero hAs hA2)
    · have hL' : L = (L - 1) + 1 := by omega
      rw [hL'] at hb
      exact ⟨L - 1, by omega, (isBlockAt_succ_none h0 hxy hxs hys hxA hyA (L - 1)).mp hb⟩
  · rintro ⟨L, hL, hb⟩
    exact ⟨L + 1, by omega, (isBlockAt_succ_none h0 hxy hxs hys hxA hyA L).mpr hb⟩

/-- ★★★ **clade 搬运（`x, y ∈ A`）**。 -/
theorem isCladeH_tail_both (h0 : f 0 = (x, y)) (hxy : x < y) (hys : y ∈ s)
    (hAs : A ⊆ s) (hxA : x ∈ A) (hyA : y ∈ A) (hA2 : 2 ≤ A.card) :
    IsCladeH s (m + 1) f A ↔ IsCladeH (s.erase y) m (Fin.tail f) (A.erase y) := by
  rw [isCladeH_iff, isCladeH_iff]
  constructor
  · rintro ⟨L, hL, hb⟩
    by_cases hL0 : L = 0
    · exact absurd (hL0 ▸ hb) (not_isBlockAt_zero hAs hA2)
    · have hL' : L = (L - 1) + 1 := by omega
      rw [hL'] at hb
      exact ⟨L - 1, by omega, (isBlockAt_succ_both h0 hxy hys hxA hyA (L - 1)).mp hb⟩
  · rintro ⟨L, hL, hb⟩
    exact ⟨L + 1, by omega, (isBlockAt_succ_both h0 hxy hys hxA hyA L).mpr hb⟩

/-- ★★★ **clade 搬运（混合对）**：混合对下 `A` **不是** `f` 的 clade。 -/
theorem not_isCladeH_mixed (h0 : f 0 = (x, y)) (hxs : x ∈ s) (hys : y ∈ s)
    (hAs : A ⊆ s) (hA2 : 2 ≤ A.card)
    (hmix : (x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A)) : ¬ IsCladeH s (m + 1) f A := by
  rw [isCladeH_iff]
  rintro ⟨L, hL, hb⟩
  by_cases hL0 : L = 0
  · exact absurd (hL0 ▸ hb) (not_isBlockAt_zero hAs hA2)
  · have hL' : L = (L - 1) + 1 := by omega
    rw [hL'] at hb
    exact not_isBlockAt_succ_mixed h0 hxs hys hmix (L - 1) hb

end Phylo.Stat.CladeCount
