/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.RankedGeneTree

/-!
# `Phylo.Stat.CoalescentHistoryCount` —— 一般 `n` 的溯祖（合并）历史计数

文献：J. F. C. Kingman, *The Coalescent*（1982）；T. Stadler & J. H. Degnan (2012)。
本文件补上 `Phylo/Stat/RankedGeneTree.lean` 登记的缺口

```
def rankedTree_card_gap : Prop := ∀ n : ℕ, 2 ≤ n → ((mergeHistories n).card : ℝ) = H n
```

即 **`n` 个标记谱系的合并（溯祖）历史数 `= n!(n−1)!/2^{n−1} = ∏_{k=2}^{n} C(k,2)`**。

## 走了哪条路线（**逐层计数**，不是双射）

任务书建议的双射 `RankedTree n ≃ {p : Finset (Fin n) // p.card = 2} × RankedTree (n-1)`
需要把「第 0 步之后剩下的 `n-1` 个块」重标号成 `Fin (n-1)`（序同构），代价高且脆。
本文件改走**逐层计数**：把合并史的定义**相对一个有限集 `s : Finset (Fin N)`** 推广
（`IsMH s m`：`m` 步把 `s` 合并成一块；`s.card = m + 1` 是「合法规模」），于是

* 「按第一步的有序对 `p`（`p.1 < p.2`，都在 `s` 里）分块」是**字面意义**的分解
  （`headFiber` / `hdecomp`），**不需要任何重标号**；
* 每个纤维与 `s.erase p.2`（元素个数 `s.card - 1`、**仍在同一个 `Fin N` 里**）上的
  历史集合双射（`card_headFiber`，映射就是 `Fin.tail`）；
* 对 `s.card` 作归纳：`|MH s| = C(|s|,2) · |MH (s.erase …)|`。

因为归纳假设是对**所有**同基数的 `s` 陈述的，`s.erase y` 直接命中归纳假设，
**全程没有出现任何「元素重标号」**。有限集层面用 `Finset.card_biUnion` 做不相交并，
只在「头部对子计数」处用一次 `Finset.card_powersetCard` 得到 `C(|s|,2)`。

## 内容

* `gchain`（`RankedGeneTree.chainMap` 的「把 `n−1` 提成参数」版本，`rfl` 即相等）
  连同 `gchain_zero` / `gchain_succ` / `gchain_succ_apply`（**逐点**形式，
  证明项规范化，避免 `dite` 的证明项在重写时对不上）；
* `IsMH` / `mhFinset` / `PairIn` / `headFiber`（相对任意有限集的合并史）；
* 折叠的基本性质：`gchain_mem`、`gchain_tail`、`gchain_le`、`gchain_y_le`、`gchain_y_eq_x`；
* 头尾分解：`isMH_tail`、`isMH_head`、`cons_tail`；
* 计数：`card_headFiber`、`card_pairIn`、`card_mhFinset`（归纳主引理）；
* ★★★ 主目标：`card_mergeHistories_eq_H`（一般 `n`）；
* 降级/附赠：`card_mergeHistories_eq_Hnat`（`ℕ` 版）、`card_mergeHistories_succ`（递推）、
  `card_mergeHistories_five`（`n = 5` 的 `180`）、`card_mergeHistories_le_H` / `_ge_H`（`≤` / `≥` 版）、
  `rankedTree_card_gap_proved`（原缺口命题的一般 `n` 形式）。

## 实现纪律

全部判定由**内核**归约（`decide` / 归纳），**未用** `native_decide`
（故没有引入 `Lean.ofReduceBool`）。全文零 `sorry`、零 `axiom`、零新增 Mathlib import。
-/

namespace Phylo.Stat.CoalescentHistoryCount

/-! ## §1 「块代表映射」折叠（`RankedGeneTree.chainMap` 的参数化版本） -/

/-- `f` 的前 `L` 步作用在恒等映射上得到的**块代表映射**。

与 `RankedGeneTree.chainMap` 是**同一个项**：`chainMap` 里写死的 `n - 1` 在这里是参数 `m`，
故 `chainMap n f L = gchain (n - 1) f L` 由 `rfl` 成立（见 `isMH_univ_iff` 的证明）。 -/
def gchain {N : ℕ} (m : ℕ) (f : Fin m → Fin N × Fin N) (L : ℕ) : Fin N → Fin N :=
  ((List.range L).filterMap (fun k => if h : k < m then some (f ⟨k, h⟩) else none)).foldl
    (fun r p => RankedGeneTree.stepMap r p.1 p.2) id

/-- 零步是恒等。 -/
theorem gchain_zero {N m : ℕ} (f : Fin m → Fin N × Fin N) : gchain m f 0 = id := rfl

/-- **递推一步**：`L < m` 时把 `f L` 作用上去，`L ≥ m` 时饱和。 -/
theorem gchain_succ {N m : ℕ} (f : Fin m → Fin N × Fin N) (L : ℕ) :
    gchain m f (L + 1) =
      (if h : L < m then
        RankedGeneTree.stepMap (gchain m f L) (f ⟨L, h⟩).1 (f ⟨L, h⟩).2
      else gchain m f L) := by
  have hfm : (List.filterMap (fun k => if h : k < m then some (f ⟨k, h⟩) else none) [L])
      = (if h : L < m then [f ⟨L, h⟩] else []) := by
    by_cases h : L < m
    · have hsome : (fun k => if h : k < m then some (f ⟨k, h⟩) else none) L
          = some (f ⟨L, h⟩) := dite_eq_left h
      rw [List.filterMap_cons_some (f := fun k => if h : k < m then some (f ⟨k, h⟩) else none)
        (l := []) hsome, dite_eq_left h]
      rfl
    · have hnone : (fun k => if h : k < m then some (f ⟨k, h⟩) else none) L = none :=
        dite_eq_right h
      rw [List.filterMap_cons_none (f := fun k => if h : k < m then some (f ⟨k, h⟩) else none)
        (l := []) hnone, dite_eq_right h]
      rfl
  unfold gchain
  rw [List.range_succ, List.filterMap_append, List.foldl_append, hfm]
  by_cases h : L < m
  · simp only [h, ↓reduceDIte, List.foldl_cons, List.foldl_nil]
  · simp only [h, ↓reduceDIte, List.foldl_nil]

/-- **递推一步（逐点、证明项规范化）**：`L < m` 时的值。
这里 `L < m` 的证明由调用方给出，故 `f ⟨L, _⟩` 的证明项在整个证明里是同一个。 -/
theorem gchain_succ_apply {N m : ℕ} (f : Fin m → Fin N × Fin N) (L : ℕ) (h : L < m)
    (w : Fin N) :
    gchain m f (L + 1) w
      = (if gchain m f L w = (f ⟨L, h⟩).2 then (f ⟨L, h⟩).1 else gchain m f L w) := by
  rw [gchain_succ]
  simp only [h, ↓reduceDIte, RankedGeneTree.stepMap]

/-- **递推一步（逐点）**：`L ≥ m` 时饱和。 -/
theorem gchain_succ_apply_not {N m : ℕ} (f : Fin m → Fin N × Fin N) (L : ℕ) (h : ¬ L < m)
    (w : Fin N) : gchain m f (L + 1) w = gchain m f L w := by
  rw [gchain_succ]
  simp only [h, ↓reduceDIte]

/-! ## §2 相对任意有限集的合并史 -/

/-- **相对 `s` 的合并史**（`s` 是该阶段**当前块代表**的集合）。

* 第一条让「每步的两个代表」落在 `s` 里；
* 第二条是 `RankedGeneTree.IsStep`：`x`、`y` 各自是所在块的（最小）代表，且 `x < y`；
* 第三条要求 `m` 步之后 `s` 整体并成一块。

`s.card = m + 1` 是「合法规模」（`m` 步把 `m+1` 个块并成 1 个块）。 -/
def IsMH {N : ℕ} (s : Finset (Fin N)) (m : ℕ) (f : Fin m → Fin N × Fin N) : Prop :=
  (∀ k : Fin m, (f k).1 ∈ s ∧ (f k).2 ∈ s) ∧
    (∀ k : Fin m, RankedGeneTree.IsStep (gchain m f (k : ℕ)) (f k).1 (f k).2) ∧
      (∀ w ∈ s, ∀ w' ∈ s, gchain m f m w = gchain m f m w')

instance {N : ℕ} (s : Finset (Fin N)) (m : ℕ) : DecidablePred (IsMH s m) := fun f => by
  unfold IsMH
  infer_instance

/-- `s` 上 `m` 步合并史的**有限集**（计数主入口）。 -/
def mhFinset (N m : ℕ) (s : Finset (Fin N)) : Finset (Fin m → Fin N × Fin N) :=
  (Finset.univ : Finset (Fin m → Fin N × Fin N)).filter (IsMH s m ·)

/-- `s` 上的一个合法「第一步」：`s` 里的**有序**块代表对 `x < y`。 -/
abbrev PairIn (N : ℕ) (s : Finset (Fin N)) : Type :=
  {p : Fin N × Fin N // p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2}

/-- 第一步取定 `p` 之后，剩下的 `m` 步（把 `m+1` 步的历史「砍掉头」）。 -/
def headFiber {N m : ℕ} (s : Finset (Fin N)) (p : PairIn N s) :
    Finset (Fin (m + 1) → Fin N × Fin N) :=
  Finset.univ.filter (fun f => f 0 = p.1 ∧ IsMH (s.erase p.1.2) m (Fin.tail f))

/-! ## §3 折叠的基本性质 -/

/-- 折叠**保集合**：每步的两个代表都在 `t` 里 ⟹ 折叠值仍在 `t` 里。 -/
theorem gchain_mem {N m : ℕ} (f : Fin m → Fin N × Fin N) {t : Finset (Fin N)}
    (ht : ∀ k : Fin m, (f k).1 ∈ t ∧ (f k).2 ∈ t) :
    ∀ (L : ℕ) (w : Fin N), w ∈ t → gchain m f L w ∈ t := by
  intro L
  induction L with
  | zero =>
    intro w hw
    rw [gchain_zero]
    exact hw
  | succ L ih =>
    intro w hw
    by_cases h : L < m
    · rw [gchain_succ_apply f L h w]
      by_cases hc : gchain m f L w = (f ⟨L, h⟩).2
      · simp only [hc, ↓reduceIte]
        exact (ht ⟨L, h⟩).1
      · simp only [hc, ↓reduceIte]
        exact ih w hw
    · rw [gchain_succ_apply_not f L h w]
      exact ih w hw

/-- **头尾兼容**：只要 `w` 不是第一步被并掉的那个代表 `y`，
`L+1` 步之后的值等于「砍掉第一步」之后 `L` 步的值。 -/
theorem gchain_tail {N m : ℕ} (f : Fin (m + 1) → Fin N × Fin N) {x y : Fin N}
    (h0 : f 0 = (x, y)) (L : ℕ) (w : Fin N) (hw : w ≠ y) :
    gchain (m + 1) f (L + 1) w = gchain m (Fin.tail f) L w := by
  have h2 : (f (0 : Fin (m + 1))).2 = y := by rw [h0]
  have hz : (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) = 0 := Fin.ext rfl
  have htail : ∀ i : Fin m, Fin.tail f i = f i.succ := fun _ => rfl
  refine Nat.le_induction (m := 0) (P := fun L _ =>
    gchain (m + 1) f (L + 1) w = gchain m (Fin.tail f) L w) ?_ ?_ L (Nat.zero_le L)
  · rw [gchain_succ_apply f 0 (Nat.zero_lt_succ m) w]
    simp only [gchain_zero, hz, h2, id_eq, hw, ↓reduceIte]
  · intro n _ ih
    by_cases h : n < m
    · have hn : n + 1 < m + 1 := by omega
      rw [gchain_succ_apply f (n + 1) hn w, ih,
        gchain_succ_apply (Fin.tail f) n h w]
      rw [show (⟨n + 1, hn⟩ : Fin (m + 1)) = (⟨n, h⟩ : Fin m).succ from Fin.ext rfl,
        htail ⟨n, h⟩]
    · have hn : ¬ (n + 1 < m + 1) := by omega
      rw [gchain_succ_apply_not f (n + 1) hn w, ih,
        gchain_succ_apply_not (Fin.tail f) n (by omega : ¬ n < m) w]

/-- 折叠**不会把代表变大**：`L` 步之后的值 `≤` 原值。 -/
theorem gchain_le {N m : ℕ} (f : Fin m → Fin N × Fin N)
    (hstep : ∀ k : Fin m, RankedGeneTree.IsStep (gchain m f (k : ℕ)) (f k).1 (f k).2) :
    ∀ (L : ℕ) (w : Fin N), gchain m f L w ≤ w := by
  intro L
  induction L with
  | zero =>
    intro w
    rw [gchain_zero]
    exact le_rfl
  | succ L ih =>
    intro w
    by_cases h : L < m
    · rw [gchain_succ_apply f L h w]
      by_cases hc : gchain m f L w = (f ⟨L, h⟩).2
      · simp only [hc, ↓reduceIte]
        exact le_trans (le_of_lt (by rw [hc]; exact (hstep ⟨L, h⟩).2.2)) (ih w)
      · simp only [hc, ↓reduceIte]
        exact ih w
    · rw [gchain_succ_apply_not f L h w]
      exact ih w

/-- 第一步把 `y` 并进 `x`（`x < y`）之后，**含 `y` 的块代表永远 `≤ x`**。 -/
theorem gchain_y_le {N m : ℕ} (f : Fin (m + 1) → Fin N × Fin N) {x y : Fin N}
    (h0 : f 0 = (x, y))
    (hstep : ∀ k : Fin (m + 1),
      RankedGeneTree.IsStep (gchain (m + 1) f (k : ℕ)) (f k).1 (f k).2) :
    ∀ L : ℕ, 1 ≤ L → gchain (m + 1) f L y ≤ x := by
  have h1 : (f (0 : Fin (m + 1))).1 = x := by rw [h0]
  have h2 : (f (0 : Fin (m + 1))).2 = y := by rw [h0]
  have hz : (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) = 0 := Fin.ext rfl
  intro L hL
  refine Nat.le_induction (m := 1) (P := fun L _ => gchain (m + 1) f L y ≤ x) ?_ ?_ L hL
  · show gchain (m + 1) f (0 + 1) y ≤ x
    rw [gchain_succ_apply f 0 (Nat.zero_lt_succ m) y]
    simp only [gchain_zero, hz, h1, h2, id_eq, ↓reduceIte, le_refl]
  · intro n _ ih
    by_cases h : n < m + 1
    · rw [gchain_succ_apply f n h y]
      by_cases hc : gchain (m + 1) f n y = (f ⟨n, h⟩).2
      · simp only [hc, ↓reduceIte]
        exact le_trans (le_of_lt (by rw [hc]; exact (hstep ⟨n, h⟩).2.2)) ih
      · simp only [hc, ↓reduceIte]
        exact ih
    · rw [gchain_succ_apply_not f n h y]
      exact ih

/-- 第一步把 `y` 并进 `x` 之后，**`y` 与 `x` 所在的块代表恒相等**。 -/
theorem gchain_y_eq_x {N m : ℕ} (f : Fin (m + 1) → Fin N × Fin N) {x y : Fin N}
    (h0 : f 0 = (x, y)) :
    ∀ L : ℕ, 1 ≤ L → gchain (m + 1) f L y = gchain (m + 1) f L x := by
  have h1 : (f (0 : Fin (m + 1))).1 = x := by rw [h0]
  have h2 : (f (0 : Fin (m + 1))).2 = y := by rw [h0]
  have hz : (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) = 0 := Fin.ext rfl
  intro L hL
  refine Nat.le_induction (m := 1) (P := fun L _ =>
    gchain (m + 1) f L y = gchain (m + 1) f L x) ?_ ?_ L hL
  · show gchain (m + 1) f (0 + 1) y = gchain (m + 1) f (0 + 1) x
    rw [gchain_succ_apply f 0 (Nat.zero_lt_succ m) y,
      gchain_succ_apply f 0 (Nat.zero_lt_succ m) x]
    simp only [gchain_zero, hz, h1, h2, id_eq]
    by_cases hxy : x = y <;> simp only [hxy, ↓reduceIte]
  · intro n _ ih
    by_cases h : n < m + 1
    · rw [gchain_succ_apply f n h y, gchain_succ_apply f n h x, ih]
    · rw [gchain_succ_apply_not f n h y, gchain_succ_apply_not f n h x, ih]

/-! ## §4 头尾分解 -/

/-- `Fin.tail` 就是 `i ↦ f i.succ`。 -/
theorem tail_apply {N m : ℕ} (f : Fin (m + 1) → Fin N × Fin N) (i : Fin m) :
    Fin.tail f i = f i.succ := rfl

/-- `Fin.cons` 是 `Fin.tail` 的左逆（`Fin.cons (f 0) (Fin.tail f) = f`）。 -/
theorem cons_tail {N m : ℕ} (f : Fin (m + 1) → Fin N × Fin N) :
    Fin.cons (f 0) (Fin.tail f) = f := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Fin.cons_zero]
  · rw [Fin.cons_succ]
    rfl

/-- **头尾分解（正向）**：`s` 上 `m+1` 步的合并史，砍掉第一步之后是
`s \ {(f 0).2}` 上 `m` 步的合并史。 -/
theorem isMH_tail {N m : ℕ} {s : Finset (Fin N)} {f : Fin (m + 1) → Fin N × Fin N}
    (hf : IsMH s (m + 1) f) : IsMH (s.erase (f 0).2) m (Fin.tail f) := by
  obtain ⟨hmem, hstep, hconst⟩ := hf
  have hxlt : (f 0).1 < (f 0).2 := (hstep 0).2.2
  have hyx : ∀ L : ℕ, 1 ≤ L → gchain (m + 1) f L (f 0).2 ≤ (f 0).1 :=
    fun L hL => gchain_y_le f rfl hstep L hL
  have hne1 : ∀ k : Fin m, (f k.succ).1 ≠ (f 0).2 := by
    intro k heq
    have hle := hyx k.succ (Nat.succ_le_succ (Nat.zero_le k))
    have heq' : gchain (m + 1) f ((k.succ : Fin (m + 1)) : ℕ) (f 0).2 = (f 0).2 := by
      rw [← heq]
      exact (hstep k.succ).1
    rw [heq'] at hle
    exact absurd (lt_of_lt_of_le hxlt hle) (lt_irrefl _)
  have hne2 : ∀ k : Fin m, (f k.succ).2 ≠ (f 0).2 := by
    intro k heq
    have hle := hyx k.succ (Nat.succ_le_succ (Nat.zero_le k))
    have heq' : gchain (m + 1) f ((k.succ : Fin (m + 1)) : ℕ) (f 0).2 = (f 0).2 := by
      rw [← heq]
      exact (hstep k.succ).2.1
    rw [heq'] at hle
    exact absurd (lt_of_lt_of_le hxlt hle) (lt_irrefl _)
  refine ⟨?_, ?_, ?_⟩
  · intro k
    rw [show (Fin.tail f k).1 = (f k.succ).1 from rfl,
      show (Fin.tail f k).2 = (f k.succ).2 from rfl, Finset.mem_erase, Finset.mem_erase]
    exact ⟨⟨hne1 k, (hmem k.succ).1⟩, ⟨hne2 k, (hmem k.succ).2⟩⟩
  · intro k
    have hk1 : (Fin.tail f k).1 ≠ (f 0).2 := hne1 k
    have hk2 : (Fin.tail f k).2 ≠ (f 0).2 := hne2 k
    have e1 : gchain m (Fin.tail f) (k : ℕ) (Fin.tail f k).1 = (Fin.tail f k).1 :=
      (gchain_tail f rfl (k : ℕ) (Fin.tail f k).1 hk1).symm.trans (hstep k.succ).1
    have e2 : gchain m (Fin.tail f) (k : ℕ) (Fin.tail f k).2 = (Fin.tail f k).2 :=
      (gchain_tail f rfl (k : ℕ) (Fin.tail f k).2 hk2).symm.trans (hstep k.succ).2.1
    exact ⟨e1, e2, (hstep k.succ).2.2⟩
  · intro w hw w' hw'
    rw [Finset.mem_erase] at hw hw'
    rw [← gchain_tail f rfl m w hw.1, ← gchain_tail f rfl m w' hw'.1]
    exact hconst w hw.2 w' hw'.2

/-- **头尾分解（逆向）**：`s \ {y}` 上 `m` 步的合并史，前面接上「把 `y` 并进 `x`」这一步，
就得到 `s` 上 `m+1` 步的合并史。 -/
theorem isMH_head {N m : ℕ} {s : Finset (Fin N)} {f : Fin (m + 1) → Fin N × Fin N}
    (hg : IsMH (s.erase (f 0).2) m (Fin.tail f))
    (hx : (f 0).1 ∈ s) (hy : (f 0).2 ∈ s) (hxy : (f 0).1 < (f 0).2) :
    IsMH s (m + 1) f := by
  obtain ⟨gmem, gstep, gconst⟩ := hg
  have h0 : f 0 = ((f 0).1, (f 0).2) := rfl
  have hmemS : ∀ k : Fin m, (f k.succ).1 ∈ s ∧ (f k.succ).2 ∈ s := by
    intro k
    exact ⟨(Finset.mem_erase.mp (gmem k).1).2, (Finset.mem_erase.mp (gmem k).2).2⟩
  have hne : ∀ k : Fin m,
      (Fin.tail f k).1 ≠ (f 0).2 ∧ (Fin.tail f k).2 ≠ (f 0).2 := by
    intro k
    exact ⟨(Finset.mem_erase.mp (gmem k).1).1, (Finset.mem_erase.mp (gmem k).2).1⟩
  refine ⟨?_, ?_, ?_⟩
  · intro k
    induction k using Fin.cases with
    | zero => exact ⟨hx, hy⟩
    | succ j => exact hmemS j
  · intro k
    induction k using Fin.cases with
    | zero =>
      show RankedGeneTree.IsStep (gchain (m + 1) f 0) (f 0).1 (f 0).2
      rw [gchain_zero]
      exact ⟨rfl, rfl, hxy⟩
    | succ j =>
      have hj := hne j
      exact ⟨(gchain_tail f h0 (j : ℕ) (Fin.tail f j).1 hj.1).trans (gstep j).1,
        (gchain_tail f h0 (j : ℕ) (Fin.tail f j).2 hj.2).trans (gstep j).2.1,
        (gstep j).2.2⟩
  · intro w hw w' hw'
    have hkey : ∀ z ∈ s, z ≠ (f 0).2 →
        gchain (m + 1) f (m + 1) z = gchain m (Fin.tail f) m z :=
      fun z _ hz => gchain_tail f h0 m z hz
    have hxne : (f 0).1 ≠ (f 0).2 := ne_of_lt hxy
    have hxer : (f 0).1 ∈ s.erase (f 0).2 := by
      rw [Finset.mem_erase]
      exact ⟨hxne, hx⟩
    by_cases hwy : w = (f 0).2
    · rw [hwy]
      by_cases hwy' : w' = (f 0).2
      · rw [hwy']
      · have hw'er : w' ∈ s.erase (f 0).2 := by
          rw [Finset.mem_erase]
          exact ⟨hwy', hw'⟩
        rw [gchain_y_eq_x f h0 (m + 1) (by omega), hkey (f 0).1 hx hxne,
          hkey w' hw' hwy', gconst (f 0).1 hxer w' hw'er]
    · by_cases hwy' : w' = (f 0).2
      · have hwer : w ∈ s.erase (f 0).2 := by
          rw [Finset.mem_erase]
          exact ⟨hwy, hw⟩
        rw [hwy', gchain_y_eq_x f h0 (m + 1) (by omega), hkey (f 0).1 hx hxne,
          hkey w hw hwy, gconst w hwer (f 0).1 hxer]
      · have hwer : w ∈ s.erase (f 0).2 := by
          rw [Finset.mem_erase]
          exact ⟨hwy, hw⟩
        have hw'er : w' ∈ s.erase (f 0).2 := by
          rw [Finset.mem_erase]
          exact ⟨hwy', hw'⟩
        rw [hkey w hw hwy, hkey w' hw' hwy', gconst w hwer w' hw'er]

/-! ## §5 计数 -/

/-- 头部纤维（第一步取定 `p`）与「砍掉第一步之后」的历史集合之间有双射 `g ↦ Fin.tail g`。 -/
theorem card_headFiber {N m : ℕ} (s : Finset (Fin N)) (p : PairIn N s) :
    (headFiber (m := m) s p).card = (mhFinset N m (s.erase p.1.2)).card := by
  refine Finset.card_bij (fun g _ => Fin.tail g) ?_ ?_ ?_
  · intro g hg
    simp only [headFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    rw [mhFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hg.2⟩
  · intro g₁ hg₁ g₂ hg₂ heq
    simp only [headFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hg₁ hg₂
    calc g₁ = Fin.cons (g₁ 0) (Fin.tail g₁) := (cons_tail g₁).symm
      _ = Fin.cons p.1 (Fin.tail g₁) := by rw [hg₁.1]
      _ = Fin.cons p.1 (Fin.tail g₂) := by rw [heq]
      _ = Fin.cons (g₂ 0) (Fin.tail g₂) := by rw [hg₂.1]
      _ = g₂ := cons_tail g₂
  · intro h hh
    rw [mhFinset, Finset.mem_filter] at hh
    refine ⟨Fin.cons (α := fun _ => Fin N × Fin N) p.1 h, ?_, ?_⟩
    · simp only [headFiber, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Fin.cons_zero (α := fun _ => Fin N × Fin N) p.1 h,
        by rw [Fin.tail_cons (α := fun _ => Fin N × Fin N) p.1 h]; exact hh.2⟩
    · exact Fin.tail_cons (α := fun _ => Fin N × Fin N) p.1 h

/-- `s` 里的**有序**对 `x < y` 恰有 `C(|s|,2)` 个。 -/
theorem card_pairIn {N : ℕ} (s : Finset (Fin N)) :
    Fintype.card (PairIn N s) = s.card.choose 2 := by
  rw [show Fintype.card (PairIn N s)
      = (Finset.univ.filter (fun p : Fin N × Fin N => p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2)).card
        from Fintype.card_subtype _,
    ← Finset.card_powersetCard 2 s]
  refine Finset.card_bij (fun p _ => ({p.1, p.2} : Finset (Fin N))) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_powersetCard]
    refine ⟨?_, Finset.card_pair hp.2.2.2.ne⟩
    intro a ha
    rw [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hp.2.1
    · exact hp.2.2.1
  · intro p hp q hq heq
    rw [Finset.mem_filter] at hp hq
    have h1 : p.1 < p.2 := hp.2.2.2
    have h2 : q.1 < q.2 := hq.2.2.2
    have e1 : p.1 = q.1 ∨ p.1 = q.2 := by
      have hmem : p.1 ∈ ({q.1, q.2} : Finset (Fin N)) := by rw [← heq]; simp
      simpa using hmem
    have e2 : p.2 = q.1 ∨ p.2 = q.2 := by
      have hmem : p.2 ∈ ({q.1, q.2} : Finset (Fin N)) := by rw [← heq]; simp
      simpa using hmem
    rcases e1 with h | h <;> rcases e2 with h' | h'
    · exact absurd (h.trans h'.symm) (ne_of_lt h1)
    · exact Prod.ext h h'
    · refine absurd (?_ : q.2 < q.1) (not_lt.mpr h2.le)
      rw [← h, ← h']
      exact h1
    · exact absurd (h.trans h'.symm) (ne_of_lt h1)
  · intro t ht
    rw [Finset.mem_powersetCard] at ht
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp ht.2
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · refine ⟨(a, b), ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ht.1 (by simp), ht.1 (by simp), hlt⟩
    · refine ⟨(b, a), ?_, by rw [Finset.pair_comm]⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ht.1 (by simp), ht.1 (by simp), hgt⟩

/-! ### §5.1 `ℕ` 版的 `H`（与 `RankedGeneTree.H` 相等的计数） -/

/-- `H` 的 `ℕ` 版本：`Hnat ℓ = ∏_{k=2}^{ℓ} C(k,2)`。 -/
def Hnat : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (n + 2) => Hnat (n + 1) * (n + 2).choose 2

/-- `Hnat` 就是乘积 `∏_{k=2}^{ℓ} C(k,2)`（结构与 `RankedGeneTree.H_eq_prod` 相同）。 -/
theorem Hnat_eq_prod : ∀ ℓ : ℕ,
    Hnat ℓ = ∏ k ∈ Finset.range (ℓ - 1), (k + 2).choose 2
  | 0 => by simp [Hnat]
  | 1 => by simp [Hnat]
  | (n + 2) => by
    have ih := Hnat_eq_prod (n + 1)
    rw [show Hnat (n + 2) = Hnat (n + 1) * (n + 2).choose 2 from rfl, ih,
      show n + 2 - 1 = n + 1 from rfl, show n + 1 - 1 = n from rfl,
      Finset.prod_range_succ]

/-- `C(k,2)`（`ℕ`）与 `Coalescent.kingmanRate k`（`ℝ`）是同一个数。 -/
theorem cast_choose_two (k : ℕ) :
    ((k.choose 2 : ℕ) : ℝ) = Coalescent.kingmanRate k := by
  have hdvd : 2 ∣ k * (k - 1) := even_iff_two_dvd.mp (Nat.even_mul_pred_self k)
  rw [Nat.choose_two_right, Coalescent.kingmanRate,
    Nat.cast_div hdvd (by norm_num : (((2 : ℕ) : ℝ)) ≠ 0)]
  rcases k with _ | k
  · norm_num
  · rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k + 1)]
    push_cast
    ring

/-- ★★ `Hnat` 与 `RankedGeneTree.H` 一致。 -/
theorem cast_Hnat (m : ℕ) : (Hnat m : ℝ) = RankedGeneTree.H m := by
  rw [Hnat_eq_prod, RankedGeneTree.H_eq_prod]
  push_cast
  exact Finset.prod_congr rfl (fun k _ => cast_choose_two (k + 2))

/-- `Hnat` 的递推一步（`n ≥ 1`）。 -/
theorem Hnat_succ (n : ℕ) (hn : 1 ≤ n) : Hnat (n + 1) = Hnat n * (n + 1).choose 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rfl

/-! ### §5.2 归纳主引理 -/

set_option maxHeartbeats 1000000 in
/-- ★★★ **归纳主引理**：`s.card = m+1` 时 `s` 上恰有 `Hnat (m+1)` 个 `m` 步合并史。 -/
theorem card_mhFinset (m : ℕ) :
    ∀ (N : ℕ) (s : Finset (Fin N)), s.card = m + 1 → (mhFinset N m s).card = Hnat (m + 1) := by
  induction m with
  | zero =>
    intro N s hs
    have hall : ∀ f : Fin 0 → Fin N × Fin N, IsMH s 0 f := by
      intro f
      refine ⟨?_, ?_, ?_⟩
      · intro k; exact Fin.elim0 k
      · intro k; exact Fin.elim0 k
      · intro w hw w' hw'
        simp only [gchain_zero]
        exact Finset.card_le_one.mp (by omega) w hw w' hw'
    have h1 : mhFinset N 0 s = Finset.univ := Finset.filter_true_of_mem (fun f _ => hall f)
    rw [h1, Finset.card_univ]
    have h2 : Fintype.card (Fin 0 → Fin N × Fin N) = 1 := by
      rw [Fintype.card_fun, Fintype.card_fin, pow_zero]
    rw [h2]
    rfl
  | succ m ih =>
    intro N s hs
    have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (PairIn N s)))
        (headFiber (m := m) s) := by
      intro p _ q _ hpq
      show Disjoint (headFiber s p) (headFiber s q)
      rw [Finset.disjoint_iff_ne]
      intro f hfp g hgq hfg
      simp only [headFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hfp hgq
      rw [← hfg] at hgq
      exact hpq (Subtype.ext (hfp.1.symm.trans hgq.1))
    have hdecomp : mhFinset N (m + 1) s
        = (Finset.univ : Finset (PairIn N s)).biUnion (headFiber s) := by
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
    rw [hdecomp, Finset.card_biUnion hdisj]
    have hsum : (∑ p ∈ (Finset.univ : Finset (PairIn N s)), (headFiber (m := m) s p).card)
        = ∑ _p : PairIn N s, Hnat (m + 1) := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [card_headFiber s p,
        ih N (s.erase p.1.2) (by rw [Finset.card_erase_of_mem p.2.2.1]; omega)]
    rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_pairIn, hs,
      Nat.mul_comm]
    rfl

/-! ### §5.3 与 `RankedGeneTree` 的编码接上，并给出主目标 -/

/-- `univ : Finset (Fin n)` 上的 `n-1` 步合并史**就是** `RankedGeneTree` 的合并史。 -/
theorem isMH_univ_iff (n : ℕ) (f : Fin (n - 1) → Fin n × Fin n) :
    IsMH (Finset.univ : Finset (Fin n)) (n - 1) f ↔ RankedGeneTree.IsMergeHistory n f := by
  unfold IsMH RankedGeneTree.IsMergeHistory gchain RankedGeneTree.chainMap
  constructor
  · rintro ⟨-, hs, hc⟩
    exact ⟨hs, fun w w' => hc w (Finset.mem_univ w) w' (Finset.mem_univ w')⟩
  · rintro ⟨hs, hc⟩
    exact ⟨fun k => ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hs, fun w _ w' _ => hc w w'⟩

/-- ★★★ **`ℕ` 版的计数**：`n ≥ 1` 时 `|RankedTree n| = Hnat n`。 -/
theorem card_mergeHistories_eq_Hnat (n : ℕ) (hn : 1 ≤ n) :
    (RankedGeneTree.mergeHistories n).card = Hnat n := by
  have hset : RankedGeneTree.mergeHistories n
      = mhFinset n (n - 1) (Finset.univ : Finset (Fin n)) := by
    ext f
    rw [RankedGeneTree.mergeHistories, mhFinset, Finset.mem_filter, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1, (isMH_univ_iff n f).mpr h.2⟩,
      fun h => ⟨h.1, (isMH_univ_iff n f).mp h.2⟩⟩
  rw [hset,
    card_mhFinset (n - 1) n (Finset.univ : Finset (Fin n)) (by
      rw [Finset.card_univ, Fintype.card_fin]
      omega),
    show n - 1 + 1 = n from by omega]

/-- ★★★ **主目标**：一般 `n`，`n` 个标记谱系的合并历史数 `= H n = ∏_{k=2}^{n} C(k,2)`。 -/
theorem card_mergeHistories_eq_H (n : ℕ) (hn : 1 ≤ n) :
    ((RankedGeneTree.mergeHistories n).card : ℝ) = RankedGeneTree.H n := by
  rw [card_mergeHistories_eq_Hnat n hn, cast_Hnat]

/-- ★★★ `RankedGeneTree.rankedTree_card_gap` 所声称的命题（一般 `n`，`2 ≤ n`）。 -/
theorem rankedTree_card_gap_proved : ∀ n : ℕ, 2 ≤ n →
    ((RankedGeneTree.mergeHistories n).card : ℝ) = RankedGeneTree.H n :=
  fun n hn => card_mergeHistories_eq_H n (by omega)

/-- ★★ **递推形式**（主目标的一步）：`|RankedTree (n+1)| = C(n+1,2) · |RankedTree n|`（`n ≥ 1`）。 -/
theorem card_mergeHistories_succ (n : ℕ) (hn : 1 ≤ n) :
    (RankedGeneTree.mergeHistories (n + 1)).card
      = (n + 1).choose 2 * (RankedGeneTree.mergeHistories n).card := by
  rw [card_mergeHistories_eq_Hnat (n + 1) (by omega), Hnat_succ n hn,
    card_mergeHistories_eq_Hnat n hn, Nat.mul_comm]

/-- ★★ `n = 5`：`180`（`= H_5 = 5!·4!/2^4`）。 -/
theorem card_mergeHistories_five : (RankedGeneTree.mergeHistories 5).card = 180 := by
  rw [card_mergeHistories_eq_Hnat 5 (by norm_num)]
  decide

/-- ★★★ `n = 5` 与论文式 (2) 的闭形式接上：`|RankedTree 5| = H 5 = 180`。 -/
theorem card_mergeHistories_five_eq_H :
    ((RankedGeneTree.mergeHistories 5).card : ℝ) = RankedGeneTree.H 5 :=
  card_mergeHistories_eq_H 5 (by norm_num)

/-- ★ `≤` 版（主目标的弱形式）。 -/
theorem card_mergeHistories_le_H (n : ℕ) (hn : 1 ≤ n) :
    ((RankedGeneTree.mergeHistories n).card : ℝ) ≤ RankedGeneTree.H n :=
  (card_mergeHistories_eq_H n hn).le

/-- ★ `≥` 版（主目标的弱形式）。 -/
theorem card_mergeHistories_ge_H (n : ℕ) (hn : 1 ≤ n) :
    RankedGeneTree.H n ≤ ((RankedGeneTree.mergeHistories n).card : ℝ) :=
  (card_mergeHistories_eq_H n hn).ge

/-! ## §6 本文件**没有**留下的缺口

`RankedGeneTree.rankedTree_card_gap`（一般 `n` 的合并史计数）已由
`card_mergeHistories_eq_H` / `rankedTree_card_gap_proved` **证出**，本文件不新开缺口。

`RankedGeneTree.lean` 里**其余**的缺口（`rankedFiberCount_gap`（Remark 6 一般 `n`）、
`sd2012_eq4_uniform_rates_gap`、`ranked4_probability_gap`）**不在本次任务范围内**，
本文件**没有**触碰、也**没有**声称。 -/

end Phylo.Stat.CoalescentHistoryCount
