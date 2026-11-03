/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MSC
import Phylo.Stat.Parsimony

/-!
# `Phylo.Stat.MassMajorizes` —— **MASS_MAJORIZES**：锚间距侧的 identifiability（W43 · S1）

## 这个文件回答什么

库内两条一致性管线的**组合骨架**早已就绪，但它们各自挂着一条**结构字段**（= 假设）：

* `Phylo/Stat/MSC.lean`：`MSCFreq.majorizes` —— 真 quartet 的 MSC 概率唯一最大；
* `Phylo/Stat/Parsimony.lean`：`MSCSite.majorizes` —— 真 quartet 的**支持概率**唯一最大。

⇒ 两条都只是「**给定** identifiability ⇒ 一致性」。本文件把这条假设**在锚间距模型里证掉**。

## 数学（`references/FOUR_POINT_2026-11-03.md` §3 ＋ `REVIEW_four_point_20261103.md` §4.2）

物种树用**相容 split 族 ＋ 正权重**表示（`F`、`w`；树度量 `= sumMetric F w`，库内已有）。对四元集
`S`（`|S| = 4`）与有向 quartet `q : Split ↥S`，定义

```text
mass(q) := Σ_{s ∈ F, s 在 S 上诱导出 q} w s
```

即 `q` 的**锚间距**（该 quartet 的内部枝长）。核心事实只有一条：

> **相容的两个 split 不可能在同一个 4-元集上诱导出不同的 `2|2` 划分。**

于是 `mass` 的三值性立刻到手：`mass(q_true) = m_Q > 0`，而另外两个 quartet 的 `mass` 恰为 `0`
（不是「更小」，是**精确为零**）。所以 `majorizes` 在 mass 侧**无条件成立**，剩下的只是
「mass 怎么变成观测到的 `cnt`」这一条模型字段（见 `MassModel` 的 docstring）。

## 与文档 §3 的对应（三处数字口径别混）

| 量 | 差 | 本文件 |
|---|---|---|
| mass 侧 | `mass(q_true) − mass(r) = m_Q` | ✅ `mass_majorizes` |
| t 侧 | `3m_Q/2`（`t = (3/2)mass − ½Total`） | 未做（S5 可选，见派单） |
| Δ 侧 | `2·C(n−1,2)·m_Q` | 未做（同上） |

## 诚实边界

* 本文件的定理**零假设**（除 `F` 两两相容、`w` 在 `F` 上为正、`q` 是 `2|2`、存在 split 诱导 `q`）；
* **`m_Q > 0` 是显式假设**（`mass_pos`）：由「存在 `s ∈ F` 诱导 `q`」＋「`w s > 0`」给出，
  **不**从 binary 自动得到；
* 「期望基因树 mass = 物种树 mass」（即 `E[d_G] = d`）**不在**本文件 —— 它是模型字段，
  见 `MassModel.meanMass`（下文）与派单 §3(b) 的口径 ii。
-/

noncomputable section

open Finset

namespace Phylo.Stat.MassMajorizes

universe u v

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## 1. 「`s` 在 `S` 上诱导出 `q`」 -/

/-- `s` 在四元集 `S` 上诱导出 `q` 的**一种定向**：`q` 的 A 侧恰是 `S ∩ s.sideA`。 -/
def InducesSide (s : Split X) (S : Finset X) (q : Split ↥S) : Prop :=
  ∀ x : ↥S, (x ∈ q.sideA ↔ x.1 ∈ s.sideA)

/-- **无向版**：`q` 的 A 侧是 `S ∩ s.sideA` 或 `S ∩ s.sideB`。

★ 取无向版是**必须**的：`Split` 把两侧有序化，而「`s` 诱导出 quartet `q`」与 `q` 的两侧谁在
`s.sideA` 上无关 —— 否则 `mass` 会依赖 `swap`，`SiteSupport.cnt_swap` 那条字段就不成立。 -/
def Induces (s : Split X) (S : Finset X) (q : Split ↥S) : Prop :=
  InducesSide s S q ∨ InducesSide s S q.swap

theorem induces_swap (s : Split X) (S : Finset X) (q : Split ↥S) :
    Induces s S q.swap ↔ Induces s S q := by
  unfold Induces
  rw [Split.swap_swap, or_comm]

/-! ## 2. 引理层 -/

section Helpers

variable {S : Finset X}

theorem mem_sideB_of_not_mem_sideA {s : Split X} {x : X} (h : x ∉ s.sideA) : x ∈ s.sideB := by
  rw [Split.sideB_eq_sdiff]
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩

theorem not_mem_sideA_of_mem_sideB {s : Split X} {x : X} (h : x ∈ s.sideB) : x ∉ s.sideA := by
  rw [Split.sideB_eq_sdiff] at h
  exact (Finset.mem_sdiff.mp h).2

theorem mem_sideA_of_not_mem_sideB {s : Split X} {x : X} (h : x ∉ s.sideB) : x ∈ s.sideA := by
  have := Finset.mem_union.mp (by rw [s.union_sides]; exact Finset.mem_univ x)
  rcases this with h' | h'
  · exact h'
  · exact absurd h' h

/-- `x ∈ sideB ↔ x ∉ sideA`（对任意载体；这里 `X` 与 `↥S` 都要用）。 -/
theorem mem_sideB_iff_not_mem_sideA {α : Type*} [Fintype α] [DecidableEq α]
    {s : Split α} {x : α} : x ∈ s.sideB ↔ x ∉ s.sideA := by
  rw [Split.sideB_eq_sdiff, Finset.mem_sdiff]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- 由 `sideA` 相等推出 split 相等（`sideB` 由「补集」确定）。 -/
theorem eq_of_sideA_eq {q r : Split ↥S} (h : q.sideA = r.sideA) : q = r := by
  refine (KPartition.eq_iff_parts _ _).mpr (funext fun i => ?_)
  fin_cases i
  · show q.parts 0 = r.parts 0
    simpa [Split.sideA] using h
  · show q.parts 1 = r.parts 1
    have h1 : q.sideB = r.sideB := by rw [Split.sideB_eq_sdiff, Split.sideB_eq_sdiff, h]
    simpa [Split.sideB] using h1

theorem card_sideB (hS : S.card = 4) (q : Split ↥S) : q.sideB.card = 4 - q.sideA.card := by
  have h1 : q.sideA.card + q.sideB.card = 4 := by
    rw [← Finset.card_union_of_disjoint q.disjoint_sides, q.union_sides, Finset.card_univ,
      Fintype.card_coe]
    exact hS
  omega

theorem fintype_card_coe (hS : S.card = 4) : Fintype.card ↥S = 4 := by
  rw [Fintype.card_coe, hS]

theorem eq_of_subset_card2 {A B : Finset ↥S} (hsub : A ⊆ B) (hA : A.card = 2)
    (hB : B.card = 2) : A = B :=
  Finset.eq_of_subset_of_card_le hsub (by omega)

/-- 不交且并满 ⇒ 互补。 -/
theorem eq_compl_of_disjoint_union {A B : Finset ↥S} (hdisj : Disjoint A B)
    (hunion : A ∪ B = Finset.univ) : B = Aᶜ := by
  ext x
  rw [Finset.mem_compl]
  constructor
  · intro hx
    exact fun hxA => (Finset.disjoint_left.mp hdisj) hxA hx
  · intro hx
    have h := Finset.mem_union.mp (by rw [hunion]; exact Finset.mem_univ x)
    rcases h with h' | h'
    · exact absurd h' hx
    · exact h'

theorem union_eq_univ_of_disjoint_card2 {A B : Finset ↥S} (hdisj : Disjoint A B)
    (hA : A.card = 2) (hB : B.card = 2) (hS : S.card = 4) : A ∪ B = Finset.univ := by
  have hcard : (A ∪ B).card = 4 := by
    rw [Finset.card_union_of_disjoint hdisj, hA, hB]
  exact Finset.eq_univ_of_card _ (by rw [hcard, fintype_card_coe hS])

/-- **核心组合引理**：相容的两个 split 不可能在同一四元集上诱导出不同的 `2|2` 划分。 -/
theorem eq_or_swap_of_compatible {s₀ s : Split X} {q r : Split ↥S}
    (hc : Split.Compatible s₀ s) (hq : InducesSide s₀ S q) (hr : InducesSide s S r)
    (hqc : q.sideA.card = 2) (hrc : r.sideA.card = 2) (hS : S.card = 4) :
    r = q ∨ r = q.swap := by
  have hqB : q.sideB.card = 2 := by rw [card_sideB hS q, hqc]
  have hrB : r.sideB.card = 2 := by rw [card_sideB hS r, hrc]
  rcases hc with h1 | h1 | h1 | h1
  · -- (i) `s₀.A ∩ s.A = ∅` ⇒ `q.A ∩ r.A = ∅`
    have hdisj : Disjoint q.sideA r.sideA :=
      Finset.disjoint_left.mpr fun x hxq hxr =>
        (Finset.disjoint_left.mp h1) ((hq x).mp hxq) ((hr x).mp hxr)
    have hu := union_eq_univ_of_disjoint_card2 hdisj hqc hrc hS
    have hrA : r.sideA = q.sideAᶜ := eq_compl_of_disjoint_union hdisj hu
    refine Or.inr (eq_of_sideA_eq ?_)
    rw [Split.swap_sideA, Split.sideB_eq_sdiff, ← Finset.compl_eq_univ_sdiff, ← hrA]
  · -- (ii) `s₀.A ∩ s.B = ∅` ⇒ `q.A ⊆ r.A`
    have hsub : q.sideA ⊆ r.sideA := by
      intro x hx
      have hxa : x.1 ∈ s₀.sideA := (hq x).mp hx
      have hnb : x.1 ∉ s.sideB := fun hb => (Finset.disjoint_left.mp h1) hxa hb
      exact (hr x).mpr (mem_sideA_of_not_mem_sideB hnb)
    exact Or.inl (eq_of_sideA_eq (eq_of_subset_card2 hsub hqc hrc).symm)
  · -- (iii) `s₀.B ∩ s.A = ∅` ⇒ `r.A ⊆ q.A`
    have hsub : r.sideA ⊆ q.sideA := by
      intro x hx
      have hxa : x.1 ∈ s.sideA := (hr x).mp hx
      have hnb : x.1 ∉ s₀.sideB := fun hb => (Finset.disjoint_left.mp h1) hb hxa
      exact (hq x).mpr (mem_sideA_of_not_mem_sideB hnb)
    exact Or.inl (eq_of_sideA_eq (eq_of_subset_card2 hsub hrc hqc))
  · -- (iv) `s₀.B ∩ s.B = ∅` ⇒ `q.B ⊆ r.A`
    have hsub : q.sideB ⊆ r.sideA := by
      intro x hx
      have hxA : x ∉ q.sideA := fun h => (Finset.disjoint_left.mp q.disjoint_sides) h hx
      have hnbA : x.1 ∉ s₀.sideA := fun h => hxA ((hq x).mpr h)
      have hb : x.1 ∈ s₀.sideB := mem_sideB_of_not_mem_sideA hnbA
      have hnb2 : x.1 ∉ s.sideB := fun h => (Finset.disjoint_left.mp h1) hb h
      exact (hr x).mpr (mem_sideA_of_not_mem_sideB hnb2)
    have h1' : q.sideB = r.sideA := eq_of_subset_card2 hsub hqB hrc
    refine Or.inr (eq_of_sideA_eq ?_)
    rw [Split.swap_sideA, ← h1']

end Helpers

/-! ## 3. 相容性对 `swap` 不变（核心引理的四次应用要用） -/

theorem compatible_swap_left {s t : Split X} (h : Split.Compatible s t) :
    Split.Compatible s.swap t := by
  simp only [Split.Compatible, Split.swap_sideA, Split.swap_sideB, disjoint_comm] at h ⊢
  tauto

theorem compatible_swap_right {s t : Split X} (h : Split.Compatible s t) :
    Split.Compatible s t.swap := by
  simp only [Split.Compatible, Split.swap_sideA, Split.swap_sideB, disjoint_comm] at h ⊢
  tauto

/-- 方向转换：`q.swap` 的 A 侧 = `q` 的 B 侧 ⇒ 把「用 `s.sideB` 定向」换成「用 `s.swap.sideA` 定向」。 -/
theorem inducesSide_swap_left (s : Split X) (S : Finset X) (q : Split ↥S) :
    InducesSide s S q.swap ↔ InducesSide s.swap S q := by
  unfold InducesSide
  simp only [Split.swap_sideA]
  constructor <;> intro h x <;>
    (have h1 := h x; simp only [mem_sideB_iff_not_mem_sideA] at h1 ⊢; tauto)

/-- **无向版核心引理**：`q` 是 `2|2`、`s₀` 诱导 `q`、`s` 诱导 `r`、`s₀` 与 `s` 相容
⇒ `r` 只能是 `q` 或 `q.swap`。 -/
theorem induces_eq_or_swap {s₀ s : Split X} {S : Finset X} {q r : Split ↥S}
    (hc : Split.Compatible s₀ s) (hq : Induces s₀ S q) (hr : Induces s S r)
    (hqc : q.sideA.card = 2) (hrc : r.sideA.card = 2) (hS : S.card = 4) :
    r = q ∨ r = q.swap := by
  rcases hq with hq | hq
  · rcases hr with hr | hr
    · exact eq_or_swap_of_compatible hc hq hr hqc hrc hS
    · rw [inducesSide_swap_left] at hr
      exact eq_or_swap_of_compatible (compatible_swap_right hc) hq hr hqc hrc hS
  · rw [inducesSide_swap_left] at hq
    rcases hr with hr | hr
    · exact eq_or_swap_of_compatible (compatible_swap_left hc) hq hr hqc hrc hS
    · rw [inducesSide_swap_left] at hr
      exact eq_or_swap_of_compatible (compatible_swap_left (compatible_swap_right hc))
        hq hr hqc hrc hS

/-! ## 4. `mass`（锚间距）与其性质

分两层（踩坑后的结构）：`massRaw` 是那个**和**，`mass` 再套一层 **2|2 闸门**。
理由：`MSCSite.majorizes` 对**所有** `r : Split ↥S` 断言（含 `1|3`），而一条树 split 在四元集上
完全可以诱导出 `1|3`（如 `{a} | {b,c,d}`）—— 若不加闸门，`mass(1|3) > 0`，`majorizes` 就是**假**的。
闸门后 `1|3` 的 `mass` 为 `0`，而真 quartet 的 `mass > 0`。

（分成两个 `def` 而不是把 `if` 写进一个 `def`：否则 `mass = ∑ … if …` 这种**陈述**会要求
`Decidable (Induces …)` 在陈述层可合成，而 `Induces` 是 `def`、实例搜索不展开它 ⇒ 陈述直接编不过。） -/

/-- 锚间距的**裸和**：`F` 中诱导出 `q` 的 split 的权重和（不看 `q` 是不是 `2|2`）。 -/
def massRaw (F : Finset (Split X)) (w : Split X → ℝ) (S : Finset X) (q : Split ↥S) : ℝ := by
  classical
  exact ∑ s ∈ F, (if Induces s S q then w s else 0)

/-- 四元集 `S` 上 quartet `q` 的**锚间距（mass）**：`massRaw` 加 **2|2 闸门**。

⚠️ 口径（派单 §3(b)）：这是**物种树侧**的质量，即 `E_G[mass_G(q)]` 的**期望**；
把 `E_G[mass_G] = mass` 这条桥（两谱系期望共祖距离 = 物种树距离）留作模型字段（`hmean`），
**不假装已证**。 -/
def mass (F : Finset (Split X)) (w : Split X → ℝ) (S : Finset X) (q : Split ↥S) : ℝ :=
  if q.sideA.card = 2 then massRaw F w S q else 0

theorem mass_of_card_ne {F : Finset (Split X)} {w : Split X → ℝ} {S : Finset X}
    {q : Split ↥S} (h : q.sideA.card ≠ 2) : mass F w S q = 0 := by
  rw [mass, if_neg h]

theorem mass_of_card_eq {F : Finset (Split X)} {w : Split X → ℝ} {S : Finset X}
    {q : Split ↥S} (h : q.sideA.card = 2) : mass F w S q = massRaw F w S q := by
  rw [mass, if_pos h]

/-! ### 4.1 `massRaw` 的性质 -/

theorem massRaw_swap (F : Finset (Split X)) (w : Split X → ℝ) (S : Finset X)
    (q : Split ↥S) : massRaw F w S q.swap = massRaw F w S q := by
  classical
  rw [massRaw]
  exact Finset.sum_congr rfl fun s _ => by rw [induces_swap]

theorem massRaw_nonneg {F : Finset (Split X)} {w : Split X → ℝ} (hw : ∀ s ∈ F, 0 < w s)
    (S : Finset X) (q : Split ↥S) : 0 ≤ massRaw F w S q := by
  classical
  rw [massRaw]
  exact Finset.sum_nonneg fun s hs => by
    split_ifs with hI
    · exact (hw s hs).le
    · exact le_refl 0

/-- ★ **`m_Q > 0` 的出口**：`F` 里有一条 split 诱导 `q`、权重为正 ⇒ `massRaw(q) > 0`。 -/
theorem massRaw_pos {F : Finset (Split X)} {w : Split X → ℝ} (hw : ∀ s ∈ F, 0 < w s)
    {S : Finset X} {q : Split ↥S} (h : ∃ s ∈ F, Induces s S q) : 0 < massRaw F w S q := by
  classical
  rw [massRaw]
  obtain ⟨s₀, hs₀, hind⟩ := h
  refine Finset.sum_pos' (fun s hs => ?_) ⟨s₀, hs₀, ?_⟩
  · split_ifs with hI
    · exact (hw s hs).le
    · exact le_refl 0
  · simpa only [hind, ↓reduceIte] using hw s₀ hs₀

/-- ★★★ **三值性**：`2|2` 且不是 `q`、`q.swap` 的 quartet，`massRaw` **精确为零**。 -/
theorem massRaw_eq_zero {F : Finset (Split X)} {w : Split X → ℝ}
    (hcomp : ∀ s ∈ F, ∀ t ∈ F, Split.Compatible s t) {s₀ : Split X} (hs₀ : s₀ ∈ F)
    {S : Finset X} {q : Split ↥S} (hq : Induces s₀ S q)
    (hqc : q.sideA.card = 2) (hS : S.card = 4) {r : Split ↥S} (hrc : r.sideA.card = 2)
    (hr1 : r ≠ q) (hr2 : r ≠ q.swap) : massRaw F w S r = 0 := by
  classical
  rw [massRaw]
  refine Finset.sum_eq_zero fun s hs => ?_
  split_ifs with hI
  · exfalso
    have h := induces_eq_or_swap (hcomp s₀ hs₀ s hs) hq hI hqc hrc hS
    tauto
  · rfl

/-! ### 4.2 `mass`（带闸门）的性质 -/

/-- `q.swap` 的 A 侧基数（`|S| = 4` 时）。 -/
theorem card_swap_sideA {S : Finset X} (hS : S.card = 4) (q : Split ↥S) :
    q.swap.sideA.card = 4 - q.sideA.card := by
  rw [Split.swap_sideA]
  exact card_sideB hS q

theorem mass_swap (F : Finset (Split X)) (w : Split X → ℝ) (S : Finset X)
    (hS : S.card = 4) (q : Split ↥S) : mass F w S q.swap = mass F w S q := by
  by_cases h : q.sideA.card = 2
  · rw [mass_of_card_eq (by rw [card_swap_sideA hS q, h]), mass_of_card_eq h, massRaw_swap]
  · rw [mass_of_card_ne (by rw [card_swap_sideA hS q]; omega), mass_of_card_ne h]

theorem mass_nonneg {F : Finset (Split X)} {w : Split X → ℝ} (hw : ∀ s ∈ F, 0 < w s)
    (S : Finset X) (q : Split ↥S) : 0 ≤ mass F w S q := by
  by_cases h : q.sideA.card = 2
  · rw [mass_of_card_eq h]; exact massRaw_nonneg hw S q
  · rw [mass_of_card_ne h]

theorem mass_pos {F : Finset (Split X)} {w : Split X → ℝ} (hw : ∀ s ∈ F, 0 < w s)
    {S : Finset X} {q : Split ↥S} (hqc : q.sideA.card = 2)
    (h : ∃ s ∈ F, Induces s S q) : 0 < mass F w S q := by
  rw [mass_of_card_eq hqc]; exact massRaw_pos hw h

theorem mass_eq_zero {F : Finset (Split X)} {w : Split X → ℝ}
    (hcomp : ∀ s ∈ F, ∀ t ∈ F, Split.Compatible s t) {s₀ : Split X} (hs₀ : s₀ ∈ F)
    {S : Finset X} {q : Split ↥S} (hq : Induces s₀ S q)
    (hqc : q.sideA.card = 2) (hS : S.card = 4) {r : Split ↥S} (hrc : r.sideA.card = 2)
    (hr1 : r ≠ q) (hr2 : r ≠ q.swap) : mass F w S r = 0 := by
  rw [mass_of_card_eq hrc]
  exact massRaw_eq_zero hcomp hs₀ hq hqc hS hrc hr1 hr2

/-- ★★★★ **MASS_MAJORIZES**（派单 §3 的目标命题，本单唯一的新数学）：

设 `F` 两两相容、`w` 在 `F` 上为正、`q` 是 `2|2` quartet、且 `F` 中**有**一条 split 在四元集 `S` 上
诱导出 `q`（这就是「`q` 是真 quartet」）。则对**任何**另一个 quartet `r`（`r ≠ q`、`r ≠ q.swap`），

```text
mass(r) = 0 < mass(q) = m_Q .
```

⇒ `q` 的锚间距**严格最大**，且另外两个 quartet 的质量**恰为零**（不是「更小」）。
对 `1|3` 的 `r` 也成立（闸门直接给 `0`）。 -/
theorem mass_majorizes {F : Finset (Split X)} {w : Split X → ℝ}
    (hw : ∀ s ∈ F, 0 < w s) (hcomp : ∀ s ∈ F, ∀ t ∈ F, Split.Compatible s t)
    {S : Finset X} {q : Split ↥S} (hqc : q.sideA.card = 2) (hS : S.card = 4)
    (hq : ∃ s ∈ F, Induces s S q) {r : Split ↥S}
    (hr1 : r ≠ q) (hr2 : r ≠ q.swap) : mass F w S r < mass F w S q := by
  have hpos := mass_pos hw hqc hq
  by_cases hrc : r.sideA.card = 2
  · obtain ⟨s₀, hs₀, hind⟩ := hq
    rw [mass_eq_zero hcomp hs₀ hind hqc hS hrc hr1 hr2]
    exact hpos
  · rw [mass_of_card_ne hrc]
    exact hpos

end Phylo.Stat.MassMajorizes
