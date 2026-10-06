/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Phylo.Stat.Stability

/-!
# `Phylo.Stat.Parsimony` —— parsimony 的一致性（unrooted quartet + ISM）

**决策（2026-10-07 老师定）**：parsimony 走 **unrooted quartet + infinite-sites（ISM）**。

## 为什么这个组合能证

Felsenstein zone 的 parsimony 不一致源于**同塑性**（homoplasy，一个位点多次替换）；
**ISM 下不发生同塑性**（每个位点至多一次替换）。文献（Liu–Edwards 2009；Mendes–Hahn 2018）
证明该组合下 parsimony 一致；Roch–Steel 2015 的 unrooted 反例是 **6 taxon**，不覆盖 4 taxon。

## 本文件证什么

* ★ `Pattern.fitchCost_eq` —— **4-叶组合核心**：对 2\|2 信息位点，
  `fitchCost(k, p) = 2 - [拓扑 k 与位点一致]`（Fitch 算法，`decide` 枚举 48 情形）；
* ★★ `parsimonyScore_le_iff` —— **最简树 = 支持位点最多的 quartet 系统**；
* ★★★ `parsimony_statisticallyConsistent` —— 接上 `Phylo.Stat.Stability` 的通用引擎。

⇒ parsimony 与 ASTRAL **共享同一套一致性骨架**（得分 = 局部支持之和），
差别只在「局部支持」的组合来源（Fitch 最少替换数 vs quartet 支持度）。
-/

universe u v

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## 4-叶组合核心（Fitch 最少替换数） -/

/-- **4-叶位点模式**（二进制字符）。 -/
abbrev Pattern := Fin 4 → Bool

namespace Pattern

/-- 位点的「分裂」：值为 `true` 的叶集。 -/
def ones (p : Pattern) : Finset (Fin 4) := Finset.univ.filter fun i => p i = true

/-- **三种无根 4-叶拓扑**：`k = 0 ↦ 01|23`，`1 ↦ 02|13`，`2 ↦ 03|12`（给出第一侧）。 -/
def pairA (k : Fin 3) : Finset (Fin 4) :=
  if k = 0 then {0, 1} else if k = 1 then {0, 2} else {0, 3}

/-- Fitch 的集合运算：`X ∩ Y`（非空时，代价 0）或 `X ∪ Y`（否则，代价 1）。 -/
def fitchSet (x y : Bool) : Finset Bool := if x = y then {x} else Finset.univ

/-- **`ab|cd` 拓扑的最少替换数**（Fitch，root 取 `ab` 侧内部节点）。

`u = Fitch(a,b)`、`v = Fitch(c,d)`，总代价 = `cost(a,b) + cost(c,d) + cost(root)`。 -/
def costTopo (a b c d : Bool) : ℕ :=
  (if a = b then 0 else 1) + (if c = d then 0 else 1)
    + (if (fitchSet a b ∩ fitchSet c d).Nonempty then 0 else 1)

/-- **拓扑 `k` 的最少替换数**。 -/
def fitchCost (k : Fin 3) (p : Pattern) : ℕ :=
  if k = 0 then costTopo (p 0) (p 1) (p 2) (p 3)
  else if k = 1 then costTopo (p 0) (p 2) (p 1) (p 3)
  else costTopo (p 0) (p 3) (p 1) (p 2)

/-- ★ **4-叶组合核心**（ISM 下 parsimony 的全部组合内容）。

对任意拓扑 `k` 与位点模式 `p`：

* `|ones| = 0` 或 `4`（无信息）：代价 `0`；
* `|ones| = 2`（**信息位点**）：代价 `1` 当且仅当拓扑 `k` 与位点的分裂一致，否则 `2`；
* `|ones| = 1` 或 `3`（**中立**）：代价 `1`（对所有拓扑相同）。

**证明**：`decide` 枚举 `Fin 4 → Bool` 的全部 16 个模式和 `Fin 3` 的 3 个拓扑（48 情形）。 -/
theorem fitchCost_eq (k : Fin 3) :
    ∀ p : Pattern, fitchCost k p =
      (if (ones p).card = 0 ∨ (ones p).card = 4 then 0
        else if (ones p).card = 2 then
          (if ones p = pairA k ∨ ones p = (pairA k)ᶜ then 1 else 2)
        else 1) := by
  fin_cases k <;> native_decide

/-- ★ **信息位点情形**（`fitchCost_eq` 的专门化，最常用）。 -/
theorem fitchCost_eq_of_card_two (k : Fin 3) {p : Pattern} (h : (ones p).card = 2) :
    fitchCost k p = if ones p = pairA k ∨ ones p = (pairA k)ᶜ then 1 else 2 := by
  rw [fitchCost_eq k p, if_neg (by rintro (h0 | h4) <;> omega), if_pos h]

end Pattern

/-! ## 全局：parsimony 得分 = 常数 − 支持计数 -/

/-- **位点支持表**：每个 4-元集上，各 quartet（有向 split）的**支持位点数**，以及
**信息位点总数**。 -/
structure SiteSupport (X : Type u) [Fintype X] [DecidableEq X] where
  /-- 信息位点总数。 -/
  info : (S : Finset X) → S.card = 4 → ℝ
  /-- 支持各 split 的位点数。 -/
  cnt : (S : Finset X) → S.card = 4 → Split ↥S → ℝ
  cnt_nonneg : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), 0 ≤ cnt S hS q
  /-- 交换两侧不改变支持数。 -/
  cnt_swap : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), cnt S hS q.swap = cnt S hS q

/-- **全局 parsimony 得分**（`SiteSupport` 版）：**不支持** `q` 的位点数。

由 `Pattern.fitchCost_eq`：对信息位点，代价 = `2 − [支持]`；中立位点代价恒为 `1`；
无信息位点代价恒为 `0`。故总代价 = `(常数) − (支持位点数)`。

（常数 = `2·信息位点 + 中立位点`，与树无关，故**最小化得分 ⟺ 最大化支持**。） -/
noncomputable def parsimonyScore (D : SiteSupport X) (q : QuartetChoice X) : ℝ :=
  ∑ S : {S : Finset X // S.card = 4}, (D.info S.1 S.2 - D.cnt S.1 S.2 (q S.1 S.2))

/-- **支持得分**：`Σ_S 支持(q_S)`。 -/
noncomputable def supportScore (D : SiteSupport X) (q : QuartetChoice X) : ℝ :=
  ∑ S : {S : Finset X // S.card = 4}, D.cnt S.1 S.2 (q S.1 S.2)

/-- ★★ **最简树 ⟺ 支持位点最多**（ISM 下 parsimony 的一致性判据）。 -/
theorem parsimonyScore_le_iff (D : SiteSupport X) (q q' : QuartetChoice X) :
    parsimonyScore D q ≤ parsimonyScore D q' ↔ supportScore D q' ≤ supportScore D q := by
  have h : parsimonyScore D q' - parsimonyScore D q = supportScore D q - supportScore D q' := by
    simp only [parsimonyScore, supportScore, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    ring
  constructor <;> intro hle <;> linarith

/-! ## 引擎：site-级 gap + 稳定性（结构与 ASTRAL 相同，得分换成支持计数） -/

/-- 与参考选择 `q0` 一致（模 `swap`）。 -/
def AgreesWith (q0 q : QuartetChoice X) : Prop :=
  ∀ (S : Finset X) (hS : S.card = 4), q S hS = q0 S hS ∨ q S hS = (q0 S hS).swap

open Classical in
theorem exists_false_of_not_agrees {q0 q : QuartetChoice X} (h : ¬ AgreesWith q0 q) :
    ∃ (S : Finset X) (hS : S.card = 4), q S hS ≠ q0 S hS ∧ q S hS ≠ (q0 S hS).swap := by
  by_contra hc
  apply h
  intro S hS
  by_cases h1 : q S hS = q0 S hS
  · exact Or.inl h1
  · refine Or.inr ?_
    by_contra h2
    exact hc ⟨S, hS, h1, h2⟩

/-- **位点数据的 `ε`-接近**。 -/
def SiteClose (D D' : SiteSupport X) (ε : ℝ) : Prop :=
  ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), |D.cnt S hS q - D'.cnt S hS q| < ε

theorem SiteClose_symm {D D' : SiteSupport X} {ε : ℝ} (h : SiteClose D D' ε) :
    SiteClose D' D ε := fun S hS q => by rw [abs_sub_comm]; exact h S hS q

/-- ★ **MSC + ISM 的位点数据**（公理化）：真树 quartet 的支持位点数唯一最大。

（Liu–Edwards 2009 / Mendes–Hahn 2018：ISM 下 parsimony 一致；
此处取其在每个 4-元集上的形式。） -/
structure MSCSite (X : Type u) [Fintype X] [DecidableEq X] extends SiteSupport X where
  /-- 真物种树。 -/
  tree : Cladogram.{u, v} X
  /-- 真树的 quartet 选择。 -/
  q : QuartetChoice X
  /-- 确实被真树展示。 -/
  displays : ∀ (S : Finset X) (hS : S.card = 4), tree.DisplaysSplitOn S (q S hS)
  /-- ★ **MSC + ISM 核心**：真树 quartet 的支持位点数唯一最大（模 `swap`）。 -/
  majorizes : ∀ (S : Finset X) (hS : S.card = 4) (r : Split ↥S),
    r ≠ q S hS → r ≠ (q S hS).swap → cnt S hS r < cnt S hS (q S hS)

namespace MSCSite

variable (M : MSCSite.{u, v} X)

/-- 局部弱形式。 -/
theorem cnt_le (S : Finset X) (hS : S.card = 4) (r : Split ↥S) :
    M.cnt S hS r ≤ M.cnt S hS (M.q S hS) := by
  by_cases h1 : r = M.q S hS
  · rw [h1]
  · by_cases h2 : r = (M.q S hS).swap
    · rw [h2, M.cnt_swap]
    · exact (M.majorizes S hS r h1 h2).le

/-- 真树作为 `QuartetTree`。 -/
def asQuartetTree : QuartetTree.{u, v} X := ⟨M.tree, M.q, M.displays⟩

@[simp] theorem asQuartetTree_q : M.asQuartetTree.q = M.q := rfl

/-- ★ 非真选择的支持得分严格小于真树。 -/
theorem supportScore_lt_of_not_agrees {q : QuartetChoice X} (h : ¬ AgreesWith M.q q) :
    supportScore M.toSiteSupport q < supportScore M.toSiteSupport M.q := by
  obtain ⟨S, hS, h1, h2⟩ := exists_false_of_not_agrees h
  exact Finset.sum_lt_sum
    (s := (Finset.univ : Finset {S : Finset X // S.card = 4}))
    (fun S1 _ => M.cnt_le S1.1 S1.2 (q S1.1 S1.2))
    ⟨⟨S, hS⟩, Finset.mem_univ _, M.majorizes S hS (q S hS) h1 h2⟩

open Classical in
/-- ★ **支持得分 gap**（有限性）。 -/
theorem exists_gap (hNE : ∃ q : QuartetChoice X, ¬ AgreesWith M.q q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : QuartetChoice X, ¬ AgreesWith M.q q →
      supportScore M.toSiteSupport q + δ ≤ supportScore M.toSiteSupport M.q := by
  classical
  obtain ⟨q0, hq0⟩ := hNE
  set S : Finset ℝ := ((Finset.univ : Finset (QuartetChoice X)).filter
      (fun q => ¬ AgreesWith M.q q)).image
      (fun q => supportScore M.toSiteSupport M.q - supportScore M.toSiteSupport q) with hSdef
  have hne : S.Nonempty := by
    refine ⟨supportScore M.toSiteSupport M.q - supportScore M.toSiteSupport q0, ?_⟩
    rw [hSdef]
    exact Finset.mem_image.mpr ⟨q0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq0⟩, rfl⟩
  refine ⟨S.min' hne, ?_, ?_⟩
  · obtain ⟨q1, hq1, heq⟩ := Finset.mem_image.mp (S.min'_mem hne)
    rw [← heq]
    have := M.supportScore_lt_of_not_agrees (Finset.mem_filter.mp hq1).2
    linarith
  · intro q hq
    have hmem : supportScore M.toSiteSupport M.q - supportScore M.toSiteSupport q ∈ S := by
      rw [hSdef]
      exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩, rfl⟩
    have h1 : S.min' hne ≤ supportScore M.toSiteSupport M.q - supportScore M.toSiteSupport q :=
      S.min'_le _ hmem
    linarith

end MSCSite

/-- **支持得分的 `ε`-扰动上界**。 -/
theorem supportScore_le_add (D D1 : SiteSupport X) (q : QuartetChoice X) {ε : ℝ}
    (hD : SiteClose D D1 ε) :
    supportScore D q ≤ supportScore D1 q + ε * (Fintype.card {S : Finset X // S.card = 4}) := by
  have hdiff : supportScore D q - supportScore D1 q ≤
      ε * (Fintype.card {S : Finset X // S.card = 4}) := by
    rw [supportScore, supportScore, ← Finset.sum_sub_distrib]
    calc (Finset.univ : Finset {S : Finset X // S.card = 4}).sum
          (fun S => D.cnt S.1 S.2 (q S.1 S.2) - D1.cnt S.1 S.2 (q S.1 S.2))
        ≤ (Finset.univ : Finset {S : Finset X // S.card = 4}).sum (fun _ => ε) :=
          Finset.sum_le_sum fun S _ => le_trans (le_abs_self _) (hD S.1 S.2 (q S.1 S.2)).le
      _ = ε * (Fintype.card {S : Finset X // S.card = 4}) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  linarith

open Classical in
/-- ★★ **稳定性**：扰动 `ε < δ/(2N+1)` 时，最简树仍是真选择。 -/
theorem stable_argmax_site (M : MSCSite.{u, v} X) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ q : QuartetChoice X, ¬ AgreesWith M.q q →
      supportScore M.toSiteSupport q + δ ≤ supportScore M.toSiteSupport M.q)
    {D : SiteSupport X}
    (hD : SiteClose D M.toSiteSupport (δ / (2 * (Fintype.card {S : Finset X // S.card = 4}) + 1)))
    {q : QuartetChoice X} (hmax : supportScore D M.q ≤ supportScore D q) :
    AgreesWith M.q q := by
  by_contra hnot
  set N : ℝ := (Fintype.card {S : Finset X // S.card = 4} : ℝ) with hNdef
  have hN0 : (0 : ℝ) ≤ N := by rw [hNdef]; exact Nat.cast_nonneg _
  set ε : ℝ := δ / (2 * N + 1) with hεdef
  have hN1 : (2 : ℝ) * N + 1 ≠ 0 := by linarith
  have hεN : ε * (2 * N + 1) = δ := by rw [hεdef, div_mul_cancel₀ _ hN1]
  have hεpos : 0 < ε := by rw [hεdef]; exact div_pos hδ (by linarith)
  have h1 : supportScore D q ≤ supportScore M.toSiteSupport q + ε * N :=
    supportScore_le_add D M.toSiteSupport q hD
  have h2 : supportScore M.toSiteSupport M.q ≤ supportScore D M.q + ε * N :=
    supportScore_le_add M.toSiteSupport D M.q (SiteClose_symm hD)
  have h3 : supportScore M.toSiteSupport q + δ ≤ supportScore M.toSiteSupport M.q := hgap q hnot
  have h4 : 2 * ε * N < δ := by rw [← hεN]; nlinarith
  linarith

/-- **parsimony 估计量**：最简树（`parsimonyScore` 最小者）。 -/
def IsParsimony (D : SiteSupport X) (qt : QuartetTree.{u, v} X) : Prop :=
  ∀ qt1 : QuartetTree.{u, v} X, parsimonyScore D qt.q ≤ parsimonyScore D qt1.q

open Classical in
/-- ★★ **最简树 ⟺ 支持得分最大**。 -/
theorem isParsimony_iff_supportMax (D : SiteSupport X) {qt : QuartetTree.{u, v} X} :
    IsParsimony D qt ↔ ∀ qt1 : QuartetTree.{u, v} X,
      supportScore D qt1.q ≤ supportScore D qt.q :=
  ⟨fun h qt1 => (parsimonyScore_le_iff D qt.q qt1.q).mp (h qt1),
    fun h qt1 => (parsimonyScore_le_iff D qt.q qt1.q).mpr (h qt1)⟩

/-- **（公理化）ISM 采样的位点大数定律**。 -/
structure SiteSampling (X : Type u) [Fintype X] [DecidableEq X] where
  /-- 第 `n` 个样本的支持表。 -/
  emp : ℕ → SiteSupport X
  /-- ★ 大数定律：经验支持表最终 `ε`-接近理论值。 -/
  converges : ∀ M : MSCSite.{u, v} X, ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n ≥ N, SiteClose (emp n) M.toSiteSupport ε

open Classical in
/-- ★★★ **parsimony 的统计一致性**（unrooted quartet + ISM，quartet 层面）。

由 `stable_argmax`（gap + 稳定性）与位点大数定律直接得到；
「最简树」通过 `isParsimony_iff_supportMax` 转成「支持得分最大」。 -/
theorem parsimony_statisticallyConsistent (M : MSCSite.{u, v} X) (sm : SiteSampling.{u, v} X)
    {E : SiteSupport X → QuartetTree.{u, v} X} (hE : ∀ D, IsParsimony D (E D))
    (hNE : ∃ q : QuartetChoice X, ¬ AgreesWith M.q q) :
    ∃ N : ℕ, ∀ n ≥ N, AgreesWith M.q (E (sm.emp n)).q := by
  classical
  obtain ⟨δ, hδ, hgap⟩ := M.exists_gap hNE
  set M' : ℝ := 2 * (Fintype.card {S : Finset X // S.card = 4} : ℝ) + 1 with hMdef
  have hMpos : 0 < M' := by
    rw [hMdef]
    have : (0 : ℝ) ≤ (Fintype.card {S : Finset X // S.card = 4} : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨N, hN⟩ := sm.converges M (δ / M') (div_pos hδ hMpos)
  refine ⟨N, fun n hn => ?_⟩
  refine stable_argmax_site (D := sm.emp n) M hδ hgap ?_ ?_
  · simpa [hMdef] using hN n hn
  · exact (isParsimony_iff_supportMax (sm.emp n)).mp (hE (sm.emp n)) M.asQuartetTree
