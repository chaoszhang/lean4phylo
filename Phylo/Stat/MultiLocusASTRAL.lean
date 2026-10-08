/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Tactic.Linarith
import Phylo.Stat.Stability

/-!
# `Phylo.Stat.MultiLocusASTRAL` —— 多标记 ASTRAL（跨标记求和归约到 ASTRAL）

> ⛔ **本文件不是 CASTER。** 本文件是「**多标记 / 多拷贝数据下的 ASTRAL 归约**」：
> 每个 4-元集上各标记（locus）各自给出一个 quartet 支持，取**跨标记之和**为得分。
> **真 CASTER** —— Zhang, Nielsen, Mirarab (2025), *Science* **387**(6737) eadk9688,
> "Direct species tree inference from whole-genome alignments" —— 是**位点 / 比对**方法，
> 其数学内容（LM 集总引理、JC69/F84/LM 位点模式权重、命题 A/B、定理 1、定理 2）
> 与本文件**完全无关**，见 `Phylo/Stat/LMLumping.lean` · `Phylo/Stat/CASTERWeights.lean` ·
> `Phylo/Stat/CASTERJC69.lean`。
>
> ## 📛 更名记录（2026-10-08，批 W8a —— 纪律 12「★ 必须对应真实声明」）
>
> 本文件原名 `Phylo/Stat/CASTER.lean`，其中四条声明因**名不符实**一并改名：
>
> | 旧名                          | 新名                                  |
> | --------------------------- | ----------------------------------- |
> | `casterScore`               | `multiLocusScore`                   |
> | `casterScore_eq`            | `multiLocusScore_eq`                |
> | `caster_isASTRAL`           | `multiLocus_isASTRAL`               |
> | `caster_statisticallyConsistent` | **删除**（理由见下）                    |
> | `caster_iso`（在 `QuartetDecides.lean`） | `multiLocus_iso`          |
>
> **文献引用也写错了**：旧 docstring 写「CASTER（Zhang–Mirarab–Rabiee et al. 2018）」，
> 但那个出处实为 **ASTRAL-III** —— Zhang, Rabiee, Sayyari, Mirarab (2018),
> *BMC Bioinformatics* **19**(S6):153。真 CASTER 是 2025 年的 *Science* 论文。
>
> ## 🔻 为什么删掉 `caster_statisticallyConsistent`
>
> 那条定理的签名是
> `(m) (sm) (_M : MultiMarkerFreq X) (_hM : _M.avg = m.freq) (hE) (hNE) : …`，
> 但**证明体只有一行** `astral_statisticallyConsistent m sm hE hNE`：
> `_M` 与 `_hM` 是**从未被使用的参数**。于是这条「定理」其实只是 ASTRAL 定理的**别名**，
> 与「多标记数据」毫无关系，却会让人误以为「多标记数据被用上了、CASTER 的一致性已证」。
>
> 多标记数据要真正支撑一条**渐近**一致性定理，还需要一个「多标记采样 ⟹ 平均频率收敛到 MSC 频率」
> 的随机模型（`NEXT.md` 的缺口 **G1**），**库内没有**。因此本文件**不再声称**它，
> 改为给出真正用到 `M` 的那条 ★★★ `multiLocus_maximizer_agrees`（有限样本、无渐近假设）。

## 本文件证什么

* ★ `multiLocusScore_eq` —— **归约定理**：`multiLocusScore(M, q) = L · astralScore(M.avg, q)`；
* ★★ `multiLocus_isASTRAL` —— 多标记 argmax ⟺ 平均频率上 ASTRAL 的 argmax（`L > 0`）；
* ★★★ `multiLocus_maximizer_agrees` —— 在 `M.avg = m.freq` 下，多标记得分最大化者在每个
  4-元集上给出真树的 quartet（模 `swap`）。**这条真正用到多标记数据 `M`**（把它当作
  「`L` 份 quartet 频率的聚合」），且**不需要**任何渐近 / 采样假设。

⇒ 换言之：多标记**不改变最优树**（`multiLocusScore_eq` + `multiLocus_isASTRAL`），
而**一旦**平均频率对齐了 MSC 频率，多标记得分最大化者就逐 quartet 恢复真树
（`multiLocus_maximizer_agrees`）。渐近一致性本身仍是 ASTRAL 侧的结论（`Phylo.Stat.MSC`）。 -/

universe u v

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- **多标记 quartet 数据**：`L` 个标记，每个给出一个 quartet 频率表。 -/
structure MultiMarkerFreq (X : Type u) [Fintype X] [DecidableEq X] where
  /-- 标记数。 -/
  L : ℕ
  /-- 至少一个标记。 -/
  Lpos : 0 < L
  /-- 第 `m` 个标记的频率表。 -/
  freq : Fin L → QuartetFreq X

namespace MultiMarkerFreq

variable (M : MultiMarkerFreq X)

/-- **平均频率表**：逐点取跨标记平均。 -/
noncomputable def avg : QuartetFreq X where
  p S hS q := (∑ m : Fin M.L, (M.freq m).p S hS q) / M.L
  p_nonneg S hS q :=
    div_nonneg (Finset.sum_nonneg fun m _ => (M.freq m).p_nonneg S hS q)
      (Nat.cast_nonneg _)
  p_sum_one S hS := by
    have hL : (M.L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp M.Lpos)
    have h1 : ∀ m : Fin M.L, (∑ q : Split ↥S, (M.freq m).p S hS q) = 1 :=
      fun m => (M.freq m).p_sum_one S hS
    rw [← Finset.sum_div, Finset.sum_comm,
      Finset.sum_congr rfl fun m _ => h1 m, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, div_self hL]
  p_swap S hS q := by
    rw [Finset.sum_congr rfl fun m _ => (M.freq m).p_swap S hS q]

end MultiMarkerFreq

/-- **多标记 ASTRAL 得分**：跨标记的 ASTRAL 得分之和。 -/
noncomputable def multiLocusScore (M : MultiMarkerFreq X) (q : QuartetChoice X) : ℝ :=
  ∑ m : Fin M.L, astralScore (M.freq m) q

open Classical in
/-- ★ **归约定理**：多标记得分 = 标记数 × 平均频率的 ASTRAL 得分。

**证明**：两次 `Finset.sum_comm` 交换求和次序 + `Sum/L` 的消去。 -/
theorem multiLocusScore_eq (M : MultiMarkerFreq X) (q : QuartetChoice X) :
    multiLocusScore M q = M.L * astralScore M.avg q := by
  have hL : (M.L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp M.Lpos)
  have hR : M.L * astralScore M.avg q =
      ∑ x : {S : Finset X // S.card = 4}, ∑ m : Fin M.L,
        (M.freq m).p x.1 x.2 (q x.1 x.2) := by
    simp only [astralScore, MultiMarkerFreq.avg]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_comm (M.L : ℝ), div_mul_cancel₀ _ hL]
  rw [hR]
  simp only [multiLocusScore, astralScore]
  rw [Finset.sum_comm]

open Classical in
/-- ★★ **多标记 argmax = 平均频率上 ASTRAL 的 argmax**（`L > 0` 时）。

即：**多标记求和与取平均给出同一个最优树** —— 标记数不改变最优树。 -/
theorem multiLocus_isASTRAL (M : MultiMarkerFreq X) {qt : QuartetTree.{u, v} X} :
    (∀ qt1 : QuartetTree.{u, v} X, multiLocusScore M qt1.q ≤ multiLocusScore M qt.q) ↔
      IsASTRAL M.avg qt := by
  have hL : (0 : ℝ) < (M.L : ℝ) := Nat.cast_pos.mpr M.Lpos
  constructor
  · intro h qt1
    have h1 : multiLocusScore M qt1.q ≤ multiLocusScore M qt.q := h qt1
    rw [multiLocusScore_eq, multiLocusScore_eq] at h1
    exact le_of_mul_le_mul_left h1 hL
  · intro h qt1
    have h1 : astralScore M.avg qt1.q ≤ astralScore M.avg qt.q := h qt1
    rw [multiLocusScore_eq, multiLocusScore_eq]
    exact mul_le_mul_of_nonneg_left h1 hL.le

open Classical in
/-- ★★★ **多标记得分最大化者逐 quartet 恢复真树**（模 `swap`）。

设多标记数据 `M` 的平均频率就是 MSC 频率（`M.avg = m.freq`；这**是**一条假设，
把它从「裸假设」变成结论正是 `NEXT.md` 的缺口 **G1**，本批**不声称**已解决），
则**多标记得分**的任一最大化者在每个 4-元集上给出的 quartet 都等于真树的 quartet（或它的 `swap`）。

与旧名 `caster_statisticallyConsistent` 的区别：本定理**真正使用** `M`
（通过 `multiLocusScore_eq` 把「`M` 的得分」换成「`M.avg` 的得分」），
且**不断言**任何渐近 / 采样结论。 -/
theorem multiLocus_maximizer_agrees (m : MSCFreq.{u, v} X) (M : MultiMarkerFreq X)
    (hM : M.avg = m.freq) {qt : QuartetTree.{u, v} X}
    (h : ∀ qt1 : QuartetTree.{u, v} X, multiLocusScore M qt1.q ≤ multiLocusScore M qt.q)
    (S : Finset X) (hS : S.card = 4) :
    qt.q S hS = m.q S hS ∨ qt.q S hS = (m.q S hS).swap := by
  have h1 : IsASTRAL M.avg qt := (multiLocus_isASTRAL M).mp h
  rw [hM] at h1
  exact astral_maximizer_agrees m h1 S hS
