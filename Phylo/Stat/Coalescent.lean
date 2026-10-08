/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Phylo.Stat.MSC

/-!
# `Phylo.Stat.Coalescent` —— Kingman 合并过程（M2）与 4 元集 ILS 公式（M1）

本文件按文献**原文**形式化两件事：

* **M2** —— Kingman (1982) *The Coalescent*, Stochastic Processes and their Applications
  **13** (1982) 235–248 的**有限 + 解析**内容：合并率 `d_k = k(k−1)/2`、跳链的等概率合并
  （`1/C(k,2)`）、逗留时间与总时间的期望；
* **M1** —— 4 元集上**不完全谱系分选**（ILS）的三拓扑概率
  `1 − ⅔e^{−t}`、`⅓e^{−t}`、`⅓e^{−t}`（`t` = 内部枝长，coalescent units，即 `2N` 世代），
  以及由此得到的 `MSCFreq.majorizes` 严格不等式。

## ⚠️ 命名更正（文献核对后的诚实报告）

任务书写的是「`P(不一致 quartet) = 1 − ⅔e^{−t}`」。**按文献原文，这是反的**：

* `1 − ⅔e^{−t}` 是**与物种树一致（concordant）**的 quartet 概率；
* 每个**不一致（discordant）** quartet 的概率是 `⅓e^{−t}`，两个不一致拓扑之和为 `⅔e^{−t}`。

出处：`references/md/AllmanDegnanRhodes2011_IdentifyingRootedSpeciesTree.md` 第 **356–360** 行
（“consider the rooted species tree `((a, b), c)` … the rooted gene tree `((A, B), C)` has probability
`p1 = 1 − (2/3) exp(−t)` … the two alternative gene trees … have probability `p2 = p3 = (1/3) exp(−t)`,
Nei 1987”）；同一条也印在 `Phylo/Stat/MSC.lean` docstring 第 **31** 行。
`ChifmanKubatko2015_IdentifiabilityarXiv1406.4811.md` §2.1（第 **329–397** 行，式 (1)）与
§6.2（第 **4201–4311** 行）给出同一模型的 gene tree **密度**，是同一公式的密度层表述。

本文件因此把 `1 − ⅔e^{−t}` 命名为 `pConcordant`、把 `⅓e^{−t}` 命名为 `pDiscordant`。

## M2 的有限化路线

连续时间 Markov 链 / 指数分布的**测度论**部分**没有**形式化（见文末「诚实边界」）。
M2 在这里做成**有限 + 解析**两条腿：

* **有限**：状态 `k` 的可合并对恰 `C(k,2)` 个（`mergePairsFinset`），跳链在它们上**均匀**；
  根种群中 4 条谱系的 6 个首次合并对按 quartet 拓扑分成 3 类、每类恰 2 个；
* **解析**：生存函数 `e^{−d_k t}`、首次合并分布函数 `1 − e^{−d_k t}`、
  期望逗留时间 `2/(k(k−1))` 与望远镜和 `Σ_{k=2}^{n} 2/(k(k−1)) = 2(1 − 1/n) < 2`。

原文位置：`d_k = ½k(k−1)` 见 Kingman 1982 **(1.7)**（**第 135 行**）；
纯死亡过程死亡率见 **第 157–158、881–882、1042 行**；跳链转移概率 `1/C(k,2)` 见 **(2.2)**
（**第 215–217 行**、**第 243 行**、**第 252–256 行**）；`T = Σ_{k=2}^{n} τ_k`、`τ_k` 独立见
**(1.11)**（**第 174–195 行**）；`E[T] = Σ 2/(k(k−1)) → 2` 见 **第 460–469 行**。

## M1 的推导（本文件已形式化的那一步）

物种树 `((a,b),(c,d))`，内部枝长 `t`：

1. `A,B` 两条谱系在内部枝内合并的概率 `1 − e^{−t}`（`d_2 = 1`）⟹ 基因树与物种树一致；
2. 反之（概率 `e^{−t}`）4 条谱系一起进入根部种群，其中**首次**合并均匀地取 `C(4,2) = 6` 个对之一，
   每个 quartet 拓扑恰由 2 个对诱导 ⟹ 每个拓扑 `2/6 = 1/3`。

故 `P(一致) = (1 − e^{−t}) + ⅓e^{−t} = 1 − ⅔e^{−t}`，`P(每个不一致) = ⅓e^{−t}`。
**关键推论**：`t > 0` 时 `⅓e^{−t} < 1 − ⅔e^{−t}` —— 这正是 `MSCFreq.majorizes` 的全部解析内容，
见 `MSCFreq.majorizes_of_quartetWeights`。

## 诚实边界（逐条）

| 条目 | 状态 |
|---|---|
| Kingman 1982 (1.7) `d_k = k(k−1)/2`、逗留密度 | **原文结论**；本文件按其值定义 `kingmanRate` / `survival` |
| Kingman 1982 (2.2) 跳链转移概率 `1/C(k,2)` | **原文结论**；本文件证其**有限核**（等概率 + 总概率 = 1） |
| Kingman 1982 (1.11)/(1.12) `E[T] = Σ 2/(k(k−1))` | **原文结论**；本文件证望远镜和与 `< 2` |
| M1 三拓扑概率 `1 − ⅔e^{−t}`、`⅓e^{−t}` | **本文件已证**（`pConcordant_eq`、`pDiscordant`、三者和 = 1） |
| M1 ⟹ `MSCFreq.majorizes` | **本文件已证**（`MSCFreq.majorizes_of_quartetWeights`） |
| Kingman 1982 (2.3) 绝对分布 `P{ℬ_k = ξ}` | ❌ **未形式化**（见下「仍阻塞」） |
| Kingman 1982 Thm 1/3/4（连续时间链、跳链 × 死亡过程独立性） | ❌ **未形式化** |

### 仍阻塞的一条（明确报告，不硬做）

把 `MSCFreq.freq` 从「公理给定的频率」换成「**由 Kingman 溯祖算出的**理论频率」
（即真正**构造**一个 `MSCFreq` 实例），本批**未完成**。原因是**库缺口，不是文献缺口**：

* 需要连续时间纯死亡过程 + 指数分布 + 「跳链与死亡过程独立」（Kingman Thm 1）的测度论形式化；
  Mathlib 无任何现成 coalescent 库（见 `Phylo/Stat/MSC.lean` docstring 第 22 行）；
* 一般 `n` 的 MSC 分布（Kingman (2.3) / Thm 3）需要「有限集划分 = `Setoid`」上的
  `Fintype` + 跳链绝对概率的归纳，属纯库工程；
* M1（4 元集 ILS 公式）本身**已完备**，且已足以**推出** `MSCFreq.majorizes`
  —— 剩下的只是「把 `freq` 填成 M1 权重」这一**接口**工作（构造 `Cladogram` /
  `DisplaysSplitOn` 见证 + 证明 `QuartetFreq.p_sum_one` 的枚举）。

因此本文件**不**声称把 `MSCFreq.majorizes` 变成了无条件定理，只声称：
**它可由本文件的 M1 推出**（DISPATCH 允许的第二条路线）。
-/

universe u v

namespace Coalescent

/-! ## M2 —— 合并率与跳链（Kingman 1982 §1–§2） -/

/-- **可合并的对数**：`k` 个等价类中可选的二元合并数 `C(k,2)`。

（Kingman 1982 第 **1184** 行：“any one of the `½k(k−1)` relations”；即 (1.5)/(2.2) 的分母。） -/
def mergePairs (k : ℕ) : ℕ := k.choose 2

/-- `C(k,2)` 的 Pascal 递推：`C(n+1,2) = n + C(n,2)`（(1.5) 的「多一条谱系多 `n` 个合并对」）。 -/
theorem mergePairs_succ (n : ℕ) : mergePairs (n + 1) = n + mergePairs n := by
  rw [mergePairs, Nat.choose_succ_succ n 1, Nat.choose_one_right n, mergePairs]

/-- **Kingman 合并率** `d_k = ½k(k−1)`。

原文：Kingman 1982 **(1.7)**（第 **135** 行）`d_k = ½k(k−1)`；`{D_t}` 的死亡率为 `d_k`
（第 **157–158** 行），等价关系链 `{R_t}` 的总转移率 `q_ξ = d_k`（(1.5)–(1.6)，第 **119–137** 行）。 -/
noncomputable def kingmanRate (k : ℕ) : ℝ := (k : ℝ) * ((k : ℝ) - 1) / 2

/-- 合并率的递推 `d_{n+1} = d_n + n`。 -/
theorem kingmanRate_succ (n : ℕ) : kingmanRate (n + 1) = kingmanRate n + (n : ℝ) := by
  rw [kingmanRate, kingmanRate]
  push_cast
  ring

/-- `C(k,2) = ½k(k−1)`：`mergePairs` 与 `kingmanRate` 是同一个数。

⚠️ **不用** `Nat.cast_choose_two`（该常数所在模块 `Mathlib.Data.Nat.Choose.Cast` **不在**
本库现有 import 闭包内，引入它会改变全量 job 数）。改用 `Nat.choose` 的递推
`mergePairs (n+1) = n + mergePairs n` 与 `d_{n+1} = d_n + n` 做归纳 —— 全程只用
已经在闭包内的 `Nat.choose_succ_succ` / `Nat.choose_one_right`。 -/
theorem mergePairs_cast (k : ℕ) : (mergePairs k : ℝ) = kingmanRate k := by
  induction k with
  | zero => simp [mergePairs, kingmanRate]
  | succ n ih =>
    rw [mergePairs_succ, Nat.cast_add, ih, kingmanRate_succ]
    ring

/-- `d_0 = 0`。 -/
theorem kingmanRate_zero : kingmanRate 0 = 0 := by
  rw [kingmanRate]; norm_num

/-- `d_1 = 0`（单个谱系不合并）。 -/
theorem kingmanRate_one : kingmanRate 1 = 0 := by
  rw [kingmanRate]; norm_num

/-- `d_2 = 1`：两条谱系的合并率为 `1`（coalescent units）。 -/
theorem kingmanRate_two : kingmanRate 2 = 1 := by
  rw [kingmanRate]; norm_num

/-- 合并率非负。 -/
theorem kingmanRate_nonneg (k : ℕ) : 0 ≤ kingmanRate k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk, kingmanRate_zero]
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h0 : (0 : ℝ) ≤ (k : ℝ) := by linarith
    have h1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
    rw [kingmanRate, div_eq_mul_inv]
    exact mul_nonneg (mul_nonneg h0 h1) (inv_nonneg.mpr (by norm_num))

/-- `k ≥ 2` 时合并率严格为正。 -/
theorem kingmanRate_pos {k : ℕ} (hk : 2 ≤ k) : 0 < kingmanRate k := by
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h0 : (0 : ℝ) < (k : ℝ) := by linarith
  have h1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  rw [kingmanRate, div_eq_mul_inv]
  exact mul_pos (mul_pos h0 h1) (inv_pos.mpr (by norm_num))

/-- **跳链转移概率**：状态 `k` 下每一个可能的合并对概率相等，皆为 `1/C(k,2)`。

原文：Kingman 1982 **(2.2)**（第 **215–217** 行）`P{ℬ_{k−1} = η | ℬ_k = ξ} = q_{ξη}/q_ξ = 1/C(k,2)`
（`ξ ≺ η`），配合第 **243** 行的 `q_{ξη}/q_ξ` 与第 **252–256** 行的 `q_ξ = d_k`。 -/
noncomputable def jumpProb (k : ℕ) : ℝ := 1 / (mergePairs k : ℝ)

/-- **(2.2) 的归一化**：状态 `k` 下所有合并对的概率之和为 `1`。 -/
theorem mergePairs_mul_jumpProb {k : ℕ} (hk : 2 ≤ k) :
    (mergePairs k : ℝ) * jumpProb k = 1 := by
  have hpos : (0 : ℝ) < (mergePairs k : ℝ) := by
    rw [mergePairs_cast]; exact kingmanRate_pos hk
  rw [jumpProb, mul_one_div]
  exact div_self (ne_of_gt hpos)

/-- 以 `kingmanRate` 表达的跳链转移概率：`1/d_k`（对**所有** `k` 成立，两侧都是 `1/C(k,2)`）。 -/
theorem jumpProb_eq_inv_rate (k : ℕ) : jumpProb k = 1 / kingmanRate k := by
  rw [jumpProb, mergePairs_cast k]

/-- **状态 `k` 的期望逗留时间** `E[τ_k] = 1/d_k = 2/(k(k−1))`。

原文：Kingman 1982 **(1.7)**（第 **129–137** 行）给出 `τ_k` 的密度 `d_k e^{−d_k t}`，
即 `τ_k ~ Exp(d_k)`，期望为 `1/d_k`；(1.11)–(1.12)（第 **174–195** 行）把
`E[T] = Σ_{k=2}^{n} E[τ_k]` 展开，求值见第 **460–469** 行。 -/
noncomputable def sojournMean (k : ℕ) : ℝ := 2 / ((k : ℝ) * ((k : ℝ) - 1))

/-- `d_k · E[τ_k] = 1`（指数分布期望的定义性恒等式）。 -/
theorem kingmanRate_mul_sojournMean {k : ℕ} (hk : 2 ≤ k) :
    kingmanRate k * sojournMean k = 1 := by
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h1 : (k : ℝ) ≠ 0 := by linarith
  have h2 : (k : ℝ) - 1 ≠ 0 := by linarith
  rw [kingmanRate, sojournMean]
  field_simp

/-- 跳链转移概率就是期望逗留时间 `1/d_k`（(2.2) 与 (1.7) 的同一个数；对**所有** `k` 成立）。 -/
theorem jumpProb_eq_sojournMean (k : ℕ) : jumpProb k = sojournMean k := by
  rw [jumpProb, mergePairs_cast k, kingmanRate, sojournMean]
  exact one_div_div _ _

/-- 状态 `2` 的期望逗留时间恰为 `1`。 -/
theorem sojournMean_two : sojournMean 2 = 1 := by
  rw [sojournMean]; norm_num

/-- `E[τ_{m+2}] = 2/((m+2)(m+1))`（望远镜和用的显式形式）。 -/
theorem sojournMean_add_two (m : ℕ) :
    sojournMean (m + 2) = 2 / (((m : ℝ) + 2) * ((m : ℝ) + 1)) := by
  rw [sojournMean]
  push_cast
  ring_nf

/-- **望远镜和**：`Σ_{j=0}^{m−1} 2/((j+2)(j+1)) = 2(1 − 1/(m+1))`。

这正是 Kingman 1982 (1.11)–(1.12)（第 **174–195** 行）与第 **460–469** 行的求和的闭形式
（取 `m = n − 1` 即 `E[T] = 2(1 − 1/n)`）。 -/
theorem sum_sojournMean_range (m : ℕ) :
    ∑ j ∈ Finset.range m, sojournMean (j + 2) = 2 * (1 - 1 / ((m : ℝ) + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, sojournMean_add_two m]
    push_cast
    have h1 : ((m : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((m : ℝ) + 2) ≠ 0 := by positivity
    have h3 : ((m : ℝ) + 1 + 1) ≠ 0 := by positivity
    field_simp
    ring

/-- ★ **Kingman 1982 (1.12)**：`n` 个谱系溯祖到 MRCA 的**期望总时间**
`E[T] = Σ_{k=2}^{n} 2/(k(k−1)) = 2(1 − 1/n)`。

原文位置：第 **174–195** 行（`T = Σ_{k=2}^{n} τ_k`，`τ_k` 相互独立）与
第 **460–469** 行（`Σ_{k=2}^{∞} 2/(k(k−1)) = 2`）。 -/
theorem expectedTotalCoalescenceTime {n : ℕ} (hn : 2 ≤ n) :
    ∑ j ∈ Finset.range (n - 1), sojournMean (j + 2) = 2 * (1 - 1 / (n : ℝ)) := by
  rw [sum_sojournMean_range]
  have h1 : 1 ≤ n := le_trans (by norm_num) hn
  have h : (((n - 1 : ℕ)) : ℝ) + 1 = (n : ℝ) := by
    rw [Nat.cast_sub h1, Nat.cast_one]
    ring
  rw [h]

/-- 期望总时间**严格小于 `2`**（Kingman 1982 第 **460–469** 行：级数和 = `2`）。 -/
theorem expectedTotalCoalescenceTime_lt_two {n : ℕ} (hn : 2 ≤ n) :
    ∑ j ∈ Finset.range (n - 1), sojournMean (j + 2) < 2 := by
  rw [expectedTotalCoalescenceTime hn]
  have hn' : (0 : ℝ) < (n : ℝ) := by
    have h : (0 : ℕ) < n := lt_of_lt_of_le (by norm_num) hn
    exact_mod_cast h
  have h : 0 < 1 / (n : ℝ) := one_div_pos.mpr hn'
  linarith

/-! ## M2 —— 跳链的**有限**核 -/

/-- 状态 `k` 下所有可能的合并：`{0,…,k−1}` 的二元子集全体（`k.choose 2` 个）。 -/
def mergePairsFinset (k : ℕ) : Finset (Finset (Fin k)) := Finset.univ.powersetCard 2

/-- `mergePairsFinset k` 的基数恰是 `C(k,2)`。 -/
theorem card_mergePairsFinset (k : ℕ) : (mergePairsFinset k).card = mergePairs k := by
  simp [mergePairsFinset, mergePairs]

/-- ★ **(2.2) 的有限核**：状态 `k` 下每个合并对等概率 `1/C(k,2)`，总概率恰为 `1`。 -/
theorem sum_uniform_jumpProb {k : ℕ} (hk : 2 ≤ k) :
    ∑ _p ∈ mergePairsFinset k, jumpProb k = 1 := by
  rw [Finset.sum_const, card_mergePairsFinset, nsmul_eq_mul]
  exact mergePairs_mul_jumpProb hk

/-- `C(4,2) = 6`：根种群中 4 条谱系的可能首次合并对个数。 -/
theorem card_mergePairsFinset_four : (mergePairsFinset 4).card = 6 := by
  rw [card_mergePairsFinset]
  decide

/-- ★★ **根种群的对称性**：4 条谱系的 `6` 个首次合并对按诱导的 quartet 拓扑分成 **3 类、每类恰 2 个**。

（`0 ∈ p ↔ 1 ∈ p` 恰刻画「`0,1` 在首次合并中同类」的对：`{0,1}` 与 `{2,3}`；
`0 ∈ p ↔ 2 ∈ p` 给出 `{0,2}` 与 `{1,3}`；`0 ∈ p ↔ 3 ∈ p` 给出 `{0,3}` 与 `{1,2}`。
配合 (2.2) 的均匀性，每个拓扑的概率为 `2/6 = 1/3`。） -/
theorem root_quartet_classes :
    (((mergePairsFinset 4).filter fun p => ((0 : Fin 4) ∈ p ↔ (1 : Fin 4) ∈ p)).card = 2) ∧
    (((mergePairsFinset 4).filter fun p => ((0 : Fin 4) ∈ p ↔ (2 : Fin 4) ∈ p)).card = 2) ∧
    (((mergePairsFinset 4).filter fun p => ((0 : Fin 4) ∈ p ↔ (3 : Fin 4) ∈ p)).card = 2) := by
  decide

/-- 由 `root_quartet_classes`：根种群中每个 quartet 拓扑的概率为 `2/6 = 1/3`。 -/
theorem root_topologyProb :
    (2 : ℝ) / ((mergePairsFinset 4).card : ℝ) = 1 / 3 := by
  rw [card_mergePairsFinset_four]
  norm_num

/-! ## M2 —— 生存函数与首次合并时间（(1.7) 的解析层） -/

/-- **生存函数**：`k` 条谱系在时间 `t` 内**未发生任何合并**的概率 `e^{−d_k t}`。

原文：Kingman 1982 **(1.7)**（第 **129–137** 行）给出逗留时间密度 `d_k e^{−d_k t}`，
故 `P(τ_k > t) = e^{−d_k t}`（指数分布的生存函数）。 -/
noncomputable def survival (k : ℕ) (t : ℝ) : ℝ := Real.exp (-(kingmanRate k) * t)

/-- **首次合并时间的分布函数** `1 − e^{−d_k t}`（(1.7) 的积分）。 -/
noncomputable def firstMergeCDF (k : ℕ) (t : ℝ) : ℝ := 1 - survival k t

/-- `survival k 0 = 1`。 -/
theorem survival_zero (k : ℕ) : survival k 0 = 1 := by
  rw [survival, mul_zero, Real.exp_zero]

/-- 生存函数严格为正。 -/
theorem survival_pos (k : ℕ) (t : ℝ) : 0 < survival k t := Real.exp_pos _

/-- **指数分布的无记忆性 / 半群性质**：`e^{−d_k(s+t)} = e^{−d_k s} · e^{−d_k t}`。 -/
theorem survival_add (k : ℕ) (s t : ℝ) : survival k (s + t) = survival k s * survival k t := by
  unfold survival
  rw [mul_add, Real.exp_add]

/-- `t ≥ 0` 时 `survival k t ≤ 1`。 -/
theorem survival_le_one (k : ℕ) {t : ℝ} (ht : 0 ≤ t) : survival k t ≤ 1 := by
  rw [survival]
  calc Real.exp (-(kingmanRate k) * t) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (by nlinarith [kingmanRate_nonneg k, ht])
    _ = 1 := Real.exp_zero

/-- `k ≥ 2` 且 `t > 0` 时生存概率**严格小于 `1`**。 -/
theorem survival_lt_one {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : 0 < t) : survival k t < 1 := by
  have hr : 0 < kingmanRate k := kingmanRate_pos hk
  rw [survival]
  calc Real.exp (-(kingmanRate k) * t) < Real.exp 0 :=
        Real.exp_lt_exp.mpr (by nlinarith)
    _ = 1 := Real.exp_zero

/-- 生存函数在 `[0, ∞)` 上**严格递减**。 -/
theorem survival_lt_survival {k : ℕ} (hk : 2 ≤ k) {s t : ℝ} (hst : s < t) :
    survival k t < survival k s := by
  have hr : 0 < kingmanRate k := kingmanRate_pos hk
  rw [survival, survival, Real.exp_lt_exp]
  nlinarith

/-- `d_2 = 1` 时的生存函数就是 `e^{−t}`。 -/
theorem survival_two (t : ℝ) : survival 2 t = Real.exp (-t) := by
  rw [survival, kingmanRate_two]
  ring_nf

/-- `d_2 = 1` 时的首次合并分布函数是 `1 − e^{−t}`。 -/
theorem firstMergeCDF_two (t : ℝ) : firstMergeCDF 2 t = 1 - Real.exp (-t) := by
  rw [firstMergeCDF, survival_two]

/-- `t ≥ 0` 时 `0 ≤ firstMergeCDF k t`。 -/
theorem firstMergeCDF_nonneg (k : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ firstMergeCDF k t := by
  have h := survival_le_one k ht
  rw [firstMergeCDF]
  linarith

/-- `k ≥ 2`、`t > 0` 时首次合并概率严格为正。 -/
theorem firstMergeCDF_pos {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : 0 < t) :
    0 < firstMergeCDF k t := by
  have h := survival_lt_one hk ht
  rw [firstMergeCDF]
  linarith

/-! ## M1 —— 4 元集 ILS 公式（`t` = 内部枝长，coalescent units） -/

/-- **一致（concordant）quartet 的概率** `P = (1 − e^{−t}) + ⅓e^{−t}`。

推导（见文件头）：`1 − e^{−t}` = `A,B` 在内部枝内合并的概率（`d_2 = 1`）；
`e^{−t}` = 未合并而进入根种群的概率，此时 4 条谱系首次合并均匀取 `C(4,2) = 6` 个对之一，
其中 `2/6 = 1/3` 给出与物种树一致的拓扑。

原文：AllmanDegnanRhodes2011 第 **356–360** 行（`1 − (2/3)exp(−t)`）。 -/
noncomputable def pConcordant (t : ℝ) : ℝ := (1 - Real.exp (-t)) + (1 / 3) * Real.exp (-t)

/-- **不一致（discordant）quartet 的概率**（两个不一致拓扑各为这个值）`⅓e^{−t}`。

原文：AllmanDegnanRhodes2011 第 **359–360** 行（`p2 = p3 = (1/3) exp(−t)`）。 -/
noncomputable def pDiscordant (t : ℝ) : ℝ := (1 / 3) * Real.exp (-t)

/-- ★★★ **M1 闭形式**：`P(一致) = 1 − ⅔e^{−t}`。 -/
theorem pConcordant_eq (t : ℝ) : pConcordant t = 1 - (2 / 3) * Real.exp (-t) := by
  rw [pConcordant]; ring

/-- `pDiscordant` 就是 `⅓ · survival 2`（与 M2 的 `e^{−t}` 接上）。 -/
theorem pDiscordant_eq_survival (t : ℝ) : pDiscordant t = (1 / 3) * survival 2 t := by
  rw [pDiscordant, survival_two]

/-- `pConcordant` 就是 `firstMergeCDF 2 t + ⅓ · survival 2 t`（M1 由 M2 的两项拼成）。 -/
theorem pConcordant_eq_kingman (t : ℝ) :
    pConcordant t = firstMergeCDF 2 t + (1 / 3) * survival 2 t := by
  rw [pConcordant, firstMergeCDF_two, survival_two]

/-- ★ **全概率为 `1`**：三个 quartet 拓扑概率之和 `= 1`。 -/
theorem pConcordant_add_two_pDiscordant (t : ℝ) :
    pConcordant t + pDiscordant t + pDiscordant t = 1 := by
  rw [pConcordant_eq, pDiscordant]; ring

/-- 一致概率 = `1` 减两个不一致概率之和。 -/
theorem pConcordant_eq_one_sub_two_pDiscordant (t : ℝ) :
    pConcordant t = 1 - 2 * pDiscordant t := by
  rw [pConcordant_eq, pDiscordant]; ring

/-- 不一致概率严格为正。 -/
theorem pDiscordant_pos (t : ℝ) : 0 < pDiscordant t := by
  rw [pDiscordant]; positivity

/-- `t > 0` 时不一致概率严格小于 `1/3`（ILS 概率有界）。 -/
theorem pDiscordant_lt_third {t : ℝ} (ht : 0 < t) : pDiscordant t < 1 / 3 := by
  have h : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  rw [pDiscordant]
  linarith

/-- `t ≥ 0` 时一致概率非负。

⚠️ **`0 ≤ t` 是必需的**：`t < 0`（内部枝长无意义）时 `1 − ⅔e^{−t}` 可为负
（如 `t = −1` 时约 `−0.81`）。 -/
theorem pConcordant_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ pConcordant t := by
  have h : Real.exp (-t) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  rw [pConcordant_eq]
  linarith

/-- 一致概率不超过 `1`。 -/
theorem pConcordant_le_one (t : ℝ) : pConcordant t ≤ 1 := by
  have h : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  rw [pConcordant_eq]
  linarith

/-- ★★★ **`MSCFreq.majorizes` 的解析核**：`t > 0` 时不一致概率**严格小于**一致概率。 -/
theorem pDiscordant_lt_pConcordant {t : ℝ} (ht : 0 < t) : pDiscordant t < pConcordant t := by
  have h : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  rw [pConcordant_eq, pDiscordant]
  linarith

/-- ★ 严格性的**充要条件**：`t ≥ 0` 时「不一致 < 一致」⟺「内部枝长 `t > 0`」。

（`t = 0` 对应星形树，三个拓扑各 `1/3`，无从分辨；这正是 MSC 需要非零内部枝的原因。） -/
theorem pDiscordant_lt_pConcordant_iff {t : ℝ} (ht : 0 ≤ t) :
    pDiscordant t < pConcordant t ↔ 0 < t := by
  refine ⟨fun h => ?_, pDiscordant_lt_pConcordant⟩
  by_contra hle
  simp only [not_lt] at hle
  have h0 : t = 0 := le_antisymm hle ht
  have hlt : ¬ (pDiscordant 0 < pConcordant 0) := by
    rw [pConcordant_eq, pDiscordant, neg_zero, Real.exp_zero]
    norm_num
  rw [h0] at h
  exact hlt h

/-- `t = 0`（星形树）时一致概率为 `1/3`。 -/
theorem pConcordant_zero : pConcordant 0 = 1 / 3 := by
  rw [pConcordant_eq, neg_zero, Real.exp_zero]; norm_num

/-- `t = 0`（星形树）时不一致概率也为 `1/3`。 -/
theorem pDiscordant_zero : pDiscordant 0 = 1 / 3 := by
  rw [pDiscordant, neg_zero, Real.exp_zero]; norm_num

/-- ★ **`QuartetFreq` 归一化约定下的权重和**：`QuartetFreq` 在**有向** split 上求和为 `1`
（`QuartetFreq.p_sum_one`），而 `QuartetFreq.p_swap` 强制两侧相等，故每个无向 quartet 拓扑的
概率须**平分**到 `q` 与 `q.swap`。4 元集上 `2|2` 部分共 6 个有向 split
（1 个一致拓扑 + 2 个不一致拓扑），其权重和恰为 `1`。 -/
theorem directed_quartetWeights_sum (t : ℝ) :
    pConcordant t / 2 + pConcordant t / 2 + (pDiscordant t / 2) * 4 = 1 := by
  rw [pConcordant_eq, pDiscordant]; ring

/-! ## M1 ⟹ `MSCFreq.majorizes`（DISPATCH 允许的第二条路线） -/

/-- ★★★ **`MSCFreq.majorizes` 由本文件的 M1 权重推出**。

`MSCFreq.majorizes`（`Phylo/Stat/MSC.lean` 第 **110–111** 行）是 MSC 侧**唯一**进入后续
一致性定理的「统计核心」。本定理证明：只要 4 元集 `S` 上的频率**是 M1 的两个值**
（一致 `1 − ⅔e^{−t}`、不一致 `⅓e^{−t}`，`t > 0`），该字段的严格不等式即为**定理**。

换言之：`MSCFreq.majorizes` 并非独立于 coalescent 的额外假设 —— 它的**全部数学内容**
就是 `pDiscordant_lt_pConcordant`。剩下的**接口**工作（把 `freq` 定义成 M1 权重并给出
`Cladogram` / `DisplaysSplitOn` 见证）见文件头「仍阻塞」。 -/
theorem MSCFreq.majorizes_of_quartetWeights {X : Type u} [Fintype X] [DecidableEq X]
    (m : MSCFreq.{u, v} X) (S : Finset X) (hS : S.card = 4) {t : ℝ} (ht : 0 < t)
    (hconc : m.freq.p S hS (m.q S hS) = pConcordant t)
    (hdisc : ∀ r : Split ↥S, r ≠ m.q S hS → r ≠ (m.q S hS).swap →
      m.freq.p S hS r = pDiscordant t) :
    ∀ r : Split ↥S, r ≠ m.q S hS → r ≠ (m.q S hS).swap →
      m.freq.p S hS r < m.freq.p S hS (m.q S hS) := by
  intro r hr hrs
  rw [hdisc r hr hrs, hconc]
  exact pDiscordant_lt_pConcordant ht

/-- 同一条的 **`QuartetFreq` 层**版本（不涉及底层树 `Cladogram`）。 -/
theorem quartetFreq_majorizes_of_quartetWeights {X : Type u} [Fintype X] [DecidableEq X]
    (D : QuartetFreq X) (S : Finset X) (hS : S.card = 4) (q : Split ↥S)
    {t : ℝ} (ht : 0 < t)
    (hconc : D.p S hS q = pConcordant t)
    (hdisc : ∀ r : Split ↥S, r ≠ q → r ≠ q.swap → D.p S hS r = pDiscordant t) :
    ∀ r : Split ↥S, r ≠ q → r ≠ q.swap → D.p S hS r < D.p S hS q := by
  intro r hr hrs
  rw [hdisc r hr hrs, hconc]
  exact pDiscordant_lt_pConcordant ht

end Coalescent
