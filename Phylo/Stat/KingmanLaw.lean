/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.KingmanCoalescent
import Phylo.Stat.KingmanJumpChain

/-!
# `Phylo.Stat.KingmanLaw` —— 把 **跳链律** 与 **逗留时间律** 接成 Theorem 1

W10a（`Phylo/Stat/KingmanJumpChain.lean`，K82 (2.1)/(2.2) 的组合核）与
W10b（`Phylo/Stat/KingmanCoalescent.lean`，K82 (1.7) 与 **Theorem 1**）是**互相解耦**做的：
W10b 把联合律写成对**任意**跳链测度 `μ` 都成立的参数形式
`nCoalescentLaw μ n = μ.prod (sojournJointLaw n)`。
**本文件把参数 `μ` 实例化成 (2.2) 给出的跳链律** —— 于是 Theorem 1 的
「**跳链 ⊗ 独立指数**」在**具体对象**上闭合。

## K82 的原文（Theorem 1，第 210–215 行）

> In an n-coalescent, the death process `(D_t ; t ≥ 0)` and the jump chain
> `(S_k ; k = n, n−1, …, 1)` are **independent**, and `R_t = S_{D_t}` for all `t ≥ 0`.

## 本文件的形式化口径（**措辞纪律：写清做到了哪一层**）

* **已做**：对**每一个层 `k`**，跳链在 `k` 块上的**边缘律** `jumpMeasure n k`
  （**由 (2.2) 的绝对概率 `jumpWeight` / `partitionProb` 构造**，`IsProbabilityMeasure` **已证**）
  与逗留时间向量 `sojournJointLaw n`（K82 (1.11) 的独立指数乘积）拼成乘积测度，
  并用 **真 `IndepFun`** 证明两者独立（不是「联合律 = 乘积」的代用语）。
* **未做**：把「**整条**跳链 `(S_n, S_{n−1}, …, S_1)`」作为**轨迹空间**上的对象；
  以及 `R_t = S_{D_t}` 这一**过程恒等式**（需要连续时间的 `D_t`，本库没有）。
  这两条都在文件末尾的诚实边界表里写明。
-/

noncomputable section

open Classical MeasureTheory

namespace Phylo.Stat.KingmanLaw

-- `Measure.pi` / `Measure.prod` 的概率性必须从「因子是概率测度」的实例取，
-- 而 `haveI` 对 `Prop` 会触发 `linter.style.haveILetI`（告警会破坏「0 字节」判据）。
-- 库内已有先例（`PhylogramContract.lean`、`SplitsDetermineTree.lean`）。
set_option linter.style.haveILetI false

open Phylo.Stat.KingmanJumpChain (PartK jumpWeight jumpWeight_nonneg jumpWeight_sum_eq_one)
open Phylo.Stat.KingmanCoalescent (nCoalescentLaw sojournJointLaw indepFun_fst_snd_nCoalescent
  isProbabilityMeasure_nCoalescentLaw fst_nCoalescentLaw snd_nCoalescentLaw)

/-- `PartK n k`（`k` 块划分）是**有限**类型，取**离散**可测空间 `⊤`。

（`Subtype.instMeasurableSpace` 那条通用路径要求 `MeasurableSpace (Part n)`，而 `Part n` 上
没有可测空间实例，故这里直接给出 —— 它只服务于本文件的测度构造。） -/
instance instMeasurableSpacePartK (n k : ℕ) : MeasurableSpace (PartK n k) := ⊤

/-- ★★★ **跳链在 `k` 层上的概率测度**：把 (2.2) 的绝对概率（= `jumpWeight` = `partitionProb`）
当成点质量权重，在有限类型 `PartK n k` 上求和。 -/
noncomputable def jumpMeasure (n k : ℕ) : Measure (PartK n k) :=
  Measure.sum fun P => ENNReal.ofReal (jumpWeight n k P) • Measure.dirac P

/-- `jumpMeasure` 在任意集合上的取值（有限和）。 -/
theorem jumpMeasure_apply (n k : ℕ) (s : Set (PartK n k)) :
    jumpMeasure n k s
      = ∑ P : PartK n k, ENNReal.ofReal (jumpWeight n k P) * (Measure.dirac P : Measure (PartK n k)) s := by
  rw [jumpMeasure, Measure.sum_apply_of_countable, tsum_fintype]
  exact Finset.sum_congr rfl fun P _ => by rw [Measure.smul_apply, smul_eq_mul]

/-- ★★★ **它是概率测度**（由 (2.2) 的归一化 `jumpWeight_sum_eq_one`）。 -/
theorem isProbabilityMeasure_jumpMeasure (n k : ℕ) (hk0 : 1 ≤ k) (hkn : k ≤ n) :
    IsProbabilityMeasure (jumpMeasure n k) := by
  refine ⟨?_⟩
  rw [jumpMeasure_apply]
  have h1 : ∀ P : PartK n k, (Measure.dirac P : Measure (PartK n k)) Set.univ = 1 :=
    fun P => Measure.dirac_apply_of_mem (Set.mem_univ P)
  rw [Finset.sum_congr rfl (fun P _ => by rw [h1 P, mul_one])]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun P _ => jumpWeight_nonneg n k P)]
  rw [jumpWeight_sum_eq_one n k hk0 hkn, ENNReal.ofReal_one]

/-- ★★★ **Theorem 1（分层形式）**：跳链在 `k` 层的状态与 `n−1` 个逗留时间**独立**。

K82 Theorem 1 说**整条**跳链与死亡过程独立；本定理是它在**每个层 `k`** 上的实例 ——
两半都是**具体对象**：左边是 (2.2) 给出的跳链律 `jumpMeasure n k`，
右边是 (1.11) 的独立指数乘积 `sojournJointLaw n`。 -/
theorem indepFun_jumpChain_sojourn (n k : ℕ) (hk0 : 1 ≤ k) (hkn : k ≤ n) (hn : 2 ≤ n) :
    ProbabilityTheory.IndepFun Prod.fst Prod.snd (nCoalescentLaw (jumpMeasure n k) n) := by
  haveI := isProbabilityMeasure_jumpMeasure n k hk0 hkn
  exact indepFun_fst_snd_nCoalescent (jumpMeasure n k) hn

/-- ★★ **联合律的两个边缘**：第一个是跳链律，第二个是独立指数乘积。
（第一边缘**不需要** `IsProbabilityMeasure`，见 `fst_nCoalescentLaw`。） -/
theorem fst_nCoalescentLaw_jumpMeasure (n k : ℕ) (_hk0 : 1 ≤ k) (_hkn : k ≤ n) (hn : 2 ≤ n) :
    (nCoalescentLaw (jumpMeasure n k) n).fst = jumpMeasure n k :=
  fst_nCoalescentLaw (jumpMeasure n k) (n := n) hn

theorem snd_nCoalescentLaw_jumpMeasure (n k : ℕ) (hk0 : 1 ≤ k) (hkn : k ≤ n) (hn : 2 ≤ n) :
    (nCoalescentLaw (jumpMeasure n k) n).snd = sojournJointLaw n := by
  haveI := isProbabilityMeasure_jumpMeasure n k hk0 hkn
  exact snd_nCoalescentLaw (jumpMeasure n k) (n := n) hn

/-- ★★★ **n-溯祖的联合律是概率测度**（(2.2) 的跳链律 ⊗ (1.11) 的独立指数）。 -/
theorem isProbabilityMeasure_nCoalescentLaw_jumpMeasure (n k : ℕ) (hk0 : 1 ≤ k) (hkn : k ≤ n)
    (hn : 2 ≤ n) : IsProbabilityMeasure (nCoalescentLaw (jumpMeasure n k) n) := by
  haveI := isProbabilityMeasure_jumpMeasure n k hk0 hkn
  exact isProbabilityMeasure_nCoalescentLaw (jumpMeasure n k) hn

/-! ## 轨迹律的**阻塞点**（精确记为可检查的缺口，**不是** `axiom`、**不是** `sorry`）

「层间一致性的测度层形式」与「整条跳链的轨迹空间对象」都归结到**同一个计数**：
**从 `k+1` 块划分 `Q` 出发，一次合并的「去向」恰有 `C(k+1,2)` 个**
（跳链每步在这 `C(k+1,2)` 个去向里**均匀**挑一个 —— 这就是 (2.1)）。
W10a 已给出**所需的两块拼图**：
* `merge_outcomes_card`：`Q.parts` 的**无序块对**恰 `C(|Q|,2)` 个；
* `card_pairSet`：使 `Q` 合并到 `P` 的**有序**块对恰 `2` 个（`⟺ MergeInto Q P`）；
* `mergeOf_eq` / `mem_offDiag` / `card_offDiag`：把「有序块对 ↔ 去向」接起来。

⇒ 两个缺口都只差**一个纤维求和**（`Finset.card_eq_sum_card_fiberwise` + `card_pairSet`），
本文件**未做**（时间所限，如实记录）。 -/

/-- ❌→✅ **缺口：一次合并的「去向」计数** —— (2.1) 的**正向**语句，
也是「跳链每步均匀挑一个块对」的**计数依据**。
`Q : PartK n (k+1)` 的一步去向 `P : PartK n k`（`MergeInto Q.1 P.1`）恰有 `C(k+1,2)` 个。

**已由 `Phylo/Stat/KingmanStep.lean` 补证**（`card_mergeTargets_cast`，**结构路线**、
纯内核：`card_pairSet` ＋ `card_offDiag` ＋ 按去向的纤维分解）。本 `def` 保留为**接口/记录**。 -/
def mergeTargets_gap : Prop :=
  ∀ (n k : ℕ), 1 ≤ k → ∀ Q : Phylo.Stat.KingmanJumpChain.PartK n (k + 1),
    ((Finset.univ.filter (fun P : Phylo.Stat.KingmanJumpChain.PartK n k =>
        Phylo.Stat.KingmanJumpChain.MergeInto Q.1 P.1)).card) = (k + 1).choose 2

/-- ❌ **缺口：层间一致性的测度层形式** ——
把 `Phylo.Stat.KingmanJumpChain.partitionProb_merge_recursion`（**实数层**）升到**测度层**：
`k` 层的律是 `k+1` 层的律经「均匀随机合并」推前。
（证明需要上面的 `mergeTargets_gap` ＋ 一步联合律的两个边缘求和。） -/
def jumpMeasure_step_gap : Prop :=
  ∀ (n k : ℕ), 1 ≤ k → k < n →
    ∃ step : Measure (Phylo.Stat.KingmanJumpChain.PartK n (k + 1) ×
        Phylo.Stat.KingmanJumpChain.PartK n k),
      IsProbabilityMeasure step ∧ step.fst = jumpMeasure n (k + 1) ∧ step.snd = jumpMeasure n k

/-! ## 诚实边界（逐条）

| 条目 | 状态 |
|---|---|
| K82 (2.2) 的跳链**绝对概率** | ✅ 在 W10a（`jumpWeight` = `partitionProb`，`+ partitionProb_sum_eq_one` / `jumpWeight_sum_eq_one`） |
| K82 (1.7) 的逗留时间**律** `Exp(d_k)` | ✅ 在 W10b（`sojournLaw` / `isProbabilityMeasure_sojournLaw` / `sojournLaw_Ioi`） |
| K82 **Theorem 1 的独立性** | ✅ **本文件**：每个层 `k` 上 `IndepFun`（**真 `IndepFun`**，两个边缘也证出） |
| 「**整条**跳链 `(S_n,…,S_1)` 作为轨迹空间对象」 | ❌ **未做**：需要 `PartK n n × … × PartK n 1` 上的**链式**联合律与转移核，本文件只做**单层**边缘（阻塞点 = 下面的两个缺口） |
| `R_t = S_{D_t}`（过程恒等式） | ❌ **未做**：需要连续时间的死亡过程 `(D_t)`（本库无 CTMC，见 W10 的路线决策） |
| 层间一致性的**测度层**形式 | ❌ **未做**（W10a 只有**实数层**的 `partitionProb_merge_recursion`）—— 已**精确记为** `jumpMeasure_step_gap`，其唯一阻塞点是 `mergeTargets_gap` |
-/

end Phylo.Stat.KingmanLaw
