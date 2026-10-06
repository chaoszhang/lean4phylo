/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Phylo.Quartet
import Phylo.Algorithm.NJ

/-!
# `Phylo.Stat.MSC` —— 多物种溯祖（MSC）的 quartet 侧**公理化接口**

`CONCEPTS.md` §3.11：MSC 下基因树可与物种树因**不完全谱系分选**（ILS）而不同；
物种树推断的「统计一致性」正是「数据量 → ∞ 时输出 → 真物种树」。

## 决策（2026-10-07 老师定）

**先把 MSC 公理化**（本文件）；**把「证明 MSC」本身另立为课题**（`Phylo.Stat.MSCProof`）。
理由：Mathlib 无 Kingman coalescent / MSC 的任何现成库，从零建是数万行工程；
而四个算法（ASTRAL / parsimony / CASTER / NJst）一致性证明的**组合骨架**
与概率层正交，可先行完成。

## 公理化进来的那一条

MSC 对 quartet 侧只有一个输出是「统计」必需的：

> **对 4 个物种，与真树一致的 quartet 拓扑的概率严格大于任何竞争拓扑。**
> （Kingman coalescent：三个拓扑概率为 `1 - ⅔e^{-t}`、`⅓e^{-t}`、`⅓e^{-t}`，`t` 为内部枝长。）

本文件把它打包成结构 `MSCFreq`（真树 + 频率 + 该不等式），
后续一切一致性定理都以「给定一个 `MSCFreq`」为假设。

## 为什么用**结构**而非 `∃`

`Exists.choose` 在 Lean 4 中**不做 ι-归约**（`Classical.choice` 是公理），
若把「真树的 quartet」写成 `∃` 再 `.choose`，就无法把 `p S hS h.choose` 与
具体表达式对齐。改成**结构字段**（`MSCFreq.q`）后一切是投影，可自由展开。

## 一致性证法的三层结构

```
① 理想一致性   MSCFreq m ⟹ E m.freq ≅ m.tree         （组合核心，各算法分头证）
② gap 引理     真树的得分严格高于次优 ⟹ 存在正 gap δ   （有限性，一次搞定）
③ 稳定性       频率扰动 < δ/界 ⟹ argmax 不变           （通用引擎，一次搞定）
──────────────────────────────────────────────────
⟹ 统计一致性   （① + ② + ③ + MSC 大数定律）
```

`② ③` 与算法无关，写在 `Phylo.Stat.Stability`；① 分头写在
`ASTRAL` / `CASTER` / `NJst` / `Parsimony`。
-/

universe u v

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- 树 `T` 在 4-元支撑集 `S` 上**展示**有向 split `q`：`q.sideA` 恰是 `T` 某条边的一侧
（限制到 `S` 上）。即 `q` 就是 `T` 在 `S` 上诱导的那个 quartet（带方向）。 -/
def Cladogram.DisplaysSplitOn (T : Cladogram.{u, v} X) (S : Finset X)
    (q : Split ↥S) : Prop :=
  ∃ s : Split X, T.IsSplitOf s ∧ ∀ x : ↥S, (x ∈ q.sideA ↔ x.1 ∈ s.sideA)

/-- **quartet 频率表**：每个 4-元叶集上一个概率分布。

分布定义在**有向** split（`Split ↥S`）上，但对 `swap` 不变 —— 于是它自然下降为
`S` 上的**无向** quartet 拓扑（3 类）上的分布，这正是 MSC 的样本空间。 -/
structure QuartetFreq (X : Type u) [Fintype X] [DecidableEq X] where
  /-- 概率。 -/
  p : (S : Finset X) → S.card = 4 → Split ↥S → ℝ
  /-- 非负。 -/
  p_nonneg : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), 0 ≤ p S hS q
  /-- 全概率为 1。 -/
  p_sum_one : ∀ (S : Finset X) (hS : S.card = 4), ∑ q : Split ↥S, p S hS q = 1
  /-- **交换两侧不改变概率**（quartet 无向）。 -/
  p_swap : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), p S hS q.swap = p S hS q

/-- **quartet 树**：一棵树 + 每个 4-元集上一个被它展示的 quartet（选一侧）。

ASTRAL 型算法的**候选空间**。（对 binary 树恒存在，见 `Phylo.Stat.QuartetDecides`。） -/
structure QuartetTree (X : Type u) [Fintype X] [DecidableEq X] where
  /-- 底层树。 -/
  tree : Cladogram.{u, v} X
  /-- 每个 4-元集上选定的 quartet。 -/
  q : (S : Finset X) → (hS : S.card = 4) → Split ↥S
  /-- 选定的 quartet 确实被树展示。 -/
  displays : ∀ (S : Finset X) (hS : S.card = 4), tree.DisplaysSplitOn S (q S hS)

/-- ★★ **MSC 型 quartet 数据**（**公理化**，2026-10-07 老师定）。

打包「真物种树 + 其 quartet 选择 + 观测频率 + **MSC 的核心不等式**」：

> **真树诱导的 quartet 在每个 4-元集上概率唯一最大（模 `swap`）。**

MSC 的全部统计内容只经 `majorizes` 这一条进入后续定理。 -/
structure MSCFreq (X : Type u) [Fintype X] [DecidableEq X] extends QuartetTree (X := X) where
  /-- 观测到的 quartet 频率（理想样本下 = MSC 理论分布）。 -/
  freq : QuartetFreq X
  /-- ★ **MSC 核心**：真树的 quartet 唯一概率最大（模 `swap`）。 -/
  majorizes : ∀ (S : Finset X) (hS : S.card = 4) (r : Split ↥S),
    r ≠ q S hS → r ≠ (q S hS).swap → freq.p S hS r < freq.p S hS (q S hS)

namespace MSCFreq

/-- `MSCFreq` 的真树（投影别名）。 -/
abbrev speciesTree (m : MSCFreq.{u, v} X) : Cladogram.{u, v} X := m.tree

/-- **MSC 的局部形式（弱）**：真树 quartet 的概率 ≥ 任何竞争 quartet 的概率。

（`majorizes` 的严格不等式在「模 `swap`」的两类上取等号，此处并成一个 `≤`。） -/
theorem p_le (m : MSCFreq.{u, v} X) (S : Finset X) (hS : S.card = 4)
    (r : Split ↥S) : m.freq.p S hS r ≤ m.freq.p S hS (m.q S hS) := by
  by_cases h1 : r = m.q S hS
  · rw [h1]
  · by_cases h2 : r = (m.q S hS).swap
    · rw [h2, m.freq.p_swap]
    · exact (m.majorizes S hS r h1 h2).le

end MSCFreq

/-- **频率的 `ε`-接近**（逐点，两个频率表之间）—— 稳定性的度量。 -/
def FreqClose (D D' : QuartetFreq X) (ε : ℝ) : Prop :=
  ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), |D.p S hS q - D'.p S hS q| < ε

/-- **物种树估计量**：从 quartet 频率给出一个树。

（ASTRAL / CASTER 是这一形状；NJst / parsimony 经各自的「再参数化」也归结到这里。） -/
abbrev Estimator (X : Type u) [Fintype X] [DecidableEq X] :=
  QuartetFreq X → Cladogram.{u, v} X

/-- **理想样本统计一致性**（一致性证明的**组合核心**）：

对任何 MSC 数据，估计量恢复真树（**同构意义**下 —— 拓扑是唯一能确定的）。

各算法分头证这一条：ASTRAL/CASTER 靠「真树唯一最大化 quartet 得分」，
NJst 靠「平均距离满足四点点条件」，parsimony 靠「最简树 = 真树」。 -/
def IdeallyConsistent (E : QuartetFreq X → Cladogram.{u, v} X) : Prop :=
  ∀ m : MSCFreq.{u, v} X, Nonempty (Iso (E m.freq) m.tree)

/-! ## 概率层：大数定律（同样公理化） -/

/-- **（公理化）MSC 采样 + 大数定律**。

* `emp n` —— `n` 个独立位点的**经验** quartet 频率；
* `converges` —— **MSC 大数定律**：经验频率最终 `ε`-接近理论频率。

⚠️ **诚实边界**：`converges` 取的是「**最终 `ε`-接近**」这一**确定性**形式，
把概率层的「几乎必然收敛」抽象掉了。把 `converges` 换成真概率陈述
（需要概率空间 + 强大数定律）即得真·依概率一致性 —— 课题 `Phylo.Stat.MSCProof`。

这样切分的好处：一致性定理的**形状**与算法内容现在就能定死，
将来只需替换 `converges` 这一个字段。 -/
structure MSCSampling (X : Type u) [Fintype X] [DecidableEq X] where
  /-- 第 `n` 个样本（`n` 个位点）的经验 quartet 频率。 -/
  emp : ℕ → QuartetFreq X
  /-- ★ **MSC 大数定律**（公理化）：经验频率最终 `ε`-接近理论频率。 -/
  converges : ∀ m : MSCFreq.{u, v} X, ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n ≥ N, FreqClose (emp n) m.freq ε

/-- **统计一致性**（依概率，经大数定律）：

估计量 `E` 在 MSC 采样下最终恢复真树的**拓扑**。

⚠️ 这是 `MSCSampling.converges`（公理化的大数定律）+ 组合核心（① + ② + ③）的推论；
不是从概率空间证出来的。见 `Phylo.Stat.Stability`。 -/
def StatisticallyConsistent (E : QuartetFreq X → Cladogram.{u, v} X)
    (sm : MSCSampling X) : Prop :=
  ∀ m : MSCFreq.{u, v} X, ∃ N : ℕ, ∀ n ≥ N, Nonempty (Iso (E (sm.emp n)) m.tree)
