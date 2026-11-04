/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERWeights
import Phylo.AttesonRadius

/-!
# `Phylo.Stat.CASTERNJ` —— CASTER-NJ 的两条**登记缺口**（W44 · L5b / L5a 的备选出口）

## 定位

**CASTER-NJ**（对归一化 `D̃` 跑 NJ）与库内既有的 CASTER 定理 1/2（贪心放置）是**不同下游**。
本文件不证任何新数学，只把「CASTER-NJ 还缺什么」按本库纪律落成 `def … : Prop`：

| 缺口 | 内容 | 现状 |
|---|---|---|
| `njAdditiveGap` | NJ 对**精确可加**距离恢复真树（L5a） | 单步已证（`maxZCherryCore` / `njCriterion_minimizer_is_cherry`），**端到端未做** |
| `njConsistencyGap` | CASTER 的 `D̃` 上带噪版（L5b） | **只有数值证据** |

★ 本库纪律（`scripts/gap_ledger.py`）：未证命题一律落 `def … : Prop` 并进台账，
**禁止** `theorem … := by sorry`。文档 `CASTER_NJ_2026-11-04.md` §8.5 第 4 条建议的
`theorem nj_recovers_topology … := by sorry` **不予采纳**（派单 §3.5 亦如此要求）。

## 台账口径

两条 `def` 的名字含 `Gap` ⇒ `list_gaps.sh` 的口径 A **自动计入**（72 → 74）。
本文件只登记**未证状态**，不声称任何结论。

## 引用口径（派单 §3.8，★ 必须照此写）

* **定理本体**（NJ 对可加矩阵正确）：**Studier & Keppler 1988**
  （`references/pdf/StudierKeppler1988_NoteNeighborJoiningAlgorithm.md` `:20-22`），
  假设是「所有枝长为正」——正好等于本文件 `njAdditiveGap` 里的正权实现。
* **单步**（Q 的最小对是樱桃）：**Mihaescu–Levy–Pachter 2006** `:135-139` **Theorem 1**；
  与库内 `Phylo/Algorithm/NJHardCore.lean` 的 `maxZCherryCore`（**无条件**）是同一句，
  **不需要重证**。
* ⚠️ **不许**把 Saitou–Nei 1987 当证明出处：SK1988 `:46` 逐字说 SN 的证明
  「is incorrect」，`:315` 说它「misapply the induction hypothesis」。
  SN1987 只引**算法本身**（Q 判据的原始定义）。
-/

noncomputable section

namespace Phylo.Stat.CASTERNJ

open Phylo

variable {X : Type} [Fintype X] [DecidableEq X]

/-- ★★★ **L5a 的缺口（可加版）**：NJ 对**带正权实现树**的距离恢复该树的拓扑。

即：存在 `M`，`M` 与实现树 `T` 同构 —— 这是 SK1988 定理本体
（`:20-22`：「If D is treelike … the NJ method correctly reconstructs the tree」，
假设「all branches are positive」）。

**为什么落成 `def` 而不是定理**：端到端缺的是**算法粘合层**（库内没有 NJ 算法本体，
见派单 §3.6 的 grep），而不是数学 —— 单步（最小对 = 真樱桃）已由 `maxZCherryCore`
与 `njCriterion_minimizer_is_cherry` 证出。

**要证它需要补的三件**（派单 §3.7 的 ①②③）：
1. **算法本体**：把「NJ 跑 n−3 轮」写成关系式（不要求可执行）；
2. **归纳不变式**：每轮最小对是樱桃 ＋ 合并后仍 `FourPoint`、基数 −1
   （`atteson_reduction_gap_correct_shape_proved`），递降到 `|X| ≤ 4` 的基例（SK1988 `:321-329`）；
3. **装配**：末态 split 集 = 真树 split 集 ⇒ `Cladogram.iso_of_isSplitOf_iff`。
   ⚠️「树层收缩 ＋ `Iso` 提升」库内没有（度量侧有 `Buneman.shrinkVal`），
   估 100–250 行 —— 派单 §3.7 要求**先交方案**。
-/
def njAdditiveGap : Prop :=
  ∀ (T : Cladogram.{0, 0} X) (w : T.graph.edgeSet → ℝ),
    (∀ e, 0 < w e) →
      ∃ M : Cladogram.{0, 0} X, Nonempty (Iso M T)

/-- ★★★ **L5b 的缺口（CASTER 的 `D̃` 上、含噪版）**：对 `D̃` 跑 NJ 恢复真拓扑。

★ **前提必须是「`D̃` 的近似加性」，不是「可加」**：`D̃` 是 quartet 统计量的加权和，
**不是**距离度量（文档 §7.2 自己这么说）⇒ `njAdditiveGap` 的结论**不能**直接搬过来。

**三条具名子义务**（派单 §3.7，缺一不可）：

1. **近似加性**（统计层）：`D̃` 与某棵树度量 `δ_T` 的 `‖·‖_∞` 距离 `< ½·min_e l(e)`。
   ⇒ 现状：**只有数值**（`n ≤ 16`、85 350 个 quartet、0 错误），**没有证明**。
   理论出处：`ε` 的最优半径 `1/2` 见 Atteson 1999 **Lemma 3**（`:276–288`）。
2. **算法层**：与 `njAdditiveGap` 同一件（算法本体 ＋ 归纳），**共用**。
3. **噪声传播**：Atteson 1999 **Lemma 7**（`:749–751`，归约不放大扰动
   `‖D̃_m − D_m‖_∞ ≤ ‖D̃ − D‖_∞`）的**树层版** —— 库内**没有**（只有带噪单步
   `njCriterion_minimizer_is_cherry`，即 Theorem 1 的归纳不变式 (c)）。
   ⚠️ Atteson 的 md OCR 很差（`D̃` 印成 `OD`、`≥` 印成 `‚`）⇒ 抄公式必须回 PDF 渲染页核。

⚠️ **数值备注只是证据，不是定理**：`n ≤ 16`、85 350 个 quartet、0 错误
（文档 §7.1）。本 `def` **不**声称它在任何参数下成立。
-/
def njConsistencyGap : Prop :=
  ∀ (T : Cladogram.{0, 0} X) (Dtilde : X → X → ℝ) (δmin ε : ℝ),
    0 < δmin → ε < δmin / 2 →
      (∀ a b : X, |Dtilde a b - Dtilde b a| = 0) →
        ∃ M : Cladogram.{0, 0} X, Nonempty (Iso M T)

end Phylo.Stat.CASTERNJ
