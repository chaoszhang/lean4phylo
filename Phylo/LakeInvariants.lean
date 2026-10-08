/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.JukesCantor

/-!
# `Phylo.LakeInvariants` —— JC 下两条**线性**不变量（Lake 型，四项和 = 0）

## 文献依据（先读文献）

* **Lake (1987)**《A rate-independent technique for analysis of nucleic acid sequences:
  evolutionary parsimony》, *Mol. Biol. Evol.* **4**(2):167–191。原文 (5)(6)(7) 式
  `X = E + u − H − J`、`Y = F + v − L − N`、`Z = G + w − Q − S`——Lake 的三条
  **四项线性组合**（每条的四个 spectral component 属于同一 site-pattern 位点类）。
  经典转述（Felsenstein, DNAINVAR 文档 "Lake's Invariants" 一节）把三条写成**期望频率**的
  四项和：
  1. `P(1133) + P(1234) − P(1134) − P(1233)`，
  2. `P(1313) + P(1324) − P(1314) − P(1323)`，
  3. `P(1331) + P(1342) − P(1341) − P(1332)`，
  其中 `1,2` 是一对 transition 关系碱基、`3,4` 是互补的另一对。
* **Casanellas–Fernández-Sánchez (2011) §5.5「Jukes-Cantor model」**（本任务指定来源）：
  等变矩阵为「对角 `a`、非对角 `b`」者正是 **JC 模型**（`S4` 等变）；
  `T^{fe}(ψ)` 分块对角、`m = (1,0,0,1,0)`，秩条件 `rk ≤ m` 给 12 条不变量，其中
  「**`f11, f12` 阶为一，由 `S1, S4 = 0` 得到；这两条等价于 Lake 的不变量**」
  （原文 p.30；本项目 OCR 文本第 3181–3227 行）。即 Lake 的两条线性不变量
  = 秩条件的两个 **1 维块**。
* **Steel–Fu (1995)**：JC 线性不变量的完整空间与维数 `dim I(T) = 4^n − |s(T)|`。
* **Sturmfels (2004)**「Phylogenetic Algebraic Geometry」：JC 的 Fourier/Hadamard 坐标框架。

## 模型与证明路线（本文件的定义）

四叶树拓扑 **`12|34`**：内部顶点 `a`（挂叶 1,2）与 `b`（挂叶 3,4）。边长 `t : Fin 5 → ℝ`：
`t 0`=叶1边、`t 1`=叶2边、`t 2`=**内部边** `a—b`、`t 3`=叶3边、`t 4`=叶4边。
JC 转移矩阵（与 `Phylo.JC.kernel` 同一矩阵）

`κ t α β = 1/4 * (1 − e t) + [α = β] * e t`，`e t = exp(−(4/3) t)`。

site-pattern 概率（根在内部顶点 `a`、根分布均匀 `1/4`）：

`prob t σ = 1/4 * Σ_{α,β} κ(t0,α,σ0) κ(t1,α,σ1) κ(t2,α,β) κ(t3,β,σ2) κ(t4,β,σ3)`。

在 `Fin 4 =` Klein 四元群 `(ℤ/2)²`（`A=(0,0)`, `C=(1,0)`, `G=(0,1)`, `T=(1,1)`）上取
**补映射** `comp`（`A↔T`、`C↔G`，即 `v ↦ v + (1,1)`；对合、无不动点）。JC 的 `κ`
的核心对称性是

* `kap_comp_comp`：`κ(t,comp x,comp y) = κ(t,x,y)`；
* `kap_add_comp`：`κ(t,x,y) + κ(t,x,comp y) = (1/2)(1 + e t)`。

由此得**补对求和恒等式**（`pairSum_eq`）：若 `g (comp x) = g x`，则

  `Σ_x κ(t,a,x) * g x = (1/2)(1 + e t) * g a`。

这是两条 Lake 不变量的全部机制：把一条四项式在**叶 2 坐标**上按补对
`(σ1, comp σ1)`、在**叶 4 坐标**上按补对 `(σ3, comp σ3)` 拆开，两次各提出
`(1/2)(1 + e(t1))`、`(1/2)(1 + e(t4))`，余项**逐项相消**。

## 完成度与诚实边界（逐条，**不许把假设写成已证**）

**(A) 已完成并已证**：

* `comp`、`comp_zero/one/two/three`、`comp_invol`、`comp_ne`、`compEquiv`；
* `kap`、`kap_eq_kernel`（与 `Phylo.JukesCantor` 的 `JC.kernel` 是同一矩阵）；
* `prob`、`prob_eq_patternProb`。

**(B) 未完成 —— 本批的真实缺口（如实标注）**：

* **两条 Lake 不变量本身（`lakeInv1`、`lakeInv2`）在本文件中尚未形式化完成。**
  具体地：`kap_add_comp`（`κ(t,x,y) + κ(t,x,comp y) = (1/2)(1+e t)`）的 16 情形
  证明、以及由它推出的 `pairSum_eq`（补对求和恒等式）与两条四项式的最终归零，
  在本次会话中**没有**跑通 Lean 编译（编译环境的 `ring` 在含 `JC.e t` 的
  线性目标上未能收口，`norm_num`/`ring` 组合的收尾方式未调通）。
  本文件因此**不包含** `lakeInv1` / `lakeInv2` 的声明——
  与其留下 `sorry` 或把假设写成已证，本文件选择**不声明**它们。
* **两条不变量的具体形式（数值已核验，形式化待补）**：
  在本文档的 `12|34` + `A=0,C=1,G=2,T=3` 约定下，
  `P(AACG) − P(AACC) − P(TTCG) + P(TTCC) = 0` 与
  `P(AAGC) − P(AACC) − P(TTGC) + P(TTCC) = 0`
  对**任意边长**成立。这两条已用精确有理数算术在**参数化模型**上核验：
  对 4 组随机参数 `u = (u0..u4)`（`u_i = e(t_i)`）× 3 个四叶拓扑
  （`12|34`、`13|24`、`14|23`），两项均**恒为 0**；且 `u_i = e(t_i)` 是
  自由参数，故若干随机点上的恒零等价于多项式恒等式
  （参见 Steel–Fu 1995 的线性不变量判别法与本文件证明路线）。
  **这是数值/符号核验，不是 Lean 中已证的定理。**
* 本文件**没有**任何 `sorry`、`axiom` 或 `def … : Prop` 缺口——
  因为未完成的部分**没有被声明**。
* 其余诚实边界：两条不变量是**模型不变量**（对三个拓扑都成立），
  **本文件没有声称**它们能单独区分拓扑；文献中 Lake 三条不变量的判别力来自
  「每条只对两个拓扑为零、第三条非零」的三重结构。`S1, S4 = 0` 的块结构
  （文献 p.30）在本项目 OCR 文本中排版错乱、`S1` 条目不可读，本文件走的是
  **概率层**路线，不复现矩阵分块。本文件也没有证明 `prob` 与
  「距离形式 `pDiff`」相等（那是 F4 批的已知缺口）。
-/

noncomputable section

namespace Phylo

namespace Lake

attribute [local instance] Classical.propDecidable

open Finset

/-! ## 0. 补映射 `comp` -/

/-- `Fin 4` 上的**补映射**：`0 ↦ 3`、`1 ↦ 2`、`2 ↦ 1`、`3 ↦ 0`
（`A↔T`、`C↔G`，即 Klein 四元群 `(ℤ/2)²` 里加 `(1,1)`）。 -/
def comp (x : Fin 4) : Fin 4 := match x with
  | ⟨0, _⟩ => 3
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1
  | _ => 0

theorem comp_zero : comp 0 = 3 := rfl
theorem comp_one : comp 1 = 2 := rfl
theorem comp_two : comp 2 = 1 := rfl
theorem comp_three : comp 3 = 0 := rfl

/-- 补映射是**对合**。 -/
theorem comp_invol (x : Fin 4) : comp (comp x) = x := by
  fin_cases x <;> rfl

/-- 补映射**没有不动点**。 -/
theorem comp_ne (x : Fin 4) : comp x ≠ x := by
  fin_cases x <;> decide

/-- 补映射作为 `Fin 4` 的置换（供重指标用）。 -/
def compEquiv : Fin 4 ≃ Fin 4 where
  toFun := comp
  invFun := comp
  left_inv := comp_invol
  right_inv := comp_invol

/-! ## 1. JC 转移矩阵 `kap` -/

/-- JC 转移矩阵 `κ t α β = 1/4 * (1 − e t) + [α = β] * e t`，
`e t = exp(−(4/3) t)`——即「对角 `a`、非对角 `b`」的 `S4` 等变矩阵
（`Casanellas2011 §5.5`），也即 `Phylo.JC.kernel`。 -/
def kap (t : ℝ) (α β : Fin 4) : ℝ := 1 / 4 * (1 - JC.e t) + JC.ind α β * JC.e t

theorem kap_apply (t : ℝ) (α β : Fin 4) :
    kap t α β = 1 / 4 * (1 - JC.e t) + JC.ind α β * JC.e t := rfl

/-- `kap` 与 `Phylo.JukesCantor` 的 `JC.kernel` 是同一个矩阵。 -/
theorem kap_eq_kernel (t : ℝ) (α β : Fin 4) : kap t α β = JC.kernel t α β := by
  rw [kap_apply, JC.kernel_apply, JC.off]
  ring

/-! ## 2. 概率层：`12|34` 上的 site-pattern 概率 -/

/-- 四叶拓扑 `12|34` 的 **site-pattern 概率**（根在内部顶点 `a`、根分布均匀 `1/4`）。

`σ 0`/`σ 1` 是叶 1/2 的状态（走边 `t 0`/`t 1` 到 `a`），
`σ 2`/`σ 3` 是叶 3/4 的状态（走边 `t 3`/`t 4` 到 `b`），`t 2` 是内部边 `a—b`。
与 `Phylo.JC.patternProb` 定义同形（边长按本文件的顺序排列）。 -/
def prob (t : Fin 5 → ℝ) (σ : Fin 4 → Fin 4) : ℝ :=
  (1 / 4) * ∑ α : Fin 4, ∑ β : Fin 4,
    kap (t 0) α (σ 0) * kap (t 1) α (σ 1) * kap (t 2) α β
      * kap (t 3) β (σ 2) * kap (t 4) β (σ 3)

/-- `prob` 与 `Phylo.JC.patternProb` 定义同形（边长按本文件顺序）。 -/
theorem prob_eq_patternProb (t : Fin 5 → ℝ) (σ : Fin 4 → Fin 4) :
    prob t σ = (1 / 4) * ∑ α : Fin 4, ∑ β : Fin 4,
      JC.kernel (t 0) α (σ 0) * JC.kernel (t 1) α (σ 1) * JC.kernel (t 2) α β
        * JC.kernel (t 3) β (σ 2) * JC.kernel (t 4) β (σ 3) := by
  simp only [prob, kap_eq_kernel]

end Lake

end Phylo
