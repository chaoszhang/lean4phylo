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
**补映射** `comp`（`A↔T`、`C↔G`，即 `v ↦ v + (1,1)`；对合、无不动点）；`comp_vec` 给出
它的向量写法 `comp = ![3,2,1,0]`，`ind_comp_comp` 给出 `[comp x = comp y] = [x = y]`。

## ★ 证明内核（本批**更正**：交接材料给的「内核」是假的）

上一版交接材料建议的两条「内核」**都不是定理**，本文件**不声明**它们：

* `kap_add_comp`（`κ(t,x,y) + κ(t,x,comp y) = (1/2)(1 + e t)`）**假**：取 `x ∉ {y, comp y}`
  （例如 `x=1, y=0`）时左端 `= 2 * (1/4)(1 − e t) = (1/2)(1 − e t) ≠ (1/2)(1 + e t)`。
  该式只在 `x ∈ {y, comp y}` 时成立（此时左右端同为 `off + lam`）。
* `pairSum_eq`（`Σ_x κ(t,a,x) g x = (1/2)(1 + e t) g a`，`g` 只需补不变）**假**：取 `g ≡ 1`
  （补不变），左端 `= Σ_x κ(t,a,x) = 1`（行和），右端 `= (1/2)(1 + e t)`，`t ≠ 0` 时不成立。
  正确的「补对」恒等式只能是 `Σ_x κ(t,a,x) g x = (1/4)(1 + e t) Σ_x g x`
  （`g` 补不变），其中仍**含** `Σ_x g x`，单独用两次消不掉。

两条不变量真正用到的机制只有两条**初等**事实（本文件已证）：

* `kap_comp_diff`：**一次「补差」的支撑只有两点**——
  `κ(t,x,comp y) − κ(t,x,y) = e t · ([x = comp y] − [x = y])`；
* `kap_cherry_eq`：**`z` 与 `comp z` 两点上的「cherry 因子」相等**——
  若 `s ≠ z` 且 `s ≠ comp z`，则 `κ(t₀,z,s) κ(t₁,z,s) = κ(t₀,comp z,s) κ(t₁,comp z,s)`
  （两者都是非对角值 `off t₀ · off t₁`）。

于是两条四项式的**精确闭式**是（`s = A`、`z = C`，`comp s = T`、`comp z = G`）：

* `lakeDiffA_expand`：`Δ := P(A,A,C,G) − P(A,A,C,C) − P(T,T,C,G) + P(T,T,C,C)`
  `= (e(t2) · e(t4) · (1/2)(1+e(t3)) / 4) · (κ(t0,G,A)κ(t1,G,A) − κ(t0,C,A)κ(t1,C,A))`；
* `lakeDiffB_expand`：`Δ' := P(A,A,G,C) − P(A,A,C,C) − P(T,T,G,C) + P(T,T,C,C)`
  `= (e(t2) · e(t3) · (1/2)(1+e(t4)) / 4) · (κ(t0,G,A)κ(t1,G,A) − κ(t0,C,A)κ(t1,C,A))`。

方括号里的两项都是 `off(t0)·off(t1)`（`A ∉ {C,G}`、`A ∉ {comp C, comp G} = {G,C}`），
故两条四项式**恒为 `0`**（`lakeInv1`、`lakeInv2`）。

**证明方式（不是假设、不是数值核验）**：`prob` 是 `α`、`β` 上的**有限**二重和，
用 `Fin.sum_univ_four` 把二重和展开成 16 个显式项、用 `simp`/`norm_num` 把指示函数
`[α = β]` 定成 `0`/`1`，再用 `ring` 在「`JC.e (t i)` 为原子」的多项式层收口
——即两条四项式的**精确符号核算**。两条不变量再由闭式的初等推论得到。

## 完成度与诚实边界（逐条，**不许把假设写成已证**）

**(A) 已完成并已证**：

* `comp`、`comp_zero/one/two/three`、`comp_invol`、`comp_ne`、`compEquiv`、`comp_vec`；
* `kap`、`kap_apply`、`kap_eq_kernel`（与 `Phylo.JukesCantor` 的 `JC.kernel` 是同一矩阵）、
  `kap_diag`、`kap_off`、`ind_comp_comp`、`kap_comp_comp`、`kap_comp_diff`、`kap_cherry_eq`；
* `prob`、`prob_eq_patternProb`；
* ★ **`lakeDiffA_expand`、`lakeInv1`、`lakeDiffB_expand`、`lakeInv2`（一般 `t`，本批证完）**：
  `lakeInv1 : prob t pAACG − prob t pAACC − prob t pTTCG + prob t pTTCC = 0`，
  `lakeInv2 : prob t pAAGC − prob t pAACC − prob t pTTGC + prob t pTTCC = 0`，
  对**任意**边长 `t : Fin 5 → ℝ` 成立（本文件中 `pAACG = ![0,0,1,2]` 等，
  即 `A=0, C=1, G=2, T=3`）。

**(B) 未完成 / 本轮**不做**的事（如实标注）**：

* 交接材料建议的 `kap_add_comp` / `pairSum_eq` 是**假命题**（反例见上），
  本文件既没有声明它们，也没有用它们。
* 两条不变量是**模型不变量**（在三个四叶拓扑上都成立），**不是**能单独区分拓扑的
  topology invariant；Lake 三条的判别力来自「每条只对两个拓扑为零」的**三重结构**。
  本文件**没有**声称任何判别力。
* 本文件只对**拓扑 `12|34`** 形式化了 `prob`；另两个拓扑（`13|24`、`14|23`）上
  同一式子的恒零**只在 Python 侧用精确有理数核验**，**未**在 Lean 中形式化
  （`Phylo.JukesCantor` 有 `pathLenB`/`pathLenC` 的（路径长度版）阴性对照，
  但那是 I1 的四点式，与本批的两条线性式不是同一件事）。
* `S1, S4 = 0` 的块结构（文献 p.30）在本项目 OCR 文本中排版错乱、`S1` 条目不可读，
  本文件走的是**概率层**路线，不复现矩阵分块、也没有做 Fourier/Hadamard 坐标推导。
* 本文件也**没有**证明 `prob` 与「距离形式 `pDiff`」相等（那是 F4 批的已知缺口）。
* 本文件**没有**任何 `sorry`、`axiom` 或 `def … : Prop` 缺口。
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

/-- 补映射的**向量写法**：`comp = ![3,2,1,0]`（`0↦3`、`1↦2`、`2↦1`、`3↦0`）。 -/
theorem comp_vec : comp = ![3, 2, 1, 0] := by
  funext x
  fin_cases x <;> rfl

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

/-- 指示函数在补映射下不变：`[comp x = comp y] = [x = y]`（`comp` 是双射）。 -/
theorem ind_comp_comp (x y : Fin 4) : JC.ind (comp x) (comp y) = JC.ind x y := by
  by_cases h : x = y
  · subst h; rw [JC.ind_self, JC.ind_self]
  · rw [JC.ind_ne h, JC.ind_ne (show comp x ≠ comp y from fun hc => h (by
      have h2 := congrArg comp hc
      rwa [comp_invol, comp_invol] at h2))]

/-- 转移矩阵**对角元**：`κ(t,x,x) = lam t = 1/4 + 3/4 · e t`。 -/
theorem kap_diag (t : ℝ) (x : Fin 4) : kap t x x = JC.lam t := by
  rw [kap_apply, JC.ind_self x, one_mul, JC.lam]
  ring

/-- 转移矩阵**非对角元**：`x ≠ y` 时 `κ(t,x,y) = off t = 1/4 − 1/4 · e t`。 -/
theorem kap_off (t : ℝ) {x y : Fin 4} (h : x ≠ y) : kap t x y = JC.off t := by
  rw [kap_apply, JC.ind_ne h, zero_mul, add_zero, JC.off]
  ring

/-- `κ` 在补映射下**不变**：`κ(t, comp x, comp y) = κ(t, x, y)`。 -/
theorem kap_comp_comp (t : ℝ) (x y : Fin 4) : kap t (comp x) (comp y) = kap t x y := by
  rw [kap_apply, kap_apply, ind_comp_comp]

/-- ★ **补差的支撑只有两点**：
`κ(t,x,comp y) − κ(t,x,y) = e t · ([x = comp y] − [x = y])`。

即：对固定的祖先状态 `x`，把叶状态 `y` 换成它的补 `comp y`，转移概率**只在**
`x ∈ {y, comp y}` 时改变——这正是两条 Lake 型不变量能够逐项相消的机制。 -/
theorem kap_comp_diff (t : ℝ) (x y : Fin 4) :
    kap t x (comp y) - kap t x y = JC.e t * (JC.ind x (comp y) - JC.ind x y) := by
  rw [kap_apply, kap_apply]
  ring

/-- ★ **`z` 与 `comp z` 上的 cherry 因子相等**：若 `s ≠ z`、`s ≠ comp z`，
则 `κ(t₀,z,s) κ(t₁,z,s) = κ(t₀,comp z,s) κ(t₁,comp z,s)`（两者都 `= off t₀ · off t₁`）。

这条与 `kap_comp_diff` 一起构成两条 Lake 型不变量的**完整机制**：
在叶 3 上做补差后只剩 `β ∈ {C,G}` 两点，而这两点上的叶子 1,2 cherry 因子相同，
故整个四项式归零。 -/
theorem kap_cherry_eq (t₀ t₁ : ℝ) (s z : Fin 4) (h1 : s ≠ z) (h2 : s ≠ comp z) :
    kap t₀ z s * kap t₁ z s = kap t₀ (comp z) s * kap t₁ (comp z) s := by
  rw [kap_off t₀ (Ne.symm h1), kap_off t₁ (Ne.symm h1),
    kap_off t₀ (Ne.symm h2), kap_off t₁ (Ne.symm h2)]

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

/-! ## 3. site-pattern 的**字母编码**（`A=0, C=1, G=2, T=3`）

本批的两条不变量用到的四个/六个 site-pattern。均为 `Fin 4 → Fin 4` 的显式函数，
下标即四片叶的碱基（叶 1,2,3,4 依次）。 -/

/-- `AACG = (A,A,C,G) = (0,0,1,2)`。 -/
def pAACG : Fin 4 → Fin 4 := ![0, 0, 1, 2]

/-- `AACC = (A,A,C,C) = (0,0,1,1)`。 -/
def pAACC : Fin 4 → Fin 4 := ![0, 0, 1, 1]

/-- `TTCG = (T,T,C,G) = (3,3,1,2)`。 -/
def pTTCG : Fin 4 → Fin 4 := ![3, 3, 1, 2]

/-- `TTCC = (T,T,C,C) = (3,3,1,1)`。 -/
def pTTCC : Fin 4 → Fin 4 := ![3, 3, 1, 1]

/-- `AAGC = (A,A,G,C) = (0,0,2,1)`。 -/
def pAAGC : Fin 4 → Fin 4 := ![0, 0, 2, 1]

/-- `TTGC = (T,T,G,C) = (3,3,2,1)`。 -/
def pTTGC : Fin 4 → Fin 4 := ![3, 3, 2, 1]

/-! ## 4. ★ 两条 Lake 型线性不变量（**一般 `t`，本批证完**）

约定：`s = A = 0`、`comp s = T = 3`、`z = C = 1`、`comp z = G = 2`。
第一条不变量的「cherry」是叶 1,2（两边 `t0`、`t1`），变动的叶是叶 4（边 `t4`），
固定的 `z/comp z` 对在叶 3（边 `t3`）；第二条的叶 3,4 角色互换。 -/

/-- ★★ **第一条四项式的精确闭式**：

`P(A,A,C,G) − P(A,A,C,C) − P(T,T,C,G) + P(T,T,C,C)
 = (e(t2) · e(t4) · (1/2)(1 + e(t3)) / 4) · (κ(t0,G,A)κ(t1,G,A) − κ(t0,C,A)κ(t1,C,A))`。

（`e(t4)` 来自变动叶 4 的一次补差，`(1/2)(1+e(t3))` 来自固定对 `{C,G}` 在叶 3 上的取值和，
`e(t2)` 来自内部边上的补差，`κ(t0,·,A)κ(t1,·,A)` 是叶 1,2 的 cherry 因子。
方括号内两项在 `A ∉ {C,G}` 时同为 `off(t0)·off(t1)`，故下一行 `lakeInv1` 归零。） -/
theorem lakeDiffA_expand (t : Fin 5 → ℝ) :
    prob t pAACG - prob t pAACC - prob t pTTCG + prob t pTTCC
      = (JC.e (t 2) * JC.e (t 4) * (1 / 2 * (1 + JC.e (t 3))) / 4)
        * (kap (t 0) 2 0 * kap (t 1) 2 0 - kap (t 0) 1 0 * kap (t 1) 1 0) := by
  simp only [prob, pAACG, pAACC, pTTCG, pTTCC, Fin.sum_univ_four, kap_apply, JC.ind]
  norm_num
  ring

/-- ★★★ **第一条 Lake 型线性不变量（一般 `t`）**：

`P(AACG) − P(AACC) − P(TTCG) + P(TTCC) = 0`，
其中 `{1,2} = {A,T} = {s, comp s}`、`{3,4} = {C,G} = {z, comp z}`
（叶 3 固定为 `z = C`，叶 4 在 `{C,G}` 上取补对）。

证明：由 `lakeDiffA_expand` 化成 `… · (κ(t0,G,A)κ(t1,G,A) − κ(t0,C,A)κ(t1,C,A))`，
再用 `kap_off`（`A ≠ C`、`A ≠ G`）把两项都定成 `off(t0)·off(t1)`，相减为 `0`。 -/
theorem lakeInv1 (t : Fin 5 → ℝ) :
    prob t pAACG - prob t pAACC - prob t pTTCG + prob t pTTCC = 0 := by
  rw [lakeDiffA_expand,
    kap_off (t 0) (by decide : (2 : Fin 4) ≠ 0),
    kap_off (t 1) (by decide : (2 : Fin 4) ≠ 0),
    kap_off (t 0) (by decide : (1 : Fin 4) ≠ 0),
    kap_off (t 1) (by decide : (1 : Fin 4) ≠ 0)]
  ring

/-- ★★ **第二条四项式的精确闭式**（叶 3,4 角色互换：变动叶是叶 3，固定对在叶 4）：

`P(A,A,G,C) − P(A,A,C,C) − P(T,T,G,C) + P(T,T,C,C)
 = (e(t2) · e(t3) · (1/2)(1 + e(t4)) / 4) · (κ(t0,G,A)κ(t1,G,A) − κ(t0,C,A)κ(t1,C,A))`。 -/
theorem lakeDiffB_expand (t : Fin 5 → ℝ) :
    prob t pAAGC - prob t pAACC - prob t pTTGC + prob t pTTCC
      = (JC.e (t 2) * JC.e (t 3) * (1 / 2 * (1 + JC.e (t 4))) / 4)
        * (kap (t 0) 2 0 * kap (t 1) 2 0 - kap (t 0) 1 0 * kap (t 1) 1 0) := by
  simp only [prob, pAAGC, pAACC, pTTGC, pTTCC, Fin.sum_univ_four, kap_apply, JC.ind]
  norm_num
  ring

/-- ★★★ **第二条 Lake 型线性不变量（一般 `t`）**：

`P(AAGC) − P(AACC) − P(TTGC) + P(TTCC) = 0`，
其中 `{1,2} = {A,T}`、`{3,4} = {C,G}`（叶 4 固定为 `z = C`，叶 3 在 `{C,G}` 上取补对）。 -/
theorem lakeInv2 (t : Fin 5 → ℝ) :
    prob t pAAGC - prob t pAACC - prob t pTTGC + prob t pTTCC = 0 := by
  rw [lakeDiffB_expand,
    kap_off (t 0) (by decide : (2 : Fin 4) ≠ 0),
    kap_off (t 1) (by decide : (2 : Fin 4) ≠ 0),
    kap_off (t 0) (by decide : (1 : Fin 4) ≠ 0),
    kap_off (t 1) (by decide : (1 : Fin 4) ≠ 0)]
  ring

end Lake

end Phylo
