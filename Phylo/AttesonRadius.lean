/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Algorithm.NJ
import Phylo.Buneman
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Phylo.Split
import Phylo.InternalEdge

/-!
# `Phylo.AttesonRadius` —— Atteson 安全半径 `1/2`（W11g · D1）

## 文献与逐行依据

`references/md/Atteson1999_PerformanceNeighborJoiningAlgorithmica.md`
（K. Atteson, *The Performance of Neighbor-Joining Methods of Phylogenetic Reconstruction*,
Algorithmica 25:251–278 (1999)）。本文件所有行号都指该 md 文件。

* **Definition 3**（`:187–197`）：`‖D̃ − D̃'‖_∞ = max_{i,j} |D̃_ij − D̃'_ij|`；
  `:192–206`：方法 `f` 有 **l₁ radius `β`**，若对每个加权二叉树 `τ` 及每个满足
  `‖D_τ − D̃‖_∞ < β · min_{e∈E(T_τ)} l(e)` 的距离矩阵 `D̃` 都有 `f(D̃) = T_τ`。
* **Lemma 3**（`:276–288`）：**没有**方法有 l₁ radius `> 1/2`（`1/2` 最优）。
* **Definition 4**（`:335–346`）：`D̃` 对 `τ` **nearly additive**，若
  `‖D̃ − D_τ‖_∞ < min_{e∈E(T_τ)} l(e) / 2`。 ← **本文件的 `safeRadius`**
* **Lemma 1**（`:160–172`）：四点条件 —— `D` 可加 ⟺ 任意四点可标号为 `i,j,k,l` 使
  `D_ij + D_kl ≤ D_ik + D_jl = D_il + D_jk`。
* **Lemma 6**（`:677–694`）：可加矩阵上合并一对**邻居** `i,j`（更新式 (6)，`:611`）仍得可加矩阵，
  对应「删去 `i,j`」的树；边权由式 (7)（`:688–694`）给出。
* **Lemma 7**（`:749–751`）：`‖D̃_m − D_m‖_∞ ≤ ‖D̃ − D‖_∞`（归约**不放大**扰动）。
* **Theorem 1**（`:868–916`）：若 NJ 方法 (1) 在近可加输入下优化判据的对必是邻居、(2) 用更新式 (6)，
  则输出 `T_τ`，即 **l₁ radius `1/2`**。证明用三个同时成立的归纳不变量
  (a) `D_m` 可加、(b) `min_e l_m(e) ≥ min_e l_1(e)`、(c) 第 `m` 步所选对是邻居。
* **式 (12)**（`:1751–1755`）：NJ 判据 `S_{i,j} = (n−2)D_ij − Σ_k D_ik − Σ_k D_jk`（**最小化**）。
  ← **本库 `Dissimilarity.Q`（`Phylo/Algorithm/NJ.lean:88`）就是它。**
* **Lemma 8**（`:1030–1033`）：`‖D̃ − D_τ‖_∞ = "` 且边 `e` 分离 `i,j` 与 `k,l` ⇒
  `i,j` 赢四点的条件（`" < l(e)` 的定量版）。
* **Lemma 10**（`:1774–1804`）：`S_{i,j} = Σ_{e∈E} w_e(i,j)·l(e)`，其中
  `w_e(i,j) = −2`（`e ∈ P_{i,j}`）、`= −2|L − L_i(e)|`（否则）。
* **Lemma 11**（`:1989–2009`）：`k,l` 不是邻居 ⟹ 存在邻居对 `i,j` 使
  `S_{k,l} − S_{i,j} ≥ 3(n−4)·min_e l(e)`（两对不交）或 `≥ 2(n−3)·min_e l(e)`（恰交一个标签）。
* **Lemma 12 / 式 (16)**（`:2181–2201`）：证明的关键是**扰动抵消**：
  `(Ŝ_kl − S_kl) + (S_ij − Ŝ_ij) = (n−2)(ε_kl − ε_ij) + Σ_m (ε_im + ε_jm − ε_km − ε_lm)`，
  其中 `ε_ab = D̃_ab − D_ab`。**朴素估计 `|Ŝ_kl − S_kl| ≤ (3n−2)ε` 会给出错误（更小）的半径**——
  抵消把 `n` 降回 `n−4`，正是 `1/2` 得以取到的原因。
* **Theorem 4**（`:2263–2303`）：**NJ has l₁ radius `1/2`**。证明：
  `Ŝ_kl − Ŝ_ij = [Ŝ_kl − S_kl + S_ij − Ŝ_ij] + [S_kl − S_ij] ≥ −6(n−4)ε + 3(n−4)·min_e l(e)
  = 3(n−4)(min_e l(e) − 2ε) > 0`，故第一轮必选邻居对，再由 Lemma 1 收口。

## 本文件证了什么 / 缺什么

✅ **已证（零 `sorry` / 零 `axiom` / 零 `native_decide`）**

* ★★★ `qPerturb_cancel`：**Atteson 式 (16) 的精确恒等式**（`:2195–2201`）；
* ★★★ `qPerturb_reduced` / `qPerturb_reduced_ik`：把上式化简成
  `(n−4)(ε_kl − ε_ij) + Σ_{m ∉ {i,j,k,l}} (…)`（`n=4` 时**恒为 0**）；
* ★★ `qPerturb_bound_disjoint` / `qPerturb_bound_shared`：**Lemma 12 的两条界**
  `≥ −6(n−4)ε`（`:2183`）与 `≥ −4(n−3)ε`（`:2187`）；
* ★★★ `njCriterion_minimizer_is_cherry`：**「`ε < safeRadius δmin` ⟹ NJ 第一轮判据的
  任何最小点都是真树的一颗樱桃」**（`n ≥ 5`；Theorem 4 的第一步，`:2266–2303`）；
* ★★★ `njCriterion_minimizer_is_cherry_card_four`：`n = 4` 版本（只用「恰交一个标签」分支）；
* ★★ `qPerturb_cancel_of_card_four`：`n = 4` 时 `Q` 的**排序在不相交对上完全不受扰动影响**；
* ★★ `linfClose_update`：**Lemma 7 的一步形式**（`:749–751`，更新式 (6) 不放大 `L∞` 扰动）；
* ★C `Fin 4` 显式数值例子：挂边 `1,2,3,4`、内部边 `5`，真矩阵与扰动矩阵上
  `Q` 的最小点都恰是两颗樱桃。

⚠️ **缺口（落成 `Prop`，都不是数学缺口，是本库的工程缺口）**

* `IsCherrySeparated`：**Atteson Lemma 11 的度量版**（`:1989–2009`）—— 本文件唯一的非纯代数假设；
* `atteson_lemma11_gap`：上述假设对树度量的**可实现性**；
* `atteson_reduction_gap`：**Atteson Lemma 6 的归约步**（`:677–694`）—— 需要类型迁移
  `X ↝ (X \ {i,j}) ∪ {u}` 与实现树层的「合并樱桃」算子。

-/

open Finset
open scoped BigOperators

noncomputable section

namespace NJ

namespace Dissimilarity

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## 0. 安全半径与「接近」谓词 -/

omit [Fintype X] [DecidableEq X] in
/-- **安全半径** `½ · δmin`（Atteson1999 Definition 3/4，`:201–204`、`:340–346`）。

`δmin` 取真加权二叉树 `τ` 的**最短边长** `min_{e∈E(τ)} l(e)`。Atteson 的结论是
（Theorem 4，`:2263`）：`‖D̃ − D_τ‖_∞ < safeRadius δmin` 时 NJ 仍输出 `τ` 的形状；
且 `1/2` 是**最优**常数（Lemma 3，`:276`）。 -/
def safeRadius (δmin : ℝ) : ℝ := δmin / 2

/-- **L∞ 接近**：`‖δ' − δ‖_∞ ≤ ε`（Atteson1999 Definition 3，`:187–197`）。 -/
def IsLinfClose (δ δ' : Dissimilarity X) (ε : ℝ) : Prop :=
  ∀ i j : X, |δ'.val i j - δ.val i j| ≤ ε

/-- **近可加**（Atteson1999 Definition 4，`:335–346`）：`‖δ' − δ_τ‖_∞ ≤ ε` 且
`ε < safeRadius δmin = δmin/2`。 -/
def NearlyAdditive (δ δ' : Dissimilarity X) (δmin ε : ℝ) : Prop :=
  IsLinfClose δ δ' ε ∧ ε < safeRadius δmin

omit [Fintype X] [DecidableEq X] in
/-- `{i,j}` 与 `{k,l}` **完全不相交**（Atteson1999 Lemma 12 第一式的情形，`:2183–2185`）。 -/
def DisjointPairs (i j k l : X) : Prop :=
  i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l

omit [Fintype X] [DecidableEq X] in
/-- `{i,j}` 与 `{k,l}` **恰交于一个标签**（Atteson1999 Lemma 12 第二式的情形，`:2187–2189`）。

四种形态各自带上后续证明所需的互异性（`i ≠ j`、`k ≠ l` 在调用处另行给出）。 -/
def SharesOneLabel (i j k l : X) : Prop :=
  (i = k ∧ j ≠ k ∧ j ≠ l) ∨ (i = l ∧ j ≠ k ∧ j ≠ l) ∨
  (j = k ∧ i ≠ k ∧ i ≠ l) ∨ (j = l ∧ i ≠ k ∧ i ≠ l)

/-- ★★ **Atteson Lemma 11 的度量版**（`:1989–2009`）—— 本文件**唯一的非纯代数假设**。

「若 `(k,l)` 不是真树 `τ` 的一颗樱桃，则存在 `τ` 的樱桃 `(i,j)`，使 NJ 判据 `Q` 在 `(k,l)` 处
比在 `(i,j)` 处至少大 `3(n−4)·δmin`（两对不交）或 `2(n−3)·δmin`（恰交一个标签）。」

✦ **为什么是假设**：Lemma 11 的证明先用 Lemma 10（`:1774–1804`）把 `Q(i,j)` 写成
`Σ_{e∈E} w_e(i,j)·l(e)`（权重只依赖拓扑），再逐边比较并使用「路径旁子树的叶数」单调性
（`:2023–2056`）。这需要**实现树 + 路径关联 + 子树叶数**这一层，本库尚未搭好。
可解性见 ★★ `atteson_lemma11_gap` 的说明。 -/
def IsCherrySeparated (δ : Dissimilarity X) (δmin : ℝ) : Prop :=
  ∀ k l : X, k ≠ l → ¬ δ.IsCherry k l →
    ∃ i j : X, δ.IsCherry i j ∧
      ((DisjointPairs i j k l ∧
          3 * ((Fintype.card X : ℝ) - 4) * δmin ≤ δ.Q k l - δ.Q i j) ∨
       (SharesOneLabel i j k l ∧
          2 * ((Fintype.card X : ℝ) - 3) * δmin ≤ δ.Q k l - δ.Q i j))

/-! ## 1. 有限和的拆解 -/

omit [DecidableEq X] in
/-- `∑ (a + b − c − d) = ∑a + ∑b − ∑c − ∑d`。 -/
theorem sum_four_sub (f g h k : X → ℝ) :
    (∑ m : X, (f m + g m - h m - k m))
      = (∑ m : X, f m) + (∑ m : X, g m) - (∑ m : X, h m) - (∑ m : X, k m) := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]

omit [Fintype X] in
/-- 三元集上的求和展开。 -/
theorem sum_three_elems (F : X → ℝ) {a b c : X}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∑ m ∈ ({a, b, c} : Finset X), F m) = F a + (F b + F c) := by
  have h1 : a ∉ ({b, c} : Finset X) := by simp [hab, hac]
  have h2 : b ∉ ({c} : Finset X) := by simp [hbc]
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]

omit [Fintype X] in
/-- 四元集上的求和展开。 -/
theorem sum_four_elems (F : X → ℝ) {a b c d : X} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (∑ m ∈ ({a, b, c, d} : Finset X), F m) = F a + (F b + (F c + F d)) := by
  have h1 : a ∉ ({b, c, d} : Finset X) := by simp [hab, hac, had]
  have h2 : b ∉ ({c, d} : Finset X) := by simp [hbc, hbd]
  have h3 : c ∉ ({d} : Finset X) := by simp [hcd]
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3, Finset.sum_singleton]

omit [Fintype X] in
/-- 三元集的基数。 -/
theorem card_three_elems (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset X).card = 3 := by
  have h1 : a ∉ ({b, c} : Finset X) := by simp [hab, hac]
  have h2 : b ∉ ({c} : Finset X) := by simp [hbc]
  rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]

omit [Fintype X] in
/-- 四元集的基数。 -/
theorem card_four_elems (a b c d : X) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Finset X).card = 4 := by
  have h1 : a ∉ ({b, c, d} : Finset X) := by simp [hab, hac, had]
  have h2 : b ∉ ({c, d} : Finset X) := by simp [hbc, hbd]
  have h3 : c ∉ ({d} : Finset X) := by simp [hcd]
  rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_singleton]

/-- 从全体中挖掉 `s` 之后的基数。 -/
theorem card_sdiff_univ (s : Finset X) :
    ((Finset.univ : Finset X) \ s).card = Fintype.card X - s.card := by
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]

/-! ## 2. 扰动抵消：Atteson 式 (16)（`:2195–2201`） -/

omit [Fintype X] in
/-- ★★★ **四点指标集上的「四元组合和」精确值**（Atteson1999 `:2205–2221` 的化简）：

`Σ_{m ∈ {i,j,k,l}} (g_im + g_jm − g_km − g_lm) = 2·g_ij − 2·g_kl`（`g` 对称且零对角）。

**正是这一项**（连同 `(n−2)(ε_kl − ε_ij)`）把系数从 `n−2` 削到 `n−4` ——
安全半径 `1/2` 能否取到，全看这里。 -/
theorem sum_quartet_four (g : X → X → ℝ) (hsymm : ∀ a b, g a b = g b a) (hdiag : ∀ a, g a a = 0)
    {i j k l : X} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (∑ m ∈ ({i, j, k, l} : Finset X), (g i m + g j m - g k m - g l m))
      = 2 * g i j - 2 * g k l := by
  rw [sum_four_elems (fun m => g i m + g j m - g k m - g l m) hij hik hil hjk hjl hkl]
  simp only [hdiag, zero_add, add_zero, sub_zero]
  rw [hsymm j i, hsymm k i, hsymm l i, hsymm k j, hsymm l j, hsymm l k]
  ring

omit [DecidableEq X] in
/-- ★ **NJ 判据 `Q` 的对称性**：`Q(i,j) = Q(j,i)`。

式 (12)（Atteson1999 `:1751–1755`）`S_{i,j} = (n−2)D_ij − Σ_k D_ik − Σ_k D_jk` 对 `i,j`
显然对称；本库 `Dissimilarity.Q` 即此式（`Phylo/Algorithm/NJ.lean:88`）。 -/
theorem Q_comm (δ : Dissimilarity X) (i j : X) : δ.Q i j = δ.Q j i := by
  simp only [Q]
  rw [δ.symm j i]
  ring

omit [DecidableEq X] in
/-- 单个 `Q` 的扰动展开（式 (16) 的左半，Atteson1999 `:2195–2201`）。 -/
theorem Q_perturb_pos (δ δ' : Dissimilarity X) (i j : X) :
    δ'.Q i j - δ.Q i j
      = ((Fintype.card X : ℝ) - 2) * (δ'.val i j - δ.val i j)
        - (∑ m : X, (δ'.val i m - δ.val i m))
        - (∑ m : X, (δ'.val j m - δ.val j m)) := by
  have e1 : (∑ m : X, δ'.val i m) - (∑ m : X, δ.val i m)
      = ∑ m : X, (δ'.val i m - δ.val i m) :=
    (Finset.sum_sub_distrib (f := fun m => δ'.val i m) (g := fun m => δ.val i m)).symm
  have e2 : (∑ m : X, δ'.val j m) - (∑ m : X, δ.val j m)
      = ∑ m : X, (δ'.val j m - δ.val j m) :=
    (Finset.sum_sub_distrib (f := fun m => δ'.val j m) (g := fun m => δ.val j m)).symm
  simp only [Q]
  linarith

omit [DecidableEq X] in
/-- 单个 `Q` 的扰动展开（式 (16) 的右半；取向与 `Q_perturb_pos` **相同**，
省去「`Σ(−f) = −Σf`」这一步）。 -/
theorem Q_perturb_neg (δ δ' : Dissimilarity X) (i j : X) :
    δ.Q i j - δ'.Q i j
      = -(((Fintype.card X : ℝ) - 2) * (δ'.val i j - δ.val i j))
        + (∑ m : X, (δ'.val i m - δ.val i m))
        + (∑ m : X, (δ'.val j m - δ.val j m)) := by
  have e1 : (∑ m : X, δ'.val i m) - (∑ m : X, δ.val i m)
      = ∑ m : X, (δ'.val i m - δ.val i m) :=
    (Finset.sum_sub_distrib (f := fun m => δ'.val i m) (g := fun m => δ.val i m)).symm
  have e2 : (∑ m : X, δ'.val j m) - (∑ m : X, δ.val j m)
      = ∑ m : X, (δ'.val j m - δ.val j m) :=
    (Finset.sum_sub_distrib (f := fun m => δ'.val j m) (g := fun m => δ.val j m)).symm
  simp only [Q]
  linarith

omit [DecidableEq X] in
/-- ★★★ **Atteson 式 (16) 的精确恒等式**（`:2195–2201`），记 `ε_ab = δ'.val a b − δ.val a b`：

`(Ŝ_kl − S_kl) + (S_ij − Ŝ_ij) = (n−2)(ε_kl − ε_ij) + Σ_m (ε_im + ε_jm − ε_km − ε_lm)`。

这是整个安全半径证明的**命门**：右端第二项对 `m ∈ {i,j,k,l}` 的贡献恰为 `2ε_ij − 2ε_kl`
（见 ★★★ `sum_quartet_four`），与第一项合并后系数从 `n−2` 掉到 `n−4`。 -/
theorem qPerturb_cancel (δ δ' : Dissimilarity X) (i j k l : X) :
    (δ'.Q k l - δ.Q k l) + (δ.Q i j - δ'.Q i j)
      = ((Fintype.card X : ℝ) - 2)
          * ((δ'.val k l - δ.val k l) - (δ'.val i j - δ.val i j))
        + ∑ m : X, ((δ'.val i m - δ.val i m) + (δ'.val j m - δ.val j m)
                    - (δ'.val k m - δ.val k m) - (δ'.val l m - δ.val l m)) := by
  rw [Q_perturb_pos δ δ' k l, Q_perturb_neg δ δ' i j]
  rw [sum_four_sub]
  ring

/-- ★★★ **式 (16) 的「已化简」形式**：把 `m ∈ {i,j,k,l}` 的四项用
★★★ `sum_quartet_four` 算掉之后，剩下 `(n−4)(ε_kl − ε_ij)` 与一个**只跑
`m ∉ {i,j,k,l}`** 的和（Atteson1999 `:2205–2221`）。 -/
theorem qPerturb_reduced (δ δ' : Dissimilarity X) {i j k l : X}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (δ'.Q k l - δ.Q k l) + (δ.Q i j - δ'.Q i j)
      = ((Fintype.card X : ℝ) - 4) * ((δ'.val k l - δ.val k l) - (δ'.val i j - δ.val i j))
        + ∑ m ∈ ((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)),
            ((δ'.val i m - δ.val i m) + (δ'.val j m - δ.val j m)
              - (δ'.val k m - δ.val k m) - (δ'.val l m - δ.val l m)) := by
  have hS := sum_quartet_four (fun a b => δ'.val a b - δ.val a b)
    (fun a b => by rw [δ.symm a b, δ'.symm a b])
    (fun a => by rw [δ.diag a, δ'.diag a, sub_self])
    hij hik hil hjk hjl hkl
  have hsplit := Finset.sum_sdiff (s₁ := ({i, j, k, l} : Finset X))
    (s₂ := (Finset.univ : Finset X))
    (f := fun m => ((δ'.val i m - δ.val i m) + (δ'.val j m - δ.val j m)
              - (δ'.val k m - δ.val k m) - (δ'.val l m - δ.val l m)))
    (Finset.subset_univ _)
  rw [qPerturb_cancel δ δ' i j k l, ← hsplit, hS]
  ring

/-- ★★ **`i = k` 时的化简**（Atteson1999 Lemma 12 第二种情形 `:2223–2252`）。 -/
theorem qPerturb_reduced_ik (δ δ' : Dissimilarity X) {i j l : X}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    (δ'.Q i l - δ.Q i l) + (δ.Q i j - δ'.Q i j)
      = ((Fintype.card X : ℝ) - 3)
          * ((δ'.val i l - δ.val i l) - (δ'.val i j - δ.val i j))
        + ∑ m ∈ ((Finset.univ : Finset X) \ ({i, j, l} : Finset X)),
            ((δ'.val j m - δ.val j m) - (δ'.val l m - δ.val l m)) := by
  have h1 : (∑ m : X, ((δ'.val i m - δ.val i m) + (δ'.val j m - δ.val j m)
              - (δ'.val i m - δ.val i m) - (δ'.val l m - δ.val l m)))
      = ∑ m : X, ((δ'.val j m - δ.val j m) - (δ'.val l m - δ.val l m)) := by
    refine Finset.sum_congr rfl ?_
    intro m _
    ring
  rw [qPerturb_cancel δ δ' i j i l, h1]
  have h3 : (∑ m ∈ ({i, j, l} : Finset X),
        ((δ'.val j m - δ.val j m) - (δ'.val l m - δ.val l m)))
      = (δ'.val i j - δ.val i j) - (δ'.val i l - δ.val i l) := by
    rw [sum_three_elems (fun m => (δ'.val j m - δ.val j m) - (δ'.val l m - δ.val l m))
      hij hil hjl]
    rw [δ.symm j i, δ'.symm j i, δ.symm l i, δ'.symm l i, δ.symm l j, δ'.symm l j,
        δ.diag j, δ'.diag j, δ.diag l, δ'.diag l]
    ring
  have h4 := Finset.sum_sdiff (s₁ := ({i, j, l} : Finset X)) (s₂ := (Finset.univ : Finset X))
    (f := fun m => ((δ'.val j m - δ.val j m) - (δ'.val l m - δ.val l m)))
    (Finset.subset_univ _)
  rw [← h4, h3]
  ring

/-! ## 3. 两条界：Atteson Lemma 12（`:2181–2189`） -/

omit [Fintype X] [DecidableEq X] in
/-- ★ `NearlyAdditive` ⟹ **`δmin > 0`**。

由 `IsLinfClose` 的**对角项** `|δ'(i,i) − δ(i,i)| = |0| = 0 ≤ ε` 得 `ε ≥ 0`，
再由 `ε < safeRadius δmin = δmin/2` 得 `δmin > 0`。

⇒ ★★★ `njCriterion_minimizer_is_cherry` 的陈述**不需**把 `δmin > 0` 列为假设
（它由 `NearlyAdditive` 自动给出）。 -/
theorem nearlyAdditive_deltaMin_pos (δ δ' : Dissimilarity X) {δmin ε : ℝ}
    (hnear : NearlyAdditive δ δ' δmin ε) (i : X) : 0 < δmin := by
  obtain ⟨hε, hεr⟩ := hnear
  have hh := hε i i
  rw [δ'.diag i, δ.diag i, sub_self, abs_zero] at hh
  rw [safeRadius] at hεr
  linarith

omit [Fintype X] [DecidableEq X] in
/-- 单点四元组合的下界：`a + b − c − d ≥ −4ε`（若 `|a|,|b|,|c|,|d| ≤ ε`）。 -/
theorem four_term_ge {a b c d ε : ℝ}
    (ha : |a| ≤ ε) (hb : |b| ≤ ε) (hc : |c| ≤ ε) (hd : |d| ≤ ε) :
    -4 * ε ≤ a + b - c - d := by
  have ha1 := (abs_le.mp ha).1
  have hb1 := (abs_le.mp hb).1
  have hc2 := (abs_le.mp hc).2
  have hd2 := (abs_le.mp hd).2
  linarith

omit [Fintype X] [DecidableEq X] in
/-- 单点二元组合的下界：`a − b ≥ −2ε`（若 `|a|,|b| ≤ ε`）。 -/
theorem two_term_ge {a b ε : ℝ} (ha : |a| ≤ ε) (hb : |b| ≤ ε) : -2 * ε ≤ a - b := by
  have ha1 := (abs_le.mp ha).1
  have hb2 := (abs_le.mp hb).2
  linarith

/-- ★★ **Atteson Lemma 12 第一式**（`:2181–2185`）：`{i,j} ∩ {k,l} = ∅` 时
`(Ŝ_kl − S_kl) + (S_ij − Ŝ_ij) ≥ −6(n−4)·ε`。 -/
theorem qPerturb_bound_disjoint (δ δ' : Dissimilarity X) {ε : ℝ}
    (hε : IsLinfClose δ δ' ε) {i j k l : X} (hij : i ≠ j)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hcard : 4 ≤ Fintype.card X) :
    -6 * ((Fintype.card X : ℝ) - 4) * ε
      ≤ (δ'.Q k l - δ.Q k l) + (δ.Q i j - δ'.Q i j) := by
  rw [qPerturb_reduced δ δ' hij hik hil hjk hjl hkl]
  have hcomp : ((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)).card
      = Fintype.card X - 4 := by
    rw [card_sdiff_univ, card_four_elems i j k l hij hik hil hjk hjl hkl]
  have hnn : (0 : ℝ) ≤ (Fintype.card X : ℝ) - 4 := by
    have h : (4 : ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast hcard
    linarith
  have hA : ((Fintype.card X : ℝ) - 4) * (-2 * ε)
      ≤ ((Fintype.card X : ℝ) - 4)
          * ((δ'.val k l - δ.val k l) - (δ'.val i j - δ.val i j)) := by
    refine mul_le_mul_of_nonneg_left ?_ hnn
    have h1 := (abs_le.mp (hε k l)).1
    have h2 := (abs_le.mp (hε i j)).2
    linarith
  have hB : -4 * (((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)).card : ℝ) * ε
      ≤ ∑ m ∈ ((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)),
          ((δ'.val i m - δ.val i m) + (δ'.val j m - δ.val j m)
            - (δ'.val k m - δ.val k m) - (δ'.val l m - δ.val l m)) := by
    have hpt : ∀ m ∈ ((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)),
        -4 * ε ≤ ((δ'.val i m - δ.val i m) + (δ'.val j m - δ.val j m)
            - (δ'.val k m - δ.val k m) - (δ'.val l m - δ.val l m)) :=
      fun m _ => four_term_ge (hε i m) (hε j m) (hε k m) (hε l m)
    have h2 := Finset.sum_le_sum hpt
    have h3 : (∑ m ∈ ((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)), (-4 * ε))
        = -4 * (((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)).card : ℝ) * ε := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    rwa [h3] at h2
  have hcast : (((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)).card : ℝ)
      = (Fintype.card X : ℝ) - 4 := by
    rw [hcomp, Nat.cast_sub hcard]
    norm_num
  rw [hcast] at hB
  linarith

/-- ★★ **Atteson Lemma 12 第二式（`i = k` 规范形）**（`:2187–2189`、`:2223–2252`）：
`(Ŝ_il − S_il) + (S_ij − Ŝ_ij) ≥ −4(n−3)·ε`。 -/
theorem qPerturb_bound_shared_canon (δ δ' : Dissimilarity X) {ε : ℝ}
    (hε : IsLinfClose δ δ' ε) {i j l : X} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hcard : 3 ≤ Fintype.card X) :
    -4 * ((Fintype.card X : ℝ) - 3) * ε
      ≤ (δ'.Q i l - δ.Q i l) + (δ.Q i j - δ'.Q i j) := by
  rw [qPerturb_reduced_ik δ δ' hij hil hjl]
  have hcomp : ((Finset.univ : Finset X) \ ({i, j, l} : Finset X)).card
      = Fintype.card X - 3 := by
    rw [card_sdiff_univ, card_three_elems i j l hij hil hjl]
  have hnn : (0 : ℝ) ≤ (Fintype.card X : ℝ) - 3 := by
    have h : (3 : ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast hcard
    linarith
  have hA : ((Fintype.card X : ℝ) - 3) * (-2 * ε)
      ≤ ((Fintype.card X : ℝ) - 3)
          * ((δ'.val i l - δ.val i l) - (δ'.val i j - δ.val i j)) := by
    refine mul_le_mul_of_nonneg_left ?_ hnn
    have h1 := (abs_le.mp (hε i l)).1
    have h2 := (abs_le.mp (hε i j)).2
    linarith
  have hB : -2 * (((Finset.univ : Finset X) \ ({i, j, l} : Finset X)).card : ℝ) * ε
      ≤ ∑ m ∈ ((Finset.univ : Finset X) \ ({i, j, l} : Finset X)),
          ((δ'.val j m - δ.val j m) - (δ'.val l m - δ.val l m)) := by
    have hpt : ∀ m ∈ ((Finset.univ : Finset X) \ ({i, j, l} : Finset X)),
        -2 * ε ≤ ((δ'.val j m - δ.val j m) - (δ'.val l m - δ.val l m)) :=
      fun m _ => two_term_ge (hε j m) (hε l m)
    have h2 := Finset.sum_le_sum hpt
    have h3 : (∑ m ∈ ((Finset.univ : Finset X) \ ({i, j, l} : Finset X)), (-2 * ε))
        = -2 * (((Finset.univ : Finset X) \ ({i, j, l} : Finset X)).card : ℝ) * ε := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    rwa [h3] at h2
  have hcast : (((Finset.univ : Finset X) \ ({i, j, l} : Finset X)).card : ℝ)
      = (Fintype.card X : ℝ) - 3 := by
    rw [hcomp, Nat.cast_sub hcard]
    norm_num
  rw [hcast] at hB
  linarith

/-- ★★ **Atteson Lemma 12 第二式（一般重合形态）**（`:2187–2189`）：
`{i,j}` 与 `{k,l}` 恰交一个标签时 `(Ŝ_kl − S_kl) + (S_ij − Ŝ_ij) ≥ −4(n−3)·ε`。

四种重合形态通过 `Q` 的对称性 `Q(a,b) = Q(b,a)` 归约到 `i = k` 规范形。 -/
theorem qPerturb_bound_shared (δ δ' : Dissimilarity X) {ε : ℝ}
    (hε : IsLinfClose δ δ' ε) {i j k l : X} (hij : i ≠ j) (hkl : k ≠ l)
    (hov : SharesOneLabel i j k l) (hcard : 3 ≤ Fintype.card X) :
    -4 * ((Fintype.card X : ℝ) - 3) * ε
      ≤ (δ'.Q k l - δ.Q k l) + (δ.Q i j - δ'.Q i j) := by
  have hQc : ∀ (ρ : Dissimilarity X) (a b : X), ρ.Q a b = ρ.Q b a := by
    intro ρ a b
    simp only [Q]
    rw [ρ.symm b a]
    ring
  rcases hov with ⟨hik, hjk, hjl⟩ | ⟨hil, hjk, hjl⟩ | ⟨hjk, hik, hil⟩ | ⟨hjl, hik, hil⟩
  · rw [← hik]
    exact qPerturb_bound_shared_canon δ δ' hε hij (hik.symm ▸ hkl) hjl hcard
  · rw [hil, hQc δ' k l, hQc δ k l]
    exact qPerturb_bound_shared_canon δ δ' hε (Ne.symm hjl) (Ne.symm hkl) hjk hcard
  · rw [hQc δ i j, hQc δ' i j, hjk]
    exact qPerturb_bound_shared_canon δ δ' hε (Ne.symm hik) hkl hil hcard
  · rw [hQc δ i j, hQc δ' i j, hQc δ' k l, hQc δ k l, hjl]
    exact qPerturb_bound_shared_canon δ δ' hε (Ne.symm hil) (Ne.symm hkl) hik hcard

/-! ## 4. ★★★ 主定理：安全半径 `1/2` 下 NJ 第一轮必取真樱桃 -/

/-- ★★★ **Atteson 安全半径：`n ≥ 5` 时 NJ 第一轮判据的任何最小点都是真树的樱桃**。

（Atteson1999 Theorem 4 的第一步，`:2266–2303`；Theorem 1 归纳的**基例**，`:889`。）

设 `δ` 是真加权二叉树的距离矩阵（「真」的全部内容通过 ★★ `IsCherrySeparated δ δmin`
以 `δmin =` 实现树最短边长的形式给出），`δ'` 是观测矩阵且
`‖δ' − δ‖_∞ ≤ ε < 1/2 · δmin`。则任何使 NJ 判据 `Q_{δ'}` 取最小值的**相异**标签对
`(a,b)` 都是 `δ` 的一颗樱桃（即真树中相邻）。

**证明链**：反设 `(a,b)` 非樱桃，由 ★★ `IsCherrySeparated` 取樱桃 `(i,j)`
⇒ 由 ★★ `qPerturb_bound_disjoint`（或 ★★ `qPerturb_bound_shared`）得
`Q_{δ'}(a,b) − Q_{δ'}(i,j) ≥ −6(n−4)ε + 3(n−4)δmin = 3(n−4)(δmin − 2ε) > 0`，
与最小性矛盾。 -/
theorem njCriterion_minimizer_is_cherry (δ δ' : Dissimilarity X) {δmin ε : ℝ}
    (hnear : NearlyAdditive δ δ' δmin ε)
    (hcard : 5 ≤ Fintype.card X) (hsep : IsCherrySeparated δ δmin)
    {a b : X} (hab : a ≠ b)
    (hmin : ∀ x y : X, x ≠ y → δ'.Q a b ≤ δ'.Q x y) :
    δ.IsCherry a b := by
  obtain ⟨hε, hεr⟩ := hnear
  by_contra hnc
  obtain ⟨i, j, hcherry, hcase⟩ := hsep a b hab hnc
  have hij : i ≠ j := hcherry.1
  have hn : (0 : ℝ) < (Fintype.card X : ℝ) - 4 := by
    have h : (5 : ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast hcard
    linarith
  have hε2 : 2 * ε < δmin := by
    rw [safeRadius] at hεr
    linarith
  have hkey : δ'.Q i j < δ'.Q a b := by
    have hdecomp : δ'.Q a b - δ'.Q i j
        = ((δ'.Q a b - δ.Q a b) + (δ.Q i j - δ'.Q i j)) + (δ.Q a b - δ.Q i j) := by ring
    have hpos : 0 < δ'.Q a b - δ'.Q i j := by
      rw [hdecomp]
      rcases hcase with ⟨hdis, hbnd⟩ | ⟨hsh, hbnd⟩
      · obtain ⟨hik, hil, hjk, hjl⟩ := hdis
        have hb := qPerturb_bound_disjoint δ δ' hε hij hik hil hjk hjl hab
          (le_trans (by norm_num : (4:ℕ) ≤ 5) hcard)
        have hfac : 3 * ((Fintype.card X : ℝ) - 4) * (δmin - 2 * ε)
            ≤ ((δ'.Q a b - δ.Q a b) + (δ.Q i j - δ'.Q i j)) + (δ.Q a b - δ.Q i j) := by
          linarith
        have hpos' : 0 < 3 * ((Fintype.card X : ℝ) - 4) * (δmin - 2 * ε) := by
          have h2 : 0 < δmin - 2 * ε := by linarith [hε2]
          exact mul_pos (mul_pos (by norm_num) hn) h2
        linarith
      · have hb := qPerturb_bound_shared δ δ' hε hij hab hsh
          (le_trans (by norm_num : (3:ℕ) ≤ 5) hcard)
        have h3 : (0 : ℝ) < (Fintype.card X : ℝ) - 3 := by
          have h : (5 : ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast hcard
          linarith
        have hfac : 2 * ((Fintype.card X : ℝ) - 3) * (δmin - 2 * ε)
            ≤ ((δ'.Q a b - δ.Q a b) + (δ.Q i j - δ'.Q i j)) + (δ.Q a b - δ.Q i j) := by
          linarith
        have hpos' : 0 < 2 * ((Fintype.card X : ℝ) - 3) * (δmin - 2 * ε) := by
          have h2 : 0 < δmin - 2 * ε := by linarith [hε2]
          exact mul_pos (mul_pos (by norm_num) h3) h2
        linarith
    linarith
  exact absurd (hmin i j hij) (not_le.mpr hkey)

/-- ★★★ **`n = 4` 版本**（Atteson1999 `:2205–2221` 的 `n = 4` 退化）。

`n = 4` 时两对不可能「不交且一为樱桃」——樱桃的补对是另一颗樱桃
—— 故分离只能走「恰交一个标签」分支，界 `2(n−3)δmin = 2δmin` 与 `−4(n−3)ε = −4ε`
仍然给出 `2(δmin − 2ε) > 0`：**半径 `1/2` 在 `n = 4` 也成立**。 -/
theorem njCriterion_minimizer_is_cherry_card_four (δ δ' : Dissimilarity X) {δmin ε : ℝ}
    (hnear : NearlyAdditive δ δ' δmin ε)
    (hcard : Fintype.card X = 4)
    (hsep : ∀ k l : X, k ≠ l → ¬ δ.IsCherry k l →
      ∃ i j : X, δ.IsCherry i j ∧ SharesOneLabel i j k l ∧
        2 * ((Fintype.card X : ℝ) - 3) * δmin ≤ δ.Q k l - δ.Q i j)
    {a b : X} (hab : a ≠ b)
    (hmin : ∀ x y : X, x ≠ y → δ'.Q a b ≤ δ'.Q x y) :
    δ.IsCherry a b := by
  obtain ⟨hε, hεr⟩ := hnear
  by_contra hnc
  obtain ⟨i, j, hcherry, hsh, hbnd⟩ := hsep a b hab hnc
  have hij : i ≠ j := hcherry.1
  have hcard3 : (3 : ℕ) ≤ Fintype.card X := by rw [hcard]; norm_num
  have h3 : (0 : ℝ) < (Fintype.card X : ℝ) - 3 := by
    rw [hcard]; norm_num
  have hε2 : 2 * ε < δmin := by
    rw [safeRadius] at hεr
    linarith
  have hkey : δ'.Q i j < δ'.Q a b := by
    have hdecomp : δ'.Q a b - δ'.Q i j
        = ((δ'.Q a b - δ.Q a b) + (δ.Q i j - δ'.Q i j)) + (δ.Q a b - δ.Q i j) := by ring
    have hpos : 0 < δ'.Q a b - δ'.Q i j := by
      rw [hdecomp]
      have hb := qPerturb_bound_shared δ δ' hε hij hab hsh hcard3
      have hfac : 2 * ((Fintype.card X : ℝ) - 3) * (δmin - 2 * ε)
          ≤ ((δ'.Q a b - δ.Q a b) + (δ.Q i j - δ'.Q i j)) + (δ.Q a b - δ.Q i j) := by
        linarith
      have hpos' : 0 < 2 * ((Fintype.card X : ℝ) - 3) * (δmin - 2 * ε) := by
        have h2 : 0 < δmin - 2 * ε := by linarith [hε2]
        exact mul_pos (mul_pos (by norm_num) h3) h2
      linarith
    linarith
  exact absurd (hmin i j hij) (not_le.mpr hkey)

/-! ## 5. `n = 4` 的精确抵消 -/

/-- ★★ **`n = 4` 时 `Q` 的排序在不相交对上完全不受扰动影响**。

由 ★★★ `qPerturb_reduced`：`n = 4` 且四标签互异时 `n − 4 = 0` 且补集为空
⇒ 式 (16) 的右端**恒为 `0`**。 -/
theorem qPerturb_cancel_of_card_four (hcard : Fintype.card X = 4)
    (δ δ' : Dissimilarity X) {i j k l : X} (hij : i ≠ j)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    δ'.Q k l - δ'.Q i j = δ.Q k l - δ.Q i j := by
  have hcomp : ((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)).card
      = Fintype.card X - 4 := by
    rw [card_sdiff_univ, card_four_elems i j k l hij hik hil hjk hjl hkl]
  have hzero : ((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)).card = 0 := by
    rw [hcomp, hcard]
  have hempty : ((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)) = ∅ :=
    Finset.card_eq_zero.mp hzero
  have hred := qPerturb_reduced δ δ' hij hik hil hjk hjl hkl
  rw [hempty, Finset.sum_empty, hcard] at hred
  norm_num at hred
  linarith

/-! ## 6. ★★ Lemma 7 的一步形式：更新式 (6) 不放大 `L∞` 扰动 -/

omit [Fintype X] [DecidableEq X] in
/-- ★★ **Atteson Lemma 7 的一步形式**（`:749–751`；更新式 (6) 见 `:611`）。

`δ_u(x) = θ·δ_i(x) + (1−θ)·δ_j(x)`（`0 ≤ θ ≤ 1`）是凸组合，
故 `|δ'_u(x) − δ_u(x)| ≤ θ·ε + (1−θ)·ε = ε`：**合并操作不放大 `L∞` 误差**。
这正是 Theorem 1 归纳（`:889–915`）中 `‖D̃_m − D_m‖_∞ ≤ ‖D̃ − D‖_∞` 的递推步。 -/
theorem linfClose_update (δ δ' : Dissimilarity X) {ε θ : ℝ} (hε : IsLinfClose δ δ' ε)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (i j x : X) :
    |(θ * δ'.val i x + (1 - θ) * δ'.val j x) - (θ * δ.val i x + (1 - θ) * δ.val j x)| ≤ ε := by
  have h1 : |δ'.val i x - δ.val i x| ≤ ε := hε i x
  have h2 : |δ'.val j x - δ.val j x| ≤ ε := hε j x
  have h3 : (θ * δ'.val i x + (1 - θ) * δ'.val j x) - (θ * δ.val i x + (1 - θ) * δ.val j x)
      = θ * (δ'.val i x - δ.val i x) + (1 - θ) * (δ'.val j x - δ.val j x) := by ring
  rw [h3]
  have hb1 : |θ * (δ'.val i x - δ.val i x)| ≤ θ * ε := by
    rw [abs_mul, abs_of_nonneg hθ0]
    exact mul_le_mul_of_nonneg_left h1 hθ0
  have hb2 : |(1 - θ) * (δ'.val j x - δ.val j x)| ≤ (1 - θ) * ε := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - θ)]
    exact mul_le_mul_of_nonneg_left h2 (by linarith)
  have htri : |θ * (δ'.val i x - δ.val i x) + (1 - θ) * (δ'.val j x - δ.val j x)|
      ≤ |θ * (δ'.val i x - δ.val i x)| + |(1 - θ) * (δ'.val j x - δ.val j x)| := by
    have h := abs_sub_le (θ * (δ'.val i x - δ.val i x)) 0
      (-((1 - θ) * (δ'.val j x - δ.val j x)))
    simpa using h
  calc |θ * (δ'.val i x - δ.val i x) + (1 - θ) * (δ'.val j x - δ.val j x)|
      ≤ |θ * (δ'.val i x - δ.val i x)| + |(1 - θ) * (δ'.val j x - δ.val j x)| := htri
    _ ≤ θ * ε + (1 - θ) * ε := add_le_add hb1 hb2
    _ = ε := by ring

/-! ## 7. ★C 最小具体例子：`Fin 4`，挂边 `1,2,3,4`、内部边 `5`

树 `((0,1),(2,3))`：`d(0,1) = 1+2 = 3`、`d(2,3) = 3+4 = 7`、
`d(0,2) = 1+5+3 = 9`、`d(0,3) = 1+5+4 = 10`、`d(1,2) = 2+5+3 = 10`、`d(1,3) = 2+5+4 = 11`。
最短边长 `δmin = 1` ⇒ `safeRadius 1 = 1/2`。

`Q(i,j) = 2·d_ij − S(i) − S(j)`（`n = 4`），`S = (22, 24, 26, 28)`，故

`Q(0,1) = Q(2,3) = −40`（**两颗樱桃**），四个交叉对全部 `= −30`。 -/

/-- `Fin 4` 上的求和展开（`∑ k : Fin 4, f k = f 0 + f 1 + f 2 + f 3`）。 -/
theorem sum_univ_four_fin (f : Fin 4 → ℝ) :
    (∑ k : Fin 4, f k) = f 0 + (f 1 + (f 2 + f 3)) := by
  have h : ({0, 1, 2, 3} : Finset (Fin 4)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by decide)
  rw [← h]
  exact sum_four_elems f (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 真距离矩阵的值函数（★C 最小例子）。 -/
def exVal : Fin 4 → Fin 4 → ℝ
  | 0, 0 => 0 | 1, 1 => 0 | 2, 2 => 0 | 3, 3 => 0
  | 0, 1 => 3 | 1, 0 => 3
  | 2, 3 => 7 | 3, 2 => 7
  | 0, 2 => 9 | 2, 0 => 9
  | 0, 3 => 10 | 3, 0 => 10
  | 1, 2 => 10 | 2, 1 => 10
  | 1, 3 => 11 | 3, 1 => 11

/-- ★C 的真相异度：树 `((0,1),(2,3))`，挂边 `1,2,3,4`、内部边 `5`。 -/
def exDiss : Dissimilarity (Fin 4) where
  val := exVal
  symm := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  diag := by intro i; fin_cases i <;> rfl

/-- 观测扰动矩阵的值函数：非对角扰动 `∈ {−1/5, +1/5, +2/5}`
（`‖ε‖_∞ = 2/5 < safeRadius 1 = 1/2`）。 -/
def exPertVal : Fin 4 → Fin 4 → ℝ
  | 0, 0 => 0 | 1, 1 => 0 | 2, 2 => 0 | 3, 3 => 0
  | 0, 1 => 17 / 5 | 1, 0 => 17 / 5
  | 2, 3 => 36 / 5 | 3, 2 => 36 / 5
  | 0, 2 => 44 / 5 | 2, 0 => 44 / 5
  | 0, 3 => 51 / 5 | 3, 0 => 51 / 5
  | 1, 2 => 49 / 5 | 2, 1 => 49 / 5
  | 1, 3 => 56 / 5 | 3, 1 => 56 / 5

/-- ★C 的观测相异度 `δ' = δ + ε`（`|ε_ij| ≤ 2/5`）。 -/
def exPert : Dissimilarity (Fin 4) where
  val := exPertVal
  symm := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  diag := by intro i; fin_cases i <;> rfl

/-- ★C：`(0,1)` 是真树的一颗樱桃（`d(0,1)+d(2,3) = 10 ≤ 20 = d(0,2)+d(1,3) = d(0,3)+d(1,2)`）。 -/
theorem exDiss_isCherry_01 : exDiss.IsCherry 0 1 := by
  refine ⟨by decide, ?_⟩
  intro k l hk0 hk1 hl0 hl1
  have hk : k = 2 ∨ k = 3 := by fin_cases k <;> simp_all
  have hl : l = 2 ∨ l = 3 := by fin_cases l <;> simp_all
  rcases hk with rfl | rfl <;> rcases hl with rfl | rfl <;>
    (simp only [exDiss, exVal]; constructor <;> norm_num)

/-- ★C：真距离矩阵上 `Q` 的六个值 —— 两颗樱桃 `(0,1)、(2,3)` 取 `−40`，
四个交叉对取 `−30`（`Q(i,j) = 2·d_ij − S(i) − S(j)`）。 -/
theorem exDiss_Q_01 : exDiss.Q 0 1 = -40 := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exDiss, exVal]
  norm_num

theorem exDiss_Q_23 : exDiss.Q 2 3 = -40 := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exDiss, exVal]
  norm_num

theorem exDiss_Q_02 : exDiss.Q 0 2 = -30 := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exDiss, exVal]
  norm_num

theorem exDiss_Q_03 : exDiss.Q 0 3 = -30 := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exDiss, exVal]
  norm_num

theorem exDiss_Q_12 : exDiss.Q 1 2 = -30 := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exDiss, exVal]
  norm_num

theorem exDiss_Q_13 : exDiss.Q 1 3 = -30 := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exDiss, exVal]
  norm_num

theorem exDiss_Q_10 : exDiss.Q 1 0 = -40 := by
  rw [Q_comm exDiss 1 0]
  exact exDiss_Q_01

theorem exDiss_Q_20 : exDiss.Q 2 0 = -30 := by
  rw [Q_comm exDiss 2 0]
  exact exDiss_Q_02

theorem exDiss_Q_30 : exDiss.Q 3 0 = -30 := by
  rw [Q_comm exDiss 3 0]
  exact exDiss_Q_03

theorem exDiss_Q_21 : exDiss.Q 2 1 = -30 := by
  rw [Q_comm exDiss 2 1]
  exact exDiss_Q_12

theorem exDiss_Q_31 : exDiss.Q 3 1 = -30 := by
  rw [Q_comm exDiss 3 1]
  exact exDiss_Q_13

theorem exDiss_Q_32 : exDiss.Q 3 2 = -40 := by
  rw [Q_comm exDiss 3 2]
  exact exDiss_Q_23

/-- ★C：真树上 `Q` 的最小点是樱桃（`Q(0,1) = Q(2,3) = −40 < −30 = ` 任何交叉对）。 -/
theorem exDiss_argmin_isCherry : ∀ i j : Fin 4, i ≠ j → exDiss.Q 0 1 ≤ exDiss.Q i j := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [exDiss_Q_01, exDiss_Q_23, exDiss_Q_02, exDiss_Q_03, exDiss_Q_12, exDiss_Q_13,
      exDiss_Q_10, exDiss_Q_20, exDiss_Q_30, exDiss_Q_21, exDiss_Q_31, exDiss_Q_32] <;>
    norm_num

/-- ★C：观测矩阵上 `Q` 的六个值 —— 与真矩阵的**排序完全一致**
（`(0,1)、(2,3)` 仍取 `−40`，交叉对一致降到 `−153/5`）。 -/
theorem exPert_Q_01 : exPert.Q 0 1 = -40 := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exPert, exPertVal]
  norm_num

theorem exPert_Q_23 : exPert.Q 2 3 = -40 := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exPert, exPertVal]
  norm_num

theorem exPert_Q_02 : exPert.Q 0 2 = -(153 / 5) := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exPert, exPertVal]
  norm_num

theorem exPert_Q_03 : exPert.Q 0 3 = -(153 / 5) := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exPert, exPertVal]
  norm_num

theorem exPert_Q_12 : exPert.Q 1 2 = -(153 / 5) := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exPert, exPertVal]
  norm_num

theorem exPert_Q_13 : exPert.Q 1 3 = -(153 / 5) := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exPert, exPertVal]
  norm_num

theorem exPert_Q_10 : exPert.Q 1 0 = -40 := by
  rw [Q_comm exPert 1 0]
  exact exPert_Q_01

theorem exPert_Q_20 : exPert.Q 2 0 = -(153 / 5) := by
  rw [Q_comm exPert 2 0]
  exact exPert_Q_02

theorem exPert_Q_30 : exPert.Q 3 0 = -(153 / 5) := by
  rw [Q_comm exPert 3 0]
  exact exPert_Q_03

theorem exPert_Q_21 : exPert.Q 2 1 = -(153 / 5) := by
  rw [Q_comm exPert 2 1]
  exact exPert_Q_12

theorem exPert_Q_31 : exPert.Q 3 1 = -(153 / 5) := by
  rw [Q_comm exPert 3 1]
  exact exPert_Q_13

theorem exPert_Q_32 : exPert.Q 3 2 = -40 := by
  rw [Q_comm exPert 3 2]
  exact exPert_Q_23

/-- ★C ★★★ **端到端**：观测矩阵 `δ'`（`‖δ' − δ‖_∞ = 2/5 < 1/2 = safeRadius 1`）上
`Q` 的最小点仍是真树的樱桃 `(0,1)`。 -/
theorem exPert_argmin_isCherry : ∀ i j : Fin 4, i ≠ j → exPert.Q 0 1 ≤ exPert.Q i j := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [exPert_Q_01, exPert_Q_23, exPert_Q_02, exPert_Q_03, exPert_Q_12, exPert_Q_13,
      exPert_Q_10, exPert_Q_20, exPert_Q_30, exPert_Q_21, exPert_Q_31, exPert_Q_32] <;>
    norm_num

/-- ★C：`δ'` 确实在安全半径内（`‖δ' − δ‖_∞ ≤ 2/5 < safeRadius 1`）。 -/
theorem exPert_nearlyAdditive : NearlyAdditive exDiss exPert 1 (2 / 5) := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [exPert, exDiss, exPertVal, exVal] <;> norm_num
  · rw [safeRadius]; norm_num

/-- 反空真：`δ` 满足四点条件（Tree metric ⟹ four-point）⇒ 缺口的**前提非空**。 -/
theorem exDiss_fourPoint : exDiss.FourPoint := by
  intro i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [exDiss, exVal] <;> norm_num

/-! ## 8. 缺口命题（**不是数学缺口，是本库的工程缺口**） -/

/-- ★★★ **缺口 1：Atteson Lemma 11 的度量版**（`:1989–2009`）的可实现性。

设 `δ` 是由**正边权**二叉树实现的距离矩阵（本库判据：`FourPoint` + `PositiveDefinite`，
见 `Phylo/Buneman.lean:589` 的 `ExistsRealizingPhylogram`），叶子数 `≥ 4`。则存在
`δmin > 0`（= 实现树的最短边长）使 ★★ `IsCherrySeparated δ δmin` 成立。

**这是把 ★★★ `njCriterion_minimizer_is_cherry` 从条件定理变成
「无条件 Atteson 安全半径定理」的**唯一**剩余缺口。**

缺的机制（Atteson Lemma 10，`:1774–1804`）：`Q(i,j) = Σ_{e∈E} w_e(i,j)·l(e)`，其中
`w_e(i,j) = −2`（`e ∈ P_{i,j}`）、`= −2|L − L_i(e)|`（否则）—— 只依赖拓扑；
于是 `Q(k,l) − Q(i,j) = Σ_e (w_e(k,l) − w_e(i,j))·l(e)`，逐边比较并使用
「路径旁子树的叶数」单调性（`:2023–2056`）即得。

**缺什么**：本库 `Phylogram` 有 `dist` 与边权，但**没有**
(a)「`Dissimilarity.IsCherry δ a b` ⟺ 树中 `a,b` 相邻」的桥，
(b)「路径关联 `e ∈ P_{i,j}` + 子树叶数 `|L_i(e)|`」的层，
(c) Lemma 10 的权重公式 `w_e`。

**反空真**：★★ `exDiss_fourPoint` 给出前提可满足；★C `exDiss_argmin_isCherry`
给出结论方向上 `n = 4` 的具体实例。 -/
def atteson_lemma11_gap (δ : Dissimilarity X) : Prop :=
  δ.FourPoint → δ.PositiveDefinite → 4 ≤ Fintype.card X →
    ∃ δmin : ℝ, 0 < δmin ∧ δ.IsCherrySeparated δmin

/-- ★★★ **缺口 2：Atteson Lemma 6 的归约步**（`:677–694` 边权公式 (7)），
即 Theorem 1（`:868–916`）归纳不变量 (a)(b) 的递推。

设 `δ` 可加（`FourPoint`）、`(i,j)` 是 `δ` 的樱桃、`θ ∈ [0,1]`。则把 `i,j` 按更新式 (6)
（`:611`）合并成新标签后，在**商标签集** `Y` 上得到的 `δm` 满足：
`card Y + 1 = card X`、非 `{i,j}` 对的取值不变、新标签处的取值是凸组合、
且 `δm.FourPoint`（⇒ 仍是可加的、更小的实例）。

**为什么落成 `Prop`（而非定理）**：本库的 `Dissimilarity` 固定在**单一类型** `X` 上，
「合并两个标签」需要类型迁移 `X ↝ (X \ {i,j}) ∪ {u}`；`Phylogram` 也没有
「合并樱桃后重取实现树」的接口。Atteson `:688–694` 的式 (7) 还额外给出
**每条边长度只增不减**，从而 `min_e l_{m+1}(e) ≥ min_e l_m(e)`（`:912–914`）——
这是归纳不变量 (b)，本 `Prop` 未把它形式化（需要边权层）。

✦ **「扰动不放大」（Lemma 7，`:749–751`）的对应部分已由 ★★ `linfClose_update` 证出**，
故缺口只剩「可加 + 最短边长不降」这一半。 -/
def atteson_reduction_gap : Prop :=
  ∀ (δ : Dissimilarity X) (i j : X) (θ : ℝ),
    δ.IsCherry i j → δ.FourPoint → 0 ≤ θ → θ ≤ 1 →
      ∃ (Y : Type) (_ : Fintype Y) (_ : DecidableEq Y) (q : X → Y) (δm : Dissimilarity Y),
        Fintype.card Y + 1 = Fintype.card X ∧
        (∀ x y : X, x ≠ i → x ≠ j → y ≠ i → y ≠ j →
          q x ≠ q y ∧ δm.val (q x) (q y) = δ.val x y) ∧
        (∀ x : X, x ≠ i → x ≠ j →
          δm.val (q x) (q j) = θ * δ.val x i + (1 - θ) * δ.val x j) ∧
        δm.FourPoint

/-- 反空真：缺口 2 的**前提**在 ★C 例子中可满足
（存在樱桃、满足四点条件、`θ = 1/2 ∈ [0,1]`）。 -/
theorem atteson_reduction_gap_hypotheses_nonempty :
    exDiss.IsCherry 0 1 ∧ exDiss.FourPoint ∧ (0 : ℝ) ≤ 1 / 2 ∧ (1 : ℝ) / 2 ≤ 1 :=
  ⟨exDiss_isCherry_01, exDiss_fourPoint, by norm_num, by norm_num⟩

/-! ## 9. ★★★ 归约步的 `FourPoint` 一半（W12e2）

`atteson_reduction_gap`（§8）要求：把樱桃 `i,j` 按 `f x = θ·δ x i + (1−θ)·δ x j` 合并成新叶 `u`
后，得到的 `δm` 仍满足四点条件。**这一半只用到 `IsCherry i j + FourPoint`**（不需要树层），
本节把它证成定理；剩下的**类型迁移** `X ↝ (X∖{i,j})∪{u}`（连同 `Dissimilarity` 构造、
`card Y + 1 = card X`）**仍是缺口**。

★D 命题核查：先在 `scripts/msc/w12e2_merge_fourpoint_check.py` 上穷举核过
（5 叶全部二叉拓扑 × 有理边权网格 × `θ ∈ {0,1/4,1/2,3/4,1}` ⇒ 1 187 500 次检查 0 反例；
5 点整值度量 `{1,2,3}` 全枚举 59 049 个，其中 653 个满足 `FourPoint ∧ IsCherry`，
**0 反例**）后才动手证明。 -/

omit [Fintype X] [DecidableEq X] in
/-- ★★ **樱桃的交叉相等**：`FourPoint` ＋ `IsCherry i j` ⟹ 对任意 `b,c ∉ {i,j}`，

　　`δ i b + δ j c = δ i c + δ j b`

（树层即「`i,j` 相邻」的交叉相等；证明用 `FourPoint (i,b,j,c)` 的两个析取支搭配
`IsCherry` 的两条不等式，再对 `b,c` 互换一次得反向不等式）。 -/
theorem IsCherry.cross_eq (δ : Dissimilarity X) (hfp : δ.FourPoint) {i j : X}
    (hch : δ.IsCherry i j) {b c : X}
    (hb : b ≠ i) (hb' : b ≠ j) (hc : c ≠ i) (hc' : c ≠ j) :
    δ.val i b + δ.val j c = δ.val i c + δ.val j b := by
  have h1 : δ.val i b + δ.val j c ≤ δ.val i c + δ.val j b := by
    rcases hfp i b j c with h | h
    · have h2 := (hch.2 b c hb hb' hc hc').2
      linarith
    · simpa [δ.symm b j] using h
  have h2 : δ.val i c + δ.val j b ≤ δ.val i b + δ.val j c := by
    rcases hfp i c j b with h | h
    · have h3 := (hch.2 c b hc hc' hb hb').2
      linarith
    · simpa [δ.symm c j] using h
  linarith

omit [Fintype X] [DecidableEq X] in
set_option linter.unusedVariables false in
/-- ★★★ **凸合并的四点条件（W12e2）**：`δ` 满足四点条件、`i,j` 是樱桃、`θ ∈ [0,1]`、
`a,b,c ∉ {i,j}`。则「把 `i,j` 合并成新叶 `u`（`d(u,x) = θ·δ x i + (1−θ)·δ x j`）」后，
四元组 `(u,a,b,c)` 满足四点条件（库内 `FourPoint` 的析取形态；`δ.val i a` 即 `δ.val a i`）。

证明：设 `A_i = δ i a + δ b c`、`P_i = δ i b + δ a c`、`Q_i = δ i c + δ a b`（`j` 同理），
由 ★★ `IsCherry.cross_eq` 得 `P_i − Q_i = P_j − Q_j`；对 `FourPoint (i,a,b,c)` 与
`FourPoint (j,a,b,c)` 的两个析取支做 4 组分类讨论，再用 `θ ≥ 0`、`1 − θ ≥ 0` 加权即得。

⚠️ `a ≠ i`、`a ≠ j` 属「`a` 未被合并」这一类型迁移前提，在纯算术证明里不出现，
故仅对本条声明关掉 `linter.unusedVariables`。 -/
theorem fourPoint_merge (δ : Dissimilarity X) (hfp : δ.FourPoint) {i j : X}
    (hch : δ.IsCherry i j) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {a b c : X}
    (ha : a ≠ i) (ha' : a ≠ j) (hb : b ≠ i) (hb' : b ≠ j) (hc : c ≠ i) (hc' : c ≠ j) :
    θ * δ.val i a + (1 - θ) * δ.val j a + δ.val b c ≤
        θ * δ.val i b + (1 - θ) * δ.val j b + δ.val a c ∨
      θ * δ.val i a + (1 - θ) * δ.val j a + δ.val b c ≤
        θ * δ.val i c + (1 - θ) * δ.val j c + δ.val a b := by
  have hce := IsCherry.cross_eq δ hfp hch hb hb' hc hc'
  have hDD : δ.val i b + δ.val a c - (δ.val i c + δ.val a b)
      = δ.val j b + δ.val a c - (δ.val j c + δ.val a b) := by linarith
  have hθ1 : (0 : ℝ) ≤ 1 - θ := by linarith
  rcases hfp i a b c with hAi | hAi
  · rcases hfp j a b c with hAj | hAj
    · left; nlinarith [hAi, hAj, h0, hθ1]
    · by_cases hcase : δ.val i b + δ.val a c ≤ δ.val i c + δ.val a b
      · right; nlinarith [hAi, hcase, hAj, h0, hθ1]
      · left
        have hPj : δ.val j c + δ.val a b ≤ δ.val j b + δ.val a c := by
          linarith [hDD, not_le.mp hcase]
        nlinarith [hAi, hAj, hPj, h0, hθ1]
  · rcases hfp j a b c with hAj | hAj
    · by_cases hcase2 : δ.val j b + δ.val a c ≤ δ.val j c + δ.val a b
      · right; nlinarith [hAi, hAj, hcase2, h0, hθ1]
      · left
        have hPi : δ.val i c + δ.val a b ≤ δ.val i b + δ.val a c := by
          linarith [hDD, not_le.mp hcase2]
        nlinarith [hAi, hPi, hAj, h0, hθ1]
    · right; nlinarith [hAi, hAj, h0, hθ1]
/-! ## 10. ★★★ 类型迁移 `X ↝ (X∖{i,j}) ∪ {u}`（W12e3）

W12e2 已把归约步的 `FourPoint` 一半证成 ★★★ `fourPoint_merge`；本节补齐**装置**：
标签类型 `Y`、合并映射 `q`、相异度 `δm`、基数等式，以及缺口的三条取值性质与 `δm.FourPoint`。

⚠️ **★D 命题核查（先说结论）**：§8 的原 `def atteson_reduction_gap` 的第二条合取
`∀ x y, x ≠ i → x ≠ j → y ≠ i → y ≠ j → q x ≠ q y ∧ …` 在 `x = y` 时要求 `q x ≠ q x` ——
**为假**（★★★ `atteson_reduction_gap_refuted`，用 ★C 例子 `exDiss` 与 `x = y = 2`）。
⇒ 本节的**修复形态** `atteson_reduction_gap_correct_shape` 只补一条 `x ≠ y`
（★★★ `atteson_reduction_gap_correct_shape_proved` 把它**证成定理**）。 -/

/-- ★★★ **反例检查：`atteson_reduction_gap` 为假**（第二条合取在 `x = y` 时自相矛盾）。

取 ★C 例子 `exDiss`（`Fin 4`，`i = 0`、`j = 1`、`θ = 1/2`；前提由 ★★ `exDiss_isCherry_01`
与 ★★ `exDiss_fourPoint` 给出）与 `x = y = 2 ∉ {0,1}`：该合取要求 `q 2 ≠ q 2`，矛盾。 -/
theorem atteson_reduction_gap_refuted : ¬ atteson_reduction_gap (X := Fin 4) := by
  intro h
  obtain ⟨Y, _, _, q, δm, _, hval, _, _⟩ :=
    h exDiss 0 1 (1 / 2) exDiss_isCherry_01 exDiss_fourPoint (by norm_num) (by norm_num)
  exact (hval 2 2 (by decide) (by decide) (by decide) (by decide)).1 rfl

/-- ★★★ **旧标签类型** `X ∖ {i,j}`（Finset 子类型：基数由 `Finset.card_sdiff` 直接给出）。 -/
abbrev MergeOld (X : Type*) [Fintype X] [DecidableEq X] (i j : X) :=
  ↥((Finset.univ : Finset X) \ {i, j})

/-- ★★★ **合并后的标签类型** `Y = (X∖{i,j}) ∪ {u}`，新标签 `u = Sum.inr ()`。 -/
abbrev MergeIdx (X : Type*) [Fintype X] [DecidableEq X] (i j : X) :=
  MergeOld X i j ⊕ Unit

/-- ★★★ **合并映射** `q : X → Y`：`i, j ↦ u`，其余 `x ↦ inl x`。 -/
noncomputable def mergeQ (i j : X) : X → MergeIdx X i j :=
  fun x => if h : x = i ∨ x = j then Sum.inr () else Sum.inl ⟨x, by
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact not_or.mp h⟩

theorem mergeQ_of_ne {x : X} (hx : x ≠ i) (hy : x ≠ j) :
    mergeQ i j x = Sum.inl ⟨x, by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      exact ⟨hx, hy⟩⟩ := by
  rw [mergeQ]
  exact dite_eq_right (fun h => h.elim hx hy)

theorem mergeQ_i : mergeQ i j i = (Sum.inr () : MergeIdx X i j) := by
  rw [mergeQ]
  exact dite_eq_left (Or.inl rfl)

theorem mergeQ_j : mergeQ i j j = (Sum.inr () : MergeIdx X i j) := by
  rw [mergeQ]
  exact dite_eq_left (Or.inr rfl)

/-- 旧标签的分量不等于 `i`。 -/
theorem mergeOld_ne_left (a : MergeOld X i j) : a.1 ≠ i := by
  have h := a.2
  rw [Finset.mem_sdiff] at h
  intro hi
  exact h.2 (by rw [hi]; exact Finset.mem_insert_self i {j})

/-- 旧标签的分量不等于 `j`。 -/
theorem mergeOld_ne_right (a : MergeOld X i j) : a.1 ≠ j := by
  have h := a.2
  rw [Finset.mem_sdiff] at h
  intro hj
  exact h.2 (by rw [hj]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self j))

/-- ★★★ **合并度量**：旧–旧取 `δ`，`u`–旧取凸组合 `θ·δ i x + (1−θ)·δ j x`，`u`–`u` 取 `0`。 -/
noncomputable def mergeVal (δ : Dissimilarity X) (i j : X) (θ : ℝ) :
    MergeIdx X i j → MergeIdx X i j → ℝ
  | Sum.inl x, Sum.inl y => δ.val x.1 y.1
  | Sum.inl x, Sum.inr _ => θ * δ.val i x.1 + (1 - θ) * δ.val j x.1
  | Sum.inr _, Sum.inl y => θ * δ.val i y.1 + (1 - θ) * δ.val j y.1
  | Sum.inr _, Sum.inr _ => 0

theorem mergeVal_symm (δ : Dissimilarity X) (i j : X) (θ : ℝ) :
    ∀ a b : MergeIdx X i j, mergeVal δ i j θ a b = mergeVal δ i j θ b a := by
  intro a b
  cases a with
  | inl x =>
    cases b with
    | inl y => exact δ.symm x.1 y.1
    | inr u => rfl
  | inr u =>
    cases b with
    | inl y => rfl
    | inr v => rfl

theorem mergeVal_self (δ : Dissimilarity X) (i j : X) (θ : ℝ) :
    ∀ a : MergeIdx X i j, mergeVal δ i j θ a a = 0 := by
  intro a
  cases a with
  | inl x => exact δ.diag x.1
  | inr u => rfl

/-- ★★★ **合并相异度** `δm : Dissimilarity Y`（类型迁移的产物）。

⚠️ 库内 `Dissimilarity` 只有 `val` / `symm` / `diag` **三个字段**，**没有**三角不等式字段
（`Phylo/Algorithm/NJ.lean:61`），故构造只需这三条。 -/
noncomputable def mergeDissim (δ : Dissimilarity X) (i j : X) (θ : ℝ) :
    Dissimilarity (MergeIdx X i j) where
  val := mergeVal δ i j θ
  symm := mergeVal_symm δ i j θ
  diag := mergeVal_self δ i j θ

/-- ★★★ **基数**：`card Y + 1 = card X`（`i ≠ j` 取自 `IsCherry` 的第一项）。 -/
theorem card_mergeIdx (hij : i ≠ j) :
    Fintype.card (MergeIdx X i j) + 1 = Fintype.card X := by
  classical
  have hpair : ({i, j} : Finset X).card = 2 := Finset.card_pair_eq_two_iff.mpr hij
  have hle : 2 ≤ Fintype.card X := by
    have h := Finset.card_le_card (Finset.subset_univ ({i, j} : Finset X))
    rwa [Finset.card_univ, hpair] at h
  have hcard : ((Finset.univ : Finset X) \ {i, j}).card = Fintype.card X - 2 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ,
      hpair]
  have hcoe : Fintype.card (MergeOld X i j) = ((Finset.univ : Finset X) \ {i, j}).card :=
    Fintype.card_coe _
  rw [Fintype.card_sum, Fintype.card_unit, hcoe, hcard]
  omega

/-- ★★★ **旧–旧取值不变**（修复形态：`x ≠ y` 是原缺口漏掉的那一条）。 -/
theorem mergeDissim_val_of_ne (δ : Dissimilarity X) (i j : X) (θ : ℝ) {x y : X}
    (hx : x ≠ i) (hx' : x ≠ j) (hy : y ≠ i) (hy' : y ≠ j) (hxy : x ≠ y) :
    mergeQ i j x ≠ mergeQ i j y ∧
      (mergeDissim δ i j θ).val (mergeQ i j x) (mergeQ i j y) = δ.val x y := by
  constructor
  · rw [mergeQ, mergeQ, dite_eq_right (fun h => h.elim hx hx'),
      dite_eq_right (fun h => h.elim hy hy')]
    intro h
    exact hxy (congrArg Subtype.val (Sum.inl.inj h))
  · rw [mergeQ, mergeQ, dite_eq_right (fun h => h.elim hx hx'),
      dite_eq_right (fun h => h.elim hy hy')]
    rfl

/-- ★★★ **新标签处取凸组合**：`δm.val (q x) (q j) = θ·δ x i + (1−θ)·δ x j`。 -/
theorem mergeDissim_val_merged (δ : Dissimilarity X) (i j : X) (θ : ℝ) {x : X}
    (hx : x ≠ i) (hx' : x ≠ j) :
    (mergeDissim δ i j θ).val (mergeQ i j x) (mergeQ i j j)
      = θ * δ.val x i + (1 - θ) * δ.val x j := by
  rw [mergeQ, dite_eq_right (fun h => h.elim hx hx'), mergeQ, dite_eq_left (Or.inr rfl)]
  show θ * δ.val i x + (1 - θ) * δ.val j x = θ * δ.val x i + (1 - θ) * δ.val x j
  rw [δ.symm x i, δ.symm x j]

/-- ★★★ **含新标签（首位）的四点条件**：由 ★★★ `fourPoint_merge` 直接得到。 -/
theorem mergeDissim_fourPoint_merged (δ : Dissimilarity X) (hfp : δ.FourPoint) {i j : X}
    (hch : δ.IsCherry i j) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (a b c : MergeOld X i j) :
    (mergeDissim δ i j θ).val (Sum.inr ()) (Sum.inl a)
        + (mergeDissim δ i j θ).val (Sum.inl b) (Sum.inl c) ≤
      (mergeDissim δ i j θ).val (Sum.inr ()) (Sum.inl b)
        + (mergeDissim δ i j θ).val (Sum.inl a) (Sum.inl c) ∨
    (mergeDissim δ i j θ).val (Sum.inr ()) (Sum.inl a)
        + (mergeDissim δ i j θ).val (Sum.inl b) (Sum.inl c) ≤
      (mergeDissim δ i j θ).val (Sum.inr ()) (Sum.inl c)
        + (mergeDissim δ i j θ).val (Sum.inl a) (Sum.inl b) :=
  fourPoint_merge δ hfp hch h0 h1 (mergeOld_ne_left a) (mergeOld_ne_right a)
    (mergeOld_ne_left b) (mergeOld_ne_right b) (mergeOld_ne_left c) (mergeOld_ne_right c)

/-- ★★★ **`δm` 满足四点条件**（16 种「新旧标签分布」逐个处理）：

* 全旧标签：就是 `δ.FourPoint`；
* 恰一个新标签（4 个位置）：归约到 ★★★ `fourPoint_merge`（不同位置对应老标签的置换）；
* 两个新标签：`d(u,u) = 0`，需要 `δ x y ≤ d(u,x) + d(u,y)`（`hH1`，由
  `FourPoint (x,y,i,i)` 与 `(x,y,j,j)` 的凸组合给出）；
* 三个/四个新标签：两侧同值时用对称性收口。

故 `δm.FourPoint` **不再需要额外假设**（`Dissimilarity` 无三角不等式字段，
退化四元组由 `FourPoint` 的自身实例补足）。 -/
theorem mergeDissim_fourPoint (δ : Dissimilarity X) (hfp : δ.FourPoint) {i j : X}
    (hch : δ.IsCherry i j) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (mergeDissim δ i j θ).FourPoint := by
  intro a b c d
  have hθ1 : (0 : ℝ) ≤ 1 - θ := by linarith
  have hH1 : ∀ x y : MergeOld X i j,
      δ.val x.1 y.1 ≤ (θ * δ.val i x.1 + (1 - θ) * δ.val j x.1)
        + (θ * δ.val i y.1 + (1 - θ) * δ.val j y.1) := by
    intro x y
    have hx : δ.val x.1 y.1 ≤ δ.val i x.1 + δ.val i y.1 := by
      rcases hfp x.1 y.1 i i with h | h <;>
        linarith [h, δ.diag i, δ.symm x.1 i, δ.symm y.1 i]
    have hy : δ.val x.1 y.1 ≤ δ.val j x.1 + δ.val j y.1 := by
      rcases hfp x.1 y.1 j j with h | h <;>
        linarith [h, δ.diag j, δ.symm x.1 j, δ.symm y.1 j]
    nlinarith [hx, hy, h0, hθ1]
  rcases a with x | ua <;> rcases b with y | ub <;> rcases c with z | uc <;>
      rcases d with w | ud <;>
    simp only [mergeDissim, mergeVal]
  · exact hfp x.1 y.1 z.1 w.1
  · rcases mergeDissim_fourPoint_merged δ hfp hch h0 h1 z x y with h | h <;>
      simp only [mergeDissim, mergeVal] at h
    · right; linarith [h, δ.symm z.1 y.1]
    · left; linarith [h, δ.symm z.1 x.1]
  · rcases mergeDissim_fourPoint_merged δ hfp hch h0 h1 w x y with h | h <;>
      simp only [mergeDissim, mergeVal] at h
    · left; linarith [h, δ.symm w.1 y.1]
    · right; linarith [h, δ.symm w.1 x.1]
  · exact Or.inl (by linarith [hH1 x y])
  · rcases mergeDissim_fourPoint_merged δ hfp hch h0 h1 x z w with h | h <;>
      simp only [mergeDissim, mergeVal] at h
    · right; linarith
    · left; linarith
  · right; linarith
  · left; linarith
  · left; linarith
  · simpa only [mergeDissim, mergeVal] using
      mergeDissim_fourPoint_merged δ hfp hch h0 h1 y z w
  · left; linarith
  · right; linarith
  · left; linarith
  · exact Or.inl (by linarith [hH1 z w])
  · left; linarith
  · left; linarith
  · left; linarith

/-! ## 11. ★★★ 修复形态：把 `x ≠ y` 补回第二条合取 -/

universe u

/-- ★★★ **`atteson_reduction_gap` 的修复形态**：与 §8 的原缺口**只差一处实质内容**
—— 补回 `x ≠ y`（原缺口在 `x = y` 时自相矛盾，见 ★★★ `atteson_reduction_gap_refuted`）。

⚠️ 另有一处**写法层面**的调整：`Y` 的宇宙随 `X` 走（`Type u`）。原缺口写死 `Type`
（即 `Type 0`），这在 `X : Type u`（`u > 0`）时要求一个**小类型** `Y : Type 0`；
数学上仍可满足（取 `Y := Fin (card X - 1)`），但需把 `δm` 沿一个枚举搬运。
本节的重心是数学内容（`δm.FourPoint`），故采用与 `X` 同宇宙的 `Y`（本 `def` 形如
`Phylo/ConsensusAxioms.lean` 的 `mnCorollary_gap`：把 `X` 量化在 `Prop` 内）。 -/
def atteson_reduction_gap_correct_shape : Prop :=
  ∀ {X : Type u} [Fintype X] [DecidableEq X] (δ : Dissimilarity X) (i j : X) (θ : ℝ),
    δ.IsCherry i j → δ.FourPoint → 0 ≤ θ → θ ≤ 1 →
      ∃ (Y : Type u) (_ : Fintype Y) (_ : DecidableEq Y) (q : X → Y) (δm : Dissimilarity Y),
        Fintype.card Y + 1 = Fintype.card X ∧
        (∀ x y : X, x ≠ i → x ≠ j → y ≠ i → y ≠ j → x ≠ y →
          q x ≠ q y ∧ δm.val (q x) (q y) = δ.val x y) ∧
        (∀ x : X, x ≠ i → x ≠ j →
          δm.val (q x) (q j) = θ * δ.val x i + (1 - θ) * δ.val x j) ∧
        δm.FourPoint

/-- ★★★ **修复形态已证成**（W12e3 收口）：类型迁移装置 `Y := (X∖{i,j}) ∪ {u}`、`q := mergeQ`、
`δm := mergeDissim` 一次性满足全部四条（基数、旧–旧不变、凸组合、`δm.FourPoint`）。

⇒ `atteson_reduction_gap` 的**唯一**障碍只是陈述层面的 `x ≠ y`（已修），
数学内容（`δm.FourPoint`）由 ★★★ `fourPoint_merge` 承担。 -/
theorem atteson_reduction_gap_correct_shape_proved :
    atteson_reduction_gap_correct_shape := by
  classical
  intro α _ _ δ i j θ hch hfp h0 h1
  exact ⟨MergeIdx α i j, inferInstance, inferInstance, mergeQ i j, mergeDissim δ i j θ,
    card_mergeIdx hch.1,
    fun x y hx hx' hy hy' hxy => mergeDissim_val_of_ne δ i j θ hx hx' hy hy' hxy,
    fun x hx hx' => mergeDissim_val_merged δ i j θ hx hx',
    mergeDissim_fourPoint δ hfp hch h0 h1⟩


end Dissimilarity

end NJ

/-! ## 12. ★★★ `sideLeafCount`：删边后一侧子树的**叶数**（W12e5）

Atteson Lemma 10（`:1774–1804`）的权重
`w_e(i,j) = −2`（`e ∈ P_ij`）、`= −2|L − L_i(e)|`（否则）
里出现的 `|L_i(e)|` 就是**删去边 `e` 后与顶点 `i` 同侧的叶数**。
库内已有 `Cladogram.sideLeaves`（`Phylo/Split.lean:529`，用 `T - e` 上的 `Reachable` 实现）
—— 但**只有叶集、没有计数 API**，本节把计数补上并给出基本性质。

⚠️ **本节不做**（仍是 `def atteson_lemma11_gap` 的缺口，§8/:831 逐字未动）：
① `w_e` 的**权重公式**本身（含 Lemma 10 的逐边比较与「路径旁子树叶数单调性」）；
② `Dissimilarity ↔ ExistsRealizingPhylogram`（`Phylo/Buneman.lean:589`）的桥（`δmin > 0` 来源）。 -/

namespace Cladogram

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- ★★★ **一侧叶数** `|L_u(e)|`：删去边 `e` 后与顶点 `u` **同侧**（在 `T - e` 中可达）的
叶标签个数 —— Atteson Lemma 10 的 `|L_i(e)|`。 -/
noncomputable def sideLeafCount (T : Cladogram X) (e : Sym2 T.V) (u : T.V) : ℕ :=
  (T.sideLeaves e u).card

omit [DecidableEq X] in
/-- 定义式展开（便于把 `sideLeafCount` 归到已有的 `sideLeaves` 引理上）。 -/
theorem sideLeafCount_eq_card_sideLeaves (T : Cladogram X) (e : Sym2 T.V) (u : T.V) :
    T.sideLeafCount e u = (T.sideLeaves e u).card := rfl

/-- ★★★ **两侧叶数之和 = 总叶数**（`sideLeaves_compl_adj` 的直接推论）：

　　`|L_a(e)| + |L_b(e)| = |X|`（`e = ⟦a,b⟧` 是树边）。

这就是 Atteson 权重里 `|L − L_i(e)|` 能写成「另一侧的叶数」的原因。 -/
theorem sideLeafCount_add_of_adj (T : Cladogram X) {a b : T.V} (hab : T.graph.Adj a b) :
    T.sideLeafCount s(a, b) a + T.sideLeafCount s(a, b) b = Fintype.card X := by
  have hle : (T.sideLeaves s(a, b) a).card ≤ Fintype.card X := by
    simpa [Finset.card_univ] using Finset.card_le_univ (T.sideLeaves s(a, b) a)
  rw [sideLeafCount, sideLeafCount, T.sideLeaves_compl_adj hab, Finset.card_compl]
  omega

/-- ★★ **侧不变性**：删边后与 `u` 同侧的顶点给出**同一个**叶集，故同一个计数。
（`sideLeaves` 只依赖 `u` 所在的一侧。） -/
theorem sideLeafCount_eq_of_inSide (T : Cladogram X) {e : Sym2 T.V} {u a : T.V}
    (h : T.inSide e u a) : T.sideLeafCount e u = T.sideLeafCount e a := by
  rw [sideLeafCount, sideLeafCount, T.sideLeaves_eq_of_inSide h]

/-- ★★ **叶边的一侧恰含 1 片叶**（`sideLeaves_leaf_edge` 的计数形式）——

　　`|L_x(⟦x,b⟧)| = 1`（`x` 是叶）。这是本节的**显式数值见证**。 -/
theorem sideLeafCount_leaf_edge (T : Cladogram X) {x : X} {b : T.V}
    (h : T.graph.Adj (T.leaf x) b) : T.sideLeafCount s(T.leaf x, b) (T.leaf x) = 1 := by
  rw [sideLeafCount, T.sideLeaves_leaf_edge h, Finset.card_singleton]

/-- ★★ **含自己那片叶的一侧非空**（`x` 总在自己那一侧）。 -/
theorem sideLeafCount_pos_self (T : Cladogram X) (e : Sym2 T.V) (x : X) :
    0 < T.sideLeafCount e (T.leaf x) :=
  Finset.card_pos.mpr ⟨x, T.mem_sideLeaves_self e x⟩

omit [DecidableEq X] in
/-- ★ **上界**：任一侧的叶数 ≤ 总叶数。 -/
theorem sideLeafCount_le_card (T : Cladogram X) (e : Sym2 T.V) (u : T.V) :
    T.sideLeafCount e u ≤ Fintype.card X := by
  rw [sideLeafCount]
  exact Finset.card_le_univ (T.sideLeaves e u)

/-- ★★ **真边两侧都含叶**（`sideLeaves_nonempty_of_adj'` 的计数形式）⇒ 任一侧的计数 ≥ 1。 -/
theorem sideLeafCount_pos_of_adj (T : Cladogram X) {a b u : T.V} (hab : T.graph.Adj a b) :
    0 < T.sideLeafCount s(a, b) u :=
  Finset.card_pos.mpr (T.sideLeaves_nonempty_of_adj' hab)

/-- ★★ **任一侧都不是全叶集**（另一侧非空）⇒ 计数 < 总叶数。 -/
theorem sideLeafCount_lt_card_of_adj (T : Cladogram X) {a b u : T.V} (hab : T.graph.Adj a b) :
    T.sideLeafCount s(a, b) u < Fintype.card X := by
  rw [sideLeafCount]
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.subset_univ _, T.sideLeaves_ne_univ_of_adj (u := u) hab⟩)

/-- ★★★ **端点非叶时一侧含 ≥ 2 片叶**（`two_le_card_sideLeaves` 的计数形式）——
这正是「路径旁子树叶数」单调性论证的**起飞点**。 -/
theorem two_le_sideLeafCount (T : Cladogram X) {u v : T.V} (huv : T.graph.Adj u v)
    (hnd : T.graph.degree u ≠ 1) : 2 ≤ T.sideLeafCount s(u, v) u :=
  T.two_le_card_sideLeaves huv hnd

/-! ### ★B 显式数值见证 -/

/-- ★B **叶边的两侧叶数**：一边 `1`、另一边 `|X| − 1`（`sideLeafCount_leaf_edge` ＋
`sideLeafCount_add_of_adj`；与 `sideLeaves_leaf_edge` 的既有结论（`= {x}`）对照一致）。 -/
example (T : Cladogram X) {x : X} {b : T.V} (h : T.graph.Adj (T.leaf x) b) :
    T.sideLeafCount s(T.leaf x, b) (T.leaf x) = 1 ∧
      T.sideLeafCount s(T.leaf x, b) (T.leaf x)
        + T.sideLeafCount s(T.leaf x, b) b = Fintype.card X :=
  ⟨T.sideLeafCount_leaf_edge h, T.sideLeafCount_add_of_adj h⟩

/-- ★B **反空真**：上面的两条性质在「至少 2 片叶」的树上互不空真。 -/
example (T : Cladogram X) {x : X} {b : T.V} (h : T.graph.Adj (T.leaf x) b) :
    0 < T.sideLeafCount s(T.leaf x, b) b :=
  T.sideLeafCount_pos_of_adj h

end Cladogram

