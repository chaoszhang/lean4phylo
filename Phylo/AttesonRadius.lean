/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Algorithm.NJ
import Phylo.Buneman
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum

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

end Dissimilarity

end NJ
