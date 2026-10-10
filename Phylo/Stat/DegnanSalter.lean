/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.Coalescent

/-!
# `Phylo.Stat.DegnanSalter` —— Degnan & Salter (2005) 式 (1)：`p_{uv}(T)`

本文件形式化 **Degnan & Salter (2005)** 的 `p_{uv}(T)`：一条枝上 `u` 条谱系
在时间 `T` 内并成 `v` 条的概率。这是那篇论文里「一切基因树概率的母机」，
式 (2) 的每一个因子都是它。

## 文献与原文形状

出处：J. H. Degnan & L. A. Salter, *Gene tree distributions under the coalescent
process*, **Evolution 59(1):24-36 (2005)**，
`references/pdf/DegnanSalter2005_GeneTreeDistributions.pdf` **第 2 页**
（期刊页码 **25**）。

> ⚠️ **`references/md/DegnanSalter2005_GeneTreeDistributions.md` 里的式 (1) 不可判读。**
> 该 md 把公式里的 `−` 映射成了 `(cid:53)` / `5`、`∑` 映射成了 `O`、
> `≥` 映射成了 `(cid:36)`，并且错位了上下标。这不是误读：同一份 md
> 第 393–421 行给出的那条「式 (1)」在数值上根本不满足 `Σ_v p_{uv}(T) = 1`。
> 本文件用的是 `pdftotext -layout -enc UTF-8` 的**重新提取**结果。

重新提取后的式 (1)（`u ≥ v ≥ 1`，`T` 以 `2N` 世代为单位，`λ_k = k(k−1)/2`）：

```text
                    u                                             prod_{y=0}^{k-2} (v-1+y)(u+1-y)
  p_{uv}(T) =  sum      (2k-1)(-1)^{k-v} e^{-k(k-1)T/2}  ----------------------------------------
                                            v!(k-v)!(v+k-1)!        prod_{y=0}^{k-2} (u+y)
             k=v
```

原文紧前的两个口径（第 2 页；md 第 384–386 行）：

> `Here u ≥ v ≥ 1, and if u = v, then p_{uv}(T) is the probability that no`
> `coalescences occur in the length of time T.`
> `In the coalescent model, T = t/(2N), where t is the number of generations and N`
> `is the effective population size.`

「所有 ordering 等概率」的模型口径在第 **5 页**（md 第 **3219–3224** 行）：

> `Assuming that all possible orderings, correct and incorrect, are equally likely`
> `(this follows the model of Yule [1924]), and that u lineages have coalesced into`
> `v lineages, the probability that the ordering of events on the branch is`
> `consistent with the gene tree is the number of correct orderings divided by the`
> `number of possible orderings.`

同一句也在 md 第 **3805–3808** 行。概率质量函数全文在 md 第 **4269 行**起
（`THE PROBABILITY MASS FUNCTION P_{c,l}(G = g)`）。Degnan–Salter 把式 (1) 归给
Rosenberg (2002)，并说明更早由 Tavaré (1984)、Watterson (1984)、
Takahata & Nei (1985) 得到（第 2 页）。

## 本文件形式化的定义

`T` 用 coalescent units，`λ_k = k(k−1)/2`。Kingman 纯死亡链的生成元
`Q`（`Q[k,k] = −λ_k`、`Q[k,k−1] = λ_k`）在 `{1,…,u}` 上是上三角、特征值
`−λ_1,…,−λ_u` 互异，故 `(sI − Q)⁻¹[u][v]` 的**部分分式**给出

```text
  p_{uv}(T) = Σ_{k=v}^{u}  c(u,v,k) · e^{-λ_k T},
  c(u,v,k) = (Π_{m=v+1}^{u} λ_m) / (Π_{m=v, m≠k}^{u} (λ_m − λ_k))
```

这正是式 (1) 的**闭合形式**，等价地写成（脚本 `(C0)` 逐项核对）

```text
  c(u,v,k) = (2k−1)(−1)^{k−v} u!(u−1)!(v+k−2)! / (v!(v−1)!(k−v)!(u−k)!(u+k−1)!)
           = (2k−1)(−1)^{k−v} [Π_{y=0}^{k−2}(v+y)] [Π_{y=0}^{k−1}(u−y)/(u+y)] / (v!(k−v)!)
```

`scripts/msc/degnansalter_puv.py` 用**精确有理数**穷举复核（`u ≤ 9`）：
`(C0)` 两种形状一致；`(C0b)` `u = 2,3,4` 与教科书 Kingman 结果逐项一致；
`(C1)` 与**独立的 Sylvester 公式** `P_k = Π_{i≠k}(Q+λ_i I)/(λ_i−λ_k)`
（并验证 `Σ_k P_k = I`）逐项一致；`(C2)` `p_uu = e^{−λ_u T}`；
`(C3)` `p_{uv}(0) = δ_{uv}`；`(C4)/(C5)` `u ≤ 6` 上非负、`Σ_v p_{uv}(T) = 1`
（300 位 Decimal）；`(C6)` `p_21 = 1 − e^{−T}`、`p_22 = e^{−T}`；
`(C7)` ODE/特征关系 `Σ_w Q[u][w] c(w,v,k) = −λ_k c(u,v,k)`。**没有用 Monte Carlo。**

⚠️ **措辞纪律**：`(C4)/(C5)/(C7)` 等是**脚本**的复核结果，**不是** Lean 定理；
Lean 内只证了下面「诚实边界」表里标 ✅ 的那一栏。

## 接合点（与库内既有溯祖设施）

* `pUV 2 1 t = Coalescent.firstMergeCDF 2 t`（`= 1 − e^{−t}`）；
* `pUV 2 2 t = Coalescent.survival 2 t`（`= e^{−t}`）；
* `1 ≤ u` 时 `pUV u u t = Coalescent.survival u t`；
* `λ_k = Coalescent.kingmanRate k`（同一个数）。

## 诚实边界（逐条，**没做到的**）

| 条目 | Lean 内状态 |
|---|---|
| `pUV` 的准确定义（部分分式/谱分解） | ✅ `pUV`、`pUVCoeff` |
| `pUV u 0 t = 0` | ✅ `pUV_zero_right` |
| `pUV u v t = 0`（`v > u`） | ✅ `pUV_eq_zero_of_gt` |
| `pUV 1 1 t = 1` | ✅ `pUV_one_one` |
| `pUV 2 2 t = Coalescent.survival 2 t` | ✅ `pUV_two_two` |
| `pUV 2 1 t = Coalescent.firstMergeCDF 2 t` | ✅ `pUV_two_one` |
| `1 ≤ u` 时 `pUV u u t = Coalescent.survival u t` | ✅ `pUV_diag` |
| 归一化的**有限情形** `pUV 2 1 t + pUV 2 2 t = 1` | ✅ `pUV_normalization_two` |
| `λ_k = Coalescent.kingmanRate k` | ✅ `lambdaR_eq_kingmanRate` |
| **归一化一般情形** `Σ_{v=1}^{u} pUV u v t = 1`（`u ≥ 3`） | ✅ **已证**（`pUV_normalization_proved`；更强的 `u ≥ 1` 见 `pUV_sum_Icc_one`） |
| **系数行和恒等式** `Σ_{v=1}^{k} c(u,v,k) = if k = 1 then 1 else 0` | ✅ **已证**（`pUVCoeff_sum_Icc_eq`；⚠️ 文件旧版 docstring 写的 `k = u` **是错的**，见下） |
| `pUV u v t ≥ 0`（一般 `u,v`） | ⚠️ **部分**：`u ≤ 3` 已证（`pUV_nonneg_upto_three`、`pUV_nonneg_two/three`）；一般 `u` 仍是缺口 `pUV_nonneg` |
| `pUV u v 0 = if u = v then 1 else 0` | ❌ 缺口 `pUV_zero_time` |
| 与式 (1)**产品形式**的逐项一致性（Lean 内） | ❌ 缺口 `pUV_eq_formula1` |

### 归一化一般情形：已证 + 旧 docstring 的错误订正（★B）

`Σ_{v=1}^{u} pUV u v t = 1` **已证**（`pUV_sum_Icc_one`，全部 `u ≥ 1`）。
证明路线（见下面 §「系数恒等式与一般归一化」）：

1. 定义清分母后的系数分子 `φ_v(x) = (∏_{m=v+1}^{u}λ_m)·∏_{m=1}^{v-1}(λ_m − x)` 与
   `E(x) = ∏_{m=1}^{u}(λ_m − x)`；
2. **望远镜恒等式** `x · Σ_{v=1}^{u}φ_v(x) = −E(x)`（对**一切** `x`；对 `u` 归纳，
   用 `φ^{(u+1)}_v = λ_{u+1}·φ^{(u)}_v`（`v ≤ u`）与 `φ^{(u+1)}_{u+1} = E^{(u)}`）；
3. 代入 `x = λ_k`（`k ≥ 2`）：由 `E(λ_k) = 0` 与 `λ_k ≠ 0` 得 `Σ_{v=1}^{k}φ_v(λ_k) = 0`，
   再由 `c(u,v,k)·D_k = φ_v(λ_k)`（`D_k = ∏_{m∈(Icc 1 u).erase k}(λ_m − λ_k) ≠ 0`）
   得**系数行和恒等式** `Σ_{v=1}^{k}c(u,v,k) = δ_{k,1}`；
4. 三角换序 `Σ_v Σ_{k≥v} = Σ_k Σ_{v≤k}`（`Finset.sum_Ico_Ico_comm`）后得
   `Σ_v pUV u v t = Σ_k e^{−λ_k t}·δ_{k,1} = e^{−λ_1 t} = 1`（`λ_1 = 0`）。

⚠️ **勘误（★B 反例检查）**：旧版本此处的 docstring 把系数恒等式写成
`Σ_{v=1}^{k} c(u,v,k) = if k = u then 1 else 0`。**这是错的**：`Σ_v` 是沿 `P_k` 的**行**求和，
正确的判别式是 `k = 1`（`λ_1 = 0` 是吸收态），不是 `k = u`。
`u = k = 3` 即反例：左边 `c(3,1,3)+c(3,2,3)+c(3,3,3) = 1/2 − 3/2 + 1 = 0`，
而 `if 3 = 3 then 1 else 0 = 1`（Lean 里见 `coefficient_identity_k_eq_u_false`）。
（另：`Σ_{k=v}^{u} c(u,v,k) = δ_{vu}` 才是「沿 `k` 求和」的那一条 —— 那是缺口
`pUV_zero_time`，与归一化用的不是同一条恒等式。）

### `pUV_nonneg` 缺什么（明确报告）

`pUV u v t ≥ 0` 在脚本（精确有理数）里对 `u ≤ 6` 验证过；Lean 内已做 `u ≤ 3`：

* `pUV 2 1 t = 1 − e^{−t} ≥ 0`、`pUV 2 2 t = e^{−t} > 0`（`pUV_nonneg_two`）；
* `pUV 3 3 t = e^{−3t} > 0`、`pUV 3 2 t = (3/2)(e^{−t} − e^{−3t}) ≥ 0`、
  `pUV 3 1 t = 1 − (3/2)e^{−t} + (1/2)e^{−3t} = (1/2)(1 − e^{−t})²(2 + e^{−t}) ≥ 0`
  （`pUV_nonneg_three`）。

一般 `u` 仍缺：`pUV` 是「系数 × 指数」的**交错和**，逐项非负**不成立**，
正确的论证要么把它当作纯死亡链 `exp(tQ)` 的转移概率（需要矩阵指数或
Kolmogorov 前向方程 + 解的唯一性），要么用「条件在首次跳跃」的卷积递推
`p_{uv}(t) = δ_{uv}e^{−λ_u t} + λ_u ∫_0^t e^{−λ_u s}p_{u−1,v}(t−s)ds`
（需要把部分分式形式与该递推接上，本质上是 Laplace 变换唯一性）。
这两条器材本批都没有，故一般情形**如实留成缺口** `pUV_nonneg`。
-/

namespace Phylo.Stat.DegnanSalter

/-! ## 基础量 -/

/-- **Kingman 合并率** `λ_k = k(k−1)/2`，以 `ℝ` 表示。

与库内 `Coalescent.kingmanRate` 是同一个数（`lambdaR_eq_kingmanRate`）。 -/
noncomputable def lambdaR (k : ℕ) : ℝ := (k : ℝ) * ((k : ℝ) - 1) / 2

@[simp] theorem lambdaR_zero : lambdaR 0 = 0 := by rw [lambdaR]; norm_num

@[simp] theorem lambdaR_one : lambdaR 1 = 0 := by rw [lambdaR]; norm_num

@[simp] theorem lambdaR_two : lambdaR 2 = 1 := by rw [lambdaR]; norm_num

@[simp] theorem lambdaR_three : lambdaR 3 = 3 := by rw [lambdaR]; norm_num

/-- `λ_k = Coalescent.kingmanRate k`（同一个数，定义相同）。 -/
theorem lambdaR_eq_kingmanRate (k : ℕ) : lambdaR k = Coalescent.kingmanRate k := rfl

/-- `k ≥ 2` 时 `λ_k > 0`。 -/
theorem lambdaR_pos {k : ℕ} (hk : 2 ≤ k) : 0 < lambdaR k := by
  rw [lambdaR_eq_kingmanRate]
  exact Coalescent.kingmanRate_pos hk

/-! ## 式 (1) 的系数与 `p_{uv}(T)` -/

/-- **式 (1) 的系数** `c(u,v,k)`：`p_uv(T)` 里 `e^{−λ_k T}` 的系数。

即 `(sI − Q)⁻¹[u][v]` 的部分分式系数
`(Π_{m=v+1}^{u} λ_m) / (Π_{m=v, m≠k}^{u} (λ_m − λ_k))`。
因子 `(if v = 0 then 0 else 1)` 处理 `v = 0`（不在式 (1) 的范围内：
那时分母里的 `λ_1 − λ_0` 会变成 `0`）。 -/
noncomputable def pUVCoeff (u v k : ℕ) : ℝ :=
  (if v = 0 then 0 else 1)
    * ((∏ m ∈ Finset.Icc (v + 1) u, lambdaR m)
        / ∏ m ∈ (Finset.Icc v u).erase k, (lambdaR m - lambdaR k))

/-- **Degnan–Salter (2005) 式 (1) 的 `p_{uv}(T)`**（谱分解 / 部分分式形式）。

`pUV u v t = Σ_{k=v}^{u} e^{−λ_k t} · c(u,v,k)`；`v = 0` 时系数全为 `0`，
故 `pUV u 0 t = 0`（`v = 0` 不在式 (1) 的范围内）。

原文：`references/pdf/DegnanSalter2005_GeneTreeDistributions.pdf` 第 2 页
（期刊页码 25）；`u ≥ v ≥ 1`，`u = v` 时它是「`T` 内不发生任何合并」的概率。 -/
noncomputable def pUV (u v : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc v u, Real.exp (-(lambdaR k) * t) * pUVCoeff u v k

/-- `pUV u 0 t = 0`（`v = 0` 不是式 (1) 的取值）。 -/
@[simp] theorem pUV_zero_right (u : ℕ) (t : ℝ) : pUV u 0 t = 0 := by
  rw [pUV]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp [pUVCoeff]

/-- `v > u` 时 `pUV u v t = 0`（式 (1) 只在 `k ≥ v` 上求和，而 `k ≤ u`）。 -/
theorem pUV_eq_zero_of_gt {u v : ℕ} (h : u < v) (t : ℝ) : pUV u v t = 0 := by
  rw [pUV, Finset.Icc_eq_empty_of_lt h, Finset.sum_empty]

/-! ## 具体系数的求值 -/

/-- `(Icc a a).erase a = ∅`。 -/
theorem erase_Icc_self (a : ℕ) : (Finset.Icc a a).erase a = (∅ : Finset ℕ) := by
  rw [Finset.Icc_self]
  simp

/-- `Icc 1 2 = {1,2}`。 -/
theorem Icc_one_two : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by
  ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega

/-- `c(1,1,1) = 1`。 -/
theorem pUVCoeff_one_one_one : pUVCoeff 1 1 1 = 1 := by
  have h1 : Finset.Icc 2 1 = (∅ : Finset ℕ) :=
    Finset.Icc_eq_empty_of_lt (by norm_num : (1 : ℕ) < 2)
  have h2 : (Finset.Icc 1 1).erase 1 = (∅ : Finset ℕ) := erase_Icc_self 1
  rw [pUVCoeff, h1, h2]
  simp

/-- `c(2,2,2) = 1`。 -/
theorem pUVCoeff_two_two_two : pUVCoeff 2 2 2 = 1 := by
  have h1 : Finset.Icc 3 2 = (∅ : Finset ℕ) :=
    Finset.Icc_eq_empty_of_lt (by norm_num : (2 : ℕ) < 3)
  have h2 : (Finset.Icc 2 2).erase 2 = (∅ : Finset ℕ) := erase_Icc_self 2
  rw [pUVCoeff, h1, h2]
  simp

/-- `c(2,1,1) = 1`。 -/
theorem pUVCoeff_two_one_one : pUVCoeff 2 1 1 = 1 := by
  have h1 : Finset.Icc 2 2 = ({2} : Finset ℕ) := Finset.Icc_self 2
  have h2 : (Finset.Icc 1 2).erase 1 = ({2} : Finset ℕ) := by
    rw [Icc_one_two]; decide
  rw [pUVCoeff, h1, h2]
  simp

/-- `c(2,1,2) = −1`。 -/
theorem pUVCoeff_two_one_two : pUVCoeff 2 1 2 = -1 := by
  have h1 : Finset.Icc 2 2 = ({2} : Finset ℕ) := Finset.Icc_self 2
  have h2 : (Finset.Icc 1 2).erase 2 = ({1} : Finset ℕ) := by
    rw [Icc_one_two]; decide
  rw [pUVCoeff, h1, h2]
  simp

/-! ## 接合点（与库内既有溯祖设施） -/

/-- `pUV 1 1 t = 1`（单条谱系；`λ_1 = 0`）。 -/
theorem pUV_one_one (t : ℝ) : pUV 1 1 t = 1 := by
  rw [pUV, show Finset.Icc 1 1 = ({1} : Finset ℕ) from Finset.Icc_self 1,
    Finset.sum_singleton, pUVCoeff_one_one_one, lambdaR_one]
  simp

/-- ★★★ **`u = 2, v = 2`**：`pUV 2 2 t = Coalescent.survival 2 t = e^{−t}`。

即「两条谱系在 `t` 内不合并」的概率 —— 正是 Degnan–Salter 的 `u = v` 口径。 -/
theorem pUV_two_two (t : ℝ) : pUV 2 2 t = Coalescent.survival 2 t := by
  rw [pUV, show Finset.Icc 2 2 = ({2} : Finset ℕ) from Finset.Icc_self 2,
    Finset.sum_singleton, pUVCoeff_two_two_two, lambdaR_two, Coalescent.survival_two]
  ring_nf

/-- ★★★ **`u = 2, v = 1`**：`pUV 2 1 t = Coalescent.firstMergeCDF 2 t = 1 − e^{−t}`。

即 `u = 2` 情形**就是**库内已有的 `Coalescent.firstMergeCDF`（`u` 条谱系中
首次合并的分布函数）。 -/
theorem pUV_two_one (t : ℝ) : pUV 2 1 t = Coalescent.firstMergeCDF 2 t := by
  rw [pUV, Icc_one_two, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2),
    pUVCoeff_two_one_one, pUVCoeff_two_one_two, lambdaR_one, lambdaR_two,
    Coalescent.firstMergeCDF_two]
  ring_nf
  rw [Real.exp_zero]

/-- ★★ **一般对角**（`1 ≤ u`）：`pUV u u t = Coalescent.survival u t`
（式 (1) 的 `u = v` 口径：「`t` 内不发生任何合并」的概率 `e^{−λ_u t}`）。 -/
theorem pUV_diag {u : ℕ} (hu : 1 ≤ u) (t : ℝ) : pUV u u t = Coalescent.survival u t := by
  have hv : u ≠ 0 := by omega
  have hcoef : pUVCoeff u u u = 1 := by
    have h1 : Finset.Icc (u + 1) u = (∅ : Finset ℕ) :=
      Finset.Icc_eq_empty_of_lt (Nat.lt_succ_self u)
    have h2 : (Finset.Icc u u).erase u = (∅ : Finset ℕ) := erase_Icc_self u
    rw [pUVCoeff, h1, h2]
    simp [hv]
  rw [pUV, show Finset.Icc u u = ({u} : Finset ℕ) from Finset.Icc_self u,
    Finset.sum_singleton, hcoef, mul_one, Coalescent.survival, lambdaR_eq_kingmanRate]

/-- ★★ **归一化的有限情形**：`pUV 2 1 t + pUV 2 2 t = 1`
（链在 `u = 2` 时只有两个状态，两条接合点直接给出归一化）。 -/
theorem pUV_normalization_two (t : ℝ) : pUV 2 1 t + pUV 2 2 t = 1 := by
  rw [pUV_two_one, pUV_two_two, Coalescent.firstMergeCDF_two, Coalescent.survival_two]
  ring

/-- `pUV 2 1 t` 的显式值：`1 − e^{−t}`。 -/
theorem pUV_two_one_eq (t : ℝ) : pUV 2 1 t = 1 - Real.exp (-t) := by
  rw [pUV_two_one, Coalescent.firstMergeCDF_two]

/-- `pUV 2 2 t` 的显式值：`e^{−t}`。 -/
theorem pUV_two_two_eq (t : ℝ) : pUV 2 2 t = Real.exp (-t) := by
  rw [pUV_two_two, Coalescent.survival_two]

/-- 一般对角的显式值（`1 ≤ u`）：`pUV u u t = e^{−λ_u t}`。 -/
theorem pUV_diag_eq {u : ℕ} (hu : 1 ≤ u) (t : ℝ) :
    pUV u u t = Real.exp (-(lambdaR u) * t) := by
  rw [pUV_diag hu, Coalescent.survival, ← lambdaR_eq_kingmanRate u]

/-! ## 系数恒等式与一般归一化（`pUV_normalization` 已证） -/

/-- `λ` 在 `m ≥ 1` 上严格单增。 -/
theorem lambdaR_lt {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) : lambdaR a < lambdaR b := by
  have hb : 1 ≤ b := by omega
  have hlt : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hsum : (0 : ℝ) < (a : ℝ) + (b : ℝ) - 1 := by
    have h1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have h2 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  rw [lambdaR, lambdaR]
  nlinarith [hlt, hsum]

theorem lambdaR_ne {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a ≠ b) :
    lambdaR a ≠ lambdaR b := by
  rcases lt_or_gt_of_ne h with h' | h'
  · exact ne_of_lt (lambdaR_lt ha h')
  · exact ne_of_gt (lambdaR_lt hb h')

/-- 清分母后的系数分子 `φ_v(x) = (∏_{m=v+1}^{u} λ_m) · ∏_{m=1}^{v-1}(λ_m − x)`。 -/
noncomputable def phiC (u v : ℕ) (x : ℝ) : ℝ :=
  (∏ m ∈ Finset.Icc (v + 1) u, lambdaR m) * ∏ m ∈ Finset.Icc 1 (v - 1), (lambdaR m - x)

/-- `E(x) = ∏_{m=1}^{u}(λ_m − x)`。 -/
noncomputable def eBig (u : ℕ) (x : ℝ) : ℝ :=
  ∏ m ∈ Finset.Icc 1 u, (lambdaR m - x)

theorem phiC_succ (u v : ℕ) (x : ℝ) (hv : v ≤ u) :
    phiC (u + 1) v x = lambdaR (u + 1) * phiC u v x := by
  unfold phiC
  rw [Finset.prod_Icc_succ_top (by omega : v + 1 ≤ u + 1)]
  ring

theorem phiC_self (u : ℕ) (x : ℝ) : phiC (u + 1) (u + 1) x = eBig u x := by
  unfold phiC eBig
  have h1 : Finset.Icc (u + 1 + 1) (u + 1) = (∅ : Finset ℕ) :=
    Finset.Icc_eq_empty_of_lt (by omega)
  have h2 : u + 1 - 1 = u := by omega
  rw [h1, h2, Finset.prod_empty, one_mul]

theorem eBig_succ (u : ℕ) (x : ℝ) : eBig (u + 1) x = eBig u x * (lambdaR (u + 1) - x) := by
  unfold eBig
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ u + 1)]

/-- ★★★ **望远镜恒等式**：`x · Σ_{v=1}^{u} φ_v(x) = −E(x)`（对 `u ≥ 1` 与**任意** `x`）。 -/
theorem telescope (u : ℕ) (hu : 1 ≤ u) (x : ℝ) :
    x * ∑ v ∈ Finset.Icc 1 u, phiC u v x = - eBig u x := by
  refine Nat.le_induction (m := 1)
    (P := fun u _ => x * ∑ v ∈ Finset.Icc 1 u, phiC u v x = - eBig u x) ?_ ?_ u hu
  · have hIcc : Finset.Icc 1 1 = ({1} : Finset ℕ) := Finset.Icc_self 1
    have hp : phiC 1 1 x = 1 := by
      unfold phiC
      have h1 : Finset.Icc 2 1 = (∅ : Finset ℕ) := Finset.Icc_eq_empty_of_lt (by norm_num)
      have h2 : Finset.Icc 1 (1 - 1) = (∅ : Finset ℕ) := by
        rw [show 1 - 1 = 0 from rfl]
        exact Finset.Icc_eq_empty_of_lt (by norm_num)
      rw [h1, h2, Finset.prod_empty, Finset.prod_empty, mul_one]
    have he : eBig 1 x = -x := by
      unfold eBig
      rw [Finset.Icc_self, Finset.prod_singleton, lambdaR_one]
      ring
    rw [hIcc, Finset.sum_singleton, hp, he]
    ring
  · intro u hu ih
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ u + 1)]
    have hstep : (∑ v ∈ Finset.Icc 1 u, phiC (u + 1) v x)
        = lambdaR (u + 1) * ∑ v ∈ Finset.Icc 1 u, phiC u v x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun v hv => by
        rw [Finset.mem_Icc] at hv
        exact phiC_succ u v x hv.2)
    rw [hstep, phiC_self, eBig_succ]
    linear_combination (lambdaR (u + 1)) * ih

/-- `E(λ_k) = 0`（`k ∈ Icc 1 u`）。 -/
theorem eBig_self_eq_zero {u k : ℕ} (hk : k ∈ Finset.Icc 1 u) : eBig u (lambdaR k) = 0 := by
  unfold eBig
  exact Finset.prod_eq_zero hk (by ring)

/-- ★★★ `k ≥ 2` 时 `Σ_{v∈Icc 1 u} φ_v(λ_k) = 0`。 -/
theorem sum_phiC_eq_zero {u k : ℕ} (hk1 : 1 ≤ k) (hku : k ≤ u) (hk2 : 2 ≤ k) :
    ∑ v ∈ Finset.Icc 1 u, phiC u v (lambdaR k) = 0 := by
  have hu : 1 ≤ u := by omega
  have htel := telescope u hu (lambdaR k)
  rw [eBig_self_eq_zero (Finset.mem_Icc.mpr ⟨hk1, hku⟩), neg_zero] at htel
  exact (mul_eq_zero.mp htel).resolve_left (ne_of_gt (lambdaR_pos hk2))

theorem sum_phiC_Icc_one_k {u k : ℕ} (hk1 : 1 ≤ k) (hku : k ≤ u) (hk2 : 2 ≤ k) :
    ∑ v ∈ Finset.Icc 1 k, phiC u v (lambdaR k) = 0 := by
  have htotal := sum_phiC_eq_zero hk1 hku hk2
  have hsplit : Finset.Icc 1 u = Finset.Icc 1 k ∪ Finset.Icc (k + 1) u := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 k) (Finset.Icc (k + 1) u) := by
    rw [Finset.disjoint_left]
    intro m hm hm'
    simp only [Finset.mem_Icc] at hm hm'
    omega
  have hsecond : ∑ v ∈ Finset.Icc (k + 1) u, phiC u v (lambdaR k) = 0 := by
    refine Finset.sum_eq_zero (fun v hv => ?_)
    rw [Finset.mem_Icc] at hv
    unfold phiC
    have hzero : (∏ m ∈ Finset.Icc 1 (v - 1), (lambdaR m - lambdaR k)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨hk1, by omega⟩) (by ring)
    rw [hzero, mul_zero]
  rw [hsplit, Finset.sum_union hdisj, hsecond, add_zero] at htotal
  exact htotal

/-- 分母 `∏_{m ∈ (Icc 1 u).erase k}(λ_m − λ_k) ≠ 0`。 -/
theorem prod_erase_ne_zero {u k : ℕ} (hk1 : 1 ≤ k) :
    (∏ m ∈ (Finset.Icc 1 u).erase k, (lambdaR m - lambdaR k)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr (fun m hm => ?_)
  rw [Finset.mem_erase, Finset.mem_Icc] at hm
  exact sub_ne_zero.mpr (lambdaR_ne hm.2.1 hk1 hm.1)

/-- 分母 `∏_{m ∈ (Icc v u).erase k}(λ_m − λ_k) ≠ 0`。 -/
theorem prod_erase_ne_zero' {u v k : ℕ} (hv1 : 1 ≤ v) (hvk : v ≤ k) :
    (∏ m ∈ (Finset.Icc v u).erase k, (lambdaR m - lambdaR k)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr (fun m hm => ?_)
  rw [Finset.mem_erase, Finset.mem_Icc] at hm
  exact sub_ne_zero.mpr (lambdaR_ne (by omega) (by omega) hm.1)

/-- ★★★ **清分母**：`c(u,v,k) · D_k = φ_v(λ_k)`（`1 ≤ v ≤ k ≤ u`）。 -/
theorem pUVCoeff_mul_prod_erase {u v k : ℕ} (hv1 : 1 ≤ v) (hvk : v ≤ k) (hku : k ≤ u) :
    pUVCoeff u v k * (∏ m ∈ (Finset.Icc 1 u).erase k, (lambdaR m - lambdaR k))
      = phiC u v (lambdaR k) := by
  have hvne : v ≠ 0 := by omega
  have hset : (Finset.Icc 1 u).erase k
      = Finset.Icc 1 (v - 1) ∪ (Finset.Icc v u).erase k := by
    ext m
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (v - 1)) ((Finset.Icc v u).erase k) := by
    rw [Finset.disjoint_left]
    intro m hm hm'
    simp only [Finset.mem_Icc] at hm
    simp only [Finset.mem_erase, Finset.mem_Icc] at hm'
    omega
  have hDen : (∏ m ∈ (Finset.Icc v u).erase k, (lambdaR m - lambdaR k)) ≠ 0 :=
    prod_erase_ne_zero' (u := u) hv1 hvk
  rw [hset, Finset.prod_union hdisj, pUVCoeff, phiC]
  simp only [hvne, ↓reduceIte, one_mul]
  set N := ∏ x ∈ Finset.Icc (v + 1) u, lambdaR x
  set P := ∏ x ∈ Finset.Icc 1 (v - 1), (lambdaR x - lambdaR k)
  set D := ∏ x ∈ (Finset.Icc v u).erase k, (lambdaR x - lambdaR k)
  have hD0 : D ≠ 0 := hDen
  have hmain : N / D * (P * D) = N * P := by
    field_simp
  exact hmain

/-- `c(u,1,1) = 1`。 -/
theorem pUVCoeff_one_one_eq_one (u : ℕ) : pUVCoeff u 1 1 = 1 := by
  have hset : (Finset.Icc 1 u).erase 1 = Finset.Icc 2 u := by
    ext m
    simp only [Finset.mem_erase, Finset.mem_Icc]
    omega
  have hne : (∏ m ∈ Finset.Icc 2 u, lambdaR m) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun m hm => ?_)
    rw [Finset.mem_Icc] at hm
    exact ne_of_gt (lambdaR_pos (by omega))
  rw [pUVCoeff, hset]
  simp only [show ¬ ((1 : ℕ) = 0) from by norm_num, ↓reduceIte, lambdaR_one, sub_zero]
  rw [one_mul]
  exact div_self hne

/-- ★★★ **系数恒等式（正确的形状）**：`Σ_{v∈Icc 1 k} c(u,v,k) = δ_{k,1}`（`1 ≤ k ≤ u`）。

⚠️ 与文件头 docstring 写的 `if k = u then 1 else 0` **不同**：正确的一侧是 `k = 1`。 -/
theorem pUVCoeff_sum_Icc_eq (u k : ℕ) (hk1 : 1 ≤ k) (hku : k ≤ u) :
    ∑ v ∈ Finset.Icc 1 k, pUVCoeff u v k = if k = 1 then 1 else 0 := by
  rcases eq_or_lt_of_le hk1 with h | h
  · rw [← h] at hku ⊢
    rw [Finset.Icc_self, Finset.sum_singleton, pUVCoeff_one_one_eq_one u]
    simp
  · have hk2 : 2 ≤ k := h
    have hkne : k ≠ 1 := by omega
    have hD : (∏ m ∈ (Finset.Icc 1 u).erase k, (lambdaR m - lambdaR k)) ≠ 0 :=
      prod_erase_ne_zero (u := u) hk1
    have hmul : (∑ v ∈ Finset.Icc 1 k, pUVCoeff u v k)
        * (∏ m ∈ (Finset.Icc 1 u).erase k, (lambdaR m - lambdaR k)) = 0 := by
      rw [Finset.sum_mul]
      refine (Eq.trans ?_ (sum_phiC_Icc_one_k hk1 hku hk2))
      exact Finset.sum_congr rfl (fun v hv => by
        rw [Finset.mem_Icc] at hv
        exact pUVCoeff_mul_prod_erase hv.1 hv.2 hku)
    have hzero : (∑ v ∈ Finset.Icc 1 k, pUVCoeff u v k) = 0 :=
      (mul_eq_zero.mp hmul).resolve_right hD
    rw [hzero]
    simp [hkne]

/-- 三角换序：`Σ_{v≤u} Σ_{k≥v} = Σ_{k≤u} Σ_{v≤k}`。 -/
theorem sum_Icc_Icc_triangle {M : Type*} [AddCommMonoid M] (u : ℕ) (f : ℕ → ℕ → M) :
    (∑ v ∈ Finset.Icc 1 u, ∑ k ∈ Finset.Icc v u, f v k)
      = ∑ k ∈ Finset.Icc 1 u, ∑ v ∈ Finset.Icc 1 k, f v k := by
  have h1 : ∀ a b : ℕ, Finset.Icc a b = Finset.Ico a (b + 1) := by
    intro a b
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  simp only [h1]
  exact Finset.sum_Ico_Ico_comm 1 (u + 1) f

/-- ★★★ **归一化（一般 `u ≥ 1`）**：`Σ_{v=1}^{u} pUV u v t = 1`。 -/
theorem pUV_sum_Icc_one (u : ℕ) (hu : 1 ≤ u) (t : ℝ) :
    ∑ v ∈ Finset.Icc 1 u, pUV u v t = 1 := by
  simp only [pUV]
  rw [sum_Icc_Icc_triangle u (fun v k => Real.exp (-(lambdaR k) * t) * pUVCoeff u v k)]
  have hfactor : ∀ k ∈ Finset.Icc 1 u,
      (∑ v ∈ Finset.Icc 1 k, Real.exp (-(lambdaR k) * t) * pUVCoeff u v k)
        = Real.exp (-(lambdaR k) * t) * ∑ v ∈ Finset.Icc 1 k, pUVCoeff u v k := by
    intro k _
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl hfactor]
  have hcoef : ∀ k ∈ Finset.Icc 1 u,
      (∑ v ∈ Finset.Icc 1 k, pUVCoeff u v k) = if k = 1 then 1 else 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact pUVCoeff_sum_Icc_eq u k hk.1 hk.2
  rw [Finset.sum_congr rfl (fun k hk => by rw [hcoef k hk])]
  rw [Finset.sum_eq_single 1]
  · simp [lambdaR_one]
  · intro k _ hk1
    simp [hk1]
  · intro h1
    exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hu⟩) h1

/-- ★B **反例**：文件头 docstring 的 `Σ_{v=1}^{k}c(u,v,k) = if k = u then 1 else 0`
**不成立**（`u = k = 3` 时左边 `0`，右边 `1`）。 -/
theorem coefficient_identity_k_eq_u_false :
    ¬ (∑ v ∈ Finset.Icc 1 3, pUVCoeff 3 v 3 = if (3 : ℕ) = 3 then 1 else 0) := by
  rw [pUVCoeff_sum_Icc_eq 3 3 (by norm_num) (by norm_num)]
  norm_num

/-- 正确形状在 `u = 3, k = 3` 上的值：`0`（= `if 3 = 1 then 1 else 0`）。 -/
theorem pUVCoeff_sum_three_three :
    (∑ v ∈ Finset.Icc 1 3, pUVCoeff 3 v 3) = 0 := by
  rw [pUVCoeff_sum_Icc_eq 3 3 (by norm_num) (by norm_num)]
  norm_num

/-! ## `pUV_nonneg` 的部分推进（`u ≤ 3`，显式闭形式） -/

/-- `c(3,2,2) = 3/2`。 -/
theorem pUVCoeff_three_two_two : pUVCoeff 3 2 2 = 3 / 2 := by
  have h1 : Finset.Icc 3 3 = ({3} : Finset ℕ) := Finset.Icc_self 3
  have h2 : (Finset.Icc 2 3).erase 2 = ({3} : Finset ℕ) := by decide
  rw [pUVCoeff, h1, h2]
  simp only [show ¬ ((2 : ℕ) = 0) from by norm_num, ↓reduceIte, Finset.prod_singleton,
    lambdaR_three, lambdaR_two, one_mul]
  norm_num

/-- `c(3,2,3) = −3/2`。 -/
theorem pUVCoeff_three_two_three : pUVCoeff 3 2 3 = -3 / 2 := by
  have h1 : Finset.Icc 3 3 = ({3} : Finset ℕ) := Finset.Icc_self 3
  have h2 : (Finset.Icc 2 3).erase 3 = ({2} : Finset ℕ) := by decide
  rw [pUVCoeff, h1, h2]
  simp only [show ¬ ((2 : ℕ) = 0) from by norm_num, ↓reduceIte, Finset.prod_singleton,
    lambdaR_three, lambdaR_two, one_mul]
  norm_num

/-- `pUV 3 2 t = (3/2)(e^{−t} − e^{−3t})`。 -/
theorem pUV_three_two_eq (t : ℝ) :
    pUV 3 2 t = (3 / 2) * (Real.exp (-t) - Real.exp (-3 * t)) := by
  rw [pUV, show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) from by decide,
    Finset.sum_pair (by norm_num : (2 : ℕ) ≠ 3), pUVCoeff_three_two_two,
    pUVCoeff_three_two_three,
    show -(lambdaR 2) * t = -t by rw [lambdaR_two]; ring,
    show -(lambdaR 3) * t = -3 * t by rw [lambdaR_three]]
  ring

/-- `pUV 3 3 t = e^{−3t}`。 -/
theorem pUV_three_three_eq (t : ℝ) : pUV 3 3 t = Real.exp (-3 * t) := by
  rw [pUV_diag_eq (by norm_num : 1 ≤ 3),
    show -(lambdaR 3) * t = -3 * t by rw [lambdaR_three]]

/-- `pUV 3 1 t = 1 − (3/2)e^{−t} + (1/2)e^{−3t}`（由已证的一般归一化 + 上面两条）。 -/
theorem pUV_three_one_eq (t : ℝ) :
    pUV 3 1 t = 1 - (3 / 2) * Real.exp (-t) + (1 / 2) * Real.exp (-3 * t) := by
  have hsum : pUV 3 1 t + pUV 3 2 t + pUV 3 3 t = 1 := by
    have h := pUV_sum_Icc_one 3 (by norm_num) t
    rw [show Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) from by decide] at h
    rw [Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2, 3} : Finset ℕ)),
      Finset.sum_insert (by decide : (2 : ℕ) ∉ ({3} : Finset ℕ)), Finset.sum_singleton] at h
    linarith
  rw [pUV_three_two_eq, pUV_three_three_eq] at hsum
  linarith

theorem pUV_two_one_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ pUV 2 1 t := by
  rw [pUV_two_one_eq, sub_nonneg,
    show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
  exact Real.exp_le_exp.mpr (by linarith)

theorem pUV_two_two_nonneg (t : ℝ) : 0 ≤ pUV 2 2 t := by
  rw [pUV_two_two_eq]
  exact (Real.exp_pos _).le

theorem pUV_three_two_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ pUV 3 2 t := by
  rw [pUV_three_two_eq]
  have hle : Real.exp (-3 * t) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
  exact mul_nonneg (by norm_num) (by linarith)

theorem pUV_three_three_nonneg (t : ℝ) : 0 ≤ pUV 3 3 t := by
  rw [pUV_three_three_eq]
  exact (Real.exp_pos _).le

/-- `pUV 3 1 t ≥ 0`（**对一切 `t`**）：`= (1/2)(1 − e^{−t})²(2 + e^{−t})`。 -/
theorem pUV_three_one_nonneg (t : ℝ) : 0 ≤ pUV 3 1 t := by
  rw [pUV_three_one_eq]
  have h3 : Real.exp (-3 * t) = Real.exp (-t) ^ 3 := by
    rw [show -3 * t = -t + (-t + -t) by ring, Real.exp_add, Real.exp_add]
    ring
  have hfac : 1 - (3 / 2) * Real.exp (-t) + (1 / 2) * Real.exp (-3 * t)
      = (1 / 2) * (1 - Real.exp (-t)) ^ 2 * (2 + Real.exp (-t)) := by
    rw [h3]
    ring
  rw [hfac]
  have h1 : (0 : ℝ) ≤ (1 - Real.exp (-t)) ^ 2 := sq_nonneg _
  have h2 : (0 : ℝ) ≤ 2 + Real.exp (-t) := by
    have := Real.exp_pos (-t)
    linarith
  exact mul_nonneg (mul_nonneg (by norm_num) h1) h2

/-- ★★ **`pUV_nonneg` 的 `u = 2` 情形**。 -/
theorem pUV_nonneg_two (v : ℕ) (hv1 : 1 ≤ v) (hvu : v ≤ 2) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ pUV 2 v t := by
  have hv : v = 1 ∨ v = 2 := by omega
  rcases hv with rfl | rfl
  · exact pUV_two_one_nonneg t ht
  · exact pUV_two_two_nonneg t

/-- ★★ **`pUV_nonneg` 的 `u = 3` 情形**。 -/
theorem pUV_nonneg_three (v : ℕ) (hv1 : 1 ≤ v) (hvu : v ≤ 3) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ pUV 3 v t := by
  have hv : v = 1 ∨ v = 2 ∨ v = 3 := by omega
  rcases hv with rfl | rfl | rfl
  · exact pUV_three_one_nonneg t
  · exact pUV_three_two_nonneg t ht
  · exact pUV_three_three_nonneg t

/-- ★★ **`pUV_nonneg` 的 `u ≤ 3` 情形**（一般 `u` 仍是缺口）。 -/
theorem pUV_nonneg_upto_three (u v : ℕ) (t : ℝ) (hu : u ≤ 3) (hv1 : 1 ≤ v) (hvu : v ≤ u)
    (ht : 0 ≤ t) : 0 ≤ pUV u v t := by
  have hu' : u = 1 ∨ u = 2 ∨ u = 3 := by omega
  rcases hu' with rfl | rfl | rfl
  · have hv : v = 1 := by omega
    rw [hv, pUV_one_one]
    norm_num
  · exact pUV_nonneg_two v hv1 hvu t ht
  · exact pUV_nonneg_three v hv1 hvu t ht

/-! ### 反空真（★：一般定理在最小非平凡例子上落地） -/

/-- ★ 非空实例：一般归一化在 `u = 3` 上（最小非平凡情形）。 -/
example (t : ℝ) : ∑ v ∈ Finset.Icc 1 3, pUV 3 v t = 1 := pUV_sum_Icc_one 3 (by norm_num) t

/-- ★ 非空实例：系数行和恒等式在 `u = 3, k = 1` 上取值 `1`。 -/
example : (∑ v ∈ Finset.Icc 1 1, pUVCoeff 3 v 1) = 1 := by
  rw [pUVCoeff_sum_Icc_eq 3 1 (by norm_num) (by norm_num)]
  norm_num

/-- ★ 非空实例：`pUV_nonneg` 的 `u ≤ 3` 情形在 `u = 3, v = 1, t = 0` 上。 -/
example : 0 ≤ pUV 3 1 0 := pUV_nonneg_upto_three 3 1 0 (by norm_num) (by norm_num)
  (by norm_num) le_rfl

/-! ## 接口与显式缺口（`def … : Prop`） -/

/-- ✅ **原缺口 `pUV_normalization`（现已证）**：一般归一化
`Σ_{v=1}^{u} pUV u v t = 1`（`u ≥ 3`）。证明见上节（`pUV_sum_Icc_one`，甚至 `u ≥ 1`）；
本 `def` 保留为**接口/文档**，不再表示缺口。 -/
def pUV_normalization : Prop :=
  ∀ (u : ℕ) (t : ℝ), 3 ≤ u → ∑ v ∈ Finset.Icc 1 u, pUV u v t = 1

/-- ✅ **`pUV_normalization` 已证**（原缺口，现已消）。 -/
theorem pUV_normalization_proved : pUV_normalization :=
  fun u t hu => pUV_sum_Icc_one u (by omega) t

/-- ❌ **仍是缺口**：`pUV u v t ≥ 0`（`1 ≤ v ≤ u`、`t ≥ 0`）。

本批已证 `u ≤ 3`（`pUV_nonneg_two` / `pUV_nonneg_three` / `pUV_nonneg_upto_three`）；
一般 `u` 缺的是「保正性」器材：矩阵指数（Kolmogorov 前向方程 + 解唯一性），
或首次跳跃卷积递推 `p_{uv}(t) = δ_{uv}e^{−λ_u t} + λ_u∫_0^t e^{−λ_u s}p_{u−1,v}(t−s)ds`
（需要把部分分式形式与它接上，本质上是 Laplace 变换唯一性）。
两条器材本批都没有 —— 见文件头「`pUV_nonneg` 缺什么」。**未证。** -/
def pUV_nonneg : Prop := ∀ (u v : ℕ) (t : ℝ), 1 ≤ v → v ≤ u → 0 ≤ t → 0 ≤ pUV u v t

/-- ❌ **缺口**：`pUV u v 0 = if u = v then 1 else 0`（即 `exp(0·Q) = I`）。

等价于「系数沿 `k` 求和为 `δ_{v,u}`」（= `Σ_k P_k = I` 的 `(u,v)` 元）。
⚠️ 这与归一化用的**行和**恒等式不是同一条：行和那条已由 `pUVCoeff_sum_Icc_eq` 证出
（`Σ_{v=1}^{k}c(u,v,k) = δ_{k,1}`，注意是 `k = 1` 而不是旧 docstring 写的 `k = u`）。**未证。** -/
def pUV_zero_time : Prop :=
  ∀ u v : ℕ, 1 ≤ v → v ≤ u → pUV u v 0 = if u = v then 1 else 0

/-- ❌ **缺口**：`pUV` 的系数与式 (1) **产品形式**的逐项一致性

```text
  c(u,v,k) = (2k−1)(−1)^{k−v} [Π_{y=0}^{k−2}(v+y)] [Π_{y=0}^{k−1}(u−y)/(u+y)] / (v!(k−v)!)
```

（右边就是重新提取的式 (1) 中 `e^{−λ_k T}` 的系数；见文件头。）
脚本 `(C0)`/`(C0c)` 在 `u ≤ 9` 上精确核对；Lean 内未证。**未证。** -/
def pUV_eq_formula1 : Prop :=
  ∀ (u v k : ℕ), 1 ≤ v → v ≤ k → k ≤ u →
    pUVCoeff u v k
      = (2 * (k : ℝ) - 1) * (-1 : ℝ) ^ (k - v)
          * (∏ y ∈ Finset.range (k - 1), ((v : ℝ) + y))
          * (∏ y ∈ Finset.range k, (((u : ℝ) - y) / ((u : ℝ) + y)))
          / ((v.factorial : ℝ) * (((k - v).factorial : ℝ)))

end Phylo.Stat.DegnanSalter
