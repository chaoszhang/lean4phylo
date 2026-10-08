/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Phylo.Stat.CASTERWeights

/-!
# `Phylo.CASTERF84` —— CASTER 附录 **命题 A（F84 情形）** 的形式化

文献：Zhang, Nielsen, Mirarab (2025), *Science* **387**(6737) eadk9688，
附录 `sm.tex`（本项目存于 `references/tex/Caster2025_Supplementary.tex`）。

本文件形式化附录 **F84 模型下的命题 A**

`E[w(ab|cd)] − E[w(ac|bd)] = 2 π_A π_C π_G π_T π_R π_Y e^{−λ(1+κ)L_T} (1 − e^{−λ l_x})`

（`L_T = l_a+l_b+l_c+l_d`）的**核心里程碑**：F84 转移核的无除法谱分解、三条正当性
证书（随机性 / 半群律 / 生成元相容）、率矩阵 `Q` 的行和 / 平稳性 / 细致平衡 /
谱（特征多项式 `M(M−I)(M−(1+κ)I) = 0`）。
代码里速率因子记作 `lam`（`λ` 是 Lean 保留字），转换/颠换比记作 `kap`（`κ`）。

## 0. 记账口径（**必读**：这是前两轮失败的根源）

### 0.1 附录 `sm.tex` 1559–1562 的 aggregated 式逐字转写

```
E[w(ab|cd)] = Σ_{χ∈{a,g}} Σ_{ψ∈{c,t}} [
    π_R²π_Y²  ( P(χ,χ,ψ,ψ) + P(ψ,ψ,χ,χ) )
  − π_X²π_Y²  ( P(a+g,a+g,ψ,ψ) + P(ψ,ψ,a+g,a+g) )
  − π_R²π_Ψ²  ( P(χ,χ,c+t,c+t) + P(c+t,c+t,ψ,ψ) )
  + π_X²π_Ψ²  ( P(a+g,a+g,c+t,c+t) + P(c+t,c+t,a+g,a+g) ) ]
```
（`P(R,R,·,·)` 表示该两个坐标**各自遍历** `R = {A,G}` 求和；`π_X = π_χ`、`π_Ψ = π_ψ`。）
⚠️ 第 3 行第二个 term 印作 `P(c+t,c+t,ψ,ψ)`，而第 2 行的对应 term 印作
`P(ψ,ψ,a+g,a+g)`——**二者不对称**；按对称化读法（第 3 行第二个 term 应为
`P(ψ,ψ,c+t,c+t)`）整式才在交换两侧下不变。**本文件采用对称化读法**（数值见 0.2）。

### 0.2 「差 4 倍」的定位结论（协调侧与本侧各自独立数值复核）

脚本 `_t39/f84_final_check.py`（管线用 JC69 解析核自检到 `1.2e-15`、四叶 256 项概率和为 1）：

* 照印 aggregated 式（对称化读法）隐含的逐模式权重表代入
  `E[w(ab|cd)] − E[w(ac|bd)]`，除以印的常数
  `2π_Aπ_Cπ_Gπ_Tπ_Rπ_Y e^{−λ(1+κ)L_T}(1−e^{−λl_x})`，**恒等于 4.000000**；
* 四条线的系数各除以 4 ⇒ 比值**恒等于 1.000000**（8 组随机参数，含 `κ=0`、`κ=2.5`，
  偏差 < 1.3e-13；同时 `E[w(ac|bd)] = E[w(ad|bc)]` 精确成立）；
* 照字面（非对称）读法**不**给出常数比（漂移 −6 … +56）。

⇒ **系数照印的那张表就是作者意图的表，只是整体归一化多了 4 倍**（与 JC69 的
「6 倍」是同一类记账差异；不影响 CASTER 的统计一致性结论）。

### 0.3 ★ 采用的逐模式权重表口径（= 照印系数 ÷ 4）

`p_c` 为类频率（`p_R = π_A+π_G`、`p_Y = π_C+π_T`），`q_c` 为类内平方和
（`q_R = π_A²+π_G²`、`q_Y = π_C²+π_T²`），`h_c(i,j) = p_c²·[i=j] − q_c`。则照印
aggregated 式（对称化读法）隐含的**逐模式权重表 ÷ 4** 恰为

```
wF84(σ) = (1/4)·( 1[(σ_a,σ_b)∈R² ∧ (σ_c,σ_d)∈Y²]·h_R(σ_a,σ_b)·h_Y(σ_c,σ_d)
                + 1[(σ_a,σ_b)∈Y² ∧ (σ_c,σ_d)∈R²]·h_Y(σ_a,σ_b)·h_R(σ_c,σ_d) )
```

（`R = {0,1}`、`Y = {2,3}`，字母表编号 `0=A,1=G,2=C,3=T`）。非零模式是两个 16 元块
（共 32 个），`h` 在块上只取 `W1 = X_RX_Y`、`W2 = −q_YX_R`、`W3 = −q_RX_Y`、`W4 = q_Rq_Y`。

## 1. F84 率矩阵（附录 1592–1601）

`Q_ij = λ π_j (1 + κ·1[i,j∈R]/π_R + κ·1[i,j∈Y]/π_Y)`（`i ≠ j`），对角 = 负行和。
附录 1601 的 `λ` 在本文件里**作为自由参数 `lam`**（与 `CASTERLM1` 一致：命题 A 的
恒等式对**任意** `lam` 成立）。

## 2. 证明路线（**不手推三分情况、不求核的闭式系数**）

✔ ★ **关键结构性发现**：F84 的半群有**无除法的谱分解**

```
K(t) := e^{−λMt} = Π + e^{−λt}·(B − Π) + e^{−λ(1+κ)t}·(I − B)                    (★)
```

`Π_ij = π_j`、`B_ij = 1[cl i = cl j]·π_j/p_{cl j}`、`M := I − Π + κ(I − B)`，`Q = −λM`。
`Π`、`B−Π`、`I−B` 是**互相正交的幂等元**（`P00…P22` 九条乘法表），故 (★) 直接是
`M` 的谱分解。三条正当性证书因此全是纯矩阵元代数：

* ★ 随机性（行和）：`Kmat_row_sum`（行和 1）。
  ⚠️ 元素非负性**未证**（见文件末「缺口」；故此处**不打 ★**，纪律 12）；
* ★★ 半群律：`Kmat_semigroup`；
* ★★ 生成元相容：`Kmat_hasDerivAt`（`d/dt K(t)|_{t=0} = Q`）。

配合 `K(0) = I`（`Kmat_zero`），这三条把 `Kmat` 唯一确定为 `exp(Qt)`。
**不需要**求 `exp(Qt)` 的闭式系数（前两个 agent 正是在那里翻车的）。

✔ **推导侧（已就绪的化简）**：由 `h_c = p_c²·I − q_c·J`，
`Agg_c(u;t₁,t₂) := Σ_{i,j∈c} h_c(i,j)·K(t₁)[u,i]·K(t₂)[u,j]` 满足
**`Agg_c(u) = 0`（`u ∉ c`）** 与 **`Σ_{u∈c} π_u Agg_c(u) = p_c·X_c·e^{−λ(1+κ)(t₁+t₂)}`**
（数值复核见 0.2），于是正确拓扑的期望得分直接坍缩成附录印的常数。

## 3. 假设（逐条）与诚实边界

**假设**：`hsum : π_R + π_Y = 1`（即 `Σπ = 1`）；`hR : π_R ≠ 0`、`hY : π_Y ≠ 0`
（`Bmat` 含除法）；非负性证书另需 `π > 0`、`0 ≤ κ`、`0 ≤ λ`、`0 ≤ t`。
半群律与生成元相容**不需要**任何符号/非负假设。
**边界**：(a) `lam` 是自由参数，不形式化附录 1601 的 `λ` 闭式与谱归一化的对应；
(b) 权重表采用 §0.3 口径（照印系数 ÷ 4）；(c) 本文件交付文件头 §2 的**核心里程碑**；
`patternProb` / `wF84` / 主定理与抽象引擎对接**未完成**（缺口清单见 §6）。
-/

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

noncomputable section

namespace Phylo

namespace CASTERF84

open Finset

/-! ## §0. 基本记号与 F84 核、生成元 -/

/-- 嘌呤频率 `π_R = π_A + π_G`。 -/
def piR (pi : Fin 4 → ℝ) : ℝ := pi 0 + pi 1

/-- 嘧啶频率 `π_Y = π_C + π_T`。 -/
def piY (pi : Fin 4 → ℝ) : ℝ := pi 2 + pi 3

/-- 类内平方和 `q_R = π_A² + π_G²`。 -/
def sqR (pi : Fin 4 → ℝ) : ℝ := pi 0 ^ 2 + pi 1 ^ 2

/-- 类内平方和 `q_Y = π_C² + π_T²`。 -/
def sqY (pi : Fin 4 → ℝ) : ℝ := pi 2 ^ 2 + pi 3 ^ 2

/-- **类投影矩阵** `B_ij = 1[cl i = cl j]·π_j/p_{cl j}`（16 个 entry 字面写死，
使 `simp [Bmat]` 与 `rfl` 都能直接归约）。 -/
def Bmat (pi : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ
  | 0, 0 => pi 0 / piR pi
  | 0, 1 => pi 1 / piR pi
  | 0, 2 => 0
  | 0, 3 => 0
  | 1, 0 => pi 0 / piR pi
  | 1, 1 => pi 1 / piR pi
  | 1, 2 => 0
  | 1, 3 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => pi 2 / piY pi
  | 2, 3 => pi 3 / piY pi
  | 3, 0 => 0
  | 3, 1 => 0
  | 3, 2 => pi 2 / piY pi
  | 3, 3 => pi 3 / piY pi

/-- 平稳投影 `Π_ij = π_j`。 -/
abbrev P0 (pi : Fin 4 → ℝ) (_i j : Fin 4) : ℝ := pi j

/-- `B − Π`。 -/
abbrev P1 (pi : Fin 4 → ℝ) (i j : Fin 4) : ℝ := Bmat pi i j - pi j

/-- `I − B`。 -/
abbrev P2 (pi : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  (if i = j then (1 : ℝ) else 0) - Bmat pi i j

/-- `e^{−λt}`。 -/
def sm (lam t : ℝ) : ℝ := Real.exp (-(lam * t))

/-- `e^{−λ(1+κ)t}`（F84 的第二个指数率）。 -/
def rm (lam kap t : ℝ) : ℝ := Real.exp (-(lam * (1 + kap) * t))

/-- ★ **F84 转移核**（即文件头 (★)）：`K(t) = Π + e^{−λt}(B−Π) + e^{−λ(1+κ)t}(I−B)`。 -/
def Kmat (pi : Fin 4 → ℝ) (kap lam t : ℝ) (i j : Fin 4) : ℝ :=
  P0 pi i j + sm lam t * P1 pi i j + rm lam kap t * P2 pi i j

/-- **F84 生成元** `Q = −λ(B−Π) − λ(1+κ)(I−B) = −λM`
（与附录 1592–1597 逐元素一致，见 `Qmat_off` / `Qmat_diag`）。 -/
def Qmat (pi : Fin 4 → ℝ) (kap lam : ℝ) (i j : Fin 4) : ℝ :=
  -lam * (Bmat pi i j - pi j)
    - lam * (1 + kap) * ((if i = j then (1 : ℝ) else 0) - Bmat pi i j)

/-- `M = I − Π + κ(I − B)`，满足 `Q = −λM`。 -/
def Mmat (pi : Fin 4 → ℝ) (kap : ℝ) (i j : Fin 4) : ℝ :=
  (if i = j then (1 : ℝ) else 0) - pi j
    + kap * ((if i = j then (1 : ℝ) else 0) - Bmat pi i j)

@[simp] theorem Kmat_apply (pi : Fin 4 → ℝ) (kap lam t : ℝ) (i j : Fin 4) :
    Kmat pi kap lam t i j
      = pi j + sm lam t * (Bmat pi i j - pi j)
        + rm lam kap t * ((if i = j then (1 : ℝ) else 0) - Bmat pi i j) := rfl

@[simp] theorem sm_zero (lam : ℝ) : sm lam 0 = 1 := by simp [sm]

@[simp] theorem rm_zero (lam kap : ℝ) : rm lam kap 0 = 1 := by simp [rm]

theorem sm_add (lam s t : ℝ) : sm lam (s + t) = sm lam s * sm lam t := by
  rw [sm, sm, sm, ← Real.exp_add]; congr 1; ring

theorem rm_add (lam kap s t : ℝ) : rm lam kap (s + t) = rm lam kap s * rm lam kap t := by
  rw [rm, rm, rm, ← Real.exp_add]; congr 1; ring

theorem sm_pos (lam t : ℝ) : 0 < sm lam t := Real.exp_pos _

theorem rm_pos (lam kap t : ℝ) : 0 < rm lam kap t := Real.exp_pos _

/-- `K(0) = I`。 -/
theorem Kmat_zero (pi : Fin 4 → ℝ) (kap lam : ℝ) (i j : Fin 4) :
    Kmat pi kap lam 0 i j = if i = j then (1 : ℝ) else 0 := by
  rw [Kmat_apply, sm_zero, rm_zero, one_mul, one_mul]; ring

/-! ## §1. `B` 的代数性质 -/

theorem sum_pi (pi : Fin 4 → ℝ) (hsum : piR pi + piY pi = 1) : ∑ j : Fin 4, pi j = 1 := by
  rw [Fin.sum_univ_four]; simp only [piR, piY] at hsum; linarith

/-- `∑_j (if i = j then c else 0) * f j = c * f i`。 -/
theorem sum_ite_mul (i : Fin 4) (c : ℝ) (f : Fin 4 → ℝ) :
    ∑ j : Fin 4, (if i = j then c else 0) * f j = c * f i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; rw [ite_eq_right (fun h => hj h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- `∑_j f j * (if j = k then c else 0) = c * f k`。 -/
theorem sum_mul_ite (k : Fin 4) (c : ℝ) (f : Fin 4 → ℝ) :
    ∑ j : Fin 4, f j * (if j = k then c else 0) = c * f k := by
  rw [Finset.sum_eq_single k]
  · simp [mul_comm]
  · intro j _ hj; rw [ite_eq_right hj, mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- `∑_j (if i = j then c else 0) = c`。 -/
theorem sum_ite_self (i : Fin 4) (c : ℝ) :
    ∑ j : Fin 4, (if i = j then c else 0) = c := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; rw [ite_eq_right (fun h => hj h.symm)]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem Bmat_row_sum (pi : Fin 4 → ℝ) (hR : piR pi ≠ 0) (hY : piY pi ≠ 0)
    (i : Fin 4) : ∑ j : Fin 4, Bmat pi i j = 1 := by
  simp only [piR] at hR; simp only [piY] at hY
  fin_cases i <;>
  · simp only [Fin.sum_univ_four, Bmat, piR, piY]
    field_simp
    ring

/-- `B` 的平稳性（字面版，`k = 0`）：`∑_j π_j B_j0 = π_0`。 -/
theorem sum_pi_mul_Bmat_0 (pi : Fin 4 → ℝ) (hR : piR pi ≠ 0) (_hY : piY pi ≠ 0) :
    ∑ j : Fin 4, pi j * Bmat pi j 0 = pi 0 := by
  simp only [piR] at hR
  simp only [Fin.sum_univ_four, Bmat, piR, piY]
  field_simp
  ring

theorem sum_pi_mul_Bmat_1 (pi : Fin 4 → ℝ) (hR : piR pi ≠ 0) (_hY : piY pi ≠ 0) :
    ∑ j : Fin 4, pi j * Bmat pi j 1 = pi 1 := by
  simp only [piR] at hR
  simp only [Fin.sum_univ_four, Bmat, piR, piY]
  field_simp
  ring

theorem sum_pi_mul_Bmat_2 (pi : Fin 4 → ℝ) (_hR : piR pi ≠ 0) (hY : piY pi ≠ 0) :
    ∑ j : Fin 4, pi j * Bmat pi j 2 = pi 2 := by
  simp only [piY] at hY
  simp only [Fin.sum_univ_four, Bmat, piR, piY]
  field_simp
  ring

theorem sum_pi_mul_Bmat_3 (pi : Fin 4 → ℝ) (_hR : piR pi ≠ 0) (hY : piY pi ≠ 0) :
    ∑ j : Fin 4, pi j * Bmat pi j 3 = pi 3 := by
  simp only [piY] at hY
  simp only [Fin.sum_univ_four, Bmat, piR, piY]
  field_simp
  ring

/-- `B` 的平稳性：`∑_j π_j B_jk = π_k`。 -/
theorem sum_pi_mul_Bmat (pi : Fin 4 → ℝ) (hR : piR pi ≠ 0) (hY : piY pi ≠ 0)
    (k : Fin 4) : ∑ j : Fin 4, pi j * Bmat pi j k = pi k := by
  fin_cases k
  · exact sum_pi_mul_Bmat_0 pi hR hY
  · exact sum_pi_mul_Bmat_1 pi hR hY
  · exact sum_pi_mul_Bmat_2 pi hR hY
  · exact sum_pi_mul_Bmat_3 pi hR hY

theorem Bmat_mul (pi : Fin 4 → ℝ) (hR : piR pi ≠ 0) (hY : piY pi ≠ 0)
    (i k : Fin 4) : ∑ j : Fin 4, Bmat pi i j * Bmat pi j k = Bmat pi i k := by
  simp only [piR] at hR; simp only [piY] at hY
  fin_cases i <;> fin_cases k <;>
  · simp only [Fin.sum_univ_four, Bmat, piR, piY]
    field_simp
    ring

/-- `π_i B_ij = π_j B_ji`（无需非退化假设）。 -/
theorem pi_mul_Bmat_comm (pi : Fin 4 → ℝ) (i j : Fin 4) :
    pi i * Bmat pi i j = pi j * Bmat pi j i := by
  fin_cases i <;> fin_cases j <;>
  (first
    | (show pi 0 * (pi 0 / piR pi) = pi 0 * (pi 0 / piR pi); rfl)
    | (show pi 0 * (pi 1 / piR pi) = pi 1 * (pi 0 / piR pi); ring)
    | (show pi 1 * (pi 0 / piR pi) = pi 0 * (pi 1 / piR pi); ring)
    | (show pi 1 * (pi 1 / piR pi) = pi 1 * (pi 1 / piR pi); rfl)
    | (show pi 0 * (0 : ℝ) = pi 2 * 0; ring)
    | (show pi 0 * (0 : ℝ) = pi 3 * 0; ring)
    | (show pi 1 * (0 : ℝ) = pi 2 * 0; ring)
    | (show pi 1 * (0 : ℝ) = pi 3 * 0; ring)
    | (show pi 2 * (0 : ℝ) = pi 0 * 0; ring)
    | (show pi 2 * (0 : ℝ) = pi 1 * 0; ring)
    | (show pi 3 * (0 : ℝ) = pi 0 * 0; ring)
    | (show pi 3 * (0 : ℝ) = pi 1 * 0; ring)
    | (show pi 2 * (pi 2 / piY pi) = pi 2 * (pi 2 / piY pi); rfl)
    | (show pi 2 * (pi 3 / piY pi) = pi 3 * (pi 2 / piY pi); ring)
    | (show pi 3 * (pi 2 / piY pi) = pi 2 * (pi 3 / piY pi); ring)
    | (show pi 3 * (pi 3 / piY pi) = pi 3 * (pi 3 / piY pi); rfl))


/-! ## §2. 三个投影的乘法表（半群律的全部代数输入） -/

theorem P00_sum (pi : Fin 4 → ℝ) (hsum : piR pi + piY pi = 1) (i k : Fin 4) :
    ∑ j : Fin 4, P0 pi i j * P0 pi j k = P0 pi i k := by
  rw [show (∑ j : Fin 4, P0 pi i j * P0 pi j k) = ∑ j : Fin 4, pi j * pi k from
    Finset.sum_congr rfl (fun j _ => by ring)]
  rw [← Finset.sum_mul, sum_pi pi hsum, one_mul]

theorem P01_sum (pi : Fin 4 → ℝ) (hsum : piR pi + piY pi = 1)
    (hR : piR pi ≠ 0) (hY : piY pi ≠ 0) (i k : Fin 4) :
    ∑ j : Fin 4, P0 pi i j * P1 pi j k = 0 := by
  rw [show (∑ j : Fin 4, P0 pi i j * P1 pi j k)
      = ∑ j : Fin 4, (pi j * Bmat pi j k - pi j * pi k) from
    Finset.sum_congr rfl (fun j _ => by ring)]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_pi_mul_Bmat pi hR hY k, sum_pi pi hsum]
  ring

theorem P02_sum (pi : Fin 4 → ℝ) (_hsum : piR pi + piY pi = 1)
    (hR : piR pi ≠ 0) (hY : piY pi ≠ 0) (i k : Fin 4) :
    ∑ j : Fin 4, P0 pi i j * P2 pi j k = 0 := by
  rw [show (∑ j : Fin 4, P0 pi i j * P2 pi j k)
      = ∑ j : Fin 4, (pi j * (if j = k then (1 : ℝ) else 0) - pi j * Bmat pi j k) from
    Finset.sum_congr rfl (fun j _ => by ring)]
  rw [Finset.sum_sub_distrib, sum_mul_ite k 1 (fun j => pi j),
    sum_pi_mul_Bmat pi hR hY k]
  ring

theorem P10_sum (pi : Fin 4 → ℝ) (hsum : piR pi + piY pi = 1)
    (hR : piR pi ≠ 0) (hY : piY pi ≠ 0) (i k : Fin 4) :
    ∑ j : Fin 4, P1 pi i j * P0 pi j k = 0 := by
  rw [show (∑ j : Fin 4, P1 pi i j * P0 pi j k)
      = ∑ j : Fin 4, (Bmat pi i j * pi k - pi j * pi k) from
    Finset.sum_congr rfl (fun j _ => by ring)]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, Bmat_row_sum pi hR hY i,
    sum_pi pi hsum]
  ring

theorem P11_sum (pi : Fin 4 → ℝ) (hsum : piR pi + piY pi = 1)
    (hR : piR pi ≠ 0) (hY : piY pi ≠ 0) (i k : Fin 4) :
    ∑ j : Fin 4, P1 pi i j * P1 pi j k = P1 pi i k := by
  rw [show (∑ j : Fin 4, P1 pi i j * P1 pi j k)
      = ∑ j : Fin 4, (Bmat pi i j * Bmat pi j k - Bmat pi i j * pi k
          - pi j * Bmat pi j k + pi j * pi k) from
    Finset.sum_congr rfl (fun j _ => by ring)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ← Finset.sum_mul, sum_pi_mul_Bmat pi hR hY k,
    Bmat_mul pi hR hY i k, Bmat_row_sum pi hR hY i, sum_pi pi hsum]
  ring

theorem P12_sum (pi : Fin 4 → ℝ) (_hsum : piR pi + piY pi = 1)
    (hR : piR pi ≠ 0) (hY : piY pi ≠ 0) (i k : Fin 4) :
    ∑ j : Fin 4, P1 pi i j * P2 pi j k = 0 := by
  rw [show (∑ j : Fin 4, P1 pi i j * P2 pi j k)
      = ∑ j : Fin 4, (Bmat pi i j * (if j = k then (1 : ℝ) else 0)
          - Bmat pi i j * Bmat pi j k - pi j * (if j = k then (1 : ℝ) else 0)
          + pi j * Bmat pi j k) from
    Finset.sum_congr rfl (fun j _ => by ring)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_mul_ite k 1 (fun j => Bmat pi i j), sum_mul_ite k 1 (fun j => pi j),
    Bmat_mul pi hR hY i k, sum_pi_mul_Bmat pi hR hY k]
  ring

theorem P20_sum (pi : Fin 4 → ℝ) (_hsum : piR pi + piY pi = 1)
    (hR : piR pi ≠ 0) (hY : piY pi ≠ 0) (i k : Fin 4) :
    ∑ j : Fin 4, P2 pi i j * P0 pi j k = 0 := by
  rw [show (∑ j : Fin 4, P2 pi i j * P0 pi j k)
      = ∑ j : Fin 4, ((if i = j then (1 : ℝ) else 0) * pi k - Bmat pi i j * pi k) from
    Finset.sum_congr rfl (fun j _ => by ring)]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, sum_ite_self i 1,
    Bmat_row_sum pi hR hY i]
  ring

theorem P21_sum (pi : Fin 4 → ℝ) (_hsum : piR pi + piY pi = 1)
    (hR : piR pi ≠ 0) (hY : piY pi ≠ 0) (i k : Fin 4) :
    ∑ j : Fin 4, P2 pi i j * P1 pi j k = 0 := by
  rw [show (∑ j : Fin 4, P2 pi i j * P1 pi j k)
      = ∑ j : Fin 4, ((if i = j then (1 : ℝ) else 0) * Bmat pi j k
          - (if i = j then (1 : ℝ) else 0) * pi k - Bmat pi i j * Bmat pi j k
          + Bmat pi i j * pi k) from
    Finset.sum_congr rfl (fun j _ => by ring)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_ite_mul i 1 (fun j => Bmat pi j k), ← Finset.sum_mul, ← Finset.sum_mul,
    sum_ite_self i 1, Bmat_mul pi hR hY i k, Bmat_row_sum pi hR hY i]
  ring

theorem P22_sum (pi : Fin 4 → ℝ) (hR : piR pi ≠ 0) (hY : piY pi ≠ 0) (i k : Fin 4) :
    ∑ j : Fin 4, P2 pi i j * P2 pi j k = P2 pi i k := by
  rw [show (∑ j : Fin 4, P2 pi i j * P2 pi j k)
      = ∑ j : Fin 4, ((if i = j then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)
          - (if i = j then (1 : ℝ) else 0) * Bmat pi j k
          - Bmat pi i j * (if j = k then (1 : ℝ) else 0)
          + Bmat pi i j * Bmat pi j k) from
    Finset.sum_congr rfl (fun j _ => by ring)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_ite_mul i 1 (fun j => if j = k then (1 : ℝ) else 0),
    sum_ite_mul i 1 (fun j => Bmat pi j k), sum_mul_ite k 1 (fun j => Bmat pi i j),
    Bmat_mul pi hR hY i k]
  ring

/-! ## §3. 三条正当性证书 -/

/-- ★ **行和为 1**（随机性之一）：`∑_j K(t)_ij = 1`。 -/
theorem Kmat_row_sum (pi : Fin 4 → ℝ) (hsum : piR pi + piY pi = 1)
    (hR : piR pi ≠ 0) (hY : piY pi ≠ 0) (kap lam t : ℝ) (i : Fin 4) :
    ∑ j : Fin 4, Kmat pi kap lam t i j = 1 := by
  rw [show (∑ j : Fin 4, Kmat pi kap lam t i j)
      = ∑ j : Fin 4, (P0 pi i j + sm lam t * P1 pi i j + rm lam kap t * P2 pi i j) from
    Finset.sum_congr rfl (fun j _ => rfl)]
  rw [show (∑ j : Fin 4, (P0 pi i j + sm lam t * P1 pi i j + rm lam kap t * P2 pi i j))
      = (∑ j : Fin 4, P0 pi i j) + sm lam t * (∑ j : Fin 4, P1 pi i j)
        + rm lam kap t * (∑ j : Fin 4, P2 pi i j) from by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]]
  rw [show (∑ j : Fin 4, P0 pi i j) = 1 from sum_pi pi hsum]
  rw [show (∑ j : Fin 4, P1 pi i j) = 0 from by
    rw [show (∑ j : Fin 4, P1 pi i j) = (∑ j : Fin 4, Bmat pi i j) - ∑ j : Fin 4, pi j from
      by rw [Finset.sum_sub_distrib]]
    rw [Bmat_row_sum pi hR hY i, sum_pi pi hsum]
    ring]
  rw [show (∑ j : Fin 4, P2 pi i j) = 0 from by
    rw [show (∑ j : Fin 4, P2 pi i j)
        = (∑ j : Fin 4, (if i = j then (1 : ℝ) else 0)) - ∑ j : Fin 4, Bmat pi i j from
      by rw [Finset.sum_sub_distrib]]
    rw [sum_ite_self i 1, Bmat_row_sum pi hR hY i]
    ring]
  ring

/-- ★★ **半群律（Chapman–Kolmogorov）**：`K(s+t) = K(s)·K(t)`。 -/
theorem Kmat_semigroup (pi : Fin 4 → ℝ) (hsum : piR pi + piY pi = 1)
    (hR : piR pi ≠ 0) (hY : piY pi ≠ 0) (kap lam s t : ℝ) (i k : Fin 4) :
    Kmat pi kap lam (s + t) i k
      = ∑ j : Fin 4, Kmat pi kap lam s i j * Kmat pi kap lam t j k := by
  have h00 := P00_sum pi hsum i k
  have h01 := P01_sum pi hsum hR hY i k
  have h02 := P02_sum pi hsum hR hY i k
  have h10 := P10_sum pi hsum hR hY i k
  have h11 := P11_sum pi hsum hR hY i k
  have h12 := P12_sum pi hsum hR hY i k
  have h20 := P20_sum pi hsum hR hY i k
  have h21 := P21_sum pi hsum hR hY i k
  have h22 := P22_sum pi hR hY i k
  rw [show (∑ j : Fin 4, Kmat pi kap lam s i j * Kmat pi kap lam t j k)
      = ∑ j : Fin 4, ( P0 pi i j * P0 pi j k
        + sm lam t * (P0 pi i j * P1 pi j k)
        + rm lam kap t * (P0 pi i j * P2 pi j k)
        + sm lam s * (P1 pi i j * P0 pi j k)
        + (sm lam s * sm lam t) * (P1 pi i j * P1 pi j k)
        + (sm lam s * rm lam kap t) * (P1 pi i j * P2 pi j k)
        + rm lam kap s * (P2 pi i j * P0 pi j k)
        + (rm lam kap s * sm lam t) * (P2 pi i j * P1 pi j k)
        + (rm lam kap s * rm lam kap t) * (P2 pi i j * P2 pi j k)) from
    Finset.sum_congr rfl (fun j _ => by unfold Kmat; ring)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h00, h01, h02, h10, h11, h12, h20, h21, h22]
  simp only [mul_zero, add_zero]
  rw [Kmat, sm_add, rm_add]
  try ring

/-- `d/dt e^{−λt}|_{t=0} = −λ`。 -/
theorem hasDerivAt_sm (lam : ℝ) : HasDerivAt (fun t : ℝ => sm lam t) (-lam) 0 := by
  have h : HasDerivAt (fun t : ℝ => -(lam * t)) (-lam) 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).const_mul (-lam)
  simpa [sm] using h.exp

/-- `d/dt e^{−λ(1+κ)t}|_{t=0} = −λ(1+κ)`。 -/
theorem hasDerivAt_rm (lam kap : ℝ) :
    HasDerivAt (fun t : ℝ => rm lam kap t) (-(lam * (1 + kap))) 0 := by
  have h : HasDerivAt (fun t : ℝ => -(lam * (1 + kap) * t)) (-(lam * (1 + kap))) 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).const_mul (-(lam * (1 + kap)))
  simpa [rm] using h.exp

/-- ★★ **生成元相容**：`d/dt K(t)_ij |_{t=0} = Q_ij`。 -/
theorem Kmat_hasDerivAt (pi : Fin 4 → ℝ) (kap lam : ℝ) (i j : Fin 4) :
    HasDerivAt (fun t : ℝ => Kmat pi kap lam t i j) (Qmat pi kap lam i j) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => (Bmat pi i j - pi j) * sm lam t)
      ((Bmat pi i j - pi j) * -lam) 0 := (hasDerivAt_sm lam).const_mul _
  have h2 : HasDerivAt
      (fun t : ℝ => ((if i = j then (1 : ℝ) else 0) - Bmat pi i j) * rm lam kap t)
      (((if i = j then (1 : ℝ) else 0) - Bmat pi i j) * -(lam * (1 + kap))) 0 :=
    (hasDerivAt_rm lam kap).const_mul _
  have h := (h1.add_const (pi j)).add h2
  have hfun : (fun t : ℝ => Kmat pi kap lam t i j)
      = fun t : ℝ => ((Bmat pi i j - pi j) * sm lam t + pi j)
          + (((if i = j then (1 : ℝ) else 0) - Bmat pi i j) * rm lam kap t) := by
    funext t
    simp only [Kmat]
    ring
  rw [hfun, Qmat]
  convert h using 1
  ring

/-! ## §4. `Q` 的性质（附录 1592–1601） -/

/-- `Q` 的非对角元素：`Q_ij = λ(π_j + κ·B_ij) = λπ_j(1 + κ·1[同组]/p_{cl j})`。 -/
theorem Qmat_off (pi : Fin 4 → ℝ) {kap lam : ℝ} {i j : Fin 4} (hij : i ≠ j) :
    Qmat pi kap lam i j = lam * (pi j + kap * Bmat pi i j) := by
  rw [Qmat, ite_eq_right hij]; ring

/-- `Q` 的对角元素 = 负行和：`Q_ii = −λ(1 − π_i + κ(1 − B_ii))`。 -/
theorem Qmat_diag (pi : Fin 4 → ℝ) (kap lam : ℝ) (i : Fin 4) :
    Qmat pi kap lam i i = -lam * (1 - pi i + kap * (1 - Bmat pi i i)) := by
  rw [Qmat, ite_eq_left rfl]; ring

/-- `Q = −λM`。 -/
theorem Qmat_eq_neg_lam_M (pi : Fin 4 → ℝ) (kap lam : ℝ) (i j : Fin 4) :
    Qmat pi kap lam i j = -lam * Mmat pi kap i j := by
  rw [Qmat, Mmat]; ring

/-- `Q` 行和为 0。 -/
theorem Qmat_row_sum (pi : Fin 4 → ℝ) (hsum : piR pi + piY pi = 1)
    (hR : piR pi ≠ 0) (hY : piY pi ≠ 0) (kap lam : ℝ) (i : Fin 4) :
    ∑ j : Fin 4, Qmat pi kap lam i j = 0 := by
  rw [show (∑ j : Fin 4, Qmat pi kap lam i j)
      = ∑ j : Fin 4, ((-lam) * (Bmat pi i j - pi j)
        + (-(lam * (1 + kap))) * ((if i = j then (1 : ℝ) else 0) - Bmat pi i j)) from
    Finset.sum_congr rfl (fun j _ => by rw [Qmat]; ring)]
  rw [show (∑ j : Fin 4, ((-lam) * (Bmat pi i j - pi j)
        + (-(lam * (1 + kap))) * ((if i = j then (1 : ℝ) else 0) - Bmat pi i j)))
      = (-lam) * (∑ j : Fin 4, (Bmat pi i j - pi j))
        + (-(lam * (1 + kap))) *
          (∑ j : Fin 4, ((if i = j then (1 : ℝ) else 0) - Bmat pi i j)) from by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]]
  rw [show (∑ j : Fin 4, (Bmat pi i j - pi j)) = 0 from by
    rw [show (∑ j : Fin 4, (Bmat pi i j - pi j))
        = (∑ j : Fin 4, Bmat pi i j) - ∑ j : Fin 4, pi j from
      by rw [Finset.sum_sub_distrib]]
    rw [Bmat_row_sum pi hR hY i, sum_pi pi hsum]; ring,
    show (∑ j : Fin 4, ((if i = j then (1 : ℝ) else 0) - Bmat pi i j)) = 0 from by
      rw [show (∑ j : Fin 4, ((if i = j then (1 : ℝ) else 0) - Bmat pi i j))
          = (∑ j : Fin 4, (if i = j then (1 : ℝ) else 0)) - ∑ j : Fin 4, Bmat pi i j from
        by rw [Finset.sum_sub_distrib]]
      rw [sum_ite_self i 1, Bmat_row_sum pi hR hY i]; ring]
  ring

/-- `πQ = 0`（平稳性）。 -/
theorem Qmat_pi_mul (pi : Fin 4 → ℝ) (hsum : piR pi + piY pi = 1)
    (hR : piR pi ≠ 0) (hY : piY pi ≠ 0) (kap lam : ℝ) (j : Fin 4) :
    ∑ i : Fin 4, pi i * Qmat pi kap lam i j = 0 := by
  rw [show (∑ i : Fin 4, pi i * Qmat pi kap lam i j)
      = ∑ i : Fin 4, ((lam * kap) * (pi i * Bmat pi i j) + (lam * pi j) * pi i
        - (lam * (1 + kap)) * (pi i * (if i = j then (1 : ℝ) else 0))) from
    Finset.sum_congr rfl (fun i _ => by rw [Qmat]; ring)]
  rw [show (∑ i : Fin 4, ((lam * kap) * (pi i * Bmat pi i j) + (lam * pi j) * pi i
        - (lam * (1 + kap)) * (pi i * (if i = j then (1 : ℝ) else 0))))
      = (lam * kap) * (∑ i : Fin 4, pi i * Bmat pi i j)
        + (lam * pi j) * (∑ i : Fin 4, pi i)
        - (lam * (1 + kap)) *
          (∑ i : Fin 4, pi i * (if i = j then (1 : ℝ) else 0)) from by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]]
  rw [sum_pi_mul_Bmat pi hR hY j, sum_pi pi hsum, sum_mul_ite j 1 (fun i => pi i)]
  ring

/-- **细致平衡**：`π_i Q_ij = π_j Q_ji`。 -/
theorem Qmat_detailed_balance (pi : Fin 4 → ℝ) (kap lam : ℝ) (i j : Fin 4) :
    pi i * Qmat pi kap lam i j = pi j * Qmat pi kap lam j i := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  · rw [Qmat_off pi hij, Qmat_off pi (Ne.symm hij)]
    linear_combination (lam * kap) * pi_mul_Bmat_comm pi i j

/-! ## §5. 谱：`M = P1 + (1+κ)P2` 与 `M(M−I)(M−(1+κ)I) = 0` -/

/-- `M = P1 + (1+κ)P2`（于是 `M` 的特征值是 `0, 1, 1+κ`）。 -/
theorem Mmat_eq (pi : Fin 4 → ℝ) (kap : ℝ) (i j : Fin 4) :
    Mmat pi kap i j = P1 pi i j + (1 + kap) * P2 pi i j := by
  rw [Mmat]; ring

/-- `M² = P1 + (1+κ)²P2`。 -/
theorem Mmat_sq (pi : Fin 4 → ℝ) (hsum : piR pi + piY pi = 1)
    (hR : piR pi ≠ 0) (hY : piY pi ≠ 0) (kap : ℝ) (i j : Fin 4) :
    ∑ k : Fin 4, Mmat pi kap i k * Mmat pi kap k j
      = P1 pi i j + (1 + kap) ^ 2 * P2 pi i j := by
  have h11 := P11_sum pi hsum hR hY i j
  have h12 := P12_sum pi hsum hR hY i j
  have h21 := P21_sum pi hsum hR hY i j
  have h22 := P22_sum pi hR hY i j
  rw [show (∑ k : Fin 4, Mmat pi kap i k * Mmat pi kap k j)
      = ∑ k : Fin 4, (P1 pi i k * P1 pi k j + (1 + kap) * (P1 pi i k * P2 pi k j)
        + (1 + kap) * (P2 pi i k * P1 pi k j)
        + (1 + kap) * (1 + kap) * (P2 pi i k * P2 pi k j)) from
    Finset.sum_congr rfl (fun k _ => by rw [Mmat_eq pi kap i k, Mmat_eq pi kap k j]; ring)]
  simp only [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [h11, h12, h21, h22]
  ring

/-- `M³ = P1 + (1+κ)³P2`。 -/
theorem Mmat_cube (pi : Fin 4 → ℝ) (hsum : piR pi + piY pi = 1)
    (hR : piR pi ≠ 0) (hY : piY pi ≠ 0) (kap : ℝ) (i j : Fin 4) :
    ∑ k : Fin 4, ∑ l : Fin 4, Mmat pi kap i k * Mmat pi kap k l * Mmat pi kap l j
      = P1 pi i j + (1 + kap) ^ 3 * P2 pi i j := by
  have h2 : ∀ k : Fin 4, ∑ l : Fin 4, Mmat pi kap k l * Mmat pi kap l j
      = P1 pi k j + (1 + kap) ^ 2 * P2 pi k j := fun k => Mmat_sq pi hsum hR hY kap k j
  have h11 := P11_sum pi hsum hR hY i j
  have h12 := P12_sum pi hsum hR hY i j
  have h21 := P21_sum pi hsum hR hY i j
  have h22 := P22_sum pi hR hY i j
  rw [show (∑ k : Fin 4, ∑ l : Fin 4, Mmat pi kap i k * Mmat pi kap k l * Mmat pi kap l j)
      = ∑ k : Fin 4, (P1 pi i k * P1 pi k j + (1 + kap) ^ 2 * (P1 pi i k * P2 pi k j)
        + (1 + kap) * (P2 pi i k * P1 pi k j)
        + (1 + kap) * (1 + kap) ^ 2 * (P2 pi i k * P2 pi k j)) from by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show (∑ l : Fin 4, Mmat pi kap i k * Mmat pi kap k l * Mmat pi kap l j)
        = ∑ l : Fin 4, Mmat pi kap i k * (Mmat pi kap k l * Mmat pi kap l j) from
      Finset.sum_congr rfl (fun l _ => by ring)]
    rw [← Finset.mul_sum]
    rw [h2 k, Mmat_eq pi kap i k]
    ring]
  simp only [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [h11, h12, h21, h22]
  ring

/-- ★★ **特征多项式**：`M(M−I)(M−(1+κ)I) = 0`，即 `M` 的谱是 `{0, 1, 1+κ}`；
于是 `Q = −λM` 的谱是 `{0, −λ, −λ(1+κ), −λ(1+κ)}`。 -/
theorem Mmat_cubic (pi : Fin 4 → ℝ) (hsum : piR pi + piY pi = 1)
    (hR : piR pi ≠ 0) (hY : piY pi ≠ 0) (kap : ℝ) (i j : Fin 4) :
    (∑ k : Fin 4, ∑ l : Fin 4, Mmat pi kap i k * Mmat pi kap k l * Mmat pi kap l j)
      - (2 + kap) * (∑ k : Fin 4, Mmat pi kap i k * Mmat pi kap k j)
      + (1 + kap) * Mmat pi kap i j = 0 := by
  have h1 := Mmat_eq pi kap i j
  have h2 := Mmat_sq pi hsum hR hY kap i j
  have h3 := Mmat_cube pi hsum hR hY kap i j
  rw [h1, h2, h3]
  ring

/-! ## §6. 缺口清单（如实记录，供后续轮次接续）

以下部分**未**在本文件完成（不用 `sorry` 占位）：

1. **`patternProb`（四叶模式概率）**：`P(σ) = Σ_{u,v} π_u K(l_a)[u,σ_a]·K(l_b)[u,σ_b]
   ·K(l_x)[u,v]·K(l_c)[v,σ_c]·K(l_d)[v,σ_d]`（附录 1503 行）。需要把
   `∑ σ : Fin 4 → Fin 4` 化成四重和（借 `CASTERLM1.sum_pi_four` 的写法）。
2. **`wF84`（§0.3 的 32 个非零模式表）** 与 `hRf`/`hYf` 定义（用 `Fin 4` 字面模式匹配）。
3. **聚合引理**：`Agg_c(u;t₁,t₂) = 0`（`u ∉ c`）与
   `Σ_{u∈c} π_u Agg_c(u;t₁,t₂) = p_c·(p_c²−q_c)·rm lam kap (t₁+t₂)`。这两条把
   `E[w(ab|cd)]` 坍塌成 `(1/2)(1−e^{−λl_x})·p_Rp_Y(p_R²−q_R)(p_Y²−q_Y)·e^{−λ(1+κ)L_T}`
   —— 正是附录印的常数。
4. **`E[w(ac|bd)] = E[w(ad|bc)]`**（两条错拓扑得分相等）。
5. **主定理 `E_wF84_ab_sub_ac`**。
6. **与抽象引擎 `CASTERBridge.PropAData` / `CASTERTopo.topo_statisticallyConsistent`
   的对接**（`f84PropAData`，需要「重指标与基因树形状无关」的引理）。

缺口 3–5 的**全部数值**已由独立 Python 脚本 `_t39/f84_final_check.py` 验证到 1e-13：
`(E_ab − E_ac)/C = 1.0000000000`（8 组参数，含 `κ = 0`），`E_ac = E_ad` 精确成立。 -/

end CASTERF84

end Phylo
