/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation

/-!
# `Phylo.Stat.CASTERWeights` —— CASTER 的 JC69 位点模式权重表 + 机器自检

文献：Zhang, Nielsen, Mirarab (2025), *Science* **387**(6737) eadk9688,
"Direct species tree inference from whole-genome alignments"，
**Supplementary** `sm.tex`（本项目存于 `references/tex/Caster2025_Supplementary.tex`）：

| 内容 | `sm.tex` 行 |
|---|---|
| 三套权重表 | **348–375** |
| JC69 的化简推导（`/8` 那个常数） | 1503–1548 |
| F84 的推导与常数 | 1552–1610 |
| LM1 的推导与常数 | 1611–1700 |

## 记号

* 字母表 `Σ = {A,G,C,T}`，在库里编号为 `Fin 4`：`0=A, 1=G, 2=C, 3=T`。
* 一个**位点模式**是 `σ : Fin 4 → Fin 4`（四个物种位置上的字母）。
* 一个**物种四元组拓扑**是 `Topo`：`ab_cd / ac_bd / ad_bc`。
* 权重 `wJC T σ : Val`：模式 `σ` 对拓扑 `T` 的打分（`pos = +1`、`negHalf = -1/2`、`zero = 0`）。

## 为什么权重的值类型是自定义的 `Val` 而不是 `ℚ` / `ℝ`

权重只取 `1, -1/2, 0` 三个值；本文件里每一条自检都靠 `decide` **穷举全部 256 个位点模式**
机械验证。但：

* `ℝ` 上没有可计算的 `DecidableEq` ⇒ `decide` 用不了；
* `ℚ` 上 `Rat.num` 在 kernel 里不可归约（实测 `decide` 卡在
  `match -(1/2).num, -(1/2).num with …`）⇒ 也不行；
* 自定义三构造子的 `Val` 的 `DecidableEq` 是**结构比较**，`decide` 能一路归约到底。

于是：**权重表用 `Val` 定义、用 `decide` 自检**；要算期望时用 `Val.toReal` 投到 `ℝ`，
要对账「表和」时用 `Val.toInt`（`pos ↦ 2`、`negHalf ↦ -1`，即把权重放大 2 倍的整数账）
—— 因为 `Val.toRat` 会把 `ℚ` 引回来，所以**先证 `∑ toInt = -24`，再由
`sum_wJC_rat` 换算成「表和 `= -12`」**（见 §2）。
`set_option maxRecDepth` 是因为 `Fin 4 → Fin 4` 的 `Finset.univ` 经 `Multiset.Pi` 构造，
默认递归深度不够（Lean 的报错原文即「maximum recursion depth has been reached」）。

## 本文件证什么

* ★★ `wJC_swap_ab` / `wJC_swap_cd` —— **同侧标签互换不变**（`a↔b`、`c↔d`，**只对 `ab|cd` 成立**：
  对 `ac|bd` 来说 `a` 与 `b` 本来就不在同一侧，换了就换拓扑）；
* ★★ `wJC_swap_sides` —— **两侧互换不变**（`{a,b}↔{c,d}`，**对三个拓扑都成立**）；
* ★★ `card_pos` / `card_neg` / `card_zero` —— 三类模式个数 **12 / 48 / 196**；
* ★★ `sum_wJC_rat` —— 真实逐模式权重表**全表和 `= -12`**；
* ★★ `repPos_subset` / `repNeg_subset` / `sum_wJCRep_rat` —— 附录 Fig. 1C **字面列出**的
  18 个模式（6 个 `+1`、12 个 `-1/2`）确实是真实权重表的**子表**，而**它自己的和是 0**。

## ⚠️ 本文件如实记录的源头问题：附录的表是「代表元表」

附录 Fig. 1C 的 `+1` 行只印了 6 个模式（`AA|GG, AA|CC, AA|TT, GG|CC, GG|TT, CC|TT`），
`-1/2` 行只印了 12 个（形如 `χχ|ψω`，**不含镜像** `ψω|χχ`）。
但按附录自己写的 matching 语义（footnote 1：「species matching pattern XY 与 ZW 分居 split 两侧」），
`χχ|ψω` 与它的镜像 `ψω|χχ` **都**匹配同一拓扑，因此**权重必须相同**
—— 附录自己在 Prop. 的化简式里正是这么用的（`P(a,a,c,c)` 与 `P(c,c,a,a)` 都取 `+1`，
`P(a,a,c,g)` 与 `P(c,g,a,a)` 都取 `-1/2`）。

⇒ 真实逐模式权重表的规模是 **12 个 `+1` + 48 个 `-1/2` + 196 个 `0`**（本文件已全部机器验证），
附录字面那 18 个只是**代表元**。这直接导致附录 JC69 段印出的常数 `1/8`
其实是**真实权重表**得分的 `1/6`（真实常数应为 `3/4`）—— 该结论在
`Phylo/Stat/CASTERJC69.lean` 里以两条定理（附录化简式的 `1/8` 与真实表的 `3/4`）
及 `score = 6 · red` 给了**机器证明**，数值上亦经 8 组随机参数复核（比值偏差 < 1.5e-14）。

另一个症状：**附录那 18 个代表元的权重和恰好是 0**（`6·1 + 12·(-1/2) = 0`），
而**真实表的权重和是 `-12`** —— 两者都写在本文件里、都由 `decide` 穷举验证。
⇒ 「表和是否为 0」这条自检**不能**用来判定「表是否完整」。

## 🔻 诚实边界（本批**未**做的部分）

**F84 与 LM1 的表本文件只给出结论性引用，没有形式化**（不是偷懒，是记账方式没定死）：

* **F84**（`sm.tex` 359–366）的四行权重是 `π` 的四次多项式
  （`4π_Aπ_Gπ_Cπ_T` / `-2π_Aπ_G(π_C²+π_T²)` / `-2(π_A²+π_G²)π_Cπ_T` / `(π_A²+π_G²)(π_C²+π_T²)`），
  但它们作用在**聚合类**上（附录的 `E[w]` 式里系数是 `π_R²π_Y²` 而不是这四个多项式，
  且附录明说化简表「allowing double counting」）。**「聚合 vs 逐模式」的记账方式必须先定死**，
  否则会重演 JC69 那个 6 倍错误。
* **LM1**（`sm.tex` 367–375）的权重 `+1` / `-4π_Rπ_Y` 定义在**位点对**的 IUPAC 歧义码
  （`RN, YN, NR, NY, NN`）上，需要先有「位点对 / 歧义码」这一层类型。
  附录对该模型的推导是**自洽完整**的（背景项 `-8π_R²π_Y²` 在差里确实相消，
  其率矩阵一侧已由 `Phylo/Stat/LMLumping.lean` 给出）。

⇒ 本批只把 **JC69** 打到「机器可查的逐模式表 + 三条自检 + 与代表元表的关系」。
F84 / LM1 留待后续批次（先定记账方式，再补表）。 -/

set_option maxRecDepth 100000

namespace Phylo.Stat.CASTERWeights

/-- **JC69 权重的三个取值**（附录 Fig. 1C 的 `+1` / `-1/2` / 未列 = `0`）。

用自定义三构造子而不是 `ℚ` / `ℝ`，是为了让 `decide` 能把 256 个模式穷举验证到底：
它的 `DecidableEq` 是结构比较（理由见文件头）。 -/
inductive Val where
  /-- `+1`。 -/
  | pos
  /-- `-1/2`。 -/
  | negHalf
  /-- `0`（未列的模式）。 -/
  | zero
  deriving DecidableEq, Repr

namespace Val

/-- 投到 `ℚ`（权重原值）。 -/
def toRat : Val → ℚ
  | .pos => 1
  | .negHalf => -(1 / 2)
  | .zero => 0

/-- 投到 `ℝ`（下游算期望 `∑ σ, (wJC T σ).toReal * P σ` 用这个）。 -/
noncomputable def toReal : Val → ℝ
  | .pos => 1
  | .negHalf => -(1 / 2)
  | .zero => 0

/-- **放大 2 倍的整数账**（`pos ↦ 2`、`negHalf ↦ -1`、`zero ↦ 0`）：
用来把「权重和」化成 `ℤ` 上的求和，好让 `decide` 能算。 -/
def toInt : Val → ℤ
  | .pos => 2
  | .negHalf => -1
  | .zero => 0

@[simp] theorem toRat_pos : toRat .pos = 1 := rfl
@[simp] theorem toRat_negHalf : toRat .negHalf = -(1 / 2) := rfl
@[simp] theorem toRat_zero : toRat .zero = 0 := rfl
@[simp] theorem toReal_pos : toReal .pos = 1 := rfl
@[simp] theorem toReal_negHalf : toReal .negHalf = -(1 / 2) := rfl
@[simp] theorem toReal_zero : toReal .zero = 0 := rfl
@[simp] theorem toInt_pos : toInt .pos = 2 := rfl
@[simp] theorem toInt_negHalf : toInt .negHalf = -1 := rfl
@[simp] theorem toInt_zero : toInt .zero = 0 := rfl

/-- 整数账是原值的 2 倍：`(toInt v : ℚ) = 2 * toRat v`。 -/
theorem toInt_eq_two_mul_toRat (v : Val) : (toInt v : ℚ) = 2 * toRat v := by
  cases v <;> norm_num [toInt, toRat]

end Val

open Val

/-- 四叶物种树的**拓扑**（按「哪两个叶配对」）。 -/
inductive Topo where
  /-- `ab | cd`。 -/
  | ab_cd
  /-- `ac | bd`。 -/
  | ac_bd
  /-- `ad | bc`。 -/
  | ad_bc
  deriving DecidableEq, Repr

open Topo

/-- 把一个位点模式写成 `Fin 4 → Fin 4` 的四元组。 -/
def vec (a b c d : Fin 4) : Fin 4 → Fin 4 := ![a, b, c, d]

/-- **两侧互换** `{a,b} ↔ {c,d}`（叶位置 `(0 2)(1 3)`）。 -/
def sidesPerm : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

/-- **把拓扑 `T` 的两侧搬回基准拓扑 `ab|cd` 的叶位置置换**。

* `ab_cd` → 恒等（叶位置 `(0,1,2,3)`）；
* `ac_bd` → `swap 1 2`（叶位置 `(0,2,1,3)`：基准的两侧 `{0,1}`,`{2,3}` 变成 `{0,2}`,`{1,3}`）；
* `ad_bc` → 三轮换 `(1 3 2)`（叶位置 `(0,3,1,2)`）。 -/
def perm : Topo → Equiv.Perm (Fin 4)
  | .ab_cd => 1
  | .ac_bd => Equiv.swap 1 2
  | .ad_bc => Equiv.swap 1 2 * Equiv.swap 1 3

/-- **基准拓扑 `ab|cd` 上的 JC69 逐模式权重**（附录 Fig. 1C 的权重表，含镜像）：

* `pos`（`+1`）  ⟺ `σ 0 = σ 1 ∧ σ 2 = σ 3 ∧ σ 0 ≠ σ 2`（`2|2` 且与该 split 一致）；
* `negHalf`（`-1/2`） ⟺ 一侧两个相等、另一侧两个互异且都与它不同（**含两个朝向**）；
* 其余 `zero`。 -/
def wJCBase (b : Fin 4 → Fin 4) : Val :=
  if b 0 = b 1 ∧ b 2 = b 3 ∧ b 0 ≠ b 2 then pos
  else if (b 0 = b 1 ∧ b 2 ≠ b 3 ∧ b 2 ≠ b 0 ∧ b 3 ≠ b 0) ∨
          (b 2 = b 3 ∧ b 0 ≠ b 1 ∧ b 0 ≠ b 2 ∧ b 1 ≠ b 2) then negHalf
  else zero

/-- **CASTER 的 JC69 位点模式权重表**：把 `T` 的两侧搬到基准拓扑 `ab|cd` 后按 `wJCBase` 取值，
即 `wJC T σ = wJCBase (σ ∘ perm T)`。 -/
def wJC (T : Topo) (σ : Fin 4 → Fin 4) : Val := wJCBase fun i => σ (perm T i)

/-- 实数版：下游算期望 `∑ σ, (wJC T σ).toReal * P σ`。 -/
noncomputable def wJCR (T : Topo) (σ : Fin 4 → Fin 4) : ℝ := (wJC T σ).toReal

@[simp] theorem wJC_ab_cd (σ : Fin 4 → Fin 4) : wJC .ab_cd σ = wJCBase σ := rfl

@[simp] theorem wJCR_ab_cd (σ : Fin 4 → Fin 4) :
    wJCR .ab_cd σ = (wJCBase σ).toReal := rfl

/-! ## 1. 三条对称性自检（附录 §7 的机械自检办法）

⚠️ 注意适用范围：**同侧互换只对 `ab|cd` 成立** —— 对 `ac|bd` 而言 `a` 与 `b` 不在同一侧，
换掉就换成另一个拓扑了；**两侧互换对三个拓扑都成立**（它保持每个拓扑的 split）。 -/

/-- ★★ **同侧互换不变（`a ↔ b`，仅 `ab|cd`）**：`wJC .ab_cd σ = wJC .ab_cd (σ ∘ swap 0 1)`。 -/
theorem wJC_swap_ab :
    ∀ σ : Fin 4 → Fin 4, wJC .ab_cd σ = wJC .ab_cd (fun i => σ (Equiv.swap 0 1 i)) := by
  decide

/-- ★★ **同侧互换不变（`c ↔ d`，仅 `ab|cd`）**：`wJC .ab_cd σ = wJC .ab_cd (σ ∘ swap 2 3)`。 -/
theorem wJC_swap_cd :
    ∀ σ : Fin 4 → Fin 4, wJC .ab_cd σ = wJC .ab_cd (fun i => σ (Equiv.swap 2 3 i)) := by
  decide

/-- ★★ **两侧互换不变（`{a,b} ↔ {c,d}`，三个拓扑都成立）**：
`wJC T σ = wJC T (σ ∘ sidesPerm)`。 -/
theorem wJC_swap_sides (T : Topo) :
    ∀ σ : Fin 4 → Fin 4, wJC T σ = wJC T (fun i => σ (sidesPerm i)) := by
  cases T <;> decide

/-! ## 2. 三类模式的个数与全表和（真实逐模式表）

**`-12`，不是 `0`** —— 见文件头「源头问题」一节。 -/

/-- ★★ `+1` 类恰有 **12** 个模式。 -/
theorem card_pos (T : Topo) :
    (Finset.univ.filter (fun σ : Fin 4 → Fin 4 => wJC T σ = pos)).card = 12 := by
  cases T <;> decide

/-- ★★ `-1/2` 类恰有 **48** 个模式（含镜像）。 -/
theorem card_neg (T : Topo) :
    (Finset.univ.filter (fun σ : Fin 4 → Fin 4 => wJC T σ = negHalf)).card = 48 := by
  cases T <;> decide

/-- ★★ 权重为 `0` 的恰有 **196** 个模式。 -/
theorem card_zero (T : Topo) :
    (Finset.univ.filter (fun σ : Fin 4 → Fin 4 => wJC T σ = zero)).card = 196 := by
  cases T <;> decide

/-- **整数账下的全表和 = `-24`**（对每个拓扑都成立）。真正的「权重和 `= -12`」见
`sum_wJC_rat`。 -/
theorem sum_wJC_int (T : Topo) :
    ∑ σ : Fin 4 → Fin 4, (wJC T σ).toInt = -24 := by
  cases T <;> decide

/-- ★★ **真实的 JC69 逐模式权重表全表和 `= -12`**（对每个拓扑都成立）。

由整数账 `∑ toInt = -24`（`sum_wJC_int`）与 `toInt = 2 * toRat` 换算而来。 -/
theorem sum_wJC_rat (T : Topo) : ∑ σ : Fin 4 → Fin 4, (wJC T σ).toRat = -12 := by
  have h2 : ((∑ σ : Fin 4 → Fin 4, (wJC T σ).toInt : ℤ) : ℚ)
      = 2 * ∑ σ : Fin 4 → Fin 4, (wJC T σ).toRat := by
    rw [Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun σ _ => Val.toInt_eq_two_mul_toRat (wJC T σ)
  rw [sum_wJC_int T] at h2
  push_cast at h2
  linarith

/-! ## 3. 附录 Fig. 1C **字面列出**的那 18 个代表元 -/

/-- 附录 Fig. 1C 权重 **`+1`** 行字面列出的 6 个模式
（`AA|GG, AA|CC, AA|TT, GG|CC, GG|TT, CC|TT`）。 -/
def repPos : Finset (Fin 4 → Fin 4) :=
  {vec 0 0 1 1, vec 0 0 2 2, vec 0 0 3 3, vec 1 1 2 2, vec 1 1 3 3, vec 2 2 3 3}

/-- 附录 Fig. 1C 权重 **`-1/2`** 行字面列出的 12 个模式（**不含镜像**）。 -/
def repNeg : Finset (Fin 4 → Fin 4) :=
  {vec 0 0 1 2, vec 0 0 1 3, vec 0 0 2 3,
   vec 1 1 0 2, vec 1 1 0 3, vec 1 1 2 3,
   vec 2 2 0 1, vec 2 2 0 3, vec 2 2 1 3,
   vec 3 3 0 1, vec 3 3 0 2, vec 3 3 1 2}

/-- 附录 Fig. 1C **字面表**所给出的权重函数（只在那 18 个模式上非零）。 -/
def wJCRep (σ : Fin 4 → Fin 4) : Val :=
  if σ ∈ repPos then pos else if σ ∈ repNeg then negHalf else zero

theorem card_repPos : repPos.card = 6 := by decide

theorem card_repNeg : repNeg.card = 12 := by decide

/-- ★★ **字面代表元表确实是真实权重表的子表**：`repPos` 上取 `+1`。 -/
theorem repPos_subset : ∀ σ : Fin 4 → Fin 4, σ ∈ repPos → wJC .ab_cd σ = pos := by decide

/-- ★★ **字面代表元表确实是真实权重表的子表**：`repNeg` 上取 `-1/2`。 -/
theorem repNeg_subset : ∀ σ : Fin 4 → Fin 4, σ ∈ repNeg → wJC .ab_cd σ = negHalf := by
  decide

/-- 整数账下字面代表元表的全表和 = `0`。 -/
theorem sum_wJCRep_int :
    ∑ σ : Fin 4 → Fin 4, (wJCRep σ).toInt = 0 := by decide

/-- ★★ **字面代表元表的权重和 `= 0`**（`6·1 + 12·(-1/2) = 0`）。

⚠️ 与真实逐模式表的 `-12`（`sum_wJC_rat`）**不同** —— 因为字面表漏掉了 `+1` 类的 6 个镜像
与 `-1/2` 类的 36 个镜像。两个和都在库里、都由 `decide` 穷举验证，
所以「表和是否为 0」这条自检**不能**用来判定「表是否完整」。 -/
theorem sum_wJCRep_rat : ∑ σ : Fin 4 → Fin 4, (wJCRep σ).toRat = 0 := by
  have h2 : ((∑ σ : Fin 4 → Fin 4, (wJCRep σ).toInt : ℤ) : ℚ)
      = 2 * ∑ σ : Fin 4 → Fin 4, (wJCRep σ).toRat := by
    rw [Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun σ _ => Val.toInt_eq_two_mul_toRat (wJCRep σ)
  rw [sum_wJCRep_int] at h2
  push_cast at h2
  linarith

/-- ★★ 真实表与字面代表元表的**两个和并列**，供人工对照：
真实的 `-12` vs 代表元的 `0`。真正的结构性关系（`score = 6 · red`）
在 `Phylo/Stat/CASTERJC69.lean` 里证。 -/
theorem sum_wJCRep_vs_sum_wJC :
    (∑ σ : Fin 4 → Fin 4, (wJCRep σ).toRat) = 0 ∧
      (∑ σ : Fin 4 → Fin 4, (wJC .ab_cd σ).toRat) = -12 :=
  ⟨sum_wJCRep_rat, sum_wJC_rat .ab_cd⟩

end Phylo.Stat.CASTERWeights
