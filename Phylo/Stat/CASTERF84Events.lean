/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERF84

/-!
# `Phylo.Stat.CASTERF84Events` —— F84 命题 A 的**推导接口**（模式概率 + 侧向事件 + 拓扑配对）

文献：Zhang, Nielsen, Mirarab (2025), *Science* **387**(6737) eadk9688，
附录 `sm.tex` **1556–1562**（F84 的期望权重，对 `(χ,ψ) ∈ R×Y` 的双重求和）。

## ⚠️ 本文件在 `2bc0d88` 之后的**语义更正**（两次独立复核，见 `scripts/f84/`）

旧版把「被评拓扑 `τ` 的**侧**」实现成「把四个叶长重新排列」：`EwF84_ac = Ew(la,lc,lx,lb,ld)`。
那是**错的**。`patt4` 里 `t1,t2` 挂在**同一个**内部结点 `p` 上、`t3,t4` 挂在 `q` 上，
所以重排叶长并没有让「叶 `a` 与叶 `c` 同标」，只是换了一棵树的叶长。后果（数值复核，
`scripts/f84/caster_f84_leancheck.py`）：

* `Ew` 对 `(t1,t2,t3,t4)` **完全对称**，于是 `EwF84 = EwF84_ac = EwF84_ad`，
  命题 A 的符号结构整个塌掉，主公式**按字面为假**（左端恒为 0）；
* 真实闭式 `Ew = 8·π_Aπ_Cπ_Gπ_T·π_Rπ_Y·(1−sm lx)·rm(t₁+t₂+t₃+t₄)`（**未**除 4 口径，
  相对印的常数是 4 倍 —— 与 `CASTER_F84_FINDING.md` 的因子 4 同一件事）。

**正确的语义**：基因树 `G` 的**模式分布**固定（姐妹叶永远是 `(a,b)` 与 `(c,d)`），
被评拓扑 `τ` 只决定**把哪两对叶当成两个侧**来分组。`ac|bd` 的两侧 `{a,c}`、`{b,d}`
横跨 `p,q` 两个结点 —— 这就是 `EwA`/`EwB`（跨结点分组）。三条核实过的恒等式：

```
(D)  Ew  (对角分组)                     = 2·π_Aπ_Cπ_Gπ_T·π_Rπ_Y·(1−sm lx)·rm(l_a l_b l_c l_d)
(XA) EwA (分组 {0,2},{1,3}，即 ac|bd)   = 0
(XB) EwB (分组 {0,3},{1,2}，即 ad|bc)   = 0
```

⇒ 对 F84（**÷4 归一化**，`Ew` 的系数取照印值除以 4）有干净的
`E[w(τ) | G] = C·[τ = topo G]`，`C := 2·π_Aπ_Cπ_Gπ_T·π_Rπ_Y·(1−sm lx)·rm(Σl)`
—— 两个**错**拓扑的期望权重**恰为 0**（`caster_f84_tabtest.py`：1e-12）。

## 🔑 为什么这使形式化变得**纯代数**

把 `sm_t := e^{−λt}`、`rm_t := e^{−λ(1+κ)t}` 当作**自由符号**（取任意值，含负数）后，
(D)/(XA)/(XB) 仍然是恒等式（`scripts/f84/caster_f84_formal.py`：3e-10 / 3e-18 / 1e-18）。
即它们是 `π_j` 与 `sm_t,rm_t` 的**有理函数恒等式** —— 所以推导层**不需要**指数运算律、
不需要 ★★★ `CASTERF84.Kmat_semigroup`，只要把 `Fin 4` 求和展开后 `field_simp; ring`。

## 🔻 诚实边界

* **÷4 归一化**：附录 (1556–1564) 的系数（照印）给出的差是印的常数 `2π_Aπ_Cπ_Gπ_Tπ_Rπ_Y…`
  的 **4 倍**；除以 4 后附录 (1585) 逐字成立。这里取 ÷4 口径，并把该差异记录在
  `CASTER_F84_FINDING.md`（作者已确认常数会另行更正）。
* `Rset = {0,1}`（`0=A`、`1=G`）、`Yset = {2,3}`（`2=C`、`3=T`）；`0..3` 是**状态**下标，
  与叶标签 `a,b,c,d` 无关。 -/

universe u

namespace Phylo.Stat.CASTERF84Events

open Phylo.CASTERF84

/-- `R = {A,G}`（`Fin 4` 记法：`0=A`、`1=G`、`2=C`、`3=T`）。 -/
def Rset : Finset (Fin 4) := {0, 1}

/-- `Y = {C,T}`。 -/
def Yset : Finset (Fin 4) := {2, 3}

/-- **四叶位点模式概率**（基因树 `ab|cd`）：内部结点取平稳分布 `π`，
位置 `1,2`（叶 `a,b`）挂在结点 `p` 上、位置 `3,4`（叶 `c,d`）挂在 `q` 上，中间边 `tx`。

⚠️ 这是**基因树**的模式分布：`t1,t2` 恒为姐妹叶 `(a,b)` 的枝长、`t3,t4` 恒为 `(c,d)` 的枝长。
被评拓扑只影响下面的事件**分组方式**，不影响本函数。 -/
noncomputable def patt4 (pi : Fin 4 → ℝ) (kap lam : ℝ) (t1 t2 tx t3 t4 : ℝ)
    (i j k l : Fin 4) : ℝ :=
  ∑ p : Fin 4, ∑ q : Fin 4,
    pi p * Kmat pi kap lam t1 p i * Kmat pi kap lam t2 p j
      * Kmat pi kap lam tx p q * Kmat pi kap lam t3 q k * Kmat pi kap lam t4 q l

/-! ## 1. 对角分组（侧 = 姐妹叶对 `(a,b)`、`(c,d)`）—— 拓扑 `ab|cd` -/

/-- **两侧各自单态**：侧 1 两叶同标于 `U`、侧 2 两叶同标于 `V`。 -/
noncomputable def mon (pi : Fin 4 → ℝ) (kap lam : ℝ) (t1 t2 tx t3 t4 : ℝ)
    (U V : Finset (Fin 4)) : ℝ :=
  ∑ i ∈ U, ∑ j ∈ V, patt4 pi kap lam t1 t2 tx t3 t4 i i j j

/-- **侧 1 纯 `U`、侧 2 单态于 `V`**。 -/
noncomputable def pureMon (pi : Fin 4 → ℝ) (kap lam : ℝ) (t1 t2 tx t3 t4 : ℝ)
    (U V : Finset (Fin 4)) : ℝ :=
  ∑ i ∈ U, ∑ j ∈ U, ∑ k ∈ V, patt4 pi kap lam t1 t2 tx t3 t4 i j k k

/-- **侧 1 单态于 `U`、侧 2 纯 `V`**。 -/
noncomputable def monPure (pi : Fin 4 → ℝ) (kap lam : ℝ) (t1 t2 tx t3 t4 : ℝ)
    (U V : Finset (Fin 4)) : ℝ :=
  ∑ i ∈ U, ∑ k ∈ V, ∑ l ∈ V, patt4 pi kap lam t1 t2 tx t3 t4 i i k l

/-- **两侧都纯**。 -/
noncomputable def pureAll (pi : Fin 4 → ℝ) (kap lam : ℝ) (t1 t2 tx t3 t4 : ℝ)
    (U V : Finset (Fin 4)) : ℝ :=
  ∑ i ∈ U, ∑ j ∈ U, ∑ k ∈ V, ∑ l ∈ V, patt4 pi kap lam t1 t2 tx t3 t4 i j k l

/-! ## 2. 跨结点分组 —— 拓扑 `ac|bd`（侧 `{a,c}`、`{b,d}`）与 `ad|bc`（侧 `{a,d}`、`{b,c}`）

两个侧都横跨 `p,q`，所以事件里必须出现 `Σ_{i∈U} K(t)_{p,i} K(t')_{q,i}`（`p ≠ q`）这样的**跨结点**和
—— 这正是旧版遗漏的东西。 -/

/-- `ac|bd` 的「两侧各自单态」（侧 1 = 处于 `0,2` 位的叶，侧 2 = 处于 `1,3` 位的叶）。 -/
noncomputable def monA (pi : Fin 4 → ℝ) (kap lam : ℝ) (t1 t2 tx t3 t4 : ℝ)
    (U V : Finset (Fin 4)) : ℝ :=
  ∑ i ∈ U, ∑ j ∈ V, patt4 pi kap lam t1 t2 tx t3 t4 i j i j

/-- `ac|bd` 的「侧 1 纯 `U`、侧 2 单态于 `V`」。 -/
noncomputable def pureMonA (pi : Fin 4 → ℝ) (kap lam : ℝ) (t1 t2 tx t3 t4 : ℝ)
    (U V : Finset (Fin 4)) : ℝ :=
  ∑ i ∈ U, ∑ j ∈ U, ∑ k ∈ V, patt4 pi kap lam t1 t2 tx t3 t4 i k j k

/-- `ac|bd` 的「侧 1 单态于 `U`、侧 2 纯 `V`」。 -/
noncomputable def monPureA (pi : Fin 4 → ℝ) (kap lam : ℝ) (t1 t2 tx t3 t4 : ℝ)
    (U V : Finset (Fin 4)) : ℝ :=
  ∑ i ∈ U, ∑ k ∈ V, ∑ l ∈ V, patt4 pi kap lam t1 t2 tx t3 t4 i k i l

/-- `ac|bd` 的「两侧都纯」。 -/
noncomputable def pureAllA (pi : Fin 4 → ℝ) (kap lam : ℝ) (t1 t2 tx t3 t4 : ℝ)
    (U V : Finset (Fin 4)) : ℝ :=
  ∑ i ∈ U, ∑ j ∈ U, ∑ k ∈ V, ∑ l ∈ V, patt4 pi kap lam t1 t2 tx t3 t4 i k j l

/-- `ad|bc` 的「两侧各自单态」（侧 1 = 处于 `0,3` 位的叶，侧 2 = 处于 `1,2` 位的叶）。 -/
noncomputable def monB (pi : Fin 4 → ℝ) (kap lam : ℝ) (t1 t2 tx t3 t4 : ℝ)
    (U V : Finset (Fin 4)) : ℝ :=
  ∑ i ∈ U, ∑ j ∈ V, patt4 pi kap lam t1 t2 tx t3 t4 i j j i

/-- `ad|bc` 的「侧 1 纯 `U`、侧 2 单态于 `V`」。 -/
noncomputable def pureMonB (pi : Fin 4 → ℝ) (kap lam : ℝ) (t1 t2 tx t3 t4 : ℝ)
    (U V : Finset (Fin 4)) : ℝ :=
  ∑ i ∈ U, ∑ j ∈ U, ∑ k ∈ V, patt4 pi kap lam t1 t2 tx t3 t4 i k k j

/-- `ad|bc` 的「侧 1 单态于 `U`、侧 2 纯 `V`」。 -/
noncomputable def monPureB (pi : Fin 4 → ℝ) (kap lam : ℝ) (t1 t2 tx t3 t4 : ℝ)
    (U V : Finset (Fin 4)) : ℝ :=
  ∑ i ∈ U, ∑ k ∈ V, ∑ l ∈ V, patt4 pi kap lam t1 t2 tx t3 t4 i k l i

/-- `ad|bc` 的「两侧都纯」。 -/
noncomputable def pureAllB (pi : Fin 4 → ℝ) (kap lam : ℝ) (t1 t2 tx t3 t4 : ℝ)
    (U V : Finset (Fin 4)) : ℝ :=
  ∑ i ∈ U, ∑ j ∈ U, ∑ k ∈ V, ∑ l ∈ V, patt4 pi kap lam t1 t2 tx t3 t4 i k l j

/-! ## 3. 三个期望权重 -/

/-- **F84 的期望权重，对角分组**（附录 aggregated 式的塌缩式；系数为 **÷4 口径**）。

`t₁,t₂` 是按**被评拓扑**排好的侧 1 两条链长、`t₃,t₄` 是侧 2、`tx` 是中间边。
（`mon`/`pureMon`/`monPure`/`pureAll` 里的类别集合固定为 `R={0,1}`、`Y={2,3}`，
即「哪一对姐妹叶落在哪个类别里」，这正是权重表的内容。） -/
noncomputable def Ew (pi : Fin 4 → ℝ) (kap lam : ℝ) (t1 t2 tx t3 t4 : ℝ) : ℝ :=
  (piR pi ^ 2 * piY pi ^ 2 * (mon pi kap lam t1 t2 tx t3 t4 Rset Yset
      + mon pi kap lam t1 t2 tx t3 t4 Yset Rset)
    - piY pi ^ 2 * sqR pi * (pureMon pi kap lam t1 t2 tx t3 t4 Rset Yset
      + monPure pi kap lam t1 t2 tx t3 t4 Yset Rset)
    - piR pi ^ 2 * sqY pi * (monPure pi kap lam t1 t2 tx t3 t4 Rset Yset
      + pureMon pi kap lam t1 t2 tx t3 t4 Yset Rset)
    + sqR pi * sqY pi * (pureAll pi kap lam t1 t2 tx t3 t4 Rset Yset
      + pureAll pi kap lam t1 t2 tx t3 t4 Yset Rset)) / 4

/-- **拓扑 `ac|bd` 的期望权重**（侧 = `{a,c}`、`{b,d}`；模式分布仍是基因树 `ab|cd`）。 -/
noncomputable def EwA (pi : Fin 4 → ℝ) (kap lam : ℝ) (t1 t2 tx t3 t4 : ℝ) : ℝ :=
  (piR pi ^ 2 * piY pi ^ 2 * (monA pi kap lam t1 t2 tx t3 t4 Rset Yset
      + monA pi kap lam t1 t2 tx t3 t4 Yset Rset)
    - piY pi ^ 2 * sqR pi * (pureMonA pi kap lam t1 t2 tx t3 t4 Rset Yset
      + monPureA pi kap lam t1 t2 tx t3 t4 Yset Rset)
    - piR pi ^ 2 * sqY pi * (monPureA pi kap lam t1 t2 tx t3 t4 Rset Yset
      + pureMonA pi kap lam t1 t2 tx t3 t4 Yset Rset)
    + sqR pi * sqY pi * (pureAllA pi kap lam t1 t2 tx t3 t4 Rset Yset
      + pureAllA pi kap lam t1 t2 tx t3 t4 Yset Rset)) / 4

/-- **拓扑 `ad|bc` 的期望权重**（侧 = `{a,d}`、`{b,c}`）。 -/
noncomputable def EwB (pi : Fin 4 → ℝ) (kap lam : ℝ) (t1 t2 tx t3 t4 : ℝ) : ℝ :=
  (piR pi ^ 2 * piY pi ^ 2 * (monB pi kap lam t1 t2 tx t3 t4 Rset Yset
      + monB pi kap lam t1 t2 tx t3 t4 Yset Rset)
    - piY pi ^ 2 * sqR pi * (pureMonB pi kap lam t1 t2 tx t3 t4 Rset Yset
      + monPureB pi kap lam t1 t2 tx t3 t4 Yset Rset)
    - piR pi ^ 2 * sqY pi * (monPureB pi kap lam t1 t2 tx t3 t4 Rset Yset
      + pureMonB pi kap lam t1 t2 tx t3 t4 Yset Rset)
    + sqR pi * sqY pi * (pureAllB pi kap lam t1 t2 tx t3 t4 Rset Yset
      + pureAllB pi kap lam t1 t2 tx t3 t4 Yset Rset)) / 4

/-- `ab|cd` 的期望权重（基因树与拓扑同为 `ab|cd`）。 -/
noncomputable def EwF84 (pi : Fin 4 → ℝ) (kap lam la lb lx lc ld : ℝ) : ℝ :=
  Ew pi kap lam la lb lx lc ld

/-- `ac|bd` 的期望权重（基因树 `ab|cd`）。 -/
noncomputable def EwF84_ac (pi : Fin 4 → ℝ) (kap lam la lb lx lc ld : ℝ) : ℝ :=
  EwA pi kap lam la lb lx lc ld

/-- `ad|bc` 的期望权重（基因树 `ab|cd`）。 -/
noncomputable def EwF84_ad (pi : Fin 4 → ℝ) (kap lam la lb lx lc ld : ℝ) : ℝ :=
  EwB pi kap lam la lb lx lc ld

@[simp] theorem EwF84_def (pi : Fin 4 → ℝ) (kap lam la lb lx lc ld : ℝ) :
    EwF84 pi kap lam la lb lx lc ld = Ew pi kap lam la lb lx lc ld := rfl

@[simp] theorem EwF84_ac_def (pi : Fin 4 → ℝ) (kap lam la lb lx lc ld : ℝ) :
    EwF84_ac pi kap lam la lb lx lc ld = EwA pi kap lam la lb lx lc ld := rfl

@[simp] theorem EwF84_ad_def (pi : Fin 4 → ℝ) (kap lam la lb lx lc ld : ℝ) :
    EwF84_ad pi kap lam la lb lx lc ld = EwB pi kap lam la lb lx lc ld := rfl

@[simp] theorem Rset_card : Rset.card = 2 := rfl

@[simp] theorem Yset_card : Yset.card = 2 := rfl

end Phylo.Stat.CASTERF84Events
