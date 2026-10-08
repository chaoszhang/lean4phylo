/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERF84

/-!
# `Phylo.Stat.CASTERF84Events` —— F84 命题 A 的**推导接口**（模式概率 + 8 个侧向事件 + 三种拓扑）

文献：Zhang, Nielsen, Mirarab (2025), *Science* **387**(6737) eadk9688，
附录 `sm.tex` **1559–1562**（F84 的期望权重，对 `(χ,ψ)∈R×Y` 的双重求和）。

## 本文件做什么

把推导层需要的**定义**固定下来（核与三条证书已在 `Phylo.Stat.CASTERF84` 里）：

1. `patt4` —— 四叶位点模式概率（基因树 `ab|cd`，内部结点取平稳分布 `π`）：
   `P(i,j,k,l) = Σ_{p,q} π_p K(t₁)_{p,i}K(t₂)_{p,j}K(tx)_{p,q}K(t₃)_{q,k}K(t₄)_{q,l}`
   （侧 1 = 链长 `t₁,t₂` 的姐妹叶对、侧 2 = `t₃,t₄`、中间边 `tx`）。
2. 四个**侧向事件**（`R = {A,G} = {0,1}`、`Y = {C,T} = {2,3}`）：
   `mon`（两侧各自单态）、`pureMon`（侧 1 纯 `U`、侧 2 单态于 `V`）、
   `monPure`（侧 1 单态于 `U`、侧 2 纯 `V`）、`pureAll`（两侧都纯）。
3. `Ew` —— 附录 aggregated 式的**塌缩式**（系数为 **÷4 口径**）：
   ```
   Ew = π_R²π_Y²·(mon(R,Y) + mon(Y,R))
      − π_Y²·sqR·(pureMon(R,Y) + monPure(Y,R))
      − π_R²·sqY·(monPure(R,Y) + pureMon(Y,R))
      + sqR·sqY ·(pureAll(R,Y) + pureAll(Y,R))
   ```
   数值上它与原 aggregated 式**完全一致**（`scripts/f84/caster_f84_collapse.py`，1.1e-13）。
4. 三种无根 quartet 拓扑的期望权重：`EwF84`（`ab|cd`）、`EwF84_ac`（`ac|bd`）、`EwF84_ad`（`ad|bc`）
   —— 把**侧**按拓扑重新分组（链长顺序与两叶标签顺序随之调整）。

## ★ 待证的主公式（**÷4 口径**，数值已验证 1.0000000000）

```
EwF84 pi kap lam la lb lx lc ld  −  EwF84_ac pi kap lam la lb lx lc ld
  = 2·π_Aπ_Cπ_Gπ_T·π_Rπ_Y · e^{−λ(1+κ)(la+lb+lc+ld)} · (1 − e^{−λlx})
```
（照印系数时右端要乘 4 —— 见 `lean4phylo/CASTER_F84_FINDING.md`。）

## 🔻 为什么这里只放定义

定义是**推导的地基**且必须与 Python 侧逐项对齐（`scripts/f84/caster_f84_collapse.py` 的
`Ew_collapsed` 使用**同一种「按拓扑给侧排序」的约定**）。主公式的证明是纯矩阵元代数，
按 `Phylo.Stat.CASTERLM1` 的结构写即可：先用 ★★★ `CASTERF84.Kmat_semigroup` 把两侧「并起来」，
再用 `scripts/f84/caster_f84_scaffold.py`、`caster_f84_factb.py`、`caster_f84_aggc.py`
里**已数值验证的三条塌缩**（`S_U` / `K(t)_{u,i}=α_tπ_i+r_tδ_{u,i}` / `Agg_c`）收口。

⚠️ **`ac|bd` 的配对 `(a,c)`、`(b,d)` 不是基因树的姐妹叶**（基因树是 `ab|cd`）！所以
`EwF84_ac` 里那两个「侧」只用于**权重表**，而预测概率 `patt4` 的姐妹叶始终是 `(a,b)` 与 `(c,d)`
—— 这正是 `Ew_ac` 把链长重排成 `(la,lc,lx,lb,ld)` 的原因（不是重新定义树）。 -/

universe u

namespace Phylo.Stat.CASTERF84Events

open Phylo.CASTERF84

/-- `R = {A,G}`（本文件用 `Fin 4` 的 `0=A,1=G,2=C,3=T`）。 -/
def Rset : Finset (Fin 4) := {0, 1}

/-- `Y = {C,T}`。 -/
def Yset : Finset (Fin 4) := {2, 3}

/-- **四叶位点模式概率**（基因树 `ab|cd`）：内部结点取平稳分布 `π`，
侧 1 = 链长 `t₁,t₂` 的姐妹叶对（标签 `i,j`）、侧 2 = `t₃,t₄`（标签 `k,l`）、中间边 `tx`。 -/
noncomputable def patt4 (pi : Fin 4 → ℝ) (kap lam : ℝ) (t1 t2 tx t3 t4 : ℝ)
    (i j k l : Fin 4) : ℝ :=
  ∑ p : Fin 4, ∑ q : Fin 4,
    pi p * Kmat pi kap lam t1 p i * Kmat pi kap lam t2 p j
      * Kmat pi kap lam tx p q * Kmat pi kap lam t3 q k * Kmat pi kap lam t4 q l

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

/-- **F84 的期望权重**（附录 aggregated 式的塌缩式；系数为 **÷4 口径**）。

`t₁,t₂` 是按**被评拓扑**排好的侧 1 两条链长、`t₃,t₄` 是侧 2、`tx` 是中间边。
（`mon`/`pureMon`/`monPure`/`pureAll` 里的类别集合固定为 `R={0,1}`、`Y={2,3}`，
即「哪一对姐妹叶落在哪个类别里」，这正是权重表的内容。） -/
noncomputable def Ew (pi : Fin 4 → ℝ) (kap lam : ℝ) (t1 t2 tx t3 t4 : ℝ) : ℝ :=
  piR pi ^ 2 * piY pi ^ 2 * (mon pi kap lam t1 t2 tx t3 t4 Rset Yset
      + mon pi kap lam t1 t2 tx t3 t4 Yset Rset)
    - piY pi ^ 2 * sqR pi * (pureMon pi kap lam t1 t2 tx t3 t4 Rset Yset
      + monPure pi kap lam t1 t2 tx t3 t4 Yset Rset)
    - piR pi ^ 2 * sqY pi * (monPure pi kap lam t1 t2 tx t3 t4 Rset Yset
      + pureMon pi kap lam t1 t2 tx t3 t4 Yset Rset)
    + sqR pi * sqY pi * (pureAll pi kap lam t1 t2 tx t3 t4 Rset Yset
      + pureAll pi kap lam t1 t2 tx t3 t4 Yset Rset)

/-- 拓扑 `ab|cd` 的期望权重（侧 = `{a,b}` 与 `{c,d}`）。 -/
noncomputable def EwF84 (pi : Fin 4 → ℝ) (kap lam la lb lx lc ld : ℝ) : ℝ :=
  Ew pi kap lam la lb lx lc ld

/-- 拓扑 `ac|bd` 的期望权重（侧 = `{a,c}` 与 `{b,d}`；注意姐妹叶仍是 `(a,b)`、`(c,d)`）。 -/
noncomputable def EwF84_ac (pi : Fin 4 → ℝ) (kap lam la lb lx lc ld : ℝ) : ℝ :=
  Ew pi kap lam la lc lx lb ld

/-- 拓扑 `ad|bc` 的期望权重（侧 = `{a,d}` 与 `{b,c}`）。 -/
noncomputable def EwF84_ad (pi : Fin 4 → ℝ) (kap lam la lb lx lc ld : ℝ) : ℝ :=
  Ew pi kap lam la ld lx lb lc

@[simp] theorem EwF84_def (pi : Fin 4 → ℝ) (kap lam la lb lx lc ld : ℝ) :
    EwF84 pi kap lam la lb lx lc ld = Ew pi kap lam la lb lx lc ld := rfl

@[simp] theorem EwF84_ac_def (pi : Fin 4 → ℝ) (kap lam la lb lx lc ld : ℝ) :
    EwF84_ac pi kap lam la lb lx lc ld = Ew pi kap lam la lc lx lb ld := rfl

@[simp] theorem EwF84_ad_def (pi : Fin 4 → ℝ) (kap lam la lb lx lc ld : ℝ) :
    EwF84_ad pi kap lam la lb lx lc ld = Ew pi kap lam la ld lx lb lc := rfl

@[simp] theorem Rset_card : Rset.card = 2 := rfl

@[simp] theorem Yset_card : Yset.card = 2 := rfl

end Phylo.Stat.CASTERF84Events
