# F84 命题 A 的形式化规格（更正版，`2bc0d88` 之后）

> 本文件是两个并行 agent 的**唯一事实源**。所有数值声称都已在 `scripts/f84/` 下有可复跑脚本。
> 协调侧（主 agent）已独立复核过下面每一条数值结论。

---

## 0. 一句话

旧接口 `Phylo/Stat/CASTERF84Events.lean`（commit `36ce9be`）**把「被评拓扑的侧」错实现成「重排叶长」**，
导致 `EwF84 = EwF84_ac = EwF84_ad`、主公式按字面**为假**。该文件已由协调侧更正（本批），
现在的三个量是：`Ew`（对角分组）、`EwA`（跨结点分组 `{0,2}/{1,3}`）、`EwB`（跨结点分组 `{0,3}/{1,2}`）。

**更正后的数学干净得多**：

```
(D)  Ew  pi kap lam t1 t2 lx t3 t4  =  C
(XA) EwA pi kap lam t1 t2 lx t3 t4  =  0
(XB) EwB pi kap lam t1 t2 lx t3 t4  =  0
C := 2·π_A·π_C·π_G·π_T·π_R·π_Y·(1 − sm lam lx)·rm lam kap t1·rm lam kap t2·rm lam kap t3·rm lam kap t4
```

即 `E[w(τ) | 基因树 G] = C·[τ = topo G]`：**两个错拓扑的期望权重恰为 0**。

---

## 1. 证据（`scripts/f84/`，都能复跑）

| 脚本 | 结论 |
|---|---|
| `caster_f84_leancheck.py` | 旧接口的 `Ew` 对 `(t1,t2,t3,t4)` **完全对称**（3.6e-12），且 `Ew = 8π_Aπ_Cπ_Gπ_Tπ_Rπ_Y(1−sm lx)rm(Σl)`（2.2e-12）⇒ 旧主公式为假 |
| `caster_f84_decide.py` | 逐字复制 `iface.py` 与我的实现并列：`E_ab = C`、`E_ac = E_ad = 0`、`(E_ab−E_ac)/C = 1`（1e-15） |
| `caster_f84_tabtest.py` | 6 组系数的穷举：只有「附录式 **÷4**」给出 `E_ab=C, E_ac=E_ad=0`（7e-13）；照印系数给 `E_ab=4C`；Fig.1D 逐模式读法漂移 |
| `caster_f84_formal.py` | ★ **把 `sm_t,rm_t` 当自由符号（含负数）后 (D)/(XA)/(XB) 仍成立**（3e-10 / 3e-18 / 1e-18） |
| `caster_f84_hyp.py` | 恒等式**不需要** `π_R+π_Y=1`；只需 `piR pi ≠ 0`、`piY pi ≠ 0` |

**⇒ 关键推论**：(D)/(XA)/(XB) 是 `π_j` 与 `sm_t, rm_t` 的**有理函数恒等式**。
推导层**不需要**指数运算律、**不需要** `CASTERF84.Kmat_semigroup`、**不需要** `Real.exp` 的任何引理
（`Real.exp …` 只是被 `ring` 当原子）。路线是：把 `Fin 4` 求和展开 → 清分母 → `ring`。

---

## 2. 归一化口径（已定，不再讨论）

`Ew`/`EwA`/`EwB` 的系数取**附录 (1556–1564) 照印值再整体除以 4**。
理由：照印系数给出的差是附录 (1585) 印的常数 `2π_Aπ_Cπ_Gπ_Tπ_Rπ_Y·e^{−λ(1+κ)L_T}(1−e^{−λ l_x})`
的 **4 倍**；÷4 后 (1585) 逐字成立。该差异属作者已确认会另行更正的常数类问题。

---

## 3. 要交付的两个文件

### 3.1 `Phylo/Stat/CASTERF84Scaffold.lean`（agent A）

`import Phylo.Stat.CASTERF84Events`；`namespace Phylo.Stat.CASTERF84Scaffold`；`open Phylo.CASTERF84`、`open Phylo.Stat.CASTERF84Events`。

**（a）脚手架**（`U` 取 `Rset` 与 `Yset` 两套；`pU := ∑ i ∈ U, pi i` 即 `piR pi` / `piY pi`）：

```
Bmat_class_sum   : ∑ i ∈ U, Bmat pi p i = if p ∈ U then 1 else 0
Kmat_col         : ∀ i ∈ U, Kmat pi kap lam t p i
                     = pi i * alphaU U pi kap lam t p + rm lam kap t * (if p = i then 1 else 0)
                   其中 alphaU U pi kap lam t p
                     := (1 − sm lam t) + (if p ∈ U then 1 else 0) * (sm lam t − rm lam kap t) / pU
Kmat_class_sum   : ∑ i ∈ U, Kmat pi kap lam t p i
                     = sm lam t * (if p ∈ U then 1 else 0) + (1 − sm lam t) * pU
Kmat_pair_sum    : ∑ i ∈ U, Kmat pi kap lam t p i * Kmat pi kap lam t' q i
                     = alphaU … t p * alphaU … t' q * (∑ i ∈ U, pi i ^ 2)
                       + alphaU … t' q * rm lam kap t  * (if p ∈ U then pi p else 0)
                       + alphaU … t p  * rm lam kap t' * (if q ∈ U then pi q else 0)
                       + rm lam kap t * rm lam kap t' * (if p = q ∧ p ∈ U then 1 else 0)
```

**（b）四个侧向事件在三种分组下的闭式**（把 (a) 代进定义即可，`∑ p : Fin 4, ∑ q : Fin 4` 展开后 `ring`）。
记 `S_U(p,t) := Kmat_class_sum` 的左端、`D_U(p,q;t,t') := Kmat_pair_sum` 的左端、`Kx := Kmat pi kap lam lx p q`：

```
mon(U,V)     = ∑ p ∑ q, pi p * D_U(p,p;t1,t2) * Kx * D_V(q,q;t3,t4)
pureMon(U,V) = ∑ p ∑ q, pi p * S_U(p,t1) * S_U(p,t2) * Kx * D_V(q,q;t3,t4)
monPure(U,V) = ∑ p ∑ q, pi p * D_U(p,p;t1,t2) * Kx * S_V(q,t3) * S_V(q,t4)
pureAll(U,V) = ∑ p ∑ q, pi p * S_U(p,t1) * S_U(p,t2) * Kx * S_V(q,t3) * S_V(q,t4)

monA(U,V)     = ∑ p ∑ q, pi p * D_U(p,q;t1,t3) * Kx * D_V(p,q;t2,t4)
pureMonA(U,V) = ∑ p ∑ q, pi p * S_U(p,t1) * S_U(q,t3) * Kx * D_V(p,q;t2,t4)
monPureA(U,V) = ∑ p ∑ q, pi p * D_U(p,q;t1,t3) * Kx * S_V(p,t2) * S_V(q,t4)
pureAllA(U,V) = ∑ p ∑ q, pi p * S_U(p,t1) * S_U(q,t3) * Kx * S_V(p,t2) * S_V(q,t4)

monB(U,V)     = ∑ p ∑ q, pi p * D_U(p,q;t1,t4) * Kx * D_V(p,q;t2,t3)
pureMonB(U,V) = ∑ p ∑ q, pi p * S_U(p,t1) * S_U(q,t4) * Kx * D_V(p,q;t2,t3)
monPureB(U,V) = ∑ p ∑ q, pi p * D_U(p,q;t1,t4) * Kx * S_V(p,t2) * S_V(q,t3)
pureAllB(U,V) = ∑ p ∑ q, pi p * S_U(p,t1) * S_U(q,t4) * Kx * S_V(p,t2) * S_V(q,t3)
```

（**先证这些闭式，再证 (D)/(XA)/(XB)**；否则 `ring` 要吞 ~28 万个单项式，必炸。）

**（c）三条主定理**（★★★）：

```
Ew_diag : Ew  pi kap lam t1 t2 lx t3 t4 = 2 * pi 0 * pi 2 * pi 1 * pi 3 * piR pi * piY pi
                                            * (1 - sm lam lx)
                                            * (rm lam kap t1 * rm lam kap t2
                                               * rm lam kap t3 * rm lam kap t4)
EwA_zero : EwA pi kap lam t1 t2 lx t3 t4 = 0
EwB_zero : EwB pi kap lam t1 t2 lx t3 t4 = 0
```

假设只需 `hR : piR pi ≠ 0`、`hY : piY pi ≠ 0`（**不要**加 `π_R+π_Y=1`，见 `caster_f84_hyp.py`）。

### 3.2 `Phylo/Stat/CASTERF84PropA.lean`（agent B）

`import Phylo.Stat.CASTERF84Events`、`Phylo.Stat.CASTERBridge`、`Phylo.Stat.CASTERGeneTree`。

```
lamF84 pi kap := piR pi * piY pi
                 / ((1 - (pi 0 ^ 2 + pi 1 ^ 2 + pi 2 ^ 2 + pi 3 ^ 2)) * piR pi * piY pi
                    + 2 * kap * (pi 0 * pi 1 * piY pi + pi 2 * pi 3 * piR pi))     -- 附录 1601

f84Const pi kap lam lx l := 2 * pi 0 * pi 2 * pi 1 * pi 3 * piR pi * piY pi
                            * (1 - sm lam lx) * (rm lam kap (l 0) * rm lam kap (l 1)
                                                 * rm lam kap (l 2) * rm lam kap (l 3))
```

9 格权重表（`l : Fin 4 → ℝ` 按 `a,b,c,d` 的**自然**叶长；`lx` 是内部枝长）：

| 基因树 `T'` \ 被评拓扑 `τ` | `ab_cd` | `ac_bd` | `ad_bc` |
|---|---|---|---|
| `ab_cd` | `Ew  l0 l1 lx l2 l3` | `EwA l0 l1 lx l2 l3` | `EwB l0 l1 lx l2 l3` |
| `ac_bd` | `EwA l0 l2 lx l1 l3` | `Ew  l0 l2 lx l1 l3` | `EwB l0 l2 lx l1 l3` |
| `ad_bc` | `EwA l0 l3 lx l1 l2` | `EwB l0 l3 lx l1 l2` | `Ew  l0 l3 lx l1 l2` |

（对角格子是「基因树的姐妹叶 = `τ` 的两侧」，故用 `Ew`；非对角格子两个侧都横跨 `p,q`，故用 `EwA`/`EwB`。）

**条件形式**（可不依赖 3.1 先落地，等 3.1 到位后加 5 行无条件版）：
把三条恒等式作为假设 `hD / hA / hB`，证明
```
f84Weight_eq      : f84Weight pi kap lam l lx T' τ
                      = (if T' = τ then f84Const pi kap lam lx l else 0)
f84PropAData_of   : PropAData (((Fin 4 → ℝ) × ℝ) × ((Fin 4 → ℝ) × ℝ))
                      其中 A θ T' τ := f84Weight θ.2.1 θ.2.2 (lamF84 θ.2.1 θ.2.2) θ.1.1 θ.1.2 T' τ
                           f θ        := f84Const θ.2.1 θ.2.2 (lamF84 θ.2.1 θ.2.2) θ.1.2 θ.1.1
f84_caster_statisticallyConsistent_of : 逐字照抄
                      Phylo.Stat.CASTERGeneTree.jc69_caster_statisticallyConsistent 的形状，
                      把 jc69PropAData 换成 f84PropAData_of …（`f84Const` 为正/可积仍作显式假设，同 JC69）
```

---

## 4. 配方（照做，别自创）

```lean
-- 小引理一律：
by
  fin_cases p <;> fin_cases q <;>          -- 把 Fin 4 变量变成 4 个字面量
  simp only [Rset, Yset, Kmat, P0, P1, P2, Bmat, piR, piY, sqR, sqY,
             Fin.sum_univ_four, Finset.mem_insert, Finset.mem_singleton] <;>
  simp only [Fin.isValue, Fin.reduceEq, if_true, if_false, reduceIte] <;>
  field_simp <;> ring
```

要点与坑：

1. **`Fin.sum_univ_four`** 把 `∑ i : Fin 4, f i` 展成 `f 0 + f 1 + f 2 + f 3`。
   `∑ i ∈ Rset, f i` 先 `simp [Rset]` 展成 `f 0 + f 1`。
2. `Bmat` 是**字面 pattern match**：只有索引是字面量时才归约 ⇒ **必须先 `fin_cases`**。
3. `if p ∈ Rset then … else …`（`p` 已字面化）用 `simp` + `Finset.mem_insert/mem_singleton`/`reduceIte` 消掉。
4. 分母只有 `piR pi`、`piY pi` ⇒ `field_simp` 后 `ring`。**`field_simp` 会留下 `a * b⁻¹`**，
   若 `ring` 收不了就先证 `div_add_div_self` 之类的小引理（见 `MEMORY.md` LM1 批的坑）。
5. **不要**去展开 `Kmat_semigroup` / `Real.exp` 的运算律：完全没有必要。
6. `Ew`/`EwA`/`EwB` 定义末尾有 `/ 4`：`ring` 对数字分母没问题。
7. **绝不要**把 `patt4` 的 16 个 `(p,q)` 项与 4 个索引求和一次性全展开后 `ring`（≈28 万单项式）。
   必须先用第 3.1(a) 的脚手架把内层求和收掉。
8. 零告警判据：`lake env lean <file>` 退出码 0 **且输出 0 字节**（`if_pos/if_neg/if_true/if_false`
   等已改名为 `ite_eq_left/ite_eq_right/ite_true/ite_false`，用旧名会告警）。
9. `lake env lean` **不产出 olean** ⇒ 交付前必须 `~/.elan/bin/lake build <module>`。

---

## 5. 环境与纪律

* 只在**自己的 WSL 镜像**里编译（例如 `~/lean4phylo-t43`、`~/lean4phylo-t44`），
  绝不在 `/mnt/c/.../lean4phylo`（正本）里 `lake build`。正本只放**源码**。
* 新文件必须按**字母序**登记进 `lean4phylo/Phylo.lean`（登记新模块 ⇒ 全量 build 的 job 数 +1）。
* 零 `sorry`、零 `axiom`、`#print axioms` 只允许 `[propext, Classical.choice, Quot.sound]`。
* docstring 里每个 ★ 条目必须对应**真实存在**的声明（纪律 12）；IUPAC 字母组合
  （`RY`、`YR` 之类）在散文里要加反引号，否则 `list_star_claims.sh` 会报。
* WSL 引号规则：**不要**在 `wsl -e bash -lc '...'` 里放引号/反斜杠/`$`；
  把 `.sh` 写到 `C:\Users\ASTER\AppData\Local\Temp\` 再 `wsl -e bash /mnt/c/.../x.sh`。
* 只改**自己那个新文件**＋`Phylo.lean` 的登记行；**不要**改别人的文件、不要 commit、不要 push。
* 交付时报告：文件 md5、`lake build` 的 job 数、`lake env lean` 的字节数、
  三条主定理的 `#print axioms` 输出、以及你**亲手数值复核**过的那一条。

---

## 6. 参考：更正前接口的失败原因（避免重蹈）

```
旧: EwF84_ac pi kap lam la lb lx lc ld = Ew pi kap lam la lc lx lb ld
```
`patt4` 里 `t1,t2` 都挂在结点 `p`、`t3,t4` 都在 `q`，所以这只换了叶长，
并没有让「叶 `a` 与叶 `c` 同标」。`ac|bd` 的两个侧横跨 `p,q`，必须用跨结点和
`∑_{i∈U} K(t1)_{p,i} K(t3)_{q,i}`（`p ≠ q`）—— 即上面的 `monA/monB` 家族。
