# W10_COALESCENT_SPEC.md —— 溯祖理论本体（Kingman coalescent）形式化规格

> **状态**：2026-10-09 W10 冻结版。派单来源 `../DISPATCH.md` §一；
> 数学出处以 `../references/md/Kingman1982_TheCoalescent.md`（下称 **K82**）为准。

## §0 环境与纪律（每个执行 agent 必读）

1. **工作目录**：`/mnt/c/Users/ASTER/WorkBuddy/Project/lean/lean4phylo`
   （Windows 侧 = `C:\Users\ASTER\WorkBuddy\Project\lean\lean4phylo`）。
   **只写你自己的那个文件**。**不要**改 `Phylo.lean`（登记由协调侧统一做）、
   **不要**改别的 agent 的文件、**不要** `git commit` / `git push`。
2. **编译一律在镜像**（正本没有物化依赖，`lake` 会去 GitHub fetch 然后超时 5 分钟）。
   * 你的镜像：**由协调侧在派单里指定**（`~/lean4phylo-t5x`）。
   * **编译必须串行**（WSL 只有 ~7GB RAM，两个 `lean` 并发会被 OOM 杀掉，
     报 `Lean exited with code 137` —— **那不是语法错误**）。一律用锁：
     ```bash
     # 先同步你的文件到镜像
     cp -r /mnt/c/Users/ASTER/WorkBuddy/Project/lean/lean4phylo/Phylo/. ~/lean4phylo-t5x/Phylo/
     # 单文件编译（快速迭代）
     ~/w10/withlock.sh ~/lean4phylo-t5x ~/.elan/bin/lake env lean Phylo/Stat/你的文件.lean
     # 单模块构建
     ~/w10/withlock.sh ~/lean4phylo-t5x ~/.elan/bin/lake build Phylo.Stat.你的模块
     ```
   * **零告警判据**：`lake env lean <file>` **exit 0 且输出 0 字节**。
3. **`import Phylo` 绝对禁止**：本库的根模块 `Phylo.lean` 会 import 你的模块 ⇒
   构成 `Phylo → 你的模块 → Phylo` 构建环，全量 build 直接失败
   （`build cycle detected`）。只 import **子模块**（`Phylo.Stat.Coalescent` 等）。
4. **零 `sorry` / 零 `axiom`**。未证项落成**显式** `def 名字 : Prop := …` 缺口
   （并在文件头「诚实边界」表格里列出）—— **宁可留缺口，不许改弱既有字段**。
5. **引用纪律**：docstring 里的每一条文献断言必须**回查原文**。行号引用 K82 的
   `../references/md/Kingman1982_TheCoalescent.md`。⚠️ K82 的 md 是 OCR，
   **公式编号在版面里被错位**（`(2.1)`/`(2.2)`/`(2.3)` 的编号出现在显示公式之后），
   引用时**用「第 N 行」+ 公式内容**双重定位，不要只写编号。
6. **公式先脚本穷举复核**（精确有理数，**不要 Monte Carlo**），脚本留档
   `scripts/msc/`。**公式抄错是本项目的高发事故。**
7. **措辞纪律**：commit message / 文件标题 / docstring 的措辞**不得宽于实际**。
   若是「并列的算术事实」就**不要**写成「推论」。
8. **文件头格式**（照抄库内既有风格）：
   ```
   /-
   Copyright (c) 2026 ASTER LAB. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: ASTER LAB
   -/
   import …            -- 只允许子模块 + Mathlib
   /-! # 模块名 —— 一句话
   …（文献出处、诚实边界表）
   -/
   ```
   ⚠️ `/-- … -/` **文档注释不能出现在 `import` 之前**（Lean 报 `unexpected token 'import'`）；
   `import` 之前只能放普通块注释 `/- … -/`。
9. **交付报告**必须包含：文件路径 · 行数 · md5 · `lake env lean` 的**原始输出**（要 0 字节）·
   你新增的 `Mathlib` import（如果有）· 你**没有**做到的部分（诚实边界）· 你的数值复核脚本结果。

---

## §1 W10a ★★★ 跳链（jump chain）：(2.1) 转移 + (2.2) 绝对概率 ⇒ PMF

**交付文件**（新建）：`Phylo/Stat/KingmanJumpChain.lean`
**命名空间**：`Phylo.Stat.KingmanJumpChain`
**允许 import**：`Phylo.Stat.Coalescent`（✅ 已实测 `Finpartition` 在其闭包内，**不需要**新 Mathlib import）。

### 1.1 状态空间

K82 第 **47–57** 行：状态空间 `E_n` = `{1,…,n}` 上的**等价关系**全体
（= 集合划分）。本库用 Mathlib 现成的 `Finpartition`：

```lean
abbrev Part (n : ℕ) := Finpartition (Finset.univ : Finset (Fin n))
-- k-块层：
abbrev PartK (n k : ℕ) := {P : Part n // P.parts.card = k}
```
（`Finpartition s` 的 `Fintype` 实例在 `Mathlib/Order/Partition/Finpartition.lean:311`
**已在闭包内**——已实测通过。⚠️ 该实例是**双指数**的：`n ≥ 5` 时**不要**用 `decide`
去枚举 `Finset.univ`，只在 `n ≤ 4` 用 `decide`。）

### 1.2 一次合并（(2.1) 的载体）

```lean
/-- 把 `Q` 的两个块 `B1, B2` 并成一个块。 -/
def mergeBlock (Q : Part n) (B1 B2 : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  insert (B1 ∪ B2) ((Q.parts.erase B1).erase B2)
```

要证的**结构引理**（(2.1) 的「有限核」）：
* `mergeBlock Q B1 B2` 满足 `Finpartition` 的三条字段（`SupIndep` / `sup = univ` / `⊥ ∉`），
  故给出 `mergePart (Q) (hB1 : B1 ∈ Q.parts) (hB2 : B2 ∈ Q.parts) (hne : B1 ≠ B2) : Part n`；
  **推论** `(mergePart …).parts.card = Q.parts.card - 1`。
* **可选但很有价值**：证明 `mergePart` 与 `B1, B2` 的**次序无关**（对称）。

### 1.3 ★★★ (2.2) 绝对概率

K82 第 **219–228 行**（绝对概率公式；OCR 把编号标成 `(2.2)`/`(2.3)`）：

> `P{S_k = ξ} = (n−k)! · k! · (k−1)! / ( n! · (n−1)! ) · ∏ᵢ λᵢ!`，
> `λ₁,…,λ_k` 为 `ξ` 各等价类的大小。

```lean
/-- ★★ Kingman 1982 (2.2)：k-块状态下**单个**划分的绝对概率。 -/
noncomputable def partitionProb (n k : ℕ) (P : Part n) : ℝ :=
  ((n - k)! : ℝ) * (k! : ℝ) * ((k - 1)! : ℝ) / ((n! : ℝ) * ((n - 1)! : ℝ))
    * ∏ B ∈ P.parts, (B.card! : ℝ)
```
（`k!` 用 `Nat.factorial`；记得 `Nat.cast`。**分母非零**要单独证：`n ≥ 1` 时 `(n! : ℝ) ≠ 0`。）

### 1.4 ★★★ 验收 ①：归一化 `Σ_{|P|=k} partitionProb n k P = 1`

**推荐路线**（比「割-排列」双射便宜得多，且是 K82 自己的证法，见第 **274–276 行**
「We prove (2.3) by backward induction on `k`, it being clearly true for `k = n`」）：

1. **基底** `k = n`：`|P| = n` 的划分**唯一**（全是单点集，即 `⊥ : Finpartition univ`），
   且 `partitionProb n n ⊥ = 1`。
2. **归纳步**由 §1.5 的**层间一致性**给出：
   `Σ_{|P|=k} partitionProb n k P = Σ_{|Q|=k+1} partitionProb n (k+1) Q`
   （因为每个 `Q` 恰有 `C(k+1,2)` 个不同的一步合并结果，见 §1.5）。
3. 于是 `k ↦ Σ_{|P|=k} partitionProb n k P` 是常数，等于 `k = n` 的值 `1`。

### 1.5 ★★★★ 验收 ②：层间一致性（**本子批的数学核心**）

**要证的形状**（`k ≤ n−1`）：
```lean
/-- 从 k+1 层出发、均匀随机合并一对块，落到 k 层的分布**恰是** k 层的绝对分布。 -/
theorem partitionProb_merge_recursion (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (P : Part n) (hP : P.parts.card = k) :
    partitionProb n k P
      = ∑ Q : Part n, (if Q.parts.card = k + 1 ∧ MergeInto Q P
                       then partitionProb n (k+1) Q / ((k+1).choose 2 : ℝ) else 0)
```
（`MergeInto Q P : Prop` = 「`P` 是 `Q` 合并某两块的结果」，用 `mergeBlock` 写。）

**证明骨架**（协调侧已核算，见 §1.7 的代数）：
* `Q` 的块大小记 `μ₁…μ_{k+1}`，`P` 由合并 `B₁,B₂` 得到；则
  `∏_{B∈Q.parts} B.card! = ∏_{B∈P.parts} B.card! · μ₁!μ₂!/(μ₁+μ₂)!`。
* 逆向：`P` 的块大小 `λ₁…λ_k`；把 `P` 的某一块 `B`（`|B| = λ`）**分裂**成两个非空块
  `A ⊔ (B\A)` 给出一个 `Q`；每个 `Q` 恰被 `(B, A)` 与 `(B, B\A)` **两种**写法覆盖。
* 于是归结为**单块分裂恒等式**（见 §1.7 (★)）：
  `Σ_{A ⊂ B, A ≠ ∅, A ≠ B} |A|! · |B\A|! = |B|! · (|B| − 1)`。

**必需的辅助引理（建议顺序）**：
```lean
/-- 把一个块 `B` 分裂成 `A ⊔ (B\A)`，得一个多一块的划分。 -/
def splitBlock (P : Part n) (B A : Finset (Fin n)) (hB : B ∈ P.parts)
    (hA : A ⊆ B) (hAne : A.Nonempty) (hAlt : A ≠ B) : Part n
/-- `A` 走遍 `B` 的**非空真**子集时 `|A|!·|B\A|!` 之和。 -/
theorem sum_powerset_factorial (B : Finset (Fin n)) (hB : 2 ≤ B.card) :
    ∑ A ∈ B.powerset.filter (fun A => A.Nonempty ∧ A ≠ B),
        (A.card! : ℝ) * ((B \ A).card! : ℝ)
      = (B.card! : ℝ) * ((B.card : ℝ) - 1)
```
`sum_powerset_factorial` 的证法（**已核算，很容易**）：先证**无限制**版本
`Σ_{A ∈ B.powerset} |A|!·|B\A|! = (|B| + 1)·|B|!`：
把 `B.powerset` 按 `powersetCard j`（`j = 0…|B|`）分组，用
`Finset.card_powersetCard`（`= |B|.choose j`）与
`Nat.choose_mul_factorial_mul_factorial`（`n.choose k * k! * (n−k)! = n!`）
得每组合计 `|B|!`，共 `|B|+1` 组；再减去 `A = ∅` 与 `A = B` 两个边界项（各 `|B|!`）。

### 1.6 ★★ 验收 ③：PMF

产出一个概率质量函数（二者任一即可，**都做更好**）：
* `noncomputable def jumpPMF (n k : ℕ) : PMF {P : Part n // P.parts.card = k}`，
  由 `partitionProb` 与 §1.4 的归一化构造（`PMF.ofFinset` 或
  `PMF.normalize`；**先查 Mathlib 现成构造器**，别手搓 `Measure`）；
* 或 `noncomputable def jumpMeasure : Measure (Part n)` 的有限测度 + `IsProbabilityMeasure`。
**同时**把 (2.1) 的**有限核**显式写出：
```lean
theorem merge_outcomes_card (Q : Part n) (hQ : 2 ≤ Q.parts.card) :
    (Q.parts.powersetCard 2).card = Q.parts.card.choose 2
theorem merge_outcomes_injective (Q : Part n) :
    Set.InjOn (fun p : {p : Finset (Finset (Fin n)) // p ∈ Q.parts.powersetCard 2} =>
                 mergePartsOf Q p.1) Set.univ
```
（即「从 `Q` 出发的 `C(k+1,2)` 个一步合并**互不相同**、每个概率 `1/C(k+1,2)`」。）

### 1.7 协调侧已核算的代数（**直接用，不要重推**）

* 由 §1.5 的递归可推出归一化（§1.4 路线），故**不必**去证「割-排列」双射。
* 递归的代数核对（`n = 4, k = 2`，`Q = {12|3|4}`，`μ = (2,1,1)`）：
  `partitionProb 4 3 Q = (1/6)`，两个 `P` 各 `(1/6)/C(3,2)` ⇒ `1/9 = partitionProb 4 2 {12|34}` ✓
* (★) 数值核对：`|B| = 3` 时 LHS `= 1!·2! × 3 = 12 = 3!·2` ✓；
  `|B| = 4` 时 LHS `= (1!3! ×4) + (2!2! ×3) = 24 + 12 = 36 = 4!·3` ✓
  （注意 `A` 与 `B\A` **成对出现**，所以上面这个「有序」和是**每个无序分裂两份**；
  §1.5 里的求和要相应乘 `1/2` 或按「`min' B ∈ A`」取代表元 —— **两种都行，选一种并写明**）。
* 归一化恒等式（供 §1.4 校验）：`Σ_{|ξ|=k} ∏λᵢ! = n!(n−1)! / ((n−k)! k! (k−1)!)`
  （`n = 4, k = 2` 时 `= 36` ✓；这就是 WorkBuddy 用脚本精确复核过的那条）。

---

## §2 W10b ★★★ 逗留时间与 Kingman Theorem 1（跳链 ⊗ 独立指数）

**交付文件**（新建）：`Phylo/Stat/KingmanCoalescent.lean`
**命名空间**：`Phylo.Stat.KingmanCoalescent`
**允许 import**：`Phylo.Stat.KingmanJumpChain`（若 W10a 尚未落地，改为 `Phylo.Stat.Coalescent`）
＋ **`Mathlib.Probability.Distributions.Exponential`**（⚠️ 实测**不在**闭包内，
这是本批唯一新增的 Mathlib import，请在文件头注明）。

### 2.1 数学内容

K82:(1.7) 第 **129–137 行**：状态 `ξ`（`|ξ| = k`）的逗留时间密度 `d_k e^{−d_k t}`，
`d_k = ½k(k−1)`；即 `τ_k ~ Exp(d_k)`。
K82:**Theorem 1** 第 **210–215 行**：

> In an n-coalescent, the death process `(D_t)` and the jump chain `(S_k)` are **independent**, and
> `R_t = S_{D_t}` for all `t ≥ 0`.

K82:(1.11) 第 **174–195 行**：`T = Σ_{k=2}^{n} τ_k`，`τ_k` **相互独立**。

### 2.2 交付

```lean
/-- K82 (1.7)：k 条谱系的逗留时间律 = 速率 `d_k` 的指数分布。 -/
noncomputable def sojournLaw (k : ℕ) : Measure ℝ := ProbabilityTheory.expMeasure (Coalescent.kingmanRate k)

theorem isProbabilityMeasure_sojournLaw {k : ℕ} (hk : 2 ≤ k) : IsProbabilityMeasure (sojournLaw k)
```
★ **与库内既有设施接上**（这是本子批最有价值的一条）：
```lean
/-- `sojournLaw k (Ioi t) = ofReal (Coalescent.survival k t)`，即 `e^{−d_k t}`。 -/
theorem sojournLaw_Ioi (k : ℕ) (t : ℝ) :
    sojournLaw k (Set.Ioi t) = ENNReal.ofReal (Coalescent.survival k t)
```
（器材：`ProbabilityTheory.cdf_expMeasure_eq`；注意 `Measure (Ioi t)` 的 CDF 约定 ——
**先读 Exponential.lean 里 `cdf_expMeasure_eq` 的准确方向**，可能要换成 `Ici`。）

```lean
/-- ★★ K82 (1.11)+(1.12)：n−1 个逗留时间的**联合律** = 独立指数之积。 -/
noncomputable def sojournJointLaw (n : ℕ) : Measure (Fin (n - 1) → ℝ) :=
  Measure.pi (fun i : Fin (n - 1) => sojournLaw (i.1 + 2))

theorem isProbabilityMeasure_sojournJointLaw {n : ℕ} (hn : 2 ≤ n) : IsProbabilityMeasure (sojournJointLaw n)
```
```lean
/-- ★★ **Theorem 1 的联合律形式**：`n`-溯祖的联合律 = 跳链 PMF ⊗ 逗留时间联合律。
    「乘积」正是 Theorem 1 的**独立性**内容。 -/
noncomputable def nCoalescentLaw (n : ℕ) : Measure (Part n × (Fin (n - 1) → ℝ)) :=
  (jumpPMF n n).toMeasure.prod (sojournJointLaw n)
/-- 两个坐标**独立**（Theorem 1）。 -/
theorem indepFun_fst_snd_nCoalescent (n : ℕ) : IndepFun Prod.fst Prod.snd (nCoalescentLaw n)
```
（若 `IndepFun` 的 API 与 `Measure.prod` 对不上，就用**等价形式**：证明
`nCoalescentLaw n = μ.prod ν` 且两个边缘分别是 `μ` / `ν` —— 这正是独立性的定义性内容；
**在诚实边界表里写明你用的是哪个等价形式**。）

★ **期望**：`E[τ_k] = 1/d_k`、`E[T] = 2(1 − 1/n)`：
```lean
theorem integral_id_sojournLaw {k : ℕ} (hk : 2 ≤ k) :
    ∫ t, t ∂(sojournLaw k) = 1 / Coalescent.kingmanRate k
theorem integral_sum_sojournJointLaw {n : ℕ} (hn : 2 ≤ n) :
    ∫ τ, ∑ i : Fin (n - 1), τ i ∂(sojournJointLaw n)
      = 2 * (1 - 1 / (n : ℝ))
```
（第二条 = `Coalescent.expectedTotalCoalescenceTime`（`Phylo/Stat/Coalescent.lean:242`）。）
**先查** Mathlib 是否已有 `integral_expMeasure` / `mean` 类引理（`grep` 镜像里的
`Mathlib/Probability/Distributions/Exponential.lean` 与 `Gamma.lean`），
**有就用**，没有就自己算（`integral_eq_lintegral_of_nonneg` 等）。

### 2.3 允许的降级

* 若 `Measure.pi` 的 `IsProbabilityMeasure` 实例条件太麻烦：可先对
  `Measure.pi` 用 `MeasureTheory.Measure.pi.instIsProbabilityMeasure`（**先 grep 确认名字**）。
* 若 `IndepFun` 走不通：用「联合律 = 乘积测度」作为 Theorem 1 的形式化，并在
  docstring 明确写「`IndepFun` 的等价形式，理由：…」。
* **不许**为了让某条编过而改弱 `Coalescent.lean` 的任何既有声明。

---

## §3 W10e ★★★ Degnan–Salter 2005：`p_{uv}(T)` 递推（一切基因树概率的母机）

**交付文件**（新建）：`Phylo/Stat/DegnanSalter.lean`
**命名空间**：`Phylo.Stat.DegnanSalter`
**允许 import**：`Phylo.Stat.Coalescent`（＋必要时 `Phylo.Stat.MSC`；**不要** `import Phylo`）。

### 3.1 文献

`../references/md/DegnanSalter2005_GeneTreeDistributions.md`：
* **`p_{uv}(T)`（式 (1)，第 375–400 行）**：一条枝上 `u` 条谱系并成 `v` 条的概率；
* 「所有 ordering 等概率」= 模型口径（第 **3213–3222** / **3806–3809** 行）；
* 概率质量函数全文（第 **4270 行** 起）。

**第一步**：先把 md 里式 (1) 的**准确形状**抄出来（含行号），
写成 docstring 里的引用块，**再**动手定义。**不要凭记忆写公式。**

### 3.2 交付（骨架优先）

```lean
/-- Degnan–Salter (2005) 式 (1)：一条枝上 `u` 条谱系在 `t` 内并成 `v` 条的概率。 -/
noncomputable def pUV (u v : ℕ) (t : ℝ) : ℝ := …   -- 按原文抄
```
要证的**结构性质**（能证几条算几条，其余落**显式缺口**）：
* `pUV` 非负；`pUV u v t = 0` 当 `v > u` 或 `v < 1`；
* `Σ_{v=1}^{u} pUV u v t = 1`（**归一化**，对 `u = 1,2,3,4` 用精确数值脚本先复核）；
* 与库内既有设施的**接合点**（★ 最重要）：
  `pUV 2 1 t = Coalescent.firstMergeCDF 2 t`（`= 1 − e^{−t}`）—— 即 Degnan–Salter 的
  `u=2` 情形就是库内已有的 `firstMergeCDF`；`pUV 2 2 t = Coalescent.survival 2 t`。
* **可选（有余力才做）**：一般 `n` 谱系树上基因树拓扑的概率递推（第 4270 行起）。

### 3.3 允许的降级

递推的一般形式如果超出时间预算，**至少**要交付：
① 式 (1) 的准确定义 + 与 `firstMergeCDF`/`survival` 的接合点；
② 归一化的**有限**情形（`u ≤ 4`，显式枚举）**或**一般情形的显式缺口（写清缺什么）。
在诚实边界表里逐条写明。

---

## §4 三个子批共同的验收清单

每子批收口（协调侧统一执行，执行 agent 只需自测前 4 条）：

1. `~/w10/withlock.sh <镜像> ~/.elan/bin/lake env lean Phylo/Stat/<你的文件>.lean`
   → **exit 0 且输出 0 字节**；
2. `… lake build Phylo.Stat.<你的模块>` → 成功；
3. 源码级 `grep -nE '^\s*sorry\s*$|:= *sorry|by *sorry|^axiom '` → **无**；
4. 你写的每条 `theorem`/`def` 名称在文件里**真实存在**（不许 docstring 里写没证的声明）；
5. （协调侧）全量 `lake build` + job 数 +1/模块；
6. （协调侧）`#print axioms` 仅 `[propext, Classical.choice, Quot.sound]`；
7. （协调侧）`scripts/check_file_imports.sh` 与 `scripts/list_star_claims.sh` 双 exit 0；
8. （协调侧）`git commit`（**不 push**）+ 回写 `HANDOVER.md` + 追加 `MEMORY.md`。
