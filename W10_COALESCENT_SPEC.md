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
* (★) 数值核对：`|B| = 3` 时**有序**和 `= 1!·2! × 3 = 12 = 3!·2` ✓；
  `|B| = 4` 时**有序**和 `= (1!3! ×4) + (2!2! ×3) = 24 + 12 = 36`，**但 `4!·3 = 72`**
  —— ⚠️ **2026-10-09 勘误（W10a 执行 agent 发现）**：本规格此处原先写「`36 = 4!×3`」，
  那是**笔误**：`36` 是**无序**分裂和（`= 4!·3/2`），**有序**和才是 `72`，
  与 §1.5 的定理陈述（有序、`= |B|!(|B|−1)`）一致。**定理陈述是对的，只有这行数字注解错了。**
  形式化一律按**有序**陈述（`sum_powerset_factorial`），全程无 `1/2` 因子。
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

## §5 W10f ★★★ ADR 2017：split 概率与「1/3 阈值」（异常区的形式化）

**交付文件**（新建）：`Phylo/Stat/SplitProbabilities.lean`
**命名空间**：`Phylo.Stat.SplitProbabilities`
**允许 import**：`Phylo.Stat.MSCProof`（已交付，给出 4 叶 MSC 权重）+ `Phylo.Stat.MSC`。
⚠️ 该模块**已登记**在 `Phylo.lean` 里，**不要**改 `Phylo.lean`。

### 5.1 文献（`../references/md/AllmanDegnanRhodes2017_SplitProbabilitiesMSC.md`）

* **Lemma 3.1**（第 **315** 行）：`|X| = n` 时，**非平凡 split 的概率之和 = `n − 3`**。
* ★★★ **Proposition 3.2**（第 **363** 行）：设 `σ` 是 `X` 上的 **binary** 物种树，
  内部枝长 `λ_i > ε ≥ 0`，`A|B` 是 `X` 的一个 split。则在 MSC 下
  > 若 `P_σ(A|B) ≥ (1/3)·exp(−ε)`，则 `A|B` 是 `σ` 展示的 split。

  并且 `1/3·exp(−ε)` **是紧的**：对任意 `α < (1/3)exp(−ε)`，存在物种树 `σ`（内部枝长 `> ε`）
  与**不被 `σ` 展示**的 split `A|B`，使 `P_σ(A|B) > α`。
* **Cor 3.3**（第 **415** 行）· **Thm 4.1**（第 **656** 行）：按「分离 `ac, bd` 的 split」求和的
  不等式（异常区的定量刻画）。**有余力再做**，先读原文抄准确形状。

### 5.2 交付（**`|X| = 4` 版本是硬性要求**，一般 `n` 允许落缺口）

`|X| = 4` 时非平凡 split 恰 3 个（三个 `2|2` 无向拓扑），与 `MSCProof` 的权重一一对应：
被展示的那个概率 `mscConcordant t`，另两个各 `mscDiscordant t`。

```lean
/-- 4 叶：`A|B` 在内部枝长 `t` 的物种树下的 MSC split 概率。 -/
noncomputable def splitProb4 (t : ℝ) (displayed : Bool) : ℝ :=
  if displayed then mscConcordant t else mscDiscordant t
```
★ 要证的（都应与 `Coalescent.pDiscordant` / `MSCProof.mscDiscordant` 接上）：
```lean
/-- ★★★ **Prop 3.2（4 叶）**：`P ≥ (1/3)exp(−ε)` ⟹ 该 split 被展示。-/
theorem prop_3_2_four {t ε : ℝ} (h : ε < t) (A : Bool) (hdis : A = false) :
    splitProb4 t A < (1 / 3) * Real.exp (-ε)
/-- ★★★ **紧性**：任意 `α < (1/3)exp(−ε)` 都存在反例。-/
theorem prop_3_2_tight_four {ε α : ℝ} (hα : α < (1 / 3) * Real.exp (-ε)) :
    ∃ t : ℝ, ε < t ∧ α < splitProb4 t false
/-- ★★ **Lemma 3.1（`n = 4`）**：三个非平凡 split 的概率之和 = `4 − 3 = 1`。-/
theorem lemma_3_1_four (t : ℝ) :
    mscConcordant t + mscDiscordant t + mscDiscordant t = 1
```
**一般 `n` 的 Lemma 3.1 / Prop 3.2** 需要「一般 `n` 的 MSC split 概率」这一尚未形式化的对象
⇒ 落成**显式 `def … : Prop` 缺口**（写清缺什么），或**有充分把握时**给出条件形式。
不许用 `sorry`。

### 5.3 与库内既有设施的接合（★ 最重要）

* `Phylo/Split.lean` 的 `Split` / `Split.IsSplitOf` / `Split.swap`（= `KPartition α 2`，**有向**）；
* `Phylo/Stat/MSC.lean` 的 `QuartetFreq` / `MSCFreq`（`majorizes` 已在 `MSCProof` 里被构造）；
* `Phylo/Stat/MSCProof.lean` 的 `mscConcordant` / `mscDiscordant` / `mscP_sum`。
**不要重造**这些；直接引用。

---

## §6 W10h ★★ Zhu–Degnan–Steel 2011：clade / clan 与互单系概率

**交付文件**（新建）：`Phylo/Stat/ReciprocalMonophyly.lean`
**命名空间**：`Phylo.Stat.ReciprocalMonophyly`
**允许 import**：`Phylo.Stat.MSCProof`（＋必要时 `Phylo.InternalEdge`）。

### 6.1 文献（`../references/md/ZhuDegnanSteel2011_CladesClansReciprocalMonophylyarXiv1101.1311.md`）

* **Theorem 4.5**（第 **452** 行）· **Theorem 5.1**（第 **849** 行）·
  **Theorem 6.3**（第 **1077** 行）· **Theorem 6.4**（第 **1171** 行）· **Prop 6.5**（第 **1265** 行）。
* **第一步（必做）**：把上述定理的**准确陈述 + 行号**抄进 docstring 的引用块
  **再**动手。**不要凭记忆写。**

### 6.2 与库内的接合

`Phylo/InternalEdge.lean` 已有
`IsClan`（第 **580** 行）· `IsClade`（第 **589** 行）· `isClade_iff_isClan_of_isBinary`。
⚠️ **先读它们的准确定义**（`IsClade A` 是「存在一条边使 `A` 恰是一侧的叶集」之类的
**树内**概念，与「**随机基因树**里 `A` 是否成单系」是**两个层次**）：
若需要「基因树里 `A` 是 clade」的**概率层**对象，请**显式定义**它（例如用
`MSCProof` 的 4 叶权重 + `IsClade` 的组合条件），并在文件头写清两层的关系。

### 6.3 交付与降级

* 骨架优先：先给 `def`（概率层对象）与至少一条**可证的**小情形（`|X| = 4` 或 rooted triple），
  一般定理落**显式缺口**（`def … : Prop`）并写清缺什么。
* ⚠️ 引用纪律：**任何** docstring 断言都必须回查原文并带行号。
* 若通读后发现该文的定理依赖本文没有的形式化基础（如一般 `n` 的基因树分布），
  **如实报告**并给出「最小可交付」版本（例如 `|X| = 4` 情形 + 与 `IsClade` 的桥）。

---

## §7 W10k ★★ 溯祖统计量（Watterson / Tajima / SFS）—— 教科书级，最便宜的加厚

**交付文件**（新建）：`Phylo/Stat/CoalescentStats.lean`
**命名空间**：`Phylo.Stat.CoalescentStats`（**不要**与 `Coalescent` 撞名）
**允许 import**：`Phylo.Stat.Coalescent`。

### 7.1 内容（全部由库内既有的 `sojournMean` / `expectedTotalCoalescenceTime` 推出）

* ★★★ **总枝长期望** `E[L_n] = Σ_{k=2}^{n} k·E[τ_k] = Σ_{k=2}^{n} 2/(k−1) = 2·H_{n−1}`：
  ```lean
  noncomputable def harmonic (m : ℕ) : ℝ := ∑ j ∈ Finset.range m, 1 / ((j : ℝ) + 1)
  noncomputable def totalTreeLengthMean (n : ℕ) : ℝ := ∑ j ∈ Finset.range (n - 1), 2 / ((j : ℝ) + 1)
  theorem totalTreeLengthMean_eq (n : ℕ) : totalTreeLengthMean n = 2 * harmonic (n - 1)
  ```
  并给出与 `Coalescent.sojournMean` 的**接合**：`k·sojournMean k = 2/(k−1)`（`k ≥ 2`）。
* ★★★ **Watterson (1975)**：无限位点模型下 `E[S] = θ·H_{n−1}`：
  ```lean
  theorem watterson_expected_segregating {n : ℕ} (θ : ℝ) (hn : 2 ≤ n) :
      (θ / 2) * totalTreeLengthMean n = θ * harmonic (n - 1)
  ```
  （`θ/2` = 每条谱系单位时间的突变率；`S` = 分离位点数。）**出处**：Watterson 1975,
  *On the number of segregating sites in genetical models without recombination*,
  Theor. Popul. Biol. **7**:256–276（**转述/教科书级**，教师允许转述）。
* ★★ **Tajima (1983)**：`E[π] = θ`（`π` = 两两差异的平均数）—— **核心恒等式**是
  `Σ_{k=2}^{n} E[τ_k]·C(k,2)·θ = θ`，即 `Σ_{k=2}^n sojournMean k * kingmanRate k = n − 1`
  （因为每位点每对谱系的突变期望是 `θ`）。请**先**把这条恒等式证出来再谈 `E[π]`。
* ★★ **SFS**：`E[ξ_i] = θ/i`（`i = 1..n−1`，`Σ_i E[ξ_i] = θ H_{n−1}`）。若一般的 `ξ_i`
  概率层对象太难，**至少**给 `Σ_{i=1}^{n−1} θ/i = θ·H_{n−1}` 与 `E[S]` 的一致**对账**，
  其余落**显式缺口**。
* **诚实边界**：以上都是**实数层期望**（与 `Coalescent.lean` 同一层次），
  **不是**测度层的随机变量。请在文件头写明这一点。

### 7.2 允许的降级

如上；但 `totalTreeLengthMean_eq` 与 `watterson_expected_segregating` **必须**交付
（它们只需望远镜和与 `Finset.sum` 交换，属低风险）。

---

## §9 W10g ★★★ ADR 2011：可识别性（rooted triple ⇒ 物种树拓扑 + **内部枝长**）

**交付文件**（新建）：`Phylo/Stat/Identifiability.lean`
**命名空间**：`Phylo.Stat.Identifiability`
**允许 import**：`Phylo.Stat.MSCProof`（已交付的 MSC 权重）。
⚠️ 该模块**已登记**，**不要**改 `Phylo.lean`。

### 9.1 文献（`../references/md/AllmanDegnanRhodes2011_IdentifyingRootedSpeciesTree.md`）

* 第 **300–306** 行（**关键公式**）：对三分支物种树（`a,b` 比 `c` 更近），设内部枝长 `t`，
  `p` = 「随机有根基因树里 `a,b` 比二者与 `c` 更近」的概率，则
  > **`t = − log( (3/2)(1 − p) )`**

  （引 Nei 1987 / Wakeley 2008）。
* ★★★ **Proposition 1**（第 **309** 行）：`n ≥ 3` 时**有根 triple 基因树拓扑的概率决定
  物种树拓扑与内部枝长**。
* ★★ **Corollary 2**（第 **316** 行）：基因树**拓扑分布**决定物种树拓扑与内部枝长。
* ⚠️ **Lemma 4**（第 **962–971** 行）**只对 5 taxa 成立**（第 **973–974** 行明言 6 taxa 起失效）；
  **Prop 3**（第 **900** 行，`|X| = 4`：`σ⁻` 可识别而 `σ⁺` 不可）依赖 4 叶无根基因树分布。

### 9.2 交付（**`|X| = 3`（rooted triple）版本是硬性要求**）

本库的 `MSCProof.mscConcordant` **正是**三分支情形下的 `p`（同一公式：`1 − ⅔e^{−t}`）。

```lean
/-- ★★★ **ADR2011 第 300–306 行的公式**：由概率 `p` 反解内部枝长。 -/
theorem branchLength_of_concordant (t : ℝ) :
    - Real.log ((3 / 2) * (1 - mscConcordant t)) = t
/-- ★★★ **内部枝长可识别**：`t ↦ p(t)` 单射。 -/
theorem mscConcordant_injective : Function.Injective mscConcordant
/-- ★★★ **拓扑可识别**：`t > 0` 时「概率最大」的那个拓扑**唯一**是真拓扑。 -/
theorem topology_identifiable {t : ℝ} (ht : 0 < t) :
    mscDiscordant t < mscConcordant t ∧
      ∀ s : ℝ, s ≤ mscDiscordant t → mscConcordant t > s
```
（最后一条就是 `mscDiscordant_lt_mscConcordant` 的「argmax」包装；**不要**重造，
直接引用 `MSCProof` 里已证的那条。）

**另加**（★ 有价值、且便宜）：`Corollary 2` 的**单射版**——由 `mscConcordant_injective`
+ 「三个拓扑概率由 `p` 决定」，给出「两个物种树的 rooted-triple 分布相同 ⇒ 内部枝长相同」。
若需要把「分布」写成对象，**显式定义**一个三元组 `(p₁,p₂,p₃)` 的记录即可。

### 9.3 降级与边界

* `n > 3` 的一般 Prop 1（每个内部边都可由某个 triple 反解）依赖「物种树的有根 triple 系统」，
  属**纯组合**；若时间不够，落**显式 `def … : Prop` 缺口**并写清。
* **Lemma 4 的 5-taxon 版本**依赖「**完整**溯祖历史的重标号对称性」（不是首次合并对的计数），
  本子批**不做**：请在文件头诚实边界表里写明「只形式化了 4 叶下的重标号对称性
  （`MSCKingman.root_topology_class_prob`），5 叶版本未做，原因是 …」。
* `Prop 3`（`σ⁺` 不可识别）依赖 4 叶**无根**基因树分布，本子批**不做**，同样如实写明。
* ⚠️ 若 `Real.log` 不在 import 闭包内，**允许**新增
  `Mathlib.Analysis.SpecialFunctions.Log.Basic`（**在文件头注明**），或把 `branchLength_of_concordant`
  改成等价的无 `log` 形式（`(3/2)(1 − p) = exp(−t)`）并**明确说明**你用了哪一种。
* 数值复核脚本留档 `scripts/msc/adr2011_identifiability.py`（精确/高精度，**不要 Monte Carlo**）：
  至少核对 `−log((3/2)(1−(1−⅔e^{−t}))) = t`（`t = 0.1 … 10`，高精度）与单射性。

---

## §10 W10d ★★ 大数定律 ⇒ 经验 quartet 频率的**几乎必然收敛**（**新定理，不动旧公理**）

**交付文件**（新建）：`Phylo/Stat/EmpiricalConvergence.lean`
**命名空间**：`Phylo.Stat.EmpiricalConvergence`
**允许 import**：`Phylo.Stat.MSC` ＋（**允许并请注明**）Mathlib 概率层
（`Mathlib.Probability.StrongLaw` / `Mathlib.Probability.Independence.*` 等）。

### 10.1 背景与**界线**（**先读，别越界**）

`Phylo/Stat/MSC.lean` 第 **159–175** 行把「MSC 采样 + 大数定律」公理化成
`MSCSampling.converges`，其形状是**确定性**的
`∀ m ε > 0, ∃ N, ∀ n ≥ N, FreqClose (emp n) m.freq ε`。
**这个形状无法由概率论「证」出来**（它没有概率空间）——
所以本子批**不去动 `MSCSampling`**（改它会把 `StatisticallyConsistent` 等既有定理全打断）。

**本子批的目标**是**新增**一条**真概率陈述**（与 W9 的「新增派生版、保持旧版兼容」同一套路）：

> 在一个真正的概率空间 `(Ω, μ)` 上，**独立同分布**的位点使**经验 quartet 频率**
> **几乎必然**收敛到理论频率。

### 10.2 交付（**骨架优先，允许降级**）

```lean
/-- 经验频率：`n` 个 iid 位点的指示函数平均。 -/
noncomputable def empFreq (n : ℕ) (ω : Ω) (S : Finset X) (hS : S.card = 4) (q : Split ↥S) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ind (ω i) S hS q

/-- ★★★ **大数定律**：`∀ᵐ ω ∂μ, Tendsto (fun n => empFreq n ω S hS q) atTop (𝓝 (m.freq.p S hS q))`。 -/
theorem empFreq_tendsto_ae … : ∀ᵐ ω ∂μ, Tendsto (fun n => empFreq n ω …) atTop (𝓝 (m.freq.p …))
```

**必做**：
1. **先查** Mathlib 有没有现成的**强大数定律**（在镜像里 `grep -rn 'strong_law\|StrongLaw' Mathlib/`）；
   **有就直接用**并在文件头写明用的是哪一条（文件 + 声明名）；
2. 若只有**弱**大数定律或**有限方差**版，**就用自己的版本**并**显式说明**：
   「本文件证的是**依概率**收敛 / 有限方差版，不是几乎必然」——**不许含糊**；
3. 把「经验频率」的**可测性**与**独立性**（iid 假设）写清楚：是**假设**还是**证出来**的，
   **必须逐条说明**。

### 10.3 允许的降级（**必须如实报告**）

* 若 Mathlib 的概率层 API（`IndepFun` / `iIndepFun` / 测度乘积）比预期重：
  **可以只做「有限 `n` 的期望」**（`E[empFreq n] = m.freq.p …`，即**无偏性**）
  ＋「方差 `= p(1−p)/n`」，并把「收敛」落成**显式缺口**（`def … : Prop`）写清缺什么。
  **这也是有价值的**（它是收敛定理的两个核心估计），但**不许**把「无偏 + 方差」说成「大数定律」。
* **不许**为了让某条编过而改弱 `MSC.lean` / `MSCSampling` 的任何既有声明。
* **不许**用 `sorry`；**不许**新造 `axiom`。

### 10.4 数值复核

留档 `scripts/msc/empirical_convergence.py`：**精确有理数**核对
「无偏性」（`Σ_i P(第 i 个位点给出 q) = n·p`）与「方差 `= p(1−p)/n`」在 `n ≤ 6`、
若干有理 `p` 上的恒等式（误差恒为 0）。**不要 Monte Carlo**。

---

## §11 W10i ★ Stadler–Degnan 2012：**ranked（带次序）基因树概率**

**交付文件**（新建）：`Phylo/Stat/RankedGeneTree.lean`
**命名空间**：`Phylo.Stat.RankedGeneTree`
**允许 import**：`Phylo.Stat.MSCProof`（已交付的 MSC 权重）＋必要时 `Phylo.Stat.KingmanCoalescent`。

### 11.1 文献

`../references/md/StadlerDegnan2012_RankedGeneTreeProbability.md`：
**Theorem 1**（第 **504** 行）· **Theorem 2**（第 **540** 行）· **Theorem 3**（第 **693** 行）。

⚠️ **第一步（必做）**：把上述定理的**准确陈述 + 行号**逐字抄进 docstring 引用块，**再**动手。
⚠️ **并且**：本批已有两篇论文的 md 出过问题（一篇 OCR 坏、一篇印刷范围错）。
所以**必须**先做一次「**冒烟测试**」：从你要用的定理里挑**一条能被独立验证的公式**
（例如某个小 `n` 的数值例子），用**精确有理数**脚本核对；**对不上就以 PDF 为准**
（镜像里可用 `pdftotext -layout -enc UTF-8 <pdf> -` 重新提取），并在文件头写明你的判定依据。

### 11.2 交付（骨架优先；`n = 3` 的显式情形是**硬性要求**）

* 先定义「**ranked 基因树**」这一**组合对象**（若库内没有）：例如在 `Cladogram` 之上加一个
  「内部顶点的**时间次序**」字段（即 coalescence 事件的先后），并给出它与**非 ranked** 拓扑的
  「遗忘映射」；
* 再给**概率**：★★★ 至少把 `n = 3`（或你能确切推出的最小情形）的 ranked 概率写成**闭形式**，
  并与库内 `MSCProof.mscConcordant` / `mscDiscordant`（以及 `KingmanCoalescent.sojournLaw`，若可达）
  **接上**；
* ★★ 若 Theorem 1 的一般递推可读通，给出**条件形式**（把「节律 / ordering 等概率」这一模型口径
  写成**显式前提**，**不要**默默当成公理）。

### 11.3 允许的降级（**必须如实报告**）

* 若 md 不可读、PDF 也提取不出可信公式：**不要硬造**。交付「组合对象 + 与非 ranked 拓扑的映射 +
  一条可证的性质（例如‘给定拓扑下 ranked 树恰有 `(n−1)!` 个’）」，把概率部分落成
  **显式 `def … : Prop` 缺口**，并写明「文献不可读，公式未采信」。
* 数值复核脚本留档 `scripts/msc/stadler_degnan_ranked.py`（精确有理数，**不要 Monte Carlo**）：
  至少核对「给定拓扑的 ranked 树计数 = `(n−1)!`」与小情形的概率和 = 1。
* 零 `sorry` / 零 `axiom`；新模块按**字母序**登记（协调侧做）；**不要**动 `Phylo.lean`。

---

## §8 三个子批共同的验收清单

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
