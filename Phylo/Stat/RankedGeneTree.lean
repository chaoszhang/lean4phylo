/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MSCProof

/-!
# `Phylo.Stat.RankedGeneTree` —— Stadler & Degnan (2012)：ranked 基因树概率的**可落地部分**

文献：T. Stadler & J. H. Degnan, *A polynomial time algorithm for calculating the probability
of a ranked gene tree given a species tree*（arXiv:1203.0414），
`references/pdf/StadlerDegnan2012_RankedGeneTreeProbability.pdf`。

## §0 冒烟测试的判定依据（**先做再落地**）

⚠️ 本批已有两篇论文的 md 出过问题（一篇 OCR 坏、一篇印刷范围错），故本文件先做冒烟测试。

**判定：以 PDF 为准**（`pdftotext -layout -enc UTF-8` 重新提取，产物留档
`scripts/msc/stadler_degnan_pdf.txt`），md 只作交叉核对。理由：

* `references/md/StadlerDegnan2012_RankedGeneTreeProbability.md` 第 **504–532** 行虽然给出
  Theorem 1 与式 (2) 的**内容**，与 PDF 一致，但该 md 把分式拆行、把公式编号 `(1)`/`(2)`
  排在公式**之后**（与 K82 的 OCR 同一毛病），单独读 md 极易抄错；
* PDF 第 **218–235** 行读出的形状是本文件采用的形状：
  ```
  Theorem 1. The probability of a ranked gene tree given a species tree is,        [PDF 第 218–219 行]
                    P[G|T] = Σ_{ℓ1=g1}^{n} P[G_{1,ℓ1}|T] / H_{ℓ1}            (1)  [PDF 第 224 行]
  where             H_{ℓ1} = ℓ1!(ℓ1 − 1)!/2^{ℓ1−1}                            (2)  [PDF 第 231 行]
  is the probability for the coalescences above the root appearing in the
  right order [8].                                                                [PDF 第 233 行]
  ```
  ⚠️ **论文这句话的措辞与式 (2) 的内容不一致**（印刷问题，不是我们读错）：
  Table 1（PDF 第 **140** 行）写的是
  「`h1k` = number of sequences of coalescences above the root of the species tree
  starting with k lineages」，所以 `H_ℓ` 是**计数**（`ℓ` 条谱系的合并序列数），
  而「**指定**次序」出现的概率是 `1/H_ℓ`。**本文件按「计数」口径形式化**，
  并同时给出 `1/H_ℓ = ∏_{k=2}^{ℓ} jumpProb k`（每一步合并两个块的概率 `1/C(k,2)` 之积）。

**数值证据（精确有理数/整数，`scripts/msc/stadler_degnan_ranked.py`，无 Monte Carlo）**：

1. 式 (2) 的闭形式 `ℓ!(ℓ−1)!/2^{ℓ−1}` 与独立来源「合并序列计数」`∏_{k=2}^{ℓ} C(k,2)`
   在 `ℓ = 2..12` **逐项相等**（`1, 3, 18, 180, 2700, 56700, …`）⟹ 式 (2) **采信**；
2. 穷举 `n = 2..7` 的全部合并序列：ranked 树数 `= H_n`（`1, 3, 18, 180, 2700, 56700`）⟹ 一致；
3. ⚠️ **任务书 §11.3 建议的「给定拓扑下 ranked 树恰有 `(n−1)!` 个」经穷举**证伪**：
   `n = 3` 时纤维数是 `1`（而 `(n−1)! = 2`）、`n = 4` 时是 `1` 或 `2`（而 `6`）、
   `n = 5` 时是 `1, 2, 3`（而 `24`）…… 论文自己的 Remark 6（PDF 第 **416–424** 行：
   「`(n−1)!/∏_i (c_i − 1)` 个 ranking，`c_i` = 内部顶点 `i` 的叶后代数」）
   才与穷举在 `n ≤ 7` **完全一致**。⟹ 本文件采信 **Remark 6**，
   并把任务书那一条记为**未经采信的规格笔误**（见 §5 缺口 G2 与诚实边界表）；
4. Theorem 3 的式 (4)（PDF 第 **219–229** 行）在论文**自己算**的例子
   `λ = (0,1,2)`、`m_3 = 2`（PDF 第 **385–413** 行）上给出 `1/2 − x + x²/2 = (1/2)(1−x)²`
   （`x = e^{−s}`），与论文用**另一条路线**（「只有一个种群有合并」时的 `g` 乘积公式，
   PDF 第 **356–357、380** 行：`P[G3,2|G4,3,T] = [g_{2,1}(s_2−s_3)]²/2`）得到的
   `[g_{2,1}(s)]²/2` **一致** ⟹ 式 (4) 的形状（含分母 `∏_{k≠j}(λ_k − λ_j)` 的符号约定）**采信**；
   另核对：`λ_j = j` 时式 (4) `= (1/m!)(1−e^{−s})^m`（`m ≤ 8`）、一般互异有理 `λ` 满足
   分片差商递推与 Lagrange 幂和恒等式 `Σ_j λ_j^r/∏_{k≠j}(λ_k−λ_j) = (−1)^m[r=m]`。

## §1 文献定理（逐字抄录 + 行号）

**Theorem 2**（PDF 第 **246–261** 行；md 第 **540–584** 行）：
```
Theorem 2. The probability P[G_{i,ℓi}|T] can be calculated for all i recursively (with ℓi ≥ gi),
   P[G_{i,ℓi}|T] = Σ_{ℓ_{i+1}=max(ℓi, g_{i+1})}^{n} P[G_{i,ℓi}|G_{i+1,ℓ_{i+1}},T] P[G_{i+1,ℓ_{i+1}}|T]   (3)
with P[G_{n−1,n}|T] = 1.
```
**Theorem 3**（PDF 第 **219–229** 行；md 第 **693–739** 行）：
```
Theorem 3. We have,
  P[G_{i−1,ℓ_{i−1}}|G_{i,ℓi},T] = Σ_{j=0}^{m_i} e^{−λ_{i,j}(s_{i−1}−s_i)} / ∏_{k=0,k≠j}^{m_i}(λ_{i,k} − λ_{i,j})  (4)
where λ_{i,j} = Σ_{z=1}^{i} C(k_{i,j,z}, 2) and C(1,2) := 0.
```
**Remark 6**（PDF 第 **416–424** 行；md 第 **1471–1476** 行）：
```
Remark 6. The probability of a gene tree topology is the sum of the probabilities of each ranked
gene tree with the given topology. A given tree topology has (n − 1)!/∏_{i=1}^{n−1}(c_i − 1) rankings,
where c_i is the number of descendant leaves of interior vertex i.
```
（另：Abstract，md 第 **54–57** 行「a ranked tree topology is a tree topology with the internal
vertices being ordered」= 本文件 `IsMergeHistory` 的口径。）

## §2 本文件交付什么（**措辞不宽于实际**）

1. **组合层**：`n` 个叶标记的 ranked 基因树拓扑 = **合并史**（每一步合并哪两个块，
   块用最小元作代表）—— `IsMergeHistory` / `mergeHistories` / `RankedTree`，
   以及「忘掉次序」的映射 `cladesOf`（= 该树的 clade 集 = 无次序拓扑）；
2. **计数层**：论文式 (2) 的 `H`（`H_eq_factorial`、`H_eq_prod`）与
   **有限枚举验证**：`n = 2, 3, 4` 的 ranked 树数 `= 1, 3, 18 = H_n`；
   `n = 4` 的无次序拓扑数 `= 15`；`n = 4` 的纤维数 `= 2`（平衡形）/`1`（caterpillar 形）、
   `n = 3` 的纤维数 `= 1`（= Remark 6 的实例核对）；
3. **`1/H_ℓ` 的概率意义**：`one_div_H_eq_prod_jumpProb`（= 每一步均匀取 `C(k,2)` 对之积），
   以及 `1/H_3 = MSCProof.rootTopoProb`（把论文的次序因子接到库内**已推导**的根部 `1/3`）；
4. **`n = 3` 的概率（硬性要求）**：`sd2012_theorem1_n3` —— Theorem 1 的求和
   在**显式的模型前提**（根以下概率 = `firstMergeCDF 2 t` / `0` / `survival 2 t`）下
   **等于** `MSCProof.mscConcordant t` / `mscDiscordant t`；配 `rankedProb3_sum_one`
   （三个 ranked 树概率和 `= 1`）与 `concordant3_iff_clades`（「`0,1` 先合并」⟺
   「忘掉次序后拓扑为 `((0,1),2)`」）；
5. **Theorem 3 的算术核**：`sd2012_eq4_example`（论文自算的 `λ=(0,1,2)` 例子）、
   `eq4_two_uniform_rates`（同一个式子按 `eq4` 定义本身展开）、
   与 `eq4_one_general`（`m = 1` 的两条竞争指数）。
6. **实现纪律**：全部有限枚举用 `decide`（内核规约），**不用** `native_decide`
   （故没有引入 `Lean.ofReduceBool`）；文件内 13 条代表定理的 `#print axioms` 均为
   `[propext, Classical.choice, Quot.sound]`。

## §3 诚实边界（**没做到的**，逐条）

| 条目 | 状态 |
|---|---|
| 论文式 (2) `H_ℓ = ℓ!(ℓ−1)!/2^{ℓ−1}` | ✅ **已证**（`H_eq_factorial`；`H_eq_prod` 给出乘积形式） |
| 「`1/H_ℓ` = 每一步均匀合并的概率之积」 | ✅ **已证**（`one_div_H_eq_prod_jumpProb`，用库内 `Coalescent.jumpProb`） |
| ranked 树计数 `= H_n`（**一般 `n`**） | ❌ **未证**（缺口 `rankedTree_card_gap`）；`n = 2, 3, 4` 已用 `decide` **枚举**验证 |
| Remark 6 的 `(n−1)!/∏(c_i−1)`（**一般 `n`**） | ❌ **未证**（缺口 `rankedFiberCount_gap`）；脚本穷举 `n ≤ 7` 核对，Lean 内验证 `n = 3, 4` 的实例 |
| **Theorem 1 的 `n = 3` 实例** | ✅ **已证**，但**模型前提显式**（`sd2012_theorem1_n3` 的 `b` 是假设，不是从 Theorem 2/3 推出的） |
| **Theorem 1 的一般 `n`** | ❌ **未做**（本文件只做 `n = 3`；一般 `n` 需要 Theorem 2/3 的输出） |
| **Theorem 2（式 (3) 的下行递推）** | ❌ **未形式化**（没有「根以下概率」的概率层对象） |
| **Theorem 3（式 (4) 的一般 `m`）** | ❌ **未形式化**（只做了 `m = 1` 的一般 `λ` 与 `λ = (0,1,2)`、`m = 2` 的算术实例 —— `sd2012_eq4_example` / `eq4_two_uniform_rates` / `eq4_one_general`；一般 `m` 落缺口 `sd2012_eq4_uniform_rates_gap`） |
| **`n = 4` 的 ranked 概率表** | ❌ **未做**（缺口 `ranked4_probability_gap`） |
| `k_{i,j,z}`（式 (4) 的 `λ_{i,j}` 谱系计数机制，§2.1） | ❌ **未形式化**（属于 Theorem 2/3 的实现细节） |
| 测度层随机变量 | ❌ **无**：本文件与 `Coalescent.lean`/`MSCProof.lean` 同一层次（**实数层**概率），不是测度层 |
| 任务书 §11.3 的「给定拓扑 ranked 树计数 `= (n−1)!`」 | ⚠️ **未采信**（脚本穷举证伪；论文 Remark 6 才是对的，见 §0 第 3 条） |
-/

namespace Phylo.Stat.RankedGeneTree

/-! ## §1 组合层：ranked 基因树拓扑 = 合并史 -/

/-- 一次合并：把 `y` 所在的块并入 `x` 所在的块。
块用**最小元**作代表（`r w` = 含 `w` 的块的最小元），故合并后原来映到 `y` 的元素改映到 `x`。 -/
def stepMap {n : ℕ} (r : Fin n → Fin n) (x y : Fin n) : Fin n → Fin n :=
  fun w => if r w = y then x else r w

/-- 前 `L` 次溯祖（合并）之后的「块代表」映射。第 `k` 步用 `f k = (x, y)` 合并 `x`、`y` 所在两块。 -/
def chainMap (n : ℕ) (f : Fin (n - 1) → Fin n × Fin n) (L : ℕ) : Fin n → Fin n :=
  ((List.range L).filterMap (fun k => if h : k < n - 1 then some (f ⟨k, h⟩) else none)).foldl
    (fun r p => stepMap r p.1 p.2) id

/-- 单步合法性：`x`、`y` 各自是所在块的**最小元**，且 `x < y`。

（这两条使编码**规范**：给定划分链，「被合并的两块」由它们的最小元唯一确定，
故每个 ranked 拓扑恰有一个合法编码；`x < y` 固定两块在 `f` 里的次序。） -/
def IsStep {n : ℕ} (r : Fin n → Fin n) (x y : Fin n) : Prop :=
  r x = x ∧ r y = y ∧ x < y

instance {n : ℕ} (r : Fin n → Fin n) (x y : Fin n) : Decidable (IsStep r x y) := by
  unfold IsStep
  infer_instance

/-- **合并史**：`n` 个叶标记上的 ranked（带次序）有根二叉树拓扑。
`f k = (x, y)`（`k = 0` 是**最近**的一次溯祖）表示第 `k` 步合并 `x`、`y` 所在的两块。 -/
def IsMergeHistory (n : ℕ) (f : Fin (n - 1) → Fin n × Fin n) : Prop :=
  (∀ k : Fin (n - 1), IsStep (chainMap n f (k : ℕ)) (f k).1 (f k).2) ∧
    (∀ w w' : Fin n, chainMap n f (n - 1) w = chainMap n f (n - 1) w')

instance (n : ℕ) : DecidablePred (IsMergeHistory n) := fun f => by
  unfold IsMergeHistory
  infer_instance

/-- `n` 个叶上的全部合并史 —— 直接写成 `(Fin n × Fin n)^(n-1)` 的**有限**子集，
故可用 `decide` 枚举（本文件 `n ≤ 4` 的全部计数都由此来）。 -/
def mergeHistories (n : ℕ) : Finset (Fin (n - 1) → Fin n × Fin n) :=
  (Finset.univ : Finset (Fin (n - 1) → Fin n × Fin n)).filter (fun f => IsMergeHistory n f)

/-- ★★★ **ranked 基因树拓扑**（`n` 个叶标记）：合并史的规范编码。 -/
abbrev RankedTree (n : ℕ) : Type := {f : Fin (n - 1) → Fin n × Fin n // IsMergeHistory n f}

/-- `RankedTree n` 的元素与 `mergeHistories n` 的元素一一对应（后者的元素就是前者的数据）。 -/
theorem mem_mergeHistories {n : ℕ} (f : Fin (n - 1) → Fin n × Fin n) :
    f ∈ mergeHistories n ↔ IsMergeHistory n f := by
  simp [mergeHistories]

/-- 一个划分（以「块代表映射」`r` 给出）的**块**集合。 -/
def blocksOf (n : ℕ) (r : Fin n → Fin n) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).image
    (fun w => (Finset.univ : Finset (Fin n)).filter (fun z => r z = r w))

/-- ★★ **忘掉次序**：合并史的**全部块**（= clade 集）= 该 ranked 树对应的**无次序**拓扑。
（同一无次序拓扑的不同 ranking 映到同一个 clade 集。） -/
def cladesOf (n : ℕ) (f : Fin (n - 1) → Fin n × Fin n) : Finset (Finset (Fin n)) :=
  (Finset.range n).biUnion (fun L => blocksOf n (chainMap n f L))

/-! ### §1.1 有限枚举（`n ≤ 4`） -/

/-- ★★★ `n = 2`：ranked 树恰 `1` 个（`= H_2 = 1!·0!/2^0`）。 -/
theorem card_mergeHistories_two : (mergeHistories 2).card = 1 := by decide

/-- ★★★ `n = 3`：ranked 树恰 `3` 个（`= H_3 = 3!·2!/2^2 = 3`）。 -/
theorem card_mergeHistories_three : (mergeHistories 3).card = 3 := by decide

set_option maxRecDepth 100000 in
/-- ★★★ `n = 4`：ranked 树恰 `18` 个（`= H_4 = 4!·3!/2^3 = 18`）。 -/
theorem card_mergeHistories_four : (mergeHistories 4).card = 18 := by decide

set_option maxRecDepth 100000 in
/-- ★★ `n = 3`：三个 ranked 树给出**三个不同**的无次序拓扑（纤维数全 `1`）。 -/
theorem card_topologies_three : ((mergeHistories 3).image (fun f => cladesOf 3 f)).card = 3 := by
  decide

set_option maxRecDepth 100000 in
/-- ★★ `n = 4`：`18` 个 ranked 树只给出 `15 = (2·4−3)!!` 个无次序拓扑。 -/
theorem card_topologies_four : ((mergeHistories 4).image (fun f => cladesOf 4 f)).card = 15 := by
  decide

/-- `Fin 3` 上拓扑 `((0,1),2)` 的 clade 集。 -/
def clades_01_2 : Finset (Finset (Fin 3)) :=
  ({{0}, {1}, {2}, {0, 1}, Finset.univ} : Finset (Finset (Fin 3)))

/-- `Fin 4` 上拓扑 `((0,1),(2,3))`（平衡形）的 clade 集。 -/
def clades_01_23 : Finset (Finset (Fin 4)) :=
  ({{0}, {1}, {2}, {3}, {0, 1}, {2, 3}, Finset.univ} : Finset (Finset (Fin 4)))

/-- `Fin 4` 上拓扑 `(((0,1),2),3)`（caterpillar 形）的 clade 集。 -/
def clades_012_3 : Finset (Finset (Fin 4)) :=
  ({{0}, {1}, {2}, {3}, {0, 1}, {0, 1, 2}, Finset.univ} : Finset (Finset (Fin 4)))

set_option maxRecDepth 100000 in
/-- ★★ **Remark 6 的 `n = 3` 实例**：拓扑 `((0,1),2)` 恰有 `1` 个 ranking
（`(n−1)!/∏(c_i−1) = 2!/(1·2) = 1`）。 -/
theorem card_rankings_01_2 :
    ((mergeHistories 3).filter (fun f => cladesOf 3 f = clades_01_2)).card = 1 := by
  decide

set_option maxRecDepth 100000 in
/-- ★★ **Remark 6 的 `n = 4` 平衡形实例**：拓扑 `((0,1),(2,3))` 恰有 `2` 个 ranking
（`3!/(1·1·3) = 2`）。 -/
theorem card_rankings_01_23 :
    ((mergeHistories 4).filter (fun f => cladesOf 4 f = clades_01_23)).card = 2 := by
  decide

set_option maxRecDepth 100000 in
/-- ★★ **Remark 6 的 `n = 4` caterpillar 形实例**：拓扑 `(((0,1),2),3)` 恰有 `1` 个 ranking
（`3!/(1·2·3) = 1`）。 -/
theorem card_rankings_012_3 :
    ((mergeHistories 4).filter (fun f => cladesOf 4 f = clades_012_3)).card = 1 := by
  decide

/-! ## §2 论文式 (2)：`H_ℓ`（根以上的合并序列数） -/

/-- ★★★ SD2012 式 (2)：`H_ℓ = ℓ!(ℓ−1)!/2^{ℓ−1}`，即「根以上从 `ℓ` 条谱系出发的**合并序列**数」
（论文 Table 1 的 `h1k`，PDF 第 **140** 行；`H_2 = 1`、`H_3 = 3`、`H_4 = 18`）。

本文件用**递推**定义（与式 (2) 的闭形式相等见 `H_eq_factorial`）：
`H_0 = H_1 = 1`，`H_{ℓ+2} = H_{ℓ+1} · C(ℓ+2, 2)`。 -/
noncomputable def H : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | (n + 2) => H (n + 1) * Coalescent.kingmanRate (n + 2)

/-- 递推一步：`H_{ℓ+1} = H_ℓ · C(ℓ+1, 2)`（`ℓ ≥ 1`）。 -/
theorem H_succ_eq (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    H (ℓ + 1) = H ℓ * Coalescent.kingmanRate (ℓ + 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ℓ ≠ 0)
  exact rfl

/-- ★★★ **式 (2) 的乘积形式**：`H_ℓ = ∏_{k=2}^{ℓ} C(k,2)`（= 「合并序列」的直接计数）。 -/
theorem H_eq_prod : ∀ ℓ : ℕ,
    H ℓ = ∏ k ∈ Finset.range (ℓ - 1), Coalescent.kingmanRate (k + 2)
  | 0 => by simp [H]
  | 1 => by simp [H]
  | (n + 2) => by
    have ih := H_eq_prod (n + 1)
    rw [show H (n + 2) = H (n + 1) * Coalescent.kingmanRate (n + 2) from rfl, ih,
      show n + 2 - 1 = n + 1 from rfl, show n + 1 - 1 = n from rfl,
      Finset.prod_range_succ]

/-- ★★★ **式 (2) 的闭形式**：`H_ℓ = ℓ!(ℓ−1)!/2^{ℓ−1}`。 -/
theorem H_eq_factorial : ∀ ℓ : ℕ,
    H ℓ = (ℓ.factorial : ℝ) * ((ℓ - 1).factorial : ℝ) / 2 ^ (ℓ - 1)
  | 0 => by norm_num [H]
  | 1 => by norm_num [H]
  | (n + 2) => by
    have ih := H_eq_factorial (n + 1)
    have hkr : Coalescent.kingmanRate (n + 2) = ((n + 2 : ℝ) * (n + 1 : ℝ)) / 2 := by
      rw [Coalescent.kingmanRate]
      push_cast
      ring
    have hf2 : ((n + 2).factorial : ℝ) = (n + 2) * ((n + 1).factorial : ℝ) := by
      rw [show n + 2 = n + 1 + 1 from rfl, Nat.factorial_succ]
      push_cast
      ring
    have hf1 : ((n + 1).factorial : ℝ) = (n + 1) * (n.factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [show H (n + 2) = H (n + 1) * Coalescent.kingmanRate (n + 2) from rfl, ih, hkr,
      show n + 2 - 1 = n + 1 from rfl, show n + 1 - 1 = n from rfl, hf2, hf1,
      show (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 2 from by rw [pow_succ]]
    ring

/-- `H_2 = 1`。 -/
theorem H_two : H 2 = 1 := by norm_num [H, Coalescent.kingmanRate]

/-- `H_3 = 3`。 -/
theorem H_three : H 3 = 3 := by norm_num [H, Coalescent.kingmanRate]

/-- `H_4 = 18`。 -/
theorem H_four : H 4 = 18 := by norm_num [H, Coalescent.kingmanRate]

/-- ★★ **计数与论文公式接上**：`n = 4` 的 ranked 树数 `= H_4`。 -/
theorem card_mergeHistories_four_eq_H : ((mergeHistories 4).card : ℝ) = H 4 := by
  rw [card_mergeHistories_four, H_four]
  norm_num

/-- ★★ **计数与论文公式接上**：`n = 3` 的 ranked 树数 `= H_3`。 -/
theorem card_mergeHistories_three_eq_H : ((mergeHistories 3).card : ℝ) = H 3 := by
  rw [card_mergeHistories_three, H_three]
  norm_num

/-- ★★★ **`1/H_ℓ` 的概率意义**：它等于「每一步在 `C(k,2)` 个可合并对里**均匀**取一对」的
概率之积（Kingman 跳链的有限核，库内 `Coalescent.jumpProb` / `sum_uniform_jumpProb`）。
即：**指定的**一条合并序列（= 一个 ranked 拓扑）的概率恰为 `1/H_ℓ`。 -/
theorem one_div_H_eq_prod_jumpProb (ℓ : ℕ) :
    1 / H ℓ = ∏ k ∈ Finset.range (ℓ - 1), Coalescent.jumpProb (k + 2) := by
  rw [H_eq_prod, one_div,
    show (∏ k ∈ Finset.range (ℓ - 1), Coalescent.jumpProb (k + 2))
        = ∏ k ∈ Finset.range (ℓ - 1), (Coalescent.kingmanRate (k + 2))⁻¹ from
      Finset.prod_congr rfl (fun k _ => by rw [Coalescent.jumpProb_eq_inv_rate, one_div]),
    Finset.prod_inv_distrib]

/-- ★★★ **与库内「根部拓扑概率」接上**：`1/H_3 = 1/3 = MSCProof.rootTopoProb`。

`MSCProof.rootTopoProb` 不是写定的常数：它是跳链均匀权重在「`0,1` 同类」这一拓扑**类**上的
求和（`MSCKingman.root_topology_class_prob`）。这正是论文「根以上次序」因子的内容。 -/
theorem one_div_H_three_eq_rootTopoProb : 1 / H 3 = MSCProof.rootTopoProb := by
  rw [H_three, MSCProof.rootTopoProb_eq_third]

/-! ## §3 `n = 3` 的 ranked 基因树概率（Theorem 1 的实例） -/

/-- 物种树 `((0,1),2)` 下的**一致（concordant）**判据：第一步（**最近**的溯祖）
就把叶 `0`、`1` 合并（第一步时各块都是单点集，故这是字面意义的「0 与 1 先合并」）。 -/
def Concordant3 (f : Fin (3 - 1) → Fin 3 × Fin 3) : Prop := f 0 = (0, 1)

instance : DecidablePred Concordant3 := fun f => by
  unfold Concordant3
  infer_instance

theorem card_concordant3 : ((mergeHistories 3).filter Concordant3).card = 1 := by decide

theorem card_not_concordant3 :
    ((mergeHistories 3).filter (fun f => ¬ Concordant3 f)).card = 2 := by decide

/-- ★★★ **SD2012 Theorem 1（式 (1)）在 `n = 3` 的条件形式**。

物种树 `((0,1),2)`，内部枝长 `t`（溯祖单位）。`b f ℓ` = 「根以下（below the root）
与 `f` 一致、且进入根部时有 `ℓ` 条谱系」的概率 —— 这是 **Theorem 2/3 的输出**，
本文件**不构造**它，而是把它作为**显式前提**（模型口径）给出（规格 §11.2 的要求：
不把模型口径默默当成公理）：

* `ℓ = 2`：叶 `0,1` 必须在内部枝内合并（概率 `1 − e^{−t}` = `firstMergeCDF 2 t`），
  而这**只**与一致的 `f` 相容（否则 `b f 2 = 0`）；
* `ℓ = 3`：内部枝内无合并（概率 `e^{−t}` = `survival 2 t`），与任何 `f` 相容。

**Theorem 1 的求和**（`g_1 = 2`、`H_2 = 1`、`H_3 = 3`）于是等于 MSC 权重：
`(1−x)/1 + x/3 = 1 − ⅔e^{−t}`（一致）与 `x/3 = ⅓e^{−t}`（不一致）。 -/
theorem sd2012_theorem1_n3 (t : ℝ) (b : RankedTree 3 → ℕ → ℝ)
    (h2c : ∀ f : RankedTree 3, Concordant3 f.1 → b f 2 = Coalescent.firstMergeCDF 2 t)
    (h2d : ∀ f : RankedTree 3, ¬ Concordant3 f.1 → b f 2 = 0)
    (h3 : ∀ f : RankedTree 3, b f 3 = Coalescent.survival 2 t) (f : RankedTree 3) :
    (∑ ℓ ∈ Finset.Icc 2 3, b f ℓ / H ℓ)
      = if Concordant3 f.1 then MSCProof.mscConcordant t else MSCProof.mscDiscordant t := by
  have hIcc : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := by decide
  rw [hIcc, Finset.sum_pair (by norm_num : (2 : ℕ) ≠ 3), H_two, H_three]
  by_cases hc : Concordant3 f.1
  · simp only [hc, ↓reduceIte]
    rw [h2c f hc, h3 f, MSCProof.mscConcordant_closed, Coalescent.firstMergeCDF_two,
      Coalescent.survival_two]
    ring
  · simp only [hc, ↓reduceIte]
    rw [h2d f hc, h3 f, MSCProof.mscDiscordant_eq, Coalescent.pDiscordant_eq_survival,
      Coalescent.survival_two]
    ring

/-- ★★★ **`n = 3` 的 ranked 概率**：Theorem 1 的式 (1)，模型输入用库内的
`Coalescent.firstMergeCDF`（`= 1 − e^{−t}`）与 `Coalescent.survival`（`= e^{−t}`）填好。
（等价于把 `sd2012_theorem1_n3` 的 `b` 取成 `belowRoot3`。） -/
noncomputable def rankedProb3 (t : ℝ) (f : Fin (3 - 1) → Fin 3 × Fin 3) : ℝ :=
  (if Concordant3 f then Coalescent.firstMergeCDF 2 t else 0) / H 2
    + Coalescent.survival 2 t / H 3

/-- ★★★ `rankedProb3` 就是 MSC 权重：一致 `1 − ⅔e^{−t}`、不一致 `⅓e^{−t}`。 -/
theorem rankedProb3_eq (t : ℝ) (f : Fin (3 - 1) → Fin 3 × Fin 3) :
    rankedProb3 t f
      = if Concordant3 f then MSCProof.mscConcordant t else MSCProof.mscDiscordant t := by
  by_cases hc : Concordant3 f
  · simp only [rankedProb3, hc, ↓reduceIte, H_two, H_three, MSCProof.mscConcordant_closed,
      Coalescent.firstMergeCDF_two, Coalescent.survival_two]
    ring
  · simp only [rankedProb3, hc, ↓reduceIte, H_two, H_three, MSCProof.mscDiscordant_eq,
      Coalescent.pDiscordant_eq_survival, Coalescent.survival_two]
    ring

theorem rankedProb3_nonneg (t : ℝ) (ht : 0 ≤ t) (f : Fin (3 - 1) → Fin 3 × Fin 3) :
    0 ≤ rankedProb3 t f := by
  rw [rankedProb3_eq]
  by_cases hc : Concordant3 f
  · simp only [hc, ↓reduceIte]
    exact MSCProof.mscConcordant_nonneg ht
  · simp only [hc, ↓reduceIte]
    exact (MSCProof.mscDiscordant_pos t).le

/-- ★★★ **归一化（`n = 3`）**：三个 ranked 基因树的概率和 `= 1`。 -/
theorem rankedProb3_sum_one (t : ℝ) :
    (∑ f ∈ mergeHistories 3,
        (if Concordant3 f then MSCProof.mscConcordant t else MSCProof.mscDiscordant t)) = 1 := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := mergeHistories 3) (p := Concordant3)
    (f := fun f => if Concordant3 f then MSCProof.mscConcordant t else MSCProof.mscDiscordant t)]
  have h1 : (∑ f ∈ (mergeHistories 3).filter Concordant3,
      (if Concordant3 f then MSCProof.mscConcordant t else MSCProof.mscDiscordant t))
      = ((mergeHistories 3).filter Concordant3).card * MSCProof.mscConcordant t := by
    calc (∑ f ∈ (mergeHistories 3).filter Concordant3,
          (if Concordant3 f then MSCProof.mscConcordant t else MSCProof.mscDiscordant t))
        = ∑ _f ∈ (mergeHistories 3).filter Concordant3, MSCProof.mscConcordant t := by
          refine Finset.sum_congr rfl ?_
          intro f hf
          rw [Finset.mem_filter] at hf
          simp only [hf.2, ↓reduceIte]
      _ = ((mergeHistories 3).filter Concordant3).card * MSCProof.mscConcordant t := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : (∑ f ∈ (mergeHistories 3).filter (fun f => ¬ Concordant3 f),
      (if Concordant3 f then MSCProof.mscConcordant t else MSCProof.mscDiscordant t))
      = ((mergeHistories 3).filter (fun f => ¬ Concordant3 f)).card * MSCProof.mscDiscordant t := by
    calc (∑ f ∈ (mergeHistories 3).filter (fun f => ¬ Concordant3 f),
          (if Concordant3 f then MSCProof.mscConcordant t else MSCProof.mscDiscordant t))
        = ∑ _f ∈ (mergeHistories 3).filter (fun f => ¬ Concordant3 f),
            MSCProof.mscDiscordant t := by
          refine Finset.sum_congr rfl ?_
          intro f hf
          rw [Finset.mem_filter] at hf
          simp only [hf.2, ↓reduceIte]
      _ = ((mergeHistories 3).filter (fun f => ¬ Concordant3 f)).card
            * MSCProof.mscDiscordant t := by
          rw [Finset.sum_const, nsmul_eq_mul]
  rw [h1, h2, card_concordant3, card_not_concordant3]
  push_cast
  linarith [MSCProof.mscConcordant_add_two t]

/-- ★★ `rankedProb3` 与 `sd2012_theorem1_n3` 同源：把模型输入取成
`b f 2 = (if Concordant3 f then firstMergeCDF 2 t else 0)`、`b f 3 = survival 2 t`，
Theorem 1 的求和就是 `rankedProb3`（`rankedProb3` 正是把这个求和展开了）。 -/
theorem rankedProb3_eq_theorem1_sum (t : ℝ) (f : Fin (3 - 1) → Fin 3 × Fin 3) :
    rankedProb3 t f
      = (if Concordant3 f then Coalescent.firstMergeCDF 2 t else 0) / H 2
        + Coalescent.survival 2 t / H 3 := rfl

/-! ## §4 Theorem 3 的算术核（式 (4)） -/

/-- SD2012 式 (4) 的形状：`Σ_{j=0}^{m} e^{−λ_j s}/∏_{k≠j}(λ_k − λ_j)`。
（论文里 `λ_{i,j} = Σ_z C(k_{i,j,z},2)`，`m = m_i`；本文件只把它当作**算术形状**用。） -/
noncomputable def eq4 (m : ℕ) (s : ℝ) (lam : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    Real.exp (-(lam j) * s) / ∏ k ∈ (Finset.range (m + 1)).erase j, (lam k - lam j)

/-- ★★ **论文自算的例子**（PDF 第 **385–413** 行）：`λ = (0,1,2)`、`m = 2` 时式 (4) 给出
`1/2 − e^{−s} + e^{−2s}/2 = (1 − e^{−s})²/2 = [g_{2,1}(s)]²/2`，
其中 `g_{2,1}(s) = Coalescent.firstMergeCDF 2 s`（两条谱系在时间 `s` 内合并的概率）。

这与论文用**另一条路线**得到的 `[g_{2,1}(s_2 − s_3)]²/2`（PDF 第 **380** 行）一致。 -/
theorem sd2012_eq4_example (s : ℝ) :
    Real.exp 0 / ((2 - (0 : ℝ)) * (1 - 0)) + Real.exp (-(1 : ℝ) * s) / ((0 - 1) * (2 - 1))
        + Real.exp (-(2 : ℝ) * s) / ((0 - 2) * (1 - 2))
      = (1 / 2) * (Coalescent.firstMergeCDF 2 s) ^ 2 := by
  have h2 : Real.exp (-(2 : ℝ) * s) = Real.exp (-s) ^ 2 := by
    rw [show -(2 : ℝ) * s = -s + -s by ring, Real.exp_add, pow_two]
  have h1 : -(1 : ℝ) * s = -s := by ring
  rw [h2, h1, Real.exp_zero, Coalescent.firstMergeCDF_two]
  ring

/-- ★ **式 (4) 在 `m = 1` 的一般 `λ`**：两条竞争指数的部分分式恒等式（纯代数，
故**没有**概率内容，只是式 (4) 的算术形状在 `m = 1` 的核对）。 -/
theorem eq4_one_general (s lam0 lam1 : ℝ) (h : lam1 ≠ lam0) :
    Real.exp (-lam0 * s) / (lam1 - lam0) + Real.exp (-lam1 * s) / (lam0 - lam1)
      = (Real.exp (-lam0 * s) - Real.exp (-lam1 * s)) / (lam1 - lam0) := by
  field_simp
  ring

/-- ★★ **论文自算的例子按 `eq4` 定义本身**（`λ_j = j`、`m = 2`）：
`eq4 2 s (j ↦ j) = (1/2)(1 − e^{−s})²` —— 与 `sd2012_eq4_example` 是同一个式子，
但这里**直接展开 `eq4` 的定义**（故 `eq4` 不是空定义）。 -/
theorem eq4_two_uniform_rates (s : ℝ) :
    eq4 2 s (fun j => (j : ℝ)) = (1 / 2) * (Coalescent.firstMergeCDF 2 s) ^ 2 := by
  rw [eq4, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  rw [show (Finset.range 3).erase 0 = ({1, 2} : Finset ℕ) from by decide,
    show (Finset.range 3).erase 1 = ({0, 2} : Finset ℕ) from by decide,
    show (Finset.range 3).erase 2 = ({0, 1} : Finset ℕ) from by decide,
    Finset.prod_pair (by norm_num : (1 : ℕ) ≠ 2),
    Finset.prod_pair (by norm_num : (0 : ℕ) ≠ 2),
    Finset.prod_pair (by norm_num : (0 : ℕ) ≠ 1)]
  norm_num
  rw [show Real.exp (-(2 * s)) = Real.exp (-s) ^ 2 by
        rw [show -(2 * s) = -s + -s by ring, Real.exp_add, pow_two],
      Coalescent.firstMergeCDF_two]
  ring

set_option maxHeartbeats 2000000 in
/-- ★★ **`n = 3`：两个口径的连接**（在 `mergeHistories 3` 内）
「叶 `0,1` 先合并」⟺「忘掉次序后的拓扑就是 `((0,1),2)`」。 -/
theorem concordant3_iff_clades : ∀ f : Fin (3 - 1) → Fin 3 × Fin 3,
    IsMergeHistory 3 f → (Concordant3 f ↔ cladesOf 3 f = clades_01_2) := by
  decide

/-! ## §5 诚实边界：显式缺口（`def … : Prop`，**不是** `axiom`，也**不是** `sorry`） -/

/-- ❌ **缺口 G1（计数，一般 `n`）**：`n` 个叶上的 ranked 树数 `= H_n`。

本文件只用 `decide` **枚举**验证了 `n = 2, 3, 4`（`1, 3, 18`），
并给出 `card_mergeHistories_four_eq_H`；一般 `n` 的归纳（「每一步合并两块」的递归计数）
**未证**。 -/
def rankedTree_card_gap : Prop := ∀ n : ℕ, 2 ≤ n → ((mergeHistories n).card : ℝ) = H n

/-- ❌ **缺口 G2（论文 Remark 6，PDF 第 416–424 行）**：给定无次序拓扑的 ranking 数
`= (n−1)!/∏_{c ∈ clades, c.card ≥ 2} (c.card − 1)`（内部顶点 ↔ 大小 `≥ 2` 的 clade）。

本文件在 Lean 内验证了 `n = 3` 与 `n = 4` 的两个实例（`card_rankings_01_2` /
`card_rankings_01_23` / `card_rankings_012_3`），一般 `n` **未证**；
`scripts/msc/stadler_degnan_ranked.py` 对 `n ≤ 7` 穷举核对过。

⚠️ 顺带记录：**任务书 §11.3 建议的「给定拓扑下 ranked 树恰有 `(n−1)!` 个」是错的**
（`n = 3` 已经反例：纤维数 `1 ≠ 2`）—— 请看 §0 冒烟测试第 3 条。 -/
def rankedFiberCount_gap : Prop :=
  ∀ (n : ℕ) (f : Fin (n - 1) → Fin n × Fin n), IsMergeHistory n f →
    ((mergeHistories n).filter (fun g => cladesOf n g = cladesOf n f)).card
      = (n - 1).factorial
        / ∏ C ∈ (cladesOf n f).filter (fun C => 2 ≤ C.card), (C.card - 1)

/-- ❌ **缺口 G3（Theorem 3 式 (4) 在 `λ_j = j` 的一般 `m`）**：
`Σ_{j=0}^{m} e^{−js}/∏_{k≠j}(k − j) = (1/m!)(1 − e^{−s})^m`。

本文件只证了 `m = 2`、`λ = (0,1,2)`（`sd2012_eq4_example` 与按 `eq4` 定义展开的
`eq4_two_uniform_rates`）与 `m = 1` 的**一般** `λ`（`eq4_one_general`，纯代数）；
`λ_j = j` 的一般 `m ≤ 8` 由脚本用二项式定理**精确**核对。 -/
def sd2012_eq4_uniform_rates_gap : Prop :=
  ∀ (m : ℕ) (s : ℝ),
    eq4 m s (fun j => (j : ℝ)) = (1 / (m.factorial : ℝ)) * (1 - Real.exp (-s)) ^ m

/-- ❌ **缺口 G4（`n = 4` 的 ranked 概率表 + 与非 ranked MSC 权重的边缘化一致性）**：
存在 `Fin 4` 上 `18` 个 ranked 树的概率表 `p`，非负、总和 `1`，
且「平衡形拓扑 `((0,1),(2,3))` 的两个 ranking 的概率之和 = 无次序 MSC 权重
`mscConcordant t`」。

⚠️ 本断言的强度：它**只有**「存在 + 边缘化」两部分，**没有**给出 SD2012 的**递推算法**
（Theorem 2/3）；本文件**既没有构造 `p`、也没有证明**这个命题。 -/
def ranked4_probability_gap : Prop :=
  ∀ t : ℝ, 0 < t → ∃ p : (Fin (4 - 1) → Fin 4 × Fin 4) → ℝ,
    (∀ f, IsMergeHistory 4 f → 0 ≤ p f) ∧
      (∑ f ∈ mergeHistories 4, p f) = 1 ∧
      (∑ f ∈ (mergeHistories 4).filter (fun f => cladesOf 4 f = clades_01_23), p f)
        = MSCProof.mscConcordant t

end Phylo.Stat.RankedGeneTree
