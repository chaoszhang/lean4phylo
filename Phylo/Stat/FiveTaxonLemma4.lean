/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CoalescentHistoryCount

/-!
# `Phylo.Stat.FiveTaxonLemma4` —— ADR2011 **Lemma 4**：5 taxa 时 15 个无根拓扑等概率

文献：E. S. Allman, J. H. Degnan, J. A. Rhodes, *Identifying the rooted species tree from the
distribution of unrooted gene trees*, J. Math. Biol. **62** (2011) 833–862。
引用一律用 `references/md/AllmanDegnanRhodes2011_IdentifyingRootedSpeciesTree.md` 的**行号**定位。

## §0 文献原文（**逐字抄录**，md 第 962–974 行）

> **Lemma 4** If all coalescent events occur above the root (temporally before the MRCA
> of all species) of a 5-taxon species tree, then all 15 of the unrooted topological gene trees
> are equally likely.
>
> **Proof** If all coalescent events occur above the root, then regardless of the species tree,
> we are considering five labeled lineages entering the ancestral population, and then
> coalescing. Because all unrooted gene trees have the same unlabeled shape, all coalescent
> histories leading to one gene tree correspond to equally likely coalescent histories
> producing another, by simply relabeling lineages.  ⊓⊔
>
> Note that the claim of this lemma is special to five taxa. For six taxa, with two different
> unrooted gene tree shapes possible, the analogous statement is not true.

（第 **962–964** 行 = 陈述，第 **966–971** 行 = Proof，第 **973–974** 行 = 紧接其后的「5 taxa 特殊性」
注记。原文的 `coales-cent` 是排版断词，此处按整词 `coalescent` 抄录；`⊓⊔` 是 QED 符号。）

## §1 本文件的数学内容

「所有溯祖事件都发生在根以上」= 基因树完全不依赖物种树，5 条带标记的谱系直接进入祖先种群后
按 Kingman 跳链合并 ⇒ **每条合并史（ranked 树）的概率只依赖步数**：第 `k` 步在 `C(k,2)` 个
可合并对中**均匀**取一对，故

* `P(一个合并史) = ∏_{k=2}^{5} 1/C(k,2) = 1/H_5 = 1/180`
  —— 库内已有 `RankedGeneTree.one_div_H_eq_prod_jumpProb`，本文件给出 `one_div_H_five`；
* 合并史总数 `= H_5 = 180`（`card_mergeHistories_five`）；
* **无根**拓扑（分裂集）恰 `15` 个（`card_unrootedTopo_five`），
  且**每个**无根拓扑的纤维（能产生它的合并史条数）**都等于 `12 = 180/15`**
  （`fiber_uniform_five`）⇒ `P(每个无根拓扑) = 12/180 = 1/15`（`lemma4_five_prob`）。

这就是 Lemma 4。主定理 `lemma4_five` 是纤维相等；`lemma4_five_prob` 是概率版 `= 1/15`。

## §2 「无根拓扑」的定义（`topoOf`：忘掉次序与根）

1. **忘掉次序**：库内的 `cladesOf n f` 把合并史映到 clade 集（= 无次序的**有根**拓扑）；
   `topoOf` 只经由 `cladesOf` 取值（`topoOf_congr`：同一个 clade 集映到同一个分裂集）；
2. **忘掉根**：取 clade 集里 `2 ≤ |C| ≤ n−2` 的 `C`（= 根以下的内部顶点，**两支都非单点**），
   映成**分裂**（bipartition）`{C, Cᶜ}`（互补的两支视为**同一个**分裂，故根的两个孩子的
   clade 自动合并成一个分裂）。⚠️ 上界必须是 `n−2` 而**不是** `n−1`：`|C| = n−1` 给出
   `C` 与单点 `w` 的二分，那是叶 `w` 的**悬垂边**而不是内部边 —— 用 `n−1` 时 `n = 5` 会得到
   `90` 个伪拓扑（见 `scripts/msc/w10_lemma4_five.py`，本文件第一版就踩过这个坑）。
   ⚠️ `cladesOf` 本身是**有根**信息，绝不能直接当作无根拓扑（`n = 4` 时有根拓扑 `15` 个、
   无根只有 `3` 个）。

于是 `topoOf n f : Finset (Finset (Finset (Fin n)))` —— 「拓扑 = 分裂的集合，分裂 = 两个互补
叶集的集合」。`n = 5` 时每个无根拓扑恰有 `2` 条内部边（`5−3 = 2`）的分裂。

## §3 证明路线与**计算口径**（⚠️ 本文件**零 `native_decide` / 零新公理**）

本文件把原文「relabeling lineages 把纤维映成纤维、`S_5` 在 15 个无根拓扑上传递」这一句
**直接落成有限组合恒等式**：`fiber_values_five` 说「全部无根拓扑的纤维值集合 `= {12}`」。

**为什么不走抽象置换路线**：`RankedGeneTree` 的合并史编码以**块的最小元**为代表
（`IsStep` 的 `r x = x`），而换标号 `σ` **不保持**「最小元」这一角色
（`σ(min B) ≠ min(σ(B))`），故 `σ • f` 一般**不是**合法合并史（`n = 3`、`σ = (0 1)`、
`f = [(0,1),(0,2)]` 就是反例：朴素换标号后在 `IsStep` 上失败）。这条抽象引理**本文件没有证**
（见 §5），改用**有限枚举**：`S_5` 的作用在枚举层被绕开，直接核验 15 个纤维全 `= 12`。

**为什么必须换枚举口径**：`RankedGeneTree.mergeHistories n` 是
`(Finset.univ : Finset (Fin (n-1) → Fin n × Fin n)).filter (IsMergeHistory n ·)` ——
`n = 5` 时是全空间 `25^4 = 390625` 个候选。内核 `decide` 在这个规模上**实测不可行**
（本机 WSL 7.9 GB RAM）：

| 测量 | 候选数 | 结果 |
|---|---|---|
| `(mergeHistories 5).card = 180`（`decide`，整空间） | `390625` | **OOM**：`exit 137`、`MAXRSS 7.24 GB`、`675 s` |
| 按第一对劈块 `piece (0,1)`/`piece (1,0)` 两条 `decide` | `2 × 15625` | 成功但 `505 s` / `MAXRSS 6.67 GB` |
| 扁平枚举（`Fin (25^3)` + `finFunctionFinEquiv`，绕开函数类型 `Finset.univ`） | `15625` | **OOM**：`exit 137`、`MAXRSS 7.51 GB` |

即：内核求值的内存 ≈ 「候选数 × `0.2–0.4 MB`」，`7.9 GB` 只允许约 `1.5×10^4` 个候选，
而 `n = 5` 的整空间是它的 `25` 倍（扁平化也救不了 ⇒ 瓶颈是**每候选的内核分配**）。

**本文件的做法（route ①：只枚举合法历史）**：✓ 合法历史只有 `H_n` 条，而「下一步能合并哪两个块」
由**当前块代表集合 `s`** 完全决定。故定义**递归生成器** `genMH N m s`：从 `s`（`|s| = m+1`）
出发，每步只对 `s` 里的**合法有序对** `PairIn N s`（`x < y`）分支，递归到 `|s| = 1`。
`n = 5` 的搜索树只有 `C(5,2)·C(4,2)·C(3,2)·C(2,2) = 10·6·3·1 = 180` 个叶子，
故 `decide` 在内核里**可行**（实测：整文件 `~170 s`、`MAXRSS ~6.5–6.9 GB`、`exit 0`、输出 0 字节）。

生成器的**忠实性**由 `mem_genMH`（`s.card = m+1` 时 `genMH N m s` 恰是 `s` 上的全部
`IsMH` 历史）给出，它用 `Phylo/Stat/CoalescentHistoryCount.lean`（**另一个 agent 交付**）的
头尾分解引理 `isMH_head` / `isMH_tail` 证明；再经 `isMH_univ_iff` 与库内编码接上
（`mergeHistories_five_eq_genMH`）。**交叉核对**：`card_mergeHistories_five`（生成器枚举）
与 `card_mergeHistories_five_via_induction`（引用 `CoalescentHistoryCount` 的归纳法一般 `n` 定理）
是同一个 `180` 的**两条独立内核证明**。

## §4 数值/穷举复核（`scripts/msc/w10_lemma4_five.py`，整数 + 精确有理数，无 Monte Carlo）

脚本**逐字复刻**本库的编码（`stepMap`/`chainMap`/`IsStep`/`IsMergeHistory`/`blocksOf`/`cladesOf`）
与 `topoOf`，独立核对（47 条 `[ok]`、0 条 FAIL）：

* `|RankedTree n| = H_n`（`n ≤ 6`：`1,1,3,18,180,2700`）与递推 `|RankedTree n| = C(n,2)·|RankedTree (n−1)|`；
* 无根拓扑数 `= (2n−5)!!`（`n = 4,5,6` 时 `3, 15, 105`），每个拓扑恰 `n−3` 条内部边；
* `n = 5`：`180` 条合并史、`15` 个无根拓扑、**每个纤维 `= 12`**、每个概率 `= 1/15`、概率和 `= 1`；
* `n = 4`：无根拓扑 `3` 个、纤维全 `6`（对照**有根** clade 集的纤维 `1 / 2`，说明有根 ≠ 无根）；
* **独立第三条路线**：SD2012 Remark 6 的 `(n−1)!/∏(c_i−1)`（有根拓扑的 ranking 数）
  与穷举的 `105` 个有根拓扑纤维**逐条相等**；固定一个无根拓扑，其 `7` 个根位置
  （`2` 条内部边 + `5` 条悬垂边）的 ranking 数多重集 `= (1,1,1,1,2,3,3)`、和为 `12`，
  且**这 7 个数对 15 个无根拓扑完全相同** —— 这正是原文 "all unrooted gene trees have the same
  unlabeled shape" 那句话的代数内容；
* 按第一对 `(x,y)` 分块：`10` 个合法首对、每块 `18` 条（非法首对 `0` 条）；
  每块给出 `3` 个拓扑 × `6` 条、每个无根拓扑恰被 `2` 块覆盖（`10 · 3 · 6 = 180 = 15 · 12`）；
* **反例边界**（原文第 973–974 行）：`n = 6` 的纤维分布 `{24: 90, 36: 15}` **不均匀**
  （`90·24 + 15·36 = 2700 = H_6`）⇒ Lemma 4 **确实只对 5 taxa 成立**。

## §5 诚实边界（**没做到的**，逐条）

| 条目 | 状态 |
|---|---|
| ★★★ **Lemma 4（主目标，`n = 5`）** | ✅ **已证**（`lemma4_five`；`fiber_uniform_five` 给出每个纤维 `= 12`）—— **纯内核** |
| ★★ 降级 1：`(mergeHistories 5).card = 180` | ✅ **已证**（`card_mergeHistories_five`，生成器枚举 `decide`）—— **纯内核**，另有归纳法交叉核对 |
| ★★ 降级 2：无根拓扑数 `= 15` | ✅ **已证**（`card_unrootedTopo_five`，生成器枚举 `decide`）—— **纯内核** |
| ★★ 降级 3：纤维相等（都 `= 12`） | ✅ **已证**（`fiber_uniform_five`，由 `fiber_values_five` 的生成器枚举推出）—— **纯内核** |
| ★ 降级 4：概率版 `P(T) = 1/15` | ✅ **已证**（`lemma4_five_prob` + `lemma4_five_prob_sum`）—— **纯内核** |
| 一般 `n` 的 `\|RankedTree n\| = H_n`（缺口 `rankedTree_card_gap`） | ✅ **已由另一文件证出**（`Phylo.Stat.CoalescentHistoryCount.card_mergeHistories_eq_H`，纯内核；本文件的 `card_mergeHistories_five_eq_H` 引用它）—— **本文件不重复证** |
| **整空间** `decide`（`mergeHistories n` 直接枚举） | ❌ **不可行**（见 §3 的三次 OOM 实测）—— 本文件用 `genMH` 绕开 |
| 「`σ • f` 仍是合法合并史」的**抽象置换引理** | ❌ **未证**（编码障碍见 §3；`S_5` 传递性因此没有单独形式化） |
| 任务书要求的「`S_5` 在 15 个无根拓扑上传递」 | ❌ **未单独形式化**（被 `fiber_values_five` 的枚举直接取代） |
| 测度层随机变量 | ❌ **无**（与 `Coalescent.lean` / `MSCProof.lean` 同处**实数层**概率） |
| Lemma 4 的一般 `n` 推广 | ❌ **不成立**（论文第 973–974 行自己指出；脚本给出 `n = 6` 的反例分布） |
-/

namespace Phylo.Stat.FiveTaxonLemma4

open Phylo.Stat.RankedGeneTree

/-! ## §1 无根拓扑（分裂集） -/

/-- 一个 clade `C` 给出的**分裂** `{C, Cᶜ}`：互补的两支视为**同一个**分裂。 -/
def splitOfClade {n : ℕ} (C : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  {C, (Finset.univ : Finset (Fin n)) \ C}

/-- ★★ **「忘掉根」**：把**有根**的 clade 集变成**无根**的分裂集。

只取满足 `2 ≤ |C| ≤ n−2` 的 clade（= 根以下的内部顶点，且**两支都非单点**）。
⚠️ 上界不能放宽到 `n−1`：`|C| = n−1` 的 clade 给出 `C` 与单点 `w` 的二分，
那是叶 `w` 的**悬垂边**而不是内部边（`n = 5` 时这个错会给出 `90` 个伪拓扑）。 -/
def splitsOfClades (n : ℕ) (Cl : Finset (Finset (Fin n))) : Finset (Finset (Finset (Fin n))) :=
  (Cl.filter (fun C => 2 ≤ C.card ∧ C.card ≤ n - 2)).image (fun C => splitOfClade C)

/-- ★★★ **无根拓扑**（`n` taxa）：`cladesOf`（忘掉次序）之后再 `splitsOfClades`（忘掉根）。 -/
def topoOf (n : ℕ) (f : Fin (n - 1) → Fin n × Fin n) : Finset (Finset (Finset (Fin n))) :=
  splitsOfClades n (cladesOf n f)

/-- `topoOf` **只依赖** clade 集：这就是「忘掉次序」（同一无次序拓扑的不同 ranking
映到同一个无根拓扑）。 -/
theorem topoOf_congr (n : ℕ) {f g : Fin (n - 1) → Fin n × Fin n}
    (h : cladesOf n f = cladesOf n g) : topoOf n f = topoOf n g := by
  rw [topoOf, topoOf, h]

/-- `n = 5` 的无根拓扑映射。 -/
def topo5 (f : Fin (5 - 1) → Fin 5 × Fin 5) : Finset (Finset (Finset (Fin 5))) := topoOf 5 f

/-- ★★★ **5 taxa 的无根拓扑类型**：出现过的分裂集（= `(mergeHistories 5).image (topoOf 5)`
的元素）。⚠️ 取成 `image` 的子类型而不是 `Finset (Finset (Finset (Fin 5)))` 本身，
是因为后者作为 `Fintype` 有 `2^(2^5) = 2^32` 个元素（任何对全空间的 `decide` 都会立刻爆炸）。 -/
abbrev UnrootedTopology5 : Type :=
  {T : Finset (Finset (Finset (Fin 5))) // T ∈ (mergeHistories 5).image (topoOf 5)}

/-- `H_5 = 180 = 10 · 6 · 3 · 1`（`H` 的递推 + 库内 `H_four = 18`）。 -/
theorem H_five : H 5 = 180 := by
  rw [H_succ_eq 4 (by norm_num), H_four]
  norm_num [Coalescent.kingmanRate]

/-- 「一条合并史的概率 = `1/H_5`」的跳链形式：`1/H_5 = ∏_{k=2}^{5} 1/C(k,2)`。 -/
theorem one_div_H_five :
    1 / H 5 = ∏ k ∈ Finset.range (5 - 1), Coalescent.jumpProb (k + 2) :=
  one_div_H_eq_prod_jumpProb 5

/-! ## §2 内核 `decide` 的小规模交叉核对（`n = 3, 4`，同一套定义） -/

set_option maxRecDepth 1000000 in
/-- `n = 3`：无根拓扑恰 `1` 个（`(2·3−5)!! = 1`）。 -/
theorem card_unrootedTopo_three : ((mergeHistories 3).image (topoOf 3)).card = 1 := by decide

set_option maxRecDepth 1000000 in
/-- `n = 3`：纤维全 `= 3 = H_3/1`。 -/
theorem fiber_uniform_three :
    ((mergeHistories 3).image (topoOf 3)).image
      (fun T => ((mergeHistories 3).filter (fun f => topoOf 3 f = T)).card) = {3} := by decide

set_option maxRecDepth 1000000 in
/-- `n = 4`：**无根**拓扑恰 `3` 个（`(2·4−5)!! = 3`；对照 `card_topologies_four = 15`
是**有根** clade 集的个数）。 -/
theorem card_unrootedTopo_four : ((mergeHistories 4).image (topoOf 4)).card = 3 := by decide

set_option maxRecDepth 1000000 in
/-- `n = 4`：无根纤维全 `= 6 = 18/3`。 -/
theorem fiber_uniform_four :
    ((mergeHistories 4).image (topoOf 4)).image
      (fun T => ((mergeHistories 4).filter (fun f => topoOf 4 f = T)).card) = {6} := by decide

/-! ## §3 递归生成器：只枚举**合法**历史（route ①） -/

/-- ★★★ **递归生成器**：从「当前块代表集合 `s`（`s.card = m+1`）」出发，每步只对 `s` 里的
合法有序对（`PairIn`，即 `x < y`）分支，生成 `s` 上 `m` 步合并史。

与 `CoalescentHistoryCount.mhFinset`（对 `Fin m → Fin N × Fin N` **全空间**过滤，
`n = 5` 时 `25^4 = 390625` 个候选）不同，本函数的分支因子是 `C(|s|,2)`，故 `n = 5` 的搜索树
只有 `10 · 6 · 3 · 1 = 180` 个叶子 —— 内核 `decide` 因此可行（这就是本文件
**不用 `native_decide`**、零新公理的原因）。 -/
def genMH (N : ℕ) : (m : ℕ) → Finset (Fin N) → Finset (Fin m → Fin N × Fin N)
  | 0, s => if s.card = 1 then Finset.univ else ∅
  | (m + 1), s =>
      (Finset.univ : Finset (Phylo.Stat.CoalescentHistoryCount.PairIn N s)).biUnion (fun p =>
        (genMH N m (s.erase (p.1).2)).image
          (fun g => Fin.cons (α := fun _ => Fin N × Fin N) p.1 g))

theorem genMH_zero (N : ℕ) (s : Finset (Fin N)) :
    genMH N 0 s = if s.card = 1 then (Finset.univ : Finset (Fin 0 → Fin N × Fin N)) else ∅ :=
  rfl

theorem genMH_succ (N m : ℕ) (s : Finset (Fin N)) :
    genMH N (m + 1) s =
      (Finset.univ : Finset (Phylo.Stat.CoalescentHistoryCount.PairIn N s)).biUnion (fun p =>
        (genMH N m (s.erase (p.1).2)).image
          (fun g => Fin.cons (α := fun _ => Fin N × Fin N) p.1 g)) :=
  rfl

/-- 0 步的历史：`s.card ≤ 1` 时恒合法（`gchain … 0 = id`）。 -/
theorem isMH_zero {N : ℕ} {s : Finset (Fin N)}
    (hs : s.card ≤ 1) (f : Fin 0 → Fin N × Fin N) :
    Phylo.Stat.CoalescentHistoryCount.IsMH s 0 f := by
  refine ⟨?_, ?_, ?_⟩
  · intro k; exact Fin.elim0 k
  · intro k; exact Fin.elim0 k
  · intro w hw w' hw'
    simp only [Phylo.Stat.CoalescentHistoryCount.gchain_zero]
    exact Finset.card_le_one.mp hs w hw w' hw'

/-- ★★★ **生成器正确性**：`s.card = m+1` 时，`genMH` 生成的恰是 `s` 上的全部合法历史
（`IsMH`）。归纳步用 `CoalescentHistoryCount.isMH_head` / `isMH_tail`。 -/
theorem mem_genMH : ∀ (m : ℕ) (N : ℕ) (s : Finset (Fin N)), s.card = m + 1 →
    ∀ f : Fin m → Fin N × Fin N,
      f ∈ genMH N m s ↔ Phylo.Stat.CoalescentHistoryCount.IsMH s m f := by
  intro m
  induction m with
  | zero =>
    intro N s hs f
    have h1 : s.card = 1 := hs
    rw [genMH_zero]
    simp only [h1, ↓reduceIte]
    exact ⟨fun _ => isMH_zero (le_of_eq h1) f, fun _ => Finset.mem_univ f⟩
  | succ m ih =>
    intro N s hs f
    rw [genMH_succ, Finset.mem_biUnion]
    simp only [Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨p, g, hg, rfl⟩
      have hpe : (s.erase (p.1).2).card = m + 1 := by
        rw [Finset.card_erase_of_mem p.2.2.1]; omega
      have hg' := (ih N (s.erase (p.1).2) hpe g).mp hg
      refine Phylo.Stat.CoalescentHistoryCount.isMH_head
        (f := Fin.cons (α := fun _ => Fin N × Fin N) p.1 g) ?_ p.2.1 p.2.2.1 p.2.2.2
      rw [Fin.cons_zero, Fin.tail_cons]
      exact hg'
    · intro hf
      have hmem := hf.1
      have hstep := hf.2.1
      refine ⟨⟨f 0, (hmem 0).1, (hmem 0).2, (hstep 0).2.2⟩, Fin.tail f, ?_, ?_⟩
      · have hpe : (s.erase (f 0).2).card = m + 1 := by
          rw [Finset.card_erase_of_mem (hmem 0).2]; omega
        exact (ih N (s.erase (f 0).2) hpe (Fin.tail f)).mpr
          (Phylo.Stat.CoalescentHistoryCount.isMH_tail hf)
      · exact Phylo.Stat.CoalescentHistoryCount.cons_tail f

set_option maxRecDepth 1000000 in
/-- ★★★ **桥**：库内的 `mergeHistories 5` 就是生成器在 `univ : Finset (Fin 5)` 上的输出
（经 `mem_genMH` + 库内编码的 `IsMH` 形式 `isMH_univ_iff`）。 -/
theorem mergeHistories_five_eq_genMH :
    mergeHistories 5 = genMH 5 4 (Finset.univ : Finset (Fin 5)) := by
  ext f
  rw [mem_mergeHistories,
    mem_genMH 4 5 (Finset.univ : Finset (Fin 5)) (by decide) f,
    Phylo.Stat.CoalescentHistoryCount.isMH_univ_iff 5 f]

/-! ## §4 5 taxa 的计数（**全部内核 `decide`**，零 `native_decide`） -/

section DecideFive

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- ★★★ **降级 1**：5 taxa 的合并史（ranked 基因树）恰 `180 = H_5` 条
（缺口 `rankedTree_card_gap` 的 `n = 5` 实例；生成器枚举，内核 `decide`）。 -/
theorem card_mergeHistories_five : (mergeHistories 5).card = 180 := by
  rw [mergeHistories_five_eq_genMH]
  decide

/-- ★★ **交叉核对**：同一个 `180` 的另一条**独立内核证明** —— 引用
`Phylo.Stat.CoalescentHistoryCount.card_mergeHistories_five`（一般 `n` 的归纳法定理导出）。 -/
theorem card_mergeHistories_five_via_induction : (mergeHistories 5).card = 180 :=
  Phylo.Stat.CoalescentHistoryCount.card_mergeHistories_five

/-- ★★★ **降级 2**：5 taxa 的**无根**拓扑恰 `15` 个（`(2·5−5)!! = 15`，与 Lemma 4 的 `15` 一致）。 -/
theorem card_unrootedTopo_five : ((mergeHistories 5).image (topoOf 5)).card = 15 := by
  rw [mergeHistories_five_eq_genMH]
  decide

/-- ★★★ **降级 3（Lemma 4 的计数核心）**：全部无根拓扑的**纤维值集合** `= {12}`
—— 即每个无根拓扑的纤维都等于 `12 = 180/15`（生成器枚举，内核 `decide`）。 -/
theorem fiber_values_five :
    ((mergeHistories 5).image (topoOf 5)).image
      (fun T => ((mergeHistories 5).filter (fun f => topoOf 5 f = T)).card) = {12} := by
  rw [mergeHistories_five_eq_genMH]
  decide

end DecideFive

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- ★★★ **每个无根拓扑的纤维 `= 12`**（`fiber_values_five` 的逐点形式）。 -/
theorem fiber_uniform_five (T : Finset (Finset (Finset (Fin 5))))
    (hT : T ∈ (mergeHistories 5).image (topoOf 5)) :
    ((mergeHistories 5).filter (fun f => topoOf 5 f = T)).card = 12 := by
  have h := Finset.mem_image_of_mem
    (s := (mergeHistories 5).image (topoOf 5))
    (f := fun T : Finset (Finset (Finset (Fin 5))) =>
      ((mergeHistories 5).filter (fun f => topoOf 5 f = T)).card) hT
  rw [fiber_values_five] at h
  simpa using h

/-- 5 taxa 的合并史数与论文式 (2) 的 `H_5` 接上（引用一般 `n` 的定理）。 -/
theorem card_mergeHistories_five_eq_H : ((mergeHistories 5).card : ℝ) = H 5 :=
  Phylo.Stat.CoalescentHistoryCount.card_mergeHistories_eq_H 5 (by norm_num)

/-! ## §5 Lemma 4 本体 -/

/-- ★★★ **ADR2011 Lemma 4（主目标）**：5 taxa 时，任意两个无根拓扑的**纤维相等**
（且由 `fiber_uniform_five` 都等于 `12`）。 -/
theorem lemma4_five (T T' : UnrootedTopology5) :
    ((mergeHistories 5).filter (fun f => topoOf 5 f = T.1)).card
      = ((mergeHistories 5).filter (fun f => topoOf 5 f = T'.1)).card := by
  rw [fiber_uniform_five T.1 T.2, fiber_uniform_five T'.1 T'.2]

/-- ★★★ **ADR2011 Lemma 4（概率版）**：每个无根拓扑的概率 `= 12 · (1/H_5) = 1/15`
（「所有溯祖事件都在根以上」⇒ 每条合并史的概率都是 `1/H_5`）。 -/
theorem lemma4_five_prob (T : UnrootedTopology5) :
    (∑ _f ∈ (mergeHistories 5).filter (fun f => topoOf 5 f = T.1), (1 / H 5)) = 1 / 15 := by
  rw [Finset.sum_const, nsmul_eq_mul, fiber_uniform_five T.1 T.2, H_five]
  norm_num

/-- ★★ Lemma 4 的概率归一化核对：`15` 个无根拓扑的概率之和 `= 1`（`15 · 1/15 = 1`）。 -/
theorem lemma4_five_prob_sum :
    (∑ T ∈ (mergeHistories 5).image (topoOf 5),
        (∑ _f ∈ (mergeHistories 5).filter (fun f => topoOf 5 f = T), (1 / H 5))) = 1 := by
  have hterm : ∀ T ∈ (mergeHistories 5).image (topoOf 5),
      (∑ _f ∈ (mergeHistories 5).filter (fun f => topoOf 5 f = T), (1 / H 5)) = 1 / 15 :=
    fun T hT => by
      rw [Finset.sum_const, nsmul_eq_mul, fiber_uniform_five T hT, H_five]
      norm_num
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_unrootedTopo_five, nsmul_eq_mul]
  norm_num

end Phylo.Stat.FiveTaxonLemma4
