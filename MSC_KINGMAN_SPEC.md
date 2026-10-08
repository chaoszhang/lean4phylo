# MSC_KINGMAN_SPEC.md —— W9 / 缺口 G5′：把 `MSCTopoSym` 从 4 叶 Kingman 溯祖构造出来

> **本文件是协调侧（dsh 主会话）写给执行 agent 的规格。**
> 目标文件：**`Phylo/Stat/MSCKingman.lean`**（新建，Phase 1）。
> 后续 Phase 2 = `Phylo/Stat/MSCInstance.lean`（接回端到端定理），**不在本批**。

---

## 0. 环境铁律（违反即白干）

1. **绝不在正本 `/mnt/c/Users/ASTER/WorkBuddy/Project/lean/lean4phylo` 里跑任何 `lake` 命令**
   （正本没有物化依赖，`lake` 会去 GitHub fetch 然后超时）。
   **只在 mirror 里编译**，mirror 目录用 **`~/lean4phylo-t40`**。
2. ⚠️ **mirror 会过期**（本项目已踩两次）。**每次验证前必须重新导出已提交状态**：
   ```bash
   rm -rf ~/lean4phylo-t40 && mkdir -p ~/lean4phylo-t40
   cd /mnt/c/Users/ASTER/WorkBuddy/Project/lean/lean4phylo
   git archive HEAD | tar -x -C ~/lean4phylo-t40
   ```
   然后把**你新写的文件**拷进去。
3. **同一时刻只允许一个 `lean` 进程**（本机 WSL 只有 7 GB 内存；并发 = 一方被 OOM 杀，
   报错是 `error: Lean exited with code 137`，**不是语法错**）。起编译前先确认：
   `if pgrep lean >/dev/null 2>&1; then echo BUSY; fi`
   —— **注意**：`pgrep -c lean` 在无匹配时会**打印 `0` 且退出码 1**，所以**不要**用
   `$(pgrep -c lean || echo 0)` 做数值比较（那是恒真的，会永远误报「忙」）。
4. **不要改 `Phylo.lean`**（登记由协调侧做）、**不要改任何既有 `.lean`**。
   你只新建**一个**文件：`Phylo/Stat/MSCKingman.lean`。
5. **PowerShell 会先展开 `wsl -e bash -c "…"` 里的 `$(…)` 与 `$?`。**
   一律把脚本写成 `.sh` 文件再 `wsl -e bash <file>`。

## 1. 零告警判据（硬）

* `lake env lean Phylo/Stat/MSCKingman.lean` ⇒ **exit 0 且输出 0 字节**（多一个 warning 就不合格）。
* 然后 `lake build Phylo.Stat.MSCKingman` ⇒ exit 0（这一步才产 olean）。
* **零 `sorry` / 零 `admit` / 零 `axiom` / 不 `import Mathlib`**（用 `Mathlib.X` 的具体子模块）。
* 常用零告警坑：`if_pos/if_neg` 已废弃 ⇒ 用 `ite_eq_left/ite_eq_right`；
  `linter.unusedSimpArgs`（simp 参数没用上）；`linter.unusedTactic`（上一步已闭合，多写的 `ring` 报
  `No goals to be solved`）。

## 2. 要补的缺口（精确）

`Phylo/Stat/CASTEREngine.lean:147` 的 `MSCTopoSym` 是**假定结构，全库 0 处具体构造**：

```lean
structure MSCTopoSym (Θ : Type*) where
  deep      : Θ → Prop
  τd        : Θ → Topo → ℝ
  τd_nonneg : ∀ θ T, 0 ≤ τd θ T
  τd_sum    : ∀ θ, ∑ T, τd θ T = 1
  not_deep  : ∀ θ, ¬ deep θ → τd θ .ab_cd = 1
  deep_ab   : ∀ θ, deep θ → τd θ .ab_cd = 1 / 3
  deep_ac   : ∀ θ, deep θ → τd θ .ac_bd = 1 / 3
```

**纪律（派单原文）**：**不得**为了让文件编过而**弱化 / 改动这些字段** —— 那会把 CASTER 的结论
**变空真**。宁可留 `def … : Prop` 缺口。

## 3. 数学内容（协调侧已核实，照此实现）

### 3.1 模型

4 叶 quartet 的物种树 `((a,b),(c,d))`。把无根内部边（分隔 `{a,b}` 与 `{c,d}`）**在根处切开**，
根以下两段长度记为 `a`（`{a,b}` 侧）、`b`（`{c,d}` 侧），**总内部枝长 `t = a + b`**（溯祖单位）。

回溯：`{a,b}` 两条谱系在根以下可合并，`P(未合并) = e^{−a}`；`{c,d}` 同理 `e^{−b}`。于是：

* **两侧都未合并**（概率 `e^{−a}e^{−b} = e^{−t}`）⇒ **4 条谱系进入根种群** ⇒ 根内所有合并都在根之上
  ⇒ 由 **ADR2011 Lemma 4**（重标号对称性）**三个无根拓扑等概率 `1/3`**。**这就是 `deep`**。
* **至少一侧在根以下合并了** ⇒ 该侧樱桃已解析 ⇒ 无根 4 叶拓扑**只能是 `ab|cd`**（点质量）。
  （若 `{a,b}` 已成樱桃而 `{c,d}` 未成，根种群只有 3 条谱系 `(ab), c, d`，唯一无根拓扑含樱桃 `{a,b}`
  ⇒ 仍是 `ab|cd`。）

⇒ `P(一致) = 1 − e^{−t} + (1/3)e^{−t} = 1 − (2/3)e^{−t}`，**与库里既有的
`Phylo.Stat.Coalescent.pConcordant`（`pConcordant_eq : pConcordant t = 1 - (2/3)*Real.exp (-t)`）
逐字一致** —— 这是 Phase 1 要打通的「概率对账」。

### 3.2 对称性（第 2 步 = 转录，不是发明）

ADR2011 Lemma 4 原文（`references/md/AllmanDegnanRhodes2011_IdentifyingRootedSpeciesTree.md`
**962–971 行**）：

> **Lemma 4** If all coalescent events occur above the root … of a **5-taxon** species tree, then
> all 15 of the unrooted topological gene trees are equally likely.
> **Proof** … Because all unrooted gene trees have the same unlabeled shape, all coalescent histories
> leading to one gene tree correspond to equally likely coalescent histories producing another,
> **by simply relabeling lineages**.

紧接着 **973–974 行**：**「Note that the claim of this lemma is special to five taxa. For six taxa,
with two diﬀerent unrooted gene tree shapes possible, the analogous statement is not true.」**

⇒ **两条硬边界（必须显式写进前提/文档）**：
1. **「同形」前提必须显式**：4 叶的 3 个无根拓扑**同形**（都是 4 叶星形加一条内边），故 4 叶安全；
   但**必须写成显式 `def AllSameShape : Prop` 并证明它**，不许默认自动成立。
2. `sm.tex` 391/393 在 `\REMOVE{}` 内（宏定义在 100 行 ⇒ **丢弃参数**）⇒ **未随附录发表**，
   是作者草稿；**1375–1378 才是已发表的**。引用时区分。

**库里已经证好的组合核心（直接复用，不要重证）** —— `Phylo/Stat/Coalescent.lean`：
* `mergePairsFinset 4`（4 条谱系的 15… 不，是 `C(4,2)=6` 个首次合并对）；
* ★★ `root_quartet_classes`（**281–290 行**）：6 个首次合并对按诱导拓扑分成 **3 类、每类恰 2 个**
  （判据 `0 ∈ p ↔ 1 ∈ p`、`↔ 2 ∈ p`、`↔ 3 ∈ p`）；
* `root_topologyProb`（**292–296 行**）：`2 / 6 = 1/3`。

## 4. 冻结接口（**逐字照用**，Phase 2 与数值脚本都按这个写）

```lean
namespace Phylo.Stat.MSCKingman

/-- 溯祖历史空间。**第一个分量刻意就是端到端定理里既有的 `(Fin 4 → ℝ) × ℝ`**
（叶长 × 内部枝长），因此既有 `PropAData` 可以沿投影**原样搬运**；
第二个分量记录「两侧是否深合并进根」。 -/
abbrev KingmanΘ : Type := ((Fin 4 → ℝ) × ℝ) × (Bool × Bool)

/-- `deep`：`{a,b}` 与 `{c,d}` **都没能在根以下合并** ⇒ 4 条谱系进根种群。 -/
def KingmanDeep (θ : KingmanΘ) : Prop := θ.2.1 = true ∧ θ.2.2 = true

/-- 条件拓扑分布：深合并 ⇒ 三拓扑各 `1/3`；否则点质量在 `ab|cd`。 -/
def Kingmanτd (θ : KingmanΘ) (T : Topo) : ℝ :=
  if KingmanDeep θ then 1 / 3 else if T = Topo.ab_cd then 1 else 0

/-- ★★★ **4 叶 Kingman 溯祖给出的 `MSCTopoSym` 具体实例**（缺口 G5′ 的正面回答）。 -/
def kingmanMSCTopoSym : MSCTopoSym KingmanΘ := …

/-- ★★ **反空真**：该实例可居留。 -/
theorem kingmanMSCTopoSym_nonempty : Nonempty (MSCTopoSym KingmanΘ) := …

/-- ★★★ **「同形」前提（ADR2011 Lemma 4 的前提在 4 叶下的显式形式）**。 -/
def AllSameShape : Prop := …

/-- ★★★ 4 叶满足同形前提（由 Coalescent 的 `root_quartet_classes` 直接给出）。 -/
theorem allSameShape_four : AllSameShape := …

/-- ★★★ **深合并 ⇒ 三拓扑等概率**（ADR2011 Lemma 4 的重标号对称性在 4 叶下的结论）。 -/
theorem kingmanMSCTopoSym_tau_eq_third
    {θ : KingmanΘ} (h : KingmanDeep θ) (T : Topo) : kingmanMSCTopoSym.τd θ T = 1 / 3 := …

/-- ★★★ **无深合并 ⇒ 点质量在 `ab|cd`**。 -/
theorem kingmanMSCTopoSym_tau_notDeep
    {θ : KingmanΘ} (h : ¬ KingmanDeep θ) : kingmanMSCTopoSym.τd θ .ab_cd = 1 := …

/-! ## 概率对账（与既有 `Coalescent.pConcordant` 接通） -/

/-- **深合并**（两侧**都未能**在根以下合并）的概率 `e^{−a} · e^{−b}`。
这就是「4 条谱系进入根种群」的概率，也是 `KingmanDeep` 的概率。 -/
def kingmanDeepProb (a b : ℝ) : ℝ := Real.exp (-a) * Real.exp (-b)

/-- ★★★ **深合并的概率 = `e^{−(a+b)}`**（半群性；对应 `Coalescent.survival_add`）。 -/
theorem kingmanDeepProb_eq (a b : ℝ) :
    kingmanDeepProb a b = Real.exp (-(a + b)) := …

/-- **无深合并**（至少一侧在根以下完成了合并）的概率 `1 − e^{−(a+b)}`。 -/
def kingmanNotDeepProb (a b : ℝ) : ℝ := 1 - Real.exp (-(a + b))

/-- ★★★ **概率对账（真正的记账，不是把 `pConcordant` 展开一遍）**：
`P(一致) = P(无深合并)·1 + P(深合并)·(1/3) = 1 − (2/3)e^{−t}`，`t = a + b`，
与 `Coalescent.pConcordant` 的**闭形式** `pConcordant_eq` 相同。 -/
theorem kingman_concordant_eq_pConcordant (a b : ℝ) :
    kingmanNotDeepProb a b * 1 + kingmanDeepProb a b * (1 / 3)
      = Coalescent.pConcordant (a + b) := …

/-- ★★★ **每个不一致拓扑的概率**恰是 `⅓e^{−t} = Coalescent.pDiscordant (a+b)`。 -/
theorem kingman_discordant_eq_pDiscordant (a b : ℝ) :
    kingmanDeepProb a b * (1 / 3) = Coalescent.pDiscordant (a + b) := …

/-- ★★★ **广义对称性前提**（比 `AllSameShape` 更弱、更好用的形式，供 Phase 2 使用）：
「根种群 4 条谱系的首次合并对等概率地落在 3 个拓扑类上」⇒ 每类 `1/3`。 -/
theorem root_topology_uniform :
    (2 : ℝ) / ((Coalescent.mergePairsFinset 4).card : ℝ) = 1 / 3 := …

end Phylo.Stat.MSCKingman
```

> ### 🔧 规格修正 v2（2026-10-09，协调侧，**执行 agent K 报告后**）
> **K 报告得对**：v1 里我把 `kingmanNotDeepProb a b := e^{−a}·e^{−b}` 命名错了 ——
> 按 §3 的模型，那个数算的是「两侧**都未能**在根以下合并」＝ **deep** 的概率，
> 不是 not-deep 的概率（`e^{−a}e^{−b} = e^{−t}`）。故：
> 1. **`kingmanDeepProb`** 用正确的名字承载这个数；`kingmanNotDeepProb` 改为 `1 − e^{−(a+b)}`。
> 2. `kingman_concordant_eq_pConcordant` 的形状改为上面这条 **非平凡记账式**
>    （v1 的形状 `(1 − e^{−t}) + (1/3)e^{−t} = pConcordant t` 其实是**定义展开**，
>    因为 `Coalescent.pConcordant t` 的定义**就是** `(1 - Real.exp (-t)) + (1/3)*Real.exp (-t)`
>    —— 只要 `simp only [Coalescent.pConcordant]` 就闭合，不含信息量）。
> 3. 新增 `kingman_discordant_eq_pDiscordant`。
>
> ⚠️ **这属于「修正命名 / 加强陈述」，不是「改弱命题」**：字段与其余陈述一律不动。

> ⚠️ 上表是**冻结接口**：名字、参数顺序、类型**不要改**。
> 若某条实在无法按此形状证出，**先报给协调侧**，不要自己改签名或改弱命题。
> 实现细节（用什么 tactic、要不要加辅助引理）随你；**辅助引理请加 `private` 或加 `_aux` 后缀**。

## 5. 允许的实现策略

* `Kingmanτd` 的 `if` 需要 `Decidable (KingmanDeep θ)`：`KingmanDeep` 是
  `Bool` 的等式合取，`Decidable` 由 `decide` + `instDecidableAnd` 自动找到，**不需要**手写。
* `τd_sum`：先 `by_cases h : KingmanDeep θ`，再用 `CASTEREngine` 里既有的
  `sum_topo : ∑ T : Topo, f T = f .ab_cd + f .ac_bd + f .ad_bc`（**去 CASTEREngine 里确认它的名字**），
  然后 `norm_num`。`1/3 + 1/3 + 1/3 = 1` 在 `ℝ` 上由 `norm_num` 收。
* `τd_nonneg`：`by_cases` + `norm_num`（`0 ≤ 1/3`、`0 ≤ 1`）。
* `AllSameShape` 的定义**直接用 `Coalescent.root_quartet_classes` 的三条合取式**（把
  `mergePairsFinset 4` 的三条 filter 基数 = 2 写成 `Prop`），`allSameShape_four` 就是
  `Coalescent.root_quartet_classes`。这样「前提」是**真实可检的命题**，不是空壳。
* `KingmanΘ` 上的 `Measure`（若你想把 §3 的概率做成真测度）：**Phase 1 不要求**，
  §4 里的 `kingmanNotDeepProb` / `kingman_concordant_eq_pConcordant` 是**实数层的对账**，先做这个。
  （真测度构造留给 Phase 2。）

## 6. 交付时必须报的判据（可复算，不要只说「过了」）

```
文件行数 / md5（md5sum）
grep -c -E '^\s*sorry\s*$|:= *sorry|by *sorry|^axiom '   → 必须 0
grep -c 'import Mathlib'                                  → 必须 0
lake env lean Phylo/Stat/MSCKingman.lean  → exit code 与 输出字节数（必须 exit 0 / 0 字节）
lake build Phylo.Stat.MSCKingman          → exit code（必须 0）＋ 末尾 3 行
本文件里每个「定理名 → 你的判断（已证完 / 卡住 + 报错原文）」清单
镜像路径 + `git archive` 导出时间（证明你的 mirror 是新鲜的）
```

**卡住时**：把 `文件:行号 + 完整 error 文本` 报给协调侧，**不要反复重编译试错**，
也不要为了编过而删定理 / 改弱命题。
