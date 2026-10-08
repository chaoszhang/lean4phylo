# MSC_INSTANCE_SPEC.md —— W9 Phase 2：把 Kingman 实例**接回**端到端定理

> 协调侧（dsh 主会话）写给执行 agent 的规格。**Phase 1 = `Phylo/Stat/MSCKingman.lean`（已完成）**，
> 本文件管 **Phase 2 = 新建 `Phylo/Stat/MSCInstance.lean`**。

## 0. 环境铁律（与 Phase 1 相同，违反即白干）

1. **只在 mirror 里编译**，mirror = **`~/lean4phylo-t41`**（Phase 1 用了 `-t40`，别和它抢）。
2. **每次验证前重新导出**已提交状态（mirror 会过期）：
   ```bash
   rm -rf ~/lean4phylo-t41 && mkdir -p ~/lean4phylo-t41
   cd /mnt/c/Users/ASTER/WorkBuddy/Project/lean/lean4phylo
   git archive HEAD | tar -x -C ~/lean4phylo-t41
   cp Phylo/Stat/MSCKingman.lean ~/lean4phylo-t41/Phylo/Stat/
   ```
   ⚠️ 但**本次基线**里 `MSCKingman.lean` 还**没进 git**（协调侧还没 commit）
   ⇒ 你必须像上面那样**手工把它拷进 mirror**。
3. **同一时刻只允许一个 `lean` 进程**（7 GB 内存）。起编译前：
   `if pgrep lean >/dev/null 2>&1; then echo BUSY; fi`
   —— **不要**用 `pgrep -c` 做数值比较（无匹配时它打印 `0` 但退出码 1）。
4. **不要改 `Phylo.lean`**（登记由协调侧做）、**不要改任何既有 `.lean`**、不要跑 `guard_batch.sh`。
   你只新建 `Phylo/Stat/MSCInstance.lean`。
5. PowerShell 会先展开 `wsl -e bash -c "…"` 里的 `$(…)` ⇒ 命令写成 `.sh` 文件再 `wsl -e bash <file>`。

## 1. 零告警判据（硬）

`lake env lean Phylo/Stat/MSCInstance.lean` ⇒ **exit 0 且 0 字节输出**；然后
`lake build Phylo.Stat.MSCInstance` ⇒ exit 0。零 `sorry` / 零 `admit` / 零 `axiom`，
**不出现单体 `import Mathlib`**（具体子模块如 `import Mathlib.X.Y` 允许）。

## 2. Phase 1 已冻结、可直接用的接口（`Phylo.Stat.MSCKingman`）

```lean
abbrev KingmanΘ : Type := ((Fin 4 → ℝ) × ℝ) × (Bool × Bool)
def KingmanDeep (θ : KingmanΘ) : Prop := θ.2.1 = true ∧ θ.2.2 = true
def Kingmanτd (θ : KingmanΘ) (T : Topo) : ℝ := …
def kingmanMSCTopoSym : MSCTopoSym KingmanΘ            -- ★★★ 具体实例（缺口 G5′）
theorem kingmanMSCTopoSym_nonempty : Nonempty (MSCTopoSym KingmanΘ)   -- ★★ 反空真
def AllSameShape : Prop ; theorem allSameShape_four : AllSameShape    -- ★★★ 同形前提
theorem kingmanMSCTopoSym_tau_eq_third : deep ⇒ τd θ T = 1/3
theorem kingmanMSCTopoSym_tau_notDeep  : ¬deep ⇒ τd θ .ab_cd = 1
```

## 3. 要做什么（三件，全部是**纯接线**，不要发明新数学）

### 3.1 `PropAData` 沿投影搬运（★ 通用小工具）

`KingmanΘ` 的**第一个分量刻意就是既有 `PropAData` 的样本空间** `(Fin 4 → ℝ) × ℝ`
（叶长 × 内部枝长），所以三个模型的命题 A 数据都可以**原样搬运**：

```lean
/-- ★★ 把 `PropAData Θ` 沿 `φ : Θ' → Θ` 前推。三条子句是纯搬运（不涉及任何模型）。 -/
def transportPropAData {Θ Θ' : Type*} (φ : Θ' → Θ) (P : PropAData Θ) : PropAData Θ' where
  A := fun θ T' τ => P.A (φ θ) T' τ
  f := fun θ => P.f (φ θ)
  clause_ab := fun θ T' h => P.clause_ab (φ θ) T' h
  clause_ac := fun θ T' h => P.clause_ac (φ θ) T' h
  clause_ad := fun θ T' h => P.clause_ad (φ θ) T' h
```

三个模型的 `PropAData` 都在 `(Fin 4 → ℝ) × ℝ` 上：
* JC69：`Phylo.Stat.CASTERGeneTree.jc69PropAData`
* LM1：`Phylo.Stat.CASTERLM1.lm1PropAData π hsum lam`
* F84：`Phylo.Stat.CASTERF84PropA.f84PropAData pi kap hR hY`（**无条件版**）
⇒ 它们全部沿 `Prod.fst : KingmanΘ → (Fin 4 → ℝ) × ℝ` 搬运。

### 3.2 三个「`S` 换成构造」的端到端定理（★★★ 本批主交付）

对 **JC69 / LM1 / F84** 各写一条**派生版**，与既有版本**逐条同形**，
只是把假设参数 `(S : MSCTopoSym Θ)` **换成固定的 `kingmanMSCTopoSym`**：

```lean
/-- ★★★ **JC69 的 CASTER 定理 1（MSC 侧取 Kingman 具体构造）**。 -/
theorem jc69_caster_statisticallyConsistent_kingman
    (ν : Measure Phylo.Stat.MSCKingman.KingmanΘ) [IsProbabilityMeasure ν]
    (hdeep : MeasurableSet {θ | Phylo.Stat.MSCKingman.kingmanMSCTopoSym.deep θ})
    (hpos : 0 < ν {θ | ¬ Phylo.Stat.MSCKingman.kingmanMSCTopoSym.deep θ})
    (hf_int : Integrable (transportPropAData Prod.fst jc69PropAData).f ν)
    (hf_pos : ∀ θ, ¬ Phylo.Stat.MSCKingman.kingmanMSCTopoSym.deep θ →
      0 < (transportPropAData Prod.fst jc69PropAData).f θ)
    (hint : ∀ T : Topo, Integrable (fun θ => ∑ T' : Topo,
      Phylo.Stat.MSCKingman.kingmanMSCTopoSym.τd θ T' *
        (transportPropAData Prod.fst jc69PropAData).A θ T' T) ν)
    (emp : ℕ → TopoWeight (Fin 4))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, TopoClose (emp n)
      (TopoIdeal.ofModel Phylo.Stat.MSCKingman.kingmanMSCTopoSym ν hdeep
        (transportPropAData Prod.fst jc69PropAData)
        hf_int hf_pos hpos hint).W ε)
    {E : ℕ → TopoChoice (Fin 4)}
    (hE : ∀ (n : ℕ) (q : TopoChoice (Fin 4)),
      topoScore (emp n) q ≤ topoScore (emp n) (E n)) :
    ∃ N : ℕ, ∀ n ≥ N, IsTrueT (fun _ _ => Topo.ab_cd) (E n) :=
  propAData_caster_statisticallyConsistent _ ν hdeep
    (transportPropAData Prod.fst jc69PropAData) hf_int hf_pos hpos hint emp hconv hE
```

LM1 与 F84 同形（只是把 `(transportPropAData Prod.fst jc69PropAData)` 换成对应实例，
并带上 `π hsum lam` / `pi kap hR hY` 这些**参数**）。**命名**：
`lm1_caster_statisticallyConsistent_kingman` / `f84_caster_statisticallyConsistent_kingman`。

> ⚠️ `hdeep` / `hpos` / `hint` / `hf_int` / `hf_pos` / `hconv` **仍然作为假设保留**
> —— 它们是**正文条件 (1)(2) 与 LLN**，与缺口 G5′ **无关**，本批不去动它们。
> 本批要求做到的是：**`S` 这一个参数被真实构造替换掉**（不再是「借来的结构」）。
> 若能顺手把 `hdeep` 对 `kingmanMSCTopoSym` 证成定理（`Bool` 是有限离散型，
> 大概率 `by simp [MSCKingman.KingmanDeep]` + 可测性即可），**请做**并命名为
> `measurableSet_kingmanDeep`；做不出来就保留假设并在 docstring 说明原因，**不要硬凑**。

### 3.3 树级收口（★★★ 让「模型 → 对称性 → 引擎 → 树」整条闭合）

既有 `Phylo.Stat.CASTERInstances.tree_iso_of_topo_consistency` 是**纯泛型**的
（只要 `hE : ∃ N, ∀ n ≥ N, IsTrueT qtrue (E n)`）。于是对三个模型各写一条
**把 3.2 的结论直接接上树级**的派生定理，结论是
`∃ N : ℕ, ∀ n ≥ N, Nonempty (Iso (Qt n).tree Ttrue.tree)`，
假设 = 3.2 的假设 + `e`/`Ttrue`/`Qt`/`hTtrue`/`hQt`/`htrue_class`/`hreal`
（逐字照抄 `Phylo/Stat/CASTERInstances.lean` 里 `jc69_recovers_true_tree` 的写法）。
命名：`jc69_recovers_true_tree_kingman` / `lm1_…` / `f84_…`。

## 4. 交付判据（照 Phase 1 的 §6：给**可复算**的数）

行数 / `md5sum` / `grep -c` 的 sorry 与 `import Mathlib` / `lake env lean` 的 **exit code 与输出字节数**（须 0）/
`lake build Phylo.Stat.MSCInstance` 的 exit code 与末尾 3 行 / 每条定理 → 已证完或卡住（附 `文件:行号 + 报错原文`）/
mirror 路径与 `git archive` 导出时间。

**卡住就报错原文给我**；不要改签名、不要改弱陈述、不要 `sorry`。
