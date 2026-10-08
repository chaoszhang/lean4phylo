# `scripts/msc/` —— W9 / 缺口 G5′（MSC 溯祖层）的独立复核脚本

## `kingman_check.py`

**协调侧（dsh 主会话）写的独立数值复核**，用于在相信 `Phylo/Stat/MSCKingman.lean`
的构造之前，先把它的**数学内容**从 4 叶 Kingman 溯祖的**历史穷举**里算出来
（**精确穷举**，不是 Monte Carlo，也不是重跑 Lean）。

模型：物种树 `((a,b),(c,d))`，根把无根内部边切成 `a`（`{a,b}` 侧）与 `b`（`{c,d}` 侧），
`t = a + b`（溯祖单位）。`{a,b}` 在根以下合并的概率 `1 − e^{−a}`，`{c,d}` 同理 `1 − e^{−b}`；
进入根种群的谱系按 Kingman 溯祖（每步在所有现存谱系里**等概率**挑一对合并）。

抽查与结论：

| 主张 | 方法 | 实测 |
|---|---|---|
| 整体拓扑分布 = `1 − (2/3)e^{−t}` / 各 `(1/3)e^{−t}` | 9 个 `t` × 5 个 `a/t` 的精确穷举 | 最大残差 **2.22e-16** |
| (A1) 两侧都没在根以下合并 ⇒ 三拓扑**等概率** | 条件分布 | **精确** `(1/3, 1/3, 1/3)`（含 `a=b=0` 星形） |
| (A2) 只有一侧成樱桃 ⇒ 拓扑**被逼成** `ab|cd` | 两个方向的穷举 | `{ab|cd: 1.0, 其余: 0}` |
| (A3) `C(4,2)=6` 个首次合并对 → **3 类、每类 2 个** | 枚举首次合并对诱导的拓扑 | `{a,b}/{c,d}`、`{a,c}/{b,d}`、`{a,d}/{b,c}` 各 2 个 |
| 与 `Coalescent.pConcordant` 的代数对账 | `(1−e^{−t}) + (1/3)e^{−t} = 1 − (2/3)e^{−t}` | 残差 **1.11e-16** |

`VERDICT: PASS`。

**(A3) 独立复现了库里的 `Coalescent.root_quartet_classes`** —— 即 ADR2011 Lemma 4
「重标号对称性」在 4 叶下的组合核心；`MSCKingman.AllSameShape` 的证明就取自它。

### 这个脚本本身修过的 4 个实现 bug（记下来免得后人重踩）
1. 无根树的**根结点方向搞反**（`history[-1]` 才是根，不是 `history[0]`）；
2. 让「簇结点」把自己携带的叶集算进**连通分量**的叶集（分量只覆盖该簇的一部分 ⇒ 叶集被算成 4）；
   正解是**按图论叶子（字母结点）**取；
3. `edges` 是集合 ⇒ 每条无向边只试了**一个方向**，另一方向的叶集被漏掉；
4. `topo_of_split(hist)` **漏写 `split_of`**，把「历史」当「split」传进去。

⇒ 教训：**「我的推导通过了数值复核」这句话，只有在我先确认复核脚本自身正确之后才有意义。**

## 运行

```
python kingman_check.py
```

无第三方依赖（只用标准库 `itertools` / `math`）。

---

# W10（溯祖理论本体）的复核脚本

> 全部**精确**运算（`fractions.Fraction` / 符号多项式 / 穷举），**没有 Monte Carlo**，
> 也**不是**重跑 Lean。每个脚本对应一个 Lean 模块，用来在「相信 Lean 里的定理」之前
> 先把它的**数学内容**独立算一遍。

| 脚本 | 对应模块 | 复核什么 | 结果 |
|---|---|---|---|
| `msc_quartet_prob.py` | `Phylo/Stat/MSCProof.lean`（W10c） | ① `Fin 4` 的 **14** 个有向 split 按基数分类：`2\|2` 恰 **6**、`1\|3` 恰 **8**；一致恰 **2**、不一致 `2\|2` 恰 **4**；② 概率表之和（把 `x = e^{−t}` 当**自由符号**）`pConc + 2·pDisc ≡ 1`，**误差恰为 0**；③ `majorizes` 的严格不等式（符号可证 + 7 组 `t` 数值展示） | **PASS** |
| `coalescent_stats.py` | `Phylo/Stat/CoalescentStats.lean`（W10k） | ① `k·E[τ_k] = 2/(k−1)`；② `E[L_n] = Σ 2/(k−1) = 2·H_{n−1}`；③ `Σ E[τ_{j+2}]·d_{j+2} = m`；④ `Σ θ/i = θ·H_{n−1}`；⑤ `θ_W` 无偏（`n ≤ 12`，`Fraction`） | **PASS**（误差恒为 0） |
| `kingman_jumpchain.py` | `Phylo/Stat/KingmanJumpChain.lean`（W10a，执行 agent A 写） | (2.2) 归一化、层间一致性递归（`n ≤ 7` 共 1148 个三元组）、单块分裂恒等式（有序和 `= \|B\|!(\|B\|−1)`）、Lah 归一路线 | **PASS**（`n ≤ 7`） |
| `degnansalter_puv.py` / `pin_formula.py` | `Phylo/Stat/DegnanSalter.lean`（W10e，执行 agent C 写） | `p_{uv}` 的 (C0)–(C8) 交叉核对（谱分解 / `lvec` 递推 / 闭乘积形式） | ⚠️ **FAIL**（协调侧实测；agent 正在回炉修公式） |
| `trivial_split_count.py` | `Phylo/Stat/TrivialSplitCount.lean`（W10，缺口 **G1** 补证） | 在「**有向** split ↔ 非空真子集 `A`（`A = sideA`）」这个**可计算代理**上穷举 `n = 2…12`：① 总数 `2^n − 2`；② `\|A\| = 1` 与 `\|Aᶜ\| = 1` 各恰 `n`（`n ≥ 2`）；③ `n ≥ 3` 时两支**不交** ⇒ 平凡恰 `2n`（`n = 2` 时两支**重合** ⇒ `2 ≠ 2n = 4`）；④ 无向平凡 `= n`；⑤ `n = 4` 时 `1\|3` 恰 **8**、`2\|2` 恰 **6**（交叉核对 `MSCProof.card_splits_two`）。⚠️ `Split (Fin n)` 的 `Fintype` 非可计算（`Fintype.ofInjective`），`decide` 枚举不了它，故走这个代理 | **PASS**（`n = 2…12`） |

### 本目录脚本自身踩过的坑（W10 新增）
* **`msc_quartet_prob.py`：f-string 里不能直接写 `{14 ...}`** —— `{` 会被当表达式，需写成 `{{…}}`。
* **数值「复核」必须先自证**：`degnansalter_puv.py` 的 (C7)/(C8) 交叉核对立刻把
  「`p_{uv}` 的公式抄错」暴露出来 —— 这正是「**脚本先跑通再相信定理**」的价值。
* `kingman_jumpchain.py` 顺带查出**协调侧规格**里的一处算术笔误：
  §1.7 (★) 的 `|B| = 4` 写了 `36`，但那是**无序**和；**有序**和是 `72 = 4!·3`。
* `trivial_split_count.py` 第一版把 `n = 4` 的 `1|3` 数成「`|A| = 1`」（4 个）而漏了
  `|Aᶜ| = 1`（即 `|A| = 3`，另 4 个）—— 被脚本自己的 (E) 交叉核对当场抓住（`4 ≠ 8`）。
  教训同上：**「有向口径下平凡 = 某一侧单点」必须两侧都数**，只数 `sideA` 会正好差一半。

## `W10Probe.lean` —— W10c 的**反空真探针**（协调侧自写）

**不是**数值脚本，是**能被 Lean 编译**的探针（8 个 `example`）：证明 `MSCProof` 的构造
**不是空真**。运行方式（**必须先 build 根模块**，否则 `import Phylo` 读到的是旧 olean）：

```
# 在镜像里（正本不能跑 lake）
cp -r <正本>/Phylo/. <镜像>/Phylo/ && cp <正本>/Phylo.lean <镜像>/
~/w10/withlock.sh <镜像> ~/.elan/bin/lake build Phylo
~/w10/withlock.sh <镜像> ~/.elan/bin/lake env lean scripts/msc/W10Probe.lean
```

实测 **exit 0 / 输出 0 字节**。8 个 `example` 覆盖：① `Nonempty (MSCFreq (Fin 4))`；
② 真树 quartet 概率**严格为正**；③ `rootTopoProb = 1/3`（**是求和**）；④/⑤ 一般 `X` 下
一致 split 与其 `swap` 都拿到 `mscConcordant t / 2`；⑥ 不一致 `2|2` 拿到 `mscDiscordant t / 2`；
⑦ `1|3` 拿到 `0`；⑧ 一般 `X` 的 `majorizes` 可直接调用。


