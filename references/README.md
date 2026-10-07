# `references/` —— 形式化缺口对应的原始文献与证明原文

> **生成**：2026-10-07
> **用途**：为 `HANDOVER.md` 中的 T1（`QuartetDecidesTree`）、T3（Buneman 存在性）、T4（`MaxZCherryCore`/NJ）、T5（SVDQuartets）等缺口提供**可直接查阅的证明原文**。
> **来源**：全部为**公开可获取**版本（arXiv / 出版社开放获取 / 作者主页 / PMC）。付费墙文献见 §5，附链接。

---

## 0. 目录结构

```
references/
├── README.md          ← 本文件（索引 + 证明出处映射）
├── pdf/               ← 原始 PDF（8 篇）
├── md/                ← 转好的 Markdown（可直接读，8 篇）
├── img/               ← Buneman 扫描件的页面图像（12 张，OCR 用）
├── ocr/               ← tesseract OCR 的逐页纯文本（12 个）
├── convert.py         ← PDF → Markdown 转换脚本（pdfminer）
└── extract_img.py     ← 扫描件 → 页面图像（pypdf）
```

**转换方法**：
- 有文本层的 PDF → `pdfminer.six` 直接抽取（保留版面顺序），再经 `cleanup.py` 修复符号。
- **扫描件**（Buneman 1971/1974）→ `pypdf` 导出页面图像 → `tesseract 5.3.4` OCR（`--psm 6`）→ 按页拼装。

**⚠️ 已知的转换局限（重要）**：
1. **扫描件 OCR**有识别错误（如 `Nand M` = `N and M`，下标/上标常丢失）。
2. **数学符号**：部分 PDF 用无 `ToUnicode` 表的字体，个别符号会残留为 `(cid:NNN)` 形态
   （常见 `∑` 已修复；希腊字母与花体仍有残留，见各文件 `grep -c "(cid:"` 计数）。
3. **arXiv 论文**开头会混入页边竖排的 arXiv 编号栏（形如单字符行），是版面副产物，可忽略。
4. **⟹ 凡是公式与符号，请以 `pdf/` 中的原始 PDF 为准**；`.md` 用于**快速阅读与检索**。

---

## 1. 缺口 → 证明出处（速查表）

| 本库缺口 | 原始证明文献 | 状态 | 在 `md/` 中的位置 |
|---|---|---|---|
| **T1 `QuartetDecidesTree`** | **Colonius & Schulze 1981**（原始）<br>**Steel 1992** | ⚠️ 均付费墙 | 见 §5 链接；**完整转述**见下 |
| ↑ 同一结果 | **Huber, Moulton, Semple, Wu 2018** | ✅ PDF+MD | `Huber2018_*.md` **§2 Theorem 1**（第 412 行） |
| ↑ 同一结果（thin/transitive/saturated 刻画） | **Huber et al. 2017 (arXiv:1702.00190)** | ✅ PDF+MD | `HuberEtAl2017_*.md` **§3 Theorem 6**（第 315 行） |
| **T4 `MaxZCherryCore`**（NJ 樱桃引理） | **Studier & Keppler 1988**（首个正确证明） | ⚠️ 付费墙 | 见 §5 |
| ↑ 同一结果（leaf-status 重证） | **Weller 2023 (arXiv:2305.18866)** | ✅ PDF+MD | `Weller2023_*.md` **Theorem 1**（124）、**Thm 2**（378） |
| ↑ 同一结果（分析学重证） | **Mihaescu, Levy, Pachter 2006 (arXiv:cs/0602041)** | ✅ PDF+MD | `MihaescuLevyPachter2006_*.md` |
| **T3 Buneman 存在性**（四点条件 ⟹ 树度量） | **Buneman 1971**（原始） | ✅ **扫描件 PDF + OCR** | `Buneman1971_*.md`（9 页） |
| ↑ 四点条件的图论证明 | **Buneman 1974** | ✅ **扫描件 PDF + OCR** | `Buneman1974_*.md`（3 页） |
| **T8 NJst 一致性** | **Allman, Degnan, Rhodes 2016 (arXiv:1604.05364)** | ✅ PDF+MD | `AllmanDegnanRhodes2016_*.md` **Thm 4.1**（610）、**4.2**（636）、**5.1**（831） |
| **T5 SVDQuartets**（可识别性） | **Chifman & Kubatko 2015 (arXiv:1406.4811)** | ✅ PDF+MD | `ChifmanKubatko2015_*.md` |

---

## 2. T1 `QuartetDecidesTree` —— quartet 系统决定 binary 树

**定理**：两棵 binary 系统发生树若有相同的 quartet 系统，则同构。
（完整 quartet 系统：每个 4-元子集恰好一个 quartet。）

### 2.1 最实用的出处：Huber 2018 Theorem 1

`md/Huber2018_QuarnetRules_Level1Networks.md` **第 412 行**：

> **Theorem 1** A quartet system `Q ⊆ Q(X)` is of the form `Q = Q(T)` for a **(necessarily unique)**
> phylogenetic X-tree `T` if and only if `Q` is **thin and saturated**.

出处说明（同文件第 407–410 行）：这来自 **Dress et al. (2012, Theorem 3.7)**，
且 **Bandelt & Dress (1986, Proposition 2)** 用略不同的术语陈述过。
其**原始来源就是 Colonius & Schulze (1981)**。

### 2.2 另一个等价刻画：Huber 2017 Theorem 6

`md/HuberEtAl2017_SymbolicTernaryMetrics.md` **第 301–316 行**：

> In 1981, **Colonius and Schulze** found that, for a quartet system `Q` on a finite taxa set `X`,
> there is a phylogenetic tree `T` on `X` such that `Q = Q_T` **if and only if** certain conditions
> on subsets of `X` with up to five elements hold. […]
>
> A quartet system `Q` is **thin** if for every 4-subset `{a,b,c,d}`, at most one of
> `ab|cd`, `ac|bd`, `ad|bc` is contained in `Q`.
> It is **transitive** if for any 5 distinct `a,b,c,d,e ∈ X`, the quartet `ab|cd` is in `Q`
> whenever both `ab|ce` and `ab|de` are in `Q`.
> It is **saturated** if for any five distinct `a,b,c,d,e ∈ X` with `ab|cd ∈ Q`,
> at least one of `ae|cd` and `ab|ce` is also in `Q`.
>
> **Theorem 6.** A quartet system `Q ⊆ Q(X)` is of the form `Q = Q(T)` for some phylogenetic tree `T`
> on `X` **if and only if** `Q` is thin, transitive and saturated.

**⟹ 对本库的直接用途**：
- 库内**已有**推理规则 `Clonius–Schultze` 的一条特例：
  `Phylo/Quartet.lean` 的 `displaysQuartet_of_displaysQuartet_common`（`ab|ce ∧ ab|de ⟹ ab|cd`），
  正是上面 **transitive** 条件中的那条规则。
- 因此 HANDOVER 的 **T1「路线 B」** 就有了明确的完备化目标：**补全 thin / transitive / saturated
  三条**（thin 与 saturated 是纯组合条件），即可得 `Σ(T) = Σ(T')`，再走 `Phylo/Laminar` 的
  `splitOf` / `toRootedTreeOfCard` 收口。

### 2.3 为什么 binary 不可去

polytomy（内部度 ≥ 4）refine 成 binary 不改变任何 quartet。Huber 2017 的 **star 情形**
（`ab|cd, ac|bd, ad|bc` 三者全在 `Q` 中）正是这个退化的形式化表达。

---

## 3. T4 `MaxZCherryCore` —— NJ 的樱桃引理

**定理**（Neighbor Joining Theorem）：设 `D` 是可被树表示的（可加）距离矩阵，
`(u,v)` 使 `q(u,v)` 最小，则存在表示 `D` 的树 `T`，其中 `(u,v)` 是一颗 cherry。

### 3.1 最易形式化的证明：Weller 2023（leaf-status）

`md/Weller2023_NeighborJoining_LeafStatus.md`：

| 位置 | 内容 |
|---|---|
| **第 124 行** | **Theorem 1（Neighbor Joining Theorem）** —— 主定理陈述 |
| 第 142–144 行 | **leaf-status 定义**：`ℓ_T(u) := Σ_{x∈L(T)} d(u,x)`（到所有**叶**的距离和） |
| **第 154 行** | **Lemma 1**：`ℓ(u) − ℓ(v) = ω(uv)·(\|L^←\| − \|L^→\|)` —— 沿边移动的 leaf-status 变化量 |
| 第 213 行 | **Corollary 1**：最小化 leaf-status 的节点不是叶 |
| **第 219 行** | **Lemma 2**：沿路径的 leaf-status 单调性（`\|L^←\| ≥ \|L^→\|` ⟺ `ℓ` 递增） |
| **第 334 行** | **Lemma 3**：cherry 的中点 `w` 使 `d(x,p) ≤ d(x,w)` 对所有 `x` 成立 |
| **第 378 行** | **Theorem 2**：`z` 最大的一对是真树的 cherry（即本库的 `MaxZCherryCore`） |
| 第 381 行 | **Theorem 2 的证明**（反证：设 `u,v` 不构成 cherry，取最小化 `ℓ` 的节点 `c`，导出矛盾） |

**形式化路线（对应 HANDOVER T3 → T4）**：
Weller 的证明**显式需要实现树 `T`** —— 这正是本库缺的 **Buneman 存在性（T3）**。
一旦 T3 完成，Weller 的 Lemma 1–3 + Theorem 2 可以逐条照搬。
库内已备好的代数骨架（`Q_eq_neg_two_ell`、`two_mul_z`、`z_hinge`、`four_point_z_iff`）
正好把「`q` 最小」翻译成「`z` 最大」，与 Weller 的 `z(u,v)` 表述直接对接。

### 3.2 另一条完整证明：Mihaescu–Levy–Pachter 2006

`md/MihaescuLevyPachter2006_WhyNeighborJoiningWorks.md`（53K 字符）——
从「NJ 贪心优化树长」的角度给出完整分析，含大量 quartet/cherry 引理。
与 Weller 的 leaf-status 视角互补，可作为交叉验证。

---

## 4. T3 Buneman 存在性 / 四点条件

### 4.1 Buneman 1971（原始论文，扫描件）

`md/Buneman1971_RecoveryOfTreesFromDissimilarity.md`（9 页，OCR）：

- 定义了**系统发生树的 split 与 quartet 的对应**；
- 给出**「两 split 可被同一棵树展示 ⟺ 四个交至少一个空」**（相容性判据）——
  这正是本库 `Phylo/Split.lean` 的 `Split.Compatible` 与
  `Cladogram.pairwiseCompatible`（Splits-Equivalence 方向一）的原始出处；
- 给出**Splits Equivalence Theorem**（见 arXiv:2004.00062 的转述：
  「`S` 是某棵系统发生 X-树的 split 集 ⟺ `S` 含全部平凡 split 且两两相容，
  且该树在同构意义下唯一」）。

### 4.2 Buneman 1974（四点条件，扫描件）

`md/Buneman1974_MetricPropertiesOfTrees.md`（3 页，OCR）——
**四点条件**（`d(x,y)+d(z,w) ≤ max{d(x,z)+d(y,w), d(x,w)+d(y,z)}`）
作为**树度量的充要条件**的原始证明。

**⟹ 对本库的用途**：`Phylo/Algorithm/NJ.lean` 的 `FourPoint` 就是这条条件；
**T3（Buneman 存在性）= 这条定理的构造方向**（条件 ⟹ 存在实现加权树）。
⭐ **本库的 `Phylo/Dendrogram.lean`（超度量 ⟹ 球族镶嵌 ⟹ 树）是现成模板**，
Buneman 的构造可照抄（把 `FourPoint δ` 化作一族镶嵌的 `Finset`，再走
`Phylo/Laminar.lean` 的 `toRootedTreeOfCard`）。

---

## 5. ⚠️ 未能下载的文献（付费墙）—— 附链接

以下 4 篇有付费墙，**无法合法获取全文**。其**核心结果与证明已被上表中开放获取的文献完整覆盖**，
故不影响 T1/T3/T4 的推进；如需要原文，请通过机构订阅访问：

| 文献 | 链接 | 说明 |
|---|---|---|
| **Colonius & Schulze 1981**<br>*Tree structures for proximity data*<br>Br. J. Math. Stat. Psychol. 34:167–180 | DOI: [10.1111/j.2044-8317.1981.tb00626.x](https://doi.org/10.1111/j.2044-8317.1981.tb00626.x) | **T1 的原始出处**。其结果已由 §2.1/§2.2 的 Huber 文献完整转述（含定理陈述与推理规则） |
| **Steel 1992**<br>*The complexity of reconstructing trees from qualitative characters and subtrees*<br>J. Classification 9:91–116 | DOI: [10.1007/BF02618470](https://doi.org/10.1007/BF02618470) | 完整 quartet 系统决定树（正方向）+ **部分系统是 NP-complete**（复杂度部分）。正方向 = §2 |
| **Studier & Keppler 1988**<br>*A note on the neighbor-joining algorithm of Saitou and Nei*<br>Mol. Biol. Evol. 5(6):729–731 | DOI: [10.1093/oxfordjournals.molbev.a040527](https://doi.org/10.1093/oxfordjournals.molbev.a040527)<br>PubMed: [3447015 附近的 PMID 3221794](https://pubmed.ncbi.nlm.nih.gov/3221794/) | NJ 的**首个正确证明**（并指出 Saitou–Nei 1987 原证明有误）。⚠️ 出版社 CDN 会返回错误文件，实测不可下载。内容已被 §3.1/§3.2 覆盖 |
| **Aho, Sagiv, Szymanski, Ullman 1981**<br>*Inferring a Tree from Lowest Common Ancestors…*<br>SIAM J. Comput. 10(3):405–421 | DOI: [10.1137/0210030](https://doi.org/10.1137/0210030) | 相容 split 系统 ⟹ 存在树（本库 `Phylo/Aho.lean` 的原始出处） |
| **Saitou & Nei 1987**<br>*The neighbor-joining method*<br>Mol. Biol. Evol. 4(4):406–425 | DOI: [10.1093/oxfordjournals.molbev.a040454](https://doi.org/10.1093/oxfordjournals.molbev.a040454)<br>PubMed 标注 "Free article" | NJ 原算法（其正确性证明有误，见上） |
| **Margush & McMorris 1981**<br>*Consensus n-trees*<br>Bull. Math. Biol. 43(2):239–244 | DOI: [10.1016/S0092-8240(81)90019-7](https://doi.org/10.1016/S0092-8240(81)90019-7) | 多数共识树（本库 `Phylo/Consensus.lean` 的原始出处） |

> **补充**：教科书 **Semple & Steel, *Phylogenetics* (2003), Oxford** 是上述多条结果的
> 统一叙述处（**§6.4** quartet 系统与推理规则、**§7.2** 四点条件 / Buneman 定理、
> **§3.8** Splits-Equivalence）。有订阅的话是最省事的单一来源。

---

## 6. 各文件与「本库缺口」的对照（一页速览）

| `md/` 文件 | 覆盖的缺口 | 关键行 |
|---|---|---|
| `Buneman1971_*.md` | 相容性判据、Splits-Equivalence（T3 相关） | 全文（9 页） |
| `Buneman1974_*.md` | **四点条件 ⟹ 树度量（T3 核心）** | 全文（3 页） |
| `Weller2023_*.md` | **NJ 樱桃引理（T4）** | 124, 154, 219, 334, **378** |
| `MihaescuLevyPachter2006_*.md` | NJ 正确性（T4 交叉验证） | 全文 |
| `Huber2018_*.md` | **quartet 决定树（T1）** | **412**（Thm 1） |
| `HuberEtAl2017_*.md` | **quartet 决定树（T1）** thin/transitive/saturated | **301–316**（Thm 6） |
| `AllmanDegnanRhodes2016_*.md` | NJst 一致性（T8） | **610**（4.1）、636（4.2）、831（5.1） |
| `ChifmanKubatko2015_*.md` | SVDQuartets 可识别性（T5） | 全文 |

---

## 7. 复现方法

```bash
# 虚拟环境（已建）
PY=/c/Users/ASTER/.workbuddy/binaries/python/envs/default/Scripts/python.exe
# PDF → Markdown
"$PY" convert.py pdf md
# 扫描件 → 页面图像
"$PY" extract_img.py pdf/Buneman1971_RecoveryOfTreesFromDissimilarity.pdf img
# OCR（走 WSL 的 tesseract 5.3.4）
wsl -e bash -lc 'cd /mnt/c/Users/ASTER/WorkBuddy/Project/lean/lean4phylo/references && \
  for f in img/Buneman1971_*.jpg; do tesseract "$f" "ocr/$(basename "$f" .jpg)" -l eng --psm 6; done'
```
