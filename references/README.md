# `references/` —— 形式化缺口对应的原始文献与证明原文

> **生成**：2026-10-07 ｜ **最后更新**：2026-10-07 13:50（新增 10 篇：不变量 / 溯祖 / supertree）
> **用途**：为 `HANDOVER.md` 的 T0 批（`QuartetDecidesTree` / Buneman / NJ / NJst / SVDQuartets）
> 与 `NEXT.md` 的后续目标（不变量 / 溯祖基座 / supertree / 低垂果实）提供**可直接查阅的证明原文**。
> **来源**：全部为**公开可获取**版本（arXiv / 出版社 OA / 作者主页 / PMC / 机构仓储）。
> **付费墙文献见 §5**，附完整链接供老师自行下载。

---

## 0. 目录结构与规模

```
references/
├── README.md          ← 本文件（索引 + 证明出处映射 + 失败链接）
├── pdf/               ← 原始 PDF（18 篇）
├── md/                ← 转好的 Markdown（18 篇，可直接读）
├── img/               ← Buneman 扫描件的页面图像（12 张，OCR + 读图用）
├── ocr/               ← tesseract OCR 的逐页纯文本（12 个）
├── convert.py         ← PDF → Markdown（pdfminer + 符号修复 + 扫描件防护）
├── extract_img.py     ← 扫描件 → 页面图像（pypdf）
└── cleanup.py         ← 单独修复 (cid:) 字形残留
```

**当前规模**：**18 篇** PDF + **18 篇** Markdown（约 1.07M 字符文本）。

**转换方法**：
- 有文本层的 PDF → `pdfminer.six` 直接抽取 + 内置 `(cid:)` 符号修复。
- **扫描件**（Buneman 1971/1974）→ `pypdf` 导出页面图像 → `tesseract 5.3.4` OCR（`--psm 6`）→ 按页拼装。
- ⚠️ `convert.py` 有**扫描件防护**：抽不出正文时**跳过**，不覆盖已有的 OCR 文本。

**⚠️ 已知的转换局限**：
1. 扫描件 OCR 有识别错误（`Nand M` = `N and M`，下标/上标常丢失）。
2. 无 `ToUnicode` 表的字体会残留 `(cid:NNN)`（常见 `∑` 已修复；希腊字母仍有残留）。
3. arXiv 论文开头会混入页边竖排的 arXiv 编号栏（形如单字符行），是版面副产物，可忽略。

### ⭐ 更好的办法：直接读图（2026-10-07 老师确认）

**dsh + DeepSeek-V4.1-Flash 具备读图能力** ⇒ **不必依赖 OCR**：

- **扫描件**（Buneman 1971/1974）：直接读 `img/` 里的页面 JPG，公式与下标原样可读。
- **任意 PDF 的公式**：先 `python extract_img.py pdf/<某篇>.pdf img` 导出页面图，再直接读图。
- **`(cid:NNN)` 残留**：遇到时以读图为准，不要猜符号。

---

## 1. 速查表 A：T0 批（见 `HANDOVER.md` §4）

| 本库缺口 | 原始证明文献 | 状态 | 在 `md/` 中的位置 |
|---|---|---|---|
| **T0.1 `QuartetDecidesTree`** | **Colonius & Schulze 1981**（原始）<br>**Steel 1992** | ⚠️ 均付费墙 | 见 §5；**完整转述**见下 |
| ↑ 同一结果 | **Huber, Moulton, Semple, Wu 2018** | ✅ | `Huber2018_*.md` **§2 Theorem 1**（412 行） |
| ↑ 同一结果（thin/transitive/saturated） | **Huber et al. 2017 (arXiv:1702.00190)** | ✅ | `HuberEtAl2017_*.md` **§3 Theorem 6**（315 行） |
| **T0.2 Buneman 存在性** | **Buneman 1971**（原始） | ✅ **扫描件 + OCR** | `Buneman1971_*.md`（9 页） |
| ↑ 四点条件的图论证明 | **Buneman 1974** | ✅ **扫描件 + OCR** | `Buneman1974_*.md`（3 页） |
| **T0.3 `MaxZCherryCore`** | **Studier & Keppler 1988** | ⚠️ 付费墙 | 见 §5 |
| ↑ 同一结果（leaf-status 重证） | **Weller 2023 (arXiv:2305.18866)** | ✅ | `Weller2023_*.md` **Thm 1**（124）、**Thm 2**（378） |
| ↑ 同一结果（分析学重证） | **Mihaescu, Levy, Pachter 2006** | ✅ | `MihaescuLevyPachter2006_*.md` |
| **T0.4 NJst 一致性** | **Allman, Degnan, Rhodes 2016 (arXiv:1604.05364)** | ✅ | `AllmanDegnanRhodes2016_*.md` **Thm 4.1**（610） |
| **T0.5 SVDQuartets 可识别性** | **Chifman & Kubatko 2015 (arXiv:1406.4811)** | ✅ | `ChifmanKubatko2015_*.md` |

---

## 2. 速查表 B：`NEXT.md` 的后续目标（本轮新增 10 篇）

### 2.1 系统发生不变量（I 组）⭐ 老师最感兴趣

| 目标 | 文献 | 状态 | 关键内容 / 位置 |
|---|---|---|---|
| **I1 四点不变量**（Cavender–Felsenstein） | Cavender & Felsenstein (1987) | ⚠️ 付费墙 | 公式在 `Sturmfels2004_*.md`、`AllmanRhodes2006_*.md` 有完整转述 |
| **I2 Lake 线性不变量** | Lake (1987) | ⚠️ 付费墙 | **`CasanellasFernandezSanchez2011_*.md` §5.5 有完整转述** |
| **I3 Hadamard / Fourier 变换** | Evans & Speed (1993) | ⚠️ 付费墙 | — |
| ↑ 同一结果（toric 理想） | **Sturmfels & Sullivant (2005)** | ✅ **新增** | `SturmfelsSullivant2005_*.md`（JC/Kimura 的 Gröbner 基，次数 ≤ 4） |
| **I4 `rank ≤ 4` / 子式为零** | **Allman & Rhodes (2006)** | ✅ **新增** | `AllmanRhodes2006_*.md`：一般 Markov 模型的不变量理想；κ=2 时**全理想 = 3×3 子式生成** |
| **I5 不变量决定拓扑** | Allman & Rhodes (2003) | ⚠️ 付费墙 | — |
| **I6 edge invariants 足够** | **Casanellas & Fernández-Sánchez (2011)** | ✅ **新增** | `CasanellasFernandezSanchez2011_*.md`：**Buneman Splits-Equivalence 的代数类比**；§5 给了 JC/K2P/K3P/GM 的**四元集显式不变量** |
| **I7 toric 理想（见 I3）** | 同 Sturmfels–Sullivant | ✅ 同上 | — |
| （辅助）代数几何综述 | **Sturmfels (2004)** | ✅ **新增** | `Sturmfels2004_*.md`：问题清单 + 条件独立 ⟹ `5×5` 子式为零的构造 |
| （辅助）两状态 tripod | **Allman & Rhodes (2011)** | ✅ **新增** | `AllmanRhodes2011_TwoStateMarkovTripodTrees_*.md` |

### 2.2 溯祖理论基座（M 组）⭐ 老师要求「基座得建立起来」

| 目标 | 文献 | 状态 | 关键内容 |
|---|---|---|---|
| **M1 4 元集 ILS 公式** | Kingman (1982) / Tajima (1983) / Hudson (1983) / Pamilo–Nei (1988) | ⚠️ 全部付费墙 | **公式 `1−⅔e^{−t}` 在 `ChifmanKubatko2015_*.md` 有完整推导** |
| **M2 溯祖等待时间** | Kingman (1982) | ⚠️ 付费墙 | 转述见 `StadlerDegnan2012_*.md`、`AllmanDegnanRhodes2017_*.md` |
| **M4 site pattern 概率** | **Chifman & Kubatko (2015)** | ✅ 已有 | `ChifmanKubatko2015_*.md` |
| **M5 ASTRAL 局部支持** | **Sayyari & Mirarab (2016)** | ✅ **新增** | `SayyariMirarab2016_*.md`：**quartet 频率 ⟹ 局部后验概率 + 溯祖单位枝长** |
| **M6 STAR 推广** | **Allman, Degnan, Rhodes (2013)** | ✅ **新增** | `AllmanDegnanRhodes2013_STARGeneralizations_*.md`：STAR 及其推广的统计一致性 |
| **M6' NJst 一致性** | **ADR (2016)** | ✅ 已有 | `AllmanDegnanRhodes2016_*.md` |
| **M6'' split 概率** | **ADR (2017)** | ✅ **新增** | `AllmanDegnanRhodes2017_SplitProbabilitiesMSC_*.md`：**只用 split 分布**；大量 MSC 下的分裂概率公式 |
| **M7 基因树分布可算** | Degnan & Salter (2005) | ⚠️ 付费墙 | — |
| **M8 unrooted ⟹ rooted** | **ADR (2011)** | ✅ **新增** | `AllmanDegnanRhodes2011_*.md`：≥5 物种时**无根**基因树分布识别**有根**物种树 |
| （辅助）ranked 基因树概率 | **Stadler & Degnan (2012)** | ✅ **新增** | `StadlerDegnan2012_*.md`：多项式时间算法 |

### 2.3 supertree 与共识（C 组）⭐ 老师「也是」

| 目标 | 文献 | 状态 |
|---|---|---|
| **C1 严格/半严格共识** | Day (1985) | ⚠️ 付费墙（**结果简单，可直接实现；已有 `Consensus.lean` 铺垫**） |
| **C2 Adams 共识** | Adams (1972) | ⚠️ 付费墙 |
| **C3/C4 R\* 与贪心共识** | Bryant (2003) | ⚠️ 付费墙（综述，章节清晰） |
| **C5 共识公理化** | McMorris & Neumann 等 | ⚠️ 付费墙 |
| **C6 MinCut Supertree** | **Semple & Steel (2000)** | ⚠️ 付费墙；**UC 仓储有全文**：<https://ir.canterbury.ac.nz/items/6d7eaea6-87b6-4784-b2fc-0179a4eaf1ff/full>（`43743_Main.pdf`） |
| **C7 supertree 不存在性** | Steel, Dress & Böcker (2000) | ⚠️ 付费墙 |

### 2.4 低垂果实（F 组）

| 目标 | 文献 | 状态 |
|---|---|---|
| **F1 字符相容性定理** | Estabrook, Johnson & McMorris (1976) | ⚠️ 付费墙；**密歇根 Deep Blue 有全文**：<http://deepblue.lib.umich.edu/bitstream/2027.42/21887/1/0000294.pdf> |
| **F2 严格共识** | = C1 | — |
| **F3 KF 距离** | Kuhner & Felsenstein (1994) | ⚠️ 付费墙；**公式清楚**（见 §5 注） |
| **F4 JC 距离校正** | Jukes & Cantor (1969) | ⚠️ 书章；**公式在 `Sturmfels2004_*.md`** |
| **F5 Lake 不变量** | = I2 | — |
| **F6 Buneman 树 / split 分解** | Buneman (1971)；Bandelt & Dress (1986) | ✅ **Buneman 1971 已下载**；Bandelt–Dress 付费墙 |
| **F7 rooted triplet（Aho 有根版）** | Aho et al. (1981)；Bryant & Steel (1995) | ⚠️ 付费墙 |
| **F8 Fitch 一般树 / Sankoff** | Fitch (1971)；Sankoff (1975) | ⚠️ 付费墙 |

---

## 3. 已下载文献清单（18 篇）

| # | `md/` 文件 | 主题 | 对应目标 |
|---|---|---|---|
| 1 | `Buneman1971_RecoveryOfTreesFromDissimilarity.md` | 相容性判据、Splits-Equivalence | T0.2 / F6 |
| 2 | `Buneman1974_MetricPropertiesOfTrees.md` | **四点条件 ⟹ 树度量** | **T0.2** |
| 3 | `Weller2023_NeighborJoining_LeafStatus.md` | NJ leaf-status | **T0.3** |
| 4 | `MihaescuLevyPachter2006_WhyNeighborJoiningWorks.md` | NJ 正确性 | T0.3 |
| 5 | `HuberEtAl2017_SymbolicTernaryMetrics.md` | **quartet 系统 thin/transitive/saturated** | **T0.1** |
| 6 | `Huber2018_QuarnetRules_Level1Networks.md` | Colonius–Schultze 推理规则 | T0.1 / N3 |
| 7 | `AllmanDegnanRhodes2016_NJst_StatisticalConsistency.md` | NJst 一致性 | **T0.4** |
| 8 | `ChifmanKubatko2015_IdentifiabilityarXiv1406.4811.md` | SVDQuartets 可识别性 + **ILS 概率推导** | T0.5 / **M1** |
| 9 | `SturmfelsSullivant2005_ToricIdealsPhyloInvariants.md` | **toric 理想 / Gröbner 基** | **I3/I7** |
| 10 | `AllmanRhodes2006_PhyloIdealsVarietiesGeneralMarkov.md` | **一般 Markov 模型的不变量理想** | **I4** |
| 11 | `CasanellasFernandezSanchez2011_RelevantInvariants.md` | **edge invariants 足够（代数版 Buneman 定理）** | **I6** |
| 12 | `Sturmfels2004_PhylogeneticAlgebraicGeometry.md` | 代数几何综述 + 问题清单 | I1/辅助 |
| 13 | `AllmanRhodes2011_TwoStateMarkovTripodTrees.md` | 两状态 tripod 模型代数分析 | I/辅助 |
| 14 | `SayyariMirarab2016_ASTRALLocalSupport.md` | **quartet 频率 ⟹ 局部后验 + 枝长** | **M5** |
| 15 | `AllmanDegnanRhodes2013_STARGeneralizations.md` | STAR 推广一致性 | **M6** |
| 16 | `AllmanDegnanRhodes2017_SplitProbabilitiesMSC.md` | MSC 下的 **split 概率** | **M6** |
| 17 | `AllmanDegnanRhodes2011_IdentifyingRootedSpeciesTree.md` | 无根基因树 ⟹ 有根物种树 | **M8** |
| 18 | `StadlerDegnan2012_RankedGeneTreeProbability.md` | ranked 基因树概率（多项式算法） | M2/M7 辅助 |

---

## 4. 复现方法

```bash
# 虚拟环境（已建）
PY=/c/Users/ASTER/.workbuddy/binaries/python/envs/default/Scripts/python.exe

# PDF → Markdown（内置符号修复 + 扫描件防护）
"$PY" convert.py pdf md

# 扫描件 → 页面图像（供读图或 OCR）
"$PY" extract_img.py pdf/Buneman1971_RecoveryOfTreesFromDissimilarity.pdf img

# OCR（走 WSL 的 tesseract 5.3.4）
wsl -e bash -lc 'cd /mnt/c/Users/ASTER/WorkBuddy/Project/lean/lean4phylo/references && \
  for f in img/Buneman1971_*.jpg; do tesseract "$f" "ocr/$(basename "$f" .jpg)" -l eng --psm 6; done'

# 单独修复符号残留
"$PY" cleanup.py
```

---

## 5. ⚠️ 未能下载的文献（付费墙）—— 附链接

### 5.1 下载失败清单（老师可自行下载）

| 文献 | 链接 | 说明 |
|---|---|---|
| **Colonius & Schulze 1981**<br>*Tree structures for proximity data*<br>Br. J. Math. Stat. Psychol. 34:167–180 | <https://doi.org/10.1111/j.2044-8317.1981.tb00626.x> | **T0.1 的原始出处**。结果已由 `Huber2018_*.md` / `HuberEtAl2017_*.md` 完整转述 |
| **Steel 1992**<br>*The complexity of reconstructing trees from qualitative characters and subtrees*<br>J. Classification 9:91–116 | <https://doi.org/10.1007/BF02618470> | 完整 quartet 系统决定树（正方向）；部分系统是 NP-complete（复杂度部分，已降级） |
| **Studier & Keppler 1988**<br>*A note on the neighbor-joining algorithm of Saitou and Nei*<br>Mol. Biol. Evol. 5(6):729–731 | <https://doi.org/10.1093/oxfordjournals.molbev.a040527><br>PubMed: <https://pubmed.ncbi.nlm.nih.gov/3221794/> | NJ 的**首个正确证明**（并指出 Saitou–Nei 1987 原证明有误）。⚠️ 出版社 CDN 返回错误文件。内容已被 `Weller2023` / `MihaescuLevyPachter2006` 覆盖 |
| **Aho, Sagiv, Szymanski, Ullman 1981**<br>*Inferring a Tree from Lowest Common Ancestors…*<br>SIAM J. Comput. 10(3):405–421 | <https://doi.org/10.1137/0210030> | 相容 split 系统 ⟹ 存在树（本库 `Phylo/Aho.lean` 的原始出处） |
| **Saitou & Nei 1987**<br>*The neighbor-joining method*<br>Mol. Biol. Evol. 4(4):406–425 | <https://doi.org/10.1093/oxfordjournals.molbev.a040454> | NJ 原算法（其正确性证明有误，见 Studier–Keppler） |
| **Margush & McMorris 1981**<br>*Consensus n-trees*<br>Bull. Math. Biol. 43(2):239–244 | <https://doi.org/10.1016/S0092-8240(81)90019-7> | 多数共识树（本库 `Phylo/Consensus.lean` 的原始出处） |
| **Cavender & Felsenstein 1987**<br>*Invariants of phylogenies in a simple case with discrete states*<br>J. Classification 4:57–71 | <https://doi.org/10.1007/BF01890075> | **I1 四点不变量的原始出处**。⚠️ **公式已在 `Sturmfels2004_*.md` 与 `AllmanRhodes2006_*.md` 有完整转述** |
| **Lake 1987**<br>*A rate-independent technique…: evolutionary parsimony*<br>Mol. Biol. Evol. 4(2):167–191 | <https://doi.org/10.1093/oxfordjournals.molbev.a040433> | **I2 Lake 线性不变量**。⚠️ **已在 `CasanellasFernandezSanchez2011_*.md` §5.5 有完整转述** |
| **Evans & Speed 1993**<br>*Invariants of some probability models used in phylogenetic inference*<br>Ann. Statist. 21(1):355–377 | <https://doi.org/10.1214/aos/1176349030><br>Project Euclid（应可免费）：<https://projecteuclid.org/journals/annals-of-statistics/volume-21/issue-1/Invariants-of-Some-Probability-Models-Used-in-Phylogenetic-Inference/10.1214/aos/1176349030.full> | **I3 Hadamard / Fourier 变换**。⚠️ 直链 PDF 下载失败，但 Project Euclid 页面通常可免费下载 |
| **Allman & Rhodes 2003**<br>*Phylogenetic invariants for the general Markov model of sequence mutation*<br>Math. Biosci. 186(2):113–144 | <https://doi.org/10.1016/j.mbs.2003.08.004> | **I5 不变量决定拓扑**。⚠️ 2006 版（已下载）是其续作 |
| **Day 1985**<br>*Optimal algorithms for comparing trees with labeled leaves*<br>J. Classification 2(1):7–28 | <https://doi.org/10.1007/BF01908061> | **C1/F2 严格共识**（结果简单，可直接实现） |
| **Adams 1972**<br>*Consensus techniques and the comparison of taxonomic trees*<br>Syst. Zool. 21(4):390–397 | <https://doi.org/10.2307/2412432> | **C2 Adams 共识** |
| **Bryant 2003**<br>*A classification of consensus methods for phylogenetics*<br>DIMACS Series 61:163–184 | <https://doi.org/10.1090/dimacs/061/12> | **C3/C4 R\* 与贪心共识**。作者主页可能免费：<https://www.math.otago.ac.nz/>（David Bryant） |
| **Semple & Steel 2000**<br>*A supertree method for rooted trees*<br>Discrete Appl. Math. 105:147–158 | <https://doi.org/10.1016/S0166-218X(00)00202-X><br>**✅ UC 仓储免费全文**：<https://ir.canterbury.ac.nz/items/6d7eaea6-87b6-4784-b2fc-0179a4eaf1ff/full>（文件 `43743_Main.pdf`） | **C6 MinCut Supertree**。⚠️ 直链下载失败（`bitstream` 链接需浏览页获取），**老师在 UC 页面上点 `43743_Main.pdf` 即可下载** |
| **Estabrook, Johnson & McMorris 1976**<br>*A mathematical foundation for the analysis of cladistic character compatibility*<br>Math. Biosci. 29:181–187 | <https://doi.org/10.1016/0025-5564(76)90045-9><br>**✅ 密歇根 Deep Blue 免费全文**：<http://deepblue.lib.umich.edu/bitstream/2027.42/21887/1/0000294.pdf> | **F1 字符相容性定理**（两两相容 ⟹ 全局相容）。⚠️ 直链下载失败（HTTP→HTTPS 重定向），**老师可直接访问 Deep Blue 页面** |
| **Meacham 1981**<br>*Compatibility analysis of phylogenetic data* | 见 `Estabrook & Meacham (1979)` *How to determine the compatibility of undirected character state trees*, Math. Biosci. 46:219–224，<https://doi.org/10.1016/0025-5564(79)90043-3> | F1 补充（无向字符状态树） |
| **Kuhner & Felsenstein 1994**<br>*A simulation comparison of phylogeny algorithms under equal and unequal evolutionary rates*<br>Mol. Biol. Evol. 11(3):459–468 | <https://doi.org/10.1093/oxfordjournals.molbev.a040126> | **F3 KF 距离**。⚠️ **公式清楚**：`KF(T,T') = √( Σ_e (w_e − w'_e)² )`；`e` 遍历两树的全部边（含终端边），缺失边权取 0；等价于树向量（= split 权重向量）的 `L²` 距离 |
| **Kingman 1982**<br>*The coalescent*<br>Stoch. Proc. Appl. 13(3):235–248 | <https://doi.org/10.1016/0304-4149(82)90011-4> | **M2 溯祖等待时间** |
| **Kingman 1982b**<br>*On the genealogy of large populations*<br>J. Appl. Prob. 19A:27–43 | <https://doi.org/10.1017/S0021900200039176> | M2 另一版本（**首次描述溯祖**） |
| **Tajima 1983**<br>*Evolutionary relationship of DNA sequences in finite populations*<br>Genetics 105(2):437–460 | <https://doi.org/10.1093/genetics/105.2.437><br>PMC 综述：<https://pmc.ncbi.nlm.nih.gov/articles/PMC5068832/> | **M1 ILS 公式**（也是首次提出 ILS） |
| **Hudson 1983**<br>*Testing the constant-rate neutral allele model with protein sequence data*<br>Evolution 37(1):203–217 | <https://doi.org/10.1111/j.1558-5646.1983.tb05528.x> | **M1 ILS 公式**（独立发现） |
| **Degnan & Salter 2005**<br>*Gene tree distributions under the coalescent process*<br>Evolution 59(1):24–37 | <https://doi.org/10.1111/j.0014-3820.2005.tb00891.x> | **M7 基因树分布可算（COAL）** |
| **Bandelt & Dress 1986**<br>*Reconstructing the shape of a tree from observed dissimilarity data*<br>Adv. Appl. Math. 7(3):309–343 | <https://doi.org/10.1016/0196-8858(86)90038-2> | **F6 split 分解 / Buneman 树** |
| **Bryant & Steel 1995**<br>*Extension operations on sets of leaf-labelled trees*<br>Adv. Appl. Math. 16(4):415–430 | <https://doi.org/10.1006/aama.1995.1021> | **F7 rooted triplet** |

### 5.2 教科书（最佳单一来源）

**Semple & Steel, *Phylogenetics* (2003), Oxford University Press** —— 上述多条结果的统一叙述处：
- **§3.8** Splits-Equivalence
- **§6.4** quartet 系统与 C–S 推理规则（= **T0.1**）
- **§7.2** 四点条件 / Buneman 定理（= **T0.2**）

**Steel, *Phylogeny: Discrete and Random Processes in Evolution* (2016), SIAM** ——
不变量（**I 组**）与溯祖（**M 组**）的权威综述。

> 💡 **重要结论**：**多数「下载失败」条目的关键公式/证明已在已下载的文献中有完整转述**
> —— 例如 I1/I2 在 `Sturmfels2004` / `AllmanRhodes2006` / `Casanellas2011` 中，
> M1 在 `ChifmanKubatko2015` 中，T0.1 在 `Huber2018` / `HuberEtAl2017` 中。
> ⇒ **不阻塞形式化推进**；付费墙文献只在需要「原始出处」时才有必要。
