# F84 记账差异的复现脚本与参照表

本目录是 `../../CASTER_F84_FINDING.md` 的**可复现证据**（纯 Python，不依赖 Lean，
不依赖第三方库，只用标准库 + numpy）。

## 结论（一句话）
附录的 **aggregated 式（`sm.tex` 1559–1562，系数照印）** 是**唯一自洽**的 F84 权重表；
它的 `E[w(ab|cd)] − E[w(ac|bd)]` 恰好是印的常数 `2π_Aπ_Cπ_Gπ_Tπ_Rπ_Y·e^{−λ(1+κ)L_T}(1−e^{−λl_x})`
的 **4 倍**。把四条线的系数各除以 4，常数就与印值一致。

## 脚本对照
| 脚本 | 做什么 |
|---|---|
| `caster_f84_check.py` | 第一版（错版，保留作对照）：当时把 matching 语义读错 |
| `caster_f84_check2.py` | 逐字实现附录 Q + 兜底 pattern 概率；三种读法对照 |
| `caster_f84_check3.py` | **决定性**：逐字实现 aggregated 式 ⇒ 比值**恒为 4.000000**；含 JC69 解析核自检（1.2e-15） |
| `caster_f84_check5.py` | `delta-P` 探针：dump aggregated 式的**隐含逐模式权重**（与 Fig. 1D 第 2/3 行角色相反） |
| `caster_f84_check6.py` | 穷举 6 种系数组 ⇒ **只有照印系数给出常数比**（= 4） |
| `caster_f84_pin.py` | 16 个钉死模式下四种行赋值穷举 ⇒ 字面 Fig. 1D **漂移**、行 2/3 对调**恒为 2** |
| `caster_f84_cand.py` | 三种候选表并列对照（AGG / SYM / LIT） |
| `caster_f84_refdump.py` | dump aggregated 式的完整隐含表（32 个非零模式）⇒ `caster_f84_reference_table.json` |
| `caster_f84_collapse.py` | ★ **关键塌缩**：8 个「侧向事件」形式与原 aggregated 式**完全一致**（1.1e-13） |
| `caster_f84_scaffold.py` | ★ 推导脚手架：`Σ_{i∈U} K(t)_{p,i} = π_U + e^{−λt}(1[p∈U] − π_U)`（2.2e-16） |

## 怎么跑（Windows 上）
```
python <脚本名>.py
```
（`caster_f84_reference_table.json` 是 `caster_f84_refdump.py` 的输出，供 Lean 侧 `wF84`/`EwF84` 自检。）
