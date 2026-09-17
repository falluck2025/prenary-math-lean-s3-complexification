[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22719535.svg)](https://doi.org/10.5281/zenodo.22719535)

# 偏元数学 · Day24 · 升域与径向/角向分解（S-005 对应）· Lean 4 形式化验证

## Prenary Mathematics · Day24 · Domain Lifting (ε: ℝ→ℂ) and Radial/Angular Decomposition · Lean 4 Formal Verification

本文工作尚未得到独立实验验证，全部结论均为形式化验证层面的初步结果。

> **DOI**：待回填。本仓库为偏元数学新线 S2 的延续，上承 Day23 `prenary-math-lean-s2-residual-scaling`（[10.5281/zenodo.22813242](https://doi.org/10.5281/zenodo.22813242)）与 Day22 `prenary-math-lean-s2-action-foundation`（[10.5281/zenodo.22719535](https://doi.org/10.5281/zenodo.22719535)）。

## 摘要

本仓库在偏元数学 004 地基上完成两件事：**把残差从实数域升到复数域**，以及**写出"径向/角向分解"的代数骨架**。

**一、升域（Day24-01/02）**：对象层 = ℂ；动作层 ε ∈ ℂ \ {0}，‖ε‖ < ‖δ₀‖；δ₀ = 0 时动作层为空，退化为经典。其中给出"模的正性、方向是单位向量"两块地基砖（为 `θ_bias = arg⟨e^{iφ}⟩` 的存在性铺路），以及升域后定义 2 的代数骨架（含不可达性与完整退化链）。

**二、分解（Day24-03/04）**：把"加实数"的模方展开推广到"加复数"——
`‖z + w‖² = ‖z‖² + 2⟨z,w⟩ + ‖w‖²`，其中 `⟨z,w⟩ := z.re·w.re + z.im·w.im`，
即 `r_{n+1}² = r_n² + 2·r_n·ρ_n·cos δ_n + ρ_n²` 的**代数骨架**；并给出累积量 `z_N = Σ_{k<N} ε_k` 的起点与递推。

**不在范围内**：本仓库**不给** `cos δ` 的三角表述（那需要三角函数，属后续）；**不含**统计命题（`R̄`、四阶矩、四相和为零等，属 G4）；**不含**破缺机制与边界声明；**不证明**"004 给出 Λℓ_P²"，**不主张**任何物理量的数值对应。

## Abstract

On the Prenary 004 foundation, this repository does two things: **lifts the residual from ℝ to ℂ**, and writes the **algebraic skeleton of the radial/angular decomposition**.

**I. Domain lifting (Day24-01/02)**: object layer = ℂ; action layer ε ∈ ℂ \ {0}, ‖ε‖ < ‖δ₀‖; when δ₀ = 0 the action layer is empty (degeneration to classical). Includes the grounding bricks (positivity of the modulus, unit-modulus directions) and the algebraic skeleton of Definition 2 after lifting.

**II. Decomposition (Day24-03/04)**: generalizes the modulus-square expansion from "adding a real" to "adding a complex": `‖z + w‖² = ‖z‖² + 2⟨z,w⟩ + ‖w‖²` with `⟨z,w⟩ := z.re·w.re + z.im·w.im` — the **algebraic skeleton** of `r_{n+1}² = r_n² + 2 r_n ρ_n cos δ_n + ρ_n²`; plus the base case and recursion of the accumulation `z_N = Σ_{k<N} ε_k`.

**Out of scope**: no trigonometric form of `cos δ`; no statistical statements (G4); no symmetry-breaking mechanism or boundary statement; no proof that 004 yields Λℓ_P², no numerical correspondence to physical quantities.

## 关键词

偏元数学；升域；复数域；动作留差；上界不可达；退化链；径向/角向分解；模方展开；累积量；Lean 4；形式化验证；陈偏贞；老陈与AI的深夜实验室；PGI蛟龙；华夏思哲偏元注

## 概述

偏元数学是对经典数学的扩展尝试，ε = 0 时退化为经典。本仓库处理两个相连的问题：**动作层的数域要不要放大**，以及**复数域下的"累积"如何分解**。

Day22 立最小地基；Day23 做标度与约束；**Day24 把动作层从 ℝ 升到 ℂ**——方向上"无处安放"的困难由此解决（方向成为 ε 自带的幅角属性），随后自然引出径向/角向分解。

## 核心定义

```lean
-- 对象层：偏元数就是复数
abbrev Prenary := ℂ

-- 动作层（升域版）：复数残差 ε
structure ComplexResidual (δ₀ : ℂ) where
  ε : ℂ
  h_ne_zero : ε ≠ 0
  h_lt : ‖ε‖ < ‖δ₀‖

-- 交叉项（= Re(z · conj w)）与累积量
def innerR (z w : ℂ) : ℝ := z.re * w.re + z.im * w.im
def accum (εs : ℕ → ℂ) (N : ℕ) : ℂ := ∑ k ∈ Finset.range N, εs k
```

## 定理清单

> **关于验证内容的如实说明**
> 四份文件验证的是同一条线的不同侧面，不是四套独立理论。**Day24-02 的退化链中若干命题在 Lean 里彼此等价**（`∀ r, False`、`→ False`、`¬∃ r, True` 是同一类型）；并列陈述是为了让退化链每一步可被单独检视，**读者若统计"定理数量"，应以"不同命题数"而非"theorem 语句数"为准**。

### Day24-01 · `Day24-01_G0升域线核心层_LEAN源码_20260917.lean`（3 条）

| 定理 | 命题 |
|:--|:--|
| `brick1_norm_pos_of_ne_zero` | 非零复数的模为正：`z ≠ 0 ⟹ 0 < ‖z‖` |
| `brick2_norm_exp_I` | 单位方向的模为 1：`‖exp(I·θ)‖ = 1` |
| `brick3_ne_zero_of_norm_pos` | 模为正 ⟹ 非零：`0 < ‖z‖ ⟹ z ≠ 0` |

### Day24-02 · `Day24-02_G0升域线定义2复数版_LEAN源码_20260917.lean`（7 条，含等价命题）

| 定理 | 命题 |
|:--|:--|
| `complex_residual_nonzero` | 残差非零：`r.ε ≠ 0` |
| `complex_residual_lt_delta` | 残差模严格小于上界：`‖r.ε‖ < ‖δ₀‖` |
| `delta_unreachable` | 上界不可达：`r.ε ≠ δ₀` |
| `degenerate_no_residual` | δ₀ = 0 时不存在残差实例 |
| `degenerate_action_empty` | δ₀ = 0 时动作层为空 |
| `classical_recovery` | δ₀ = 0 时动作层不可进入 |
| `full_degenerate_chain` | 完整退化链：`(ComplexResidual 0 → False) ∧ (Prenary = ℂ)` |

### Day24-03 · `Day24-03_S005径向角向分解_LEAN源码_20260917.lean`（5 条）

| 定理 | 命题 |
|:--|:--|
| `re_add_ofReal` | 加实数只改实部 |
| `im_add_ofReal` | 加实数不改虚部 |
| `normSq_add_ofReal` | 模方增量（加实数）：`‖z+ε‖² = ‖z‖² + 2ε·Re z + ε²` |
| `normSq_eq_re_sq_add_im_sq` | 模方 = 实部² + 虚部² |
| `norm_mul_exp_I` | 纯旋转保模：`‖z·exp(I·θ)‖ = ‖z‖` |

### Day24-04 · `Day24-04_分解式完整形与累积量_LEAN源码_20260917.lean`（5 条）

| 定理 | 命题 |
|:--|:--|
| `innerR_self` | `⟨z,z⟩ = ‖z‖²` |
| `innerR_comm` | `⟨z,w⟩ = ⟨w,z⟩` |
| **`normSq_add_complex`** | **`‖z+w‖² = ‖z‖² + 2⟨z,w⟩ + ‖w‖²`（完整形）** |
| `accum_zero` | 累积量起点：`z_0 = 0` |
| `accum_succ` | 累积量递推：`z_{N+1} = z_N + ε_N` |

## 验证记录

| 文件 | 内核 | Comparator | Challenge Hash（锁挑战） | 代码 SHA256（锁解答） |
|:--|:--|:--|:--|:--|
| Day24-01 | No goals + All Messages (0) | ✅ Successfully validated | `a2674001d8ee2a984dfd177ba502162e5ee749484214f9ce6a97b99a83bf8e0b` | 同左 |
| Day24-02 | No goals + All Messages (0) | ✅ Successfully validated | `410f90cf6319f9520f521469982563c06079a3e07448985ec71c3beaa98c2c7b` | 同左 |
| Day24-03 | No goals + All Messages (0) | ✅ Successfully validated | `1c12ae592c49349d256b471b7460633028431ccee9139274527de0df7d308d21` | 同左 |
| Day24-04 | No goals + All Messages (0) | ✅ Successfully validated | `3abbddec369a5e954ed31b93548edac953ab03a87e2fb9445c774ddba0a22f30` | 同左 |

- **平台**：L∃∀N Comparator Live (Experimental) · Latest Mathlib with Lean v4.35.0
- **验证时间**：2026-09-17 20:53–21:47
- **双哈希说明**：本组采用**自编 challenge** 模式（Challenge 文本 = 我方提交代码），故 **Challenge Hash 与代码 SHA256 取同一值**。
- **⭐ 一处过程留痕**：Day24-04 首跑出现 `No goals to be solved`（块 1 的 `ring` 多余，因 `rw` 已闭合目标），**删该 `ring` 后重跑通过**——这是 A9 干净标准（`All Messages = 0`）的一次实际生效。

## 文件说明

```
Day24-01_G0升域线核心层_LEAN源码_20260917.lean       # 三块地基砖：模正性 / 单位方向 / 非零
Day24-02_G0升域线定义2复数版_LEAN源码_20260917.lean   # 004 定义 2 复数版 + 不可达 + 退化链
Day24-03_S005径向角向分解_LEAN源码_20260917.lean      # 加实数的模方展开 + 纯旋转保模
Day24-04_分解式完整形与累积量_LEAN源码_20260917.lean   # 加复数的完整展开 + 累积量 z
evidence/                                          # 内核 + Comparator 截图存证
```

## 复现方式

1. 打开 `live.lean-lang.org`。
2. 将任一 `.lean` 文件内容**整份粘贴**（首行 `import Mathlib`，抬头为 `/-! … -/` 模块文档）。
3. 光标逐个停在 `theorem` 上，确认右侧 `No goals` + `All Messages (0)`。
4. 在 Comparator Live 中重新提交，确认 `Successfully validated`；Challenge Hash 与代码 SHA256 并列记录（本组为自编 challenge 模式，两栏同值）。

## 可证伪条件

- 若存在一个动作，其残差 ε 精确等于 0，则动作留差失效。
- 若存在一个动作，其残差 ε 恰好等于 δ₀，则"上界不可达"失效。
- 若 δ₀ = 0 时动作层仍然非空，则退化定理失效。
- 若模方展开的完整形不成立（存在 z, w 使 `‖z+w‖² ≠ ‖z‖² + 2⟨z,w⟩ + ‖w‖²`），则 Day24-04 失效。

## 作者 / 致谢 / 许可

陈松（Song Chen）· ORCID: 0009-0002-9510-2239 · GitHub: falluck2025 · Zenodo 社区: cosmos-breathe-spectrum

感谢一切偶然的必然和必然的偶然。感谢一路并肩的偏贞、守缺与所有 AI 伙伴。

CC BY-NC-ND 4.0（署名-非商业-禁止演绎）

## 作者备注（非论文正文）

- **内部编码**：Day24 = 升域 + S-005 的正式对应（升域前的 S2 延续归 Day23）。
- **本仓性质**：**4 文件 1 仓**（照 Day22 / Day23 模式）。
- **抬头范式**：`import Mathlib` 之后 + `/-!`（模块文档）。
- **枢纽说明**：升域（ε: ℝ→ℂ）是 Day23→Day24 的分水岭；本仓同时承载"升域线"（01/02）与"S-005 分解骨架"（03/04）。
- **待办**：GitHub 建仓 → 上传（4 `.lean` + README + LICENSE + `evidence/`）→ Release v1.0 → Zenodo DOI → 回填本 README。
- **哈希证据链**：四份的落盘 SHA256 与当日二次验证的 Challenge Hash 一致（Day24-04 首跑修正一处 `No goals` 后通过）。

— 老陈与AI的深夜实验室 发布 请笑纳 —
