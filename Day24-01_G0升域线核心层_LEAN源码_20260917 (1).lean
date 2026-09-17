import Mathlib

/-! ================================================================
   偏元数学 · Day24 · G0 升域线 · 核心层首推（三块砖）
   ------------------------------------------------------------------
   核心：为 "θ_bias = arg⟨e^{iφ}⟩ 存在" 打地基砖——
         模的正性、方向是单位向量。
   本稿范围：三块，风险由低到高，逐块验证。
   不做：本件给的是"构件"，**不含**"θ_bias 存在"本身；
         后者要等这里通了再往上搭。不含统计命题与破缺机制。
   注：Day24 = 升域 + S-005 的正式对应；本件为其第 1 节（升域线核心层）；
       上承 Day23 prenary-math-lean-s2-residual-scaling
       与 Day22 prenary-math-lean-s2-action-foundation。
   日期：2026-09-17（重跑版）
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace G0V1

/- 砖 1（低风险）：非零复数的模是正的 -/
theorem brick1_norm_pos_of_ne_zero (z : ℂ) (hz : z ≠ 0) : 0 < ‖z‖ :=
  norm_pos_iff.mpr hz

/- 砖 2（中风险）：单位方向 e^{iθ} 的模为 1 -/
theorem brick2_norm_exp_I (θ : ℝ) : ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/- 砖 3（低风险）：模为正 ⟹ 非零 -/
theorem brick3_ne_zero_of_norm_pos (z : ℂ) (h : 0 < ‖z‖) : z ≠ 0 :=
  norm_pos_iff.mp h

end G0V1
