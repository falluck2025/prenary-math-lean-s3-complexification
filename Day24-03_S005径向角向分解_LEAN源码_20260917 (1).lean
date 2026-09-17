import Mathlib

/-! ================================================================
   偏元数学 · Day24 · S-005 数学侧 · 径向/角向分解（核心层）
   ------------------------------------------------------------------
   核心：为 S-005 的"径向增量 = ε·cos φ"打地基砖。
   本稿范围：分四块，风险由低到高，逐块验证——
     块 1、3 是"分量的代数"（低风险）
     块 2 是"模方的二阶展开"（中风险）
     块 4 是"纯旋转保模"，对应"φ = π/2 时零累积"（中风险）
   不做：本件给的是代数骨架，**不含**"均匀 ⟹ √n"这类统计命题
         （那需要分布与期望，属后续 G4）；不含边界声明与破缺机制。
   注：Day24 = 升域 + S-005 的正式对应；本件为其第 3 节（S-005 首块）；
       上承 Day23 prenary-math-lean-s2-residual-scaling
       与 Day22 prenary-math-lean-s2-action-foundation。
   日期：2026-09-17（重跑版）
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace S005Core

/- 块 1a（低风险）：加实数只改实部 -/
theorem re_add_ofReal (z : ℂ) (ε : ℝ) : (z + (ε : ℂ)).re = z.re + ε := by
  simp [Complex.add_re, Complex.ofReal_re]

/- 块 1b（低风险）：加实数不改虚部 -/
theorem im_add_ofReal (z : ℂ) (ε : ℝ) : (z + (ε : ℂ)).im = z.im := by
  simp [Complex.add_im, Complex.ofReal_im]

/- 块 2（中风险）：模方的增量 = 2·ε·Re z + ε²
   用途：一阶忽略 ε² ⟹ Δ(|z|²) ≈ 2·ε·Re z ⟹ Δ|z| ≈ ε·(Re z)/|z| = ε·cos φ -/
theorem normSq_add_ofReal (z : ℂ) (ε : ℝ) :
    Complex.normSq (z + (ε : ℂ)) = Complex.normSq z + 2 * ε * z.re + ε ^ 2 := by
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/- 块 3（低风险）：模方 = 实部² + 虚部² -/
theorem normSq_eq_re_sq_add_im_sq (z : ℂ) :
    Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.normSq_apply]
  ring

/- 块 4（中风险）：纯旋转保模 —— 对应"φ = π/2 时零累积" -/
theorem norm_mul_exp_I (z : ℂ) (θ : ℝ) :
    ‖z * Complex.exp (Complex.I * (θ : ℂ))‖ = ‖z‖ := by
  rw [Complex.norm_mul]
  have h : ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [h, mul_one]

end S005Core
