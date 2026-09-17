import Mathlib

/-! ================================================================
   偏元数学 · Day24 · S-005 数学侧 · 径向/角向分解（完整形 · 代数骨架）
   ------------------------------------------------------------------
   核心：把"加实数 ε"的模方展开（Day24-03 块 2）推广到"加复数 w"：
         ‖z + w‖² = ‖z‖² + 2⟨z,w⟩ + ‖w‖²,   ⟨z,w⟩ := z.re·w.re + z.im·w.im
         即  r_{n+1}² = r_n² + 2·r_n·ρ_n·cos δ_n + ρ_n²  的代数骨架
         （cos δ 的三角表述、以及"平均场 z"的分布性质，属后续）。
   本稿范围：交叉项的代数 + 模方展开完整版 + 累积量 z 的起点与递推，共 5 条。
   不做：不给 cos δ 的三角定义；不含统计命题（属 G4）；
         不含破缺机制与边界声明。
   注：Day24 = 升域 + S-005 的正式对应；本件为其第 4 节（完整形）；
       上承 Day24-03（径向/角向分解核心层）、Day24-01/02（升域线）。
   日期：2026-09-17
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace S005Decomp

/-- 交叉项：z 与 w 的实内积（等于 Re(z · conj w)） -/
def innerR (z w : ℂ) : ℝ := z.re * w.re + z.im * w.im

/-- 累积量（平均场）：z_N = Σ_{k<N} ε_k -/
def accum (εs : ℕ → ℂ) (N : ℕ) : ℂ := ∑ k ∈ Finset.range N, εs k

-- 块 1：交叉项自身 = 模方（z = w 时）
--   ※ rw 后目标两侧已同一表达式、自动闭合，故不再追加 ring（否则报 No goals to be solved）
theorem innerR_self (z : ℂ) : innerR z z = Complex.normSq z := by
  unfold innerR
  rw [Complex.normSq_apply]

-- 块 2：交叉项对称
theorem innerR_comm (z w : ℂ) : innerR z w = innerR w z := by
  unfold innerR
  ring

-- 块 3：模方展开（完整版）—— ‖z+w‖² = ‖z‖² + 2⟨z,w⟩ + ‖w‖²
theorem normSq_add_complex (z w : ℂ) :
    Complex.normSq (z + w) = Complex.normSq z + 2 * innerR z w + Complex.normSq w := by
  unfold innerR
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply]
  simp [Complex.add_re, Complex.add_im]
  ring

-- 块 4：累积量起点（N = 0 时 z = 0）
theorem accum_zero (εs : ℕ → ℂ) : accum εs 0 = 0 := by
  unfold accum
  simp

-- 块 5：累积量递推（z_{N+1} = z_N + ε_N）
theorem accum_succ (εs : ℕ → ℂ) (N : ℕ) : accum εs (N + 1) = accum εs N + εs N := by
  unfold accum
  rw [Finset.sum_range_succ]

end S005Decomp
