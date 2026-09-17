import Mathlib

/-! ================================================================
   偏元数学 · Day24 · G0 升域线 · 004 定义 2 复数版（升域第一步）
   ------------------------------------------------------------------
   核心：把 004 定义 2 的 ε 从 ℝ 升到 ℂ——对象层 = ℂ，动作层 ε ∈ ℂ \ {0}，
         ‖ε‖ < ‖δ₀‖，δ₀ = 0 退化为经典。
   本稿范围：分四块，风险由低到高——
     块 1、2 是"升域后残差的基本性质"（低风险）
     块 3 是"模的严格小于"（中风险）
     块 4 是"退化：δ₀ = 0 时动作层为空"（低风险）
   不做：不含 C4（{φ_n} 不能全同）、不含径向/角向分解（属 S-005）、
         不含任何统计命题（属后续 G4）。
   注：Day24 = 升域 + S-005 的正式对应；本件为其第 2 节；
       上承 Day23 prenary-math-lean-s2-residual-scaling
       与 Day22 prenary-math-lean-s2-action-foundation。
   日期：2026-09-17（重跑版）
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace G0Def2

-- 块 1（低风险）：对象层 = ℂ，升域后 ε ∈ ℂ \ {0}
abbrev Prenary := ℂ

structure ComplexResidual (δ₀ : ℂ) where
  ε : ℂ
  h_ne_zero : ε ≠ 0
  h_lt : ‖ε‖ < ‖δ₀‖

-- 块 2（低风险）：残差非零 / 模严格小于上界
theorem complex_residual_nonzero {δ₀ : ℂ} (r : ComplexResidual δ₀) :
    r.ε ≠ 0 :=
  r.h_ne_zero

theorem complex_residual_lt_delta {δ₀ : ℂ} (r : ComplexResidual δ₀) :
    ‖r.ε‖ < ‖δ₀‖ :=
  r.h_lt

-- 块 3（中风险）：上界不可达（ε ≠ δ₀）
--   ※ 与 9/16 旧稿相比，此处由 "rw + exact lt_irrefl" 改为 "absurd 一步闭合"，
--     以规避 A9 干净标准下的 "No goals to be solved" 风险（结论不变）。
theorem delta_unreachable {δ₀ : ℂ} (r : ComplexResidual δ₀) :
    r.ε ≠ δ₀ := by
  intro h
  exact absurd (h ▸ r.h_lt) (lt_irrefl _)

-- 块 4（低风险）：退化：δ₀ = 0 时动作层为空
theorem degenerate_no_residual (_r : ComplexResidual 0) :
    False := by
  have h_lt : ‖_r.ε‖ < ‖(0 : ℂ)‖ := _r.h_lt
  have h_zero : ‖(0 : ℂ)‖ = 0 := by simp
  rw [h_zero] at h_lt
  have h_nonneg : 0 ≤ ‖_r.ε‖ := norm_nonneg _
  linarith

theorem degenerate_action_empty :
    (∀ _r : ComplexResidual 0, False) := by
  intro _r
  exact degenerate_no_residual _r

theorem classical_recovery :
    (ComplexResidual 0 → False) := by
  intro _r
  exact degenerate_no_residual _r

theorem full_degenerate_chain :
    (ComplexResidual 0 → False) ∧ (Prenary = ℂ) := by
  constructor
  · intro _r
    exact degenerate_no_residual _r
  · rfl

end G0Def2
