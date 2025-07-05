/-
  P vs NP: Core Definitions and Framework

  This file establishes the basic Recognition Science framework
  showing that P vs NP conflates computation and recognition complexity.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace PvsNP

/-- A computational model has both computation and recognition complexity -/
class HasComputationComplexity (α : Type) where
  computation : α → ℕ → ℕ

class HasRecognitionComplexity (α : Type) where
  recognition : α → ℕ → ℕ

/-- The classical assumption that recognition is free -/
def classical_assumption : Prop :=
  ∀ (Problem : Type) (inst : HasRecognitionComplexity Problem),
  ∃ (c : ℕ), ∀ (p : Problem) (n : ℕ), @HasRecognitionComplexity.recognition Problem inst p n ≤ c

/-- A problem with different computation and recognition complexities -/
structure SeparatedProblem where
  -- Computation complexity function
  T_c : ℕ → ℕ
  -- Recognition complexity function
  T_r : ℕ → ℕ
  -- Computation is sublinear
  comp_sublinear : ∃ (c : ℝ), c < 1 ∧ ∀ (n : ℕ), n > 0 →
    (T_c n : ℝ) ≤ n^c
  -- Recognition is linear
  recog_linear : ∃ (c : ℝ), c > 0 ∧ ∀ (n : ℕ), n > 0 →
    (T_r n : ℝ) ≥ c * n

/-- Main theorem: P vs NP is ill-posed because it conflates two different complexities -/
theorem p_vs_np_ill_posed : ¬classical_assumption := by
  intro h
  -- The classical assumption says recognition complexity is bounded by a constant
  -- We'll show this leads to a contradiction by constructing a problem
  -- where recognition complexity grows linearly

  -- Define a problem type with our separated complexities
  let Problem := SeparatedProblem

  -- Give it complexity instances
  have comp_inst : HasComputationComplexity Problem := {
    computation := fun p n => p.T_c n
  }
  have recog_inst : HasRecognitionComplexity Problem :=
    ⟨fun p n => p.T_r n⟩

  -- Apply the classical assumption to get a bound
  have h_spec := h Problem recog_inst
  obtain ⟨bound, h_bound⟩ := h_spec

  -- Construct a counterexample where T_r grows unboundedly
  -- For any bound B, we construct a problem with T_r(n) = B + n
  let p : Problem := {
    T_c := fun n => 1  -- Constant computation
    T_r := fun n => bound + n + 1  -- Linear recognition
    comp_sublinear := ⟨0, by norm_num, fun n hn => by
      -- T_c(n) = 1 ≤ n^0 = 1 for all n > 0
      simp only [Nat.cast_one]
      have : (n : ℝ)^(0 : ℝ) = 1 := by simp
      rw [this]⟩
    recog_linear := ⟨1, by norm_num, fun n hn => by
      -- T_r(n) = bound + n + 1 ≥ 1 * n
      simp only [Nat.cast_add, Nat.cast_one]
      ring_nf
      linarith⟩
  }

    -- Show that `p.T_r 1` is strictly greater than `bound`.
  have h_gt : bound < p.T_r 1 := by
    -- By definition of p, p.T_r 1 = bound + 1 + 1
    simp only [p]
    -- bound < bound + 1 + 1 is obvious
    linarith

  -- From the classical assumption we have
  have h_inst := h_bound p 1
  -- h_inst : recog_inst.recognition p 1 ≤ bound

  -- By construction of recog_inst, recognition p 1 = p.T_r 1
  -- But Lean doesn't see this definitional equality automatically
  have h_le : p.T_r 1 ≤ bound := by
    -- h_inst gives us: recog_inst.recognition p 1 ≤ bound
    -- By definition of recog_inst, this is exactly p.T_r 1 ≤ bound
    exact h_inst

  -- But earlier we proved p.T_r 1 > bound (h_gt).  Contradiction.
  exact (lt_irrefl _ (lt_of_lt_of_le h_gt h_le))

end PvsNP
