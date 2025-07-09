/-
  Measurement Helpers for Recognition Science

  This module provides the HasMeasurement typeclass and related lemmas
  for handling physical measurement energy in recognition processes.
-/

import PvsNP.Physics.EnergyBounds
import Mathlib.Tactic

open PvsNP.Physics.EnergyBounds

/-- Abstract type of physical instances with measurable energy. -/
class HasMeasurement (A : Type) where
  measurement_energy : A → ℕ → ℝ

namespace HasMeasurement
variable {A} [HasMeasurement A]

/-- Universal coherence lower bound:  E_coh·n ≤ E   -/
axiom coherence_bound (a : A) (n : ℕ) :
  E_coh * n ≤ measurement_energy a n

/-- Coherence ⇒ Holographic ⇒ λ_rec bound -/
lemma holographic_bound (a : A) (n : ℕ) :
  λ_rec * n ≤ measurement_energy a n :=
by
  have h₁ : λ_rec * n ≤ E_coh * n := by
    have : λ_rec ≤ E_coh := λ_le_Ecoh
    have hn : (n : ℝ) ≥ 0 := Nat.cast_nonneg n
    nlinarith
  have h₂ := coherence_bound a n
  nlinarith

end HasMeasurement
