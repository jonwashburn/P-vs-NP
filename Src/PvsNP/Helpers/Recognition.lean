/-
  Recognition Problem Helpers

  This module provides the RecognitionProblem structure and key lemmas
  for baseline recognition costs and non-negativity.
-/

import PvsNP.Helpers.Measurement
import Mathlib.Tactic

open PvsNP.Physics.EnergyBounds PvsNP.Helpers.HasMeasurement

structure RecognitionProblem where
  Instance   : Type
  [measInst] : HasMeasurement Instance
  recogn_cost : Instance → ℕ → ℝ
  cost_def    : ∀ (i : Instance) (n : ℕ),
    recogn_cost i n = (HasMeasurement.measurement_energy i n) /
                      PvsNP.Physics.EnergyBounds.energyPerOp

namespace RecognitionProblem
open PvsNP.Physics.EnergyBounds HasMeasurement

lemma baseline (P : RecognitionProblem) (i : P.Instance) (n : ℕ) :
  λ_rec * n ≤ P.recogn_cost i n :=
by
  have h := holographic_bound i n
  have hpos : energyPerOp > 0 := eOp_pos
  have := (div_le_iff hpos).mpr h
  simpa [P.cost_def, mul_comm] using this

lemma nonneg (P : RecognitionProblem) (i : P.Instance) (n : ℕ) :
  0 ≤ P.recogn_cost i n :=
by
  have h := baseline P i n
  have hλ : λ_rec * n ≥ 0 := by
    have hλpos : λ_rec ≥ 0 := le_of_lt λ_rec_pos
    have hn : (n : ℝ) ≥ 0 := Nat.cast_nonneg n
    exact mul_nonneg hλpos hn
  have : 0 ≤ λ_rec * n := hλ
  exact le_trans this h

end RecognitionProblem
