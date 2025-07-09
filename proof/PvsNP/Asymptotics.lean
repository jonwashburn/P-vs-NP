/-
  P vs NP: Asymptotic Analysis Helpers

  This file provides asymptotic analysis lemmas needed for the
  Recognition Science separation theorem.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace PvsNP.Asymptotics

open Filter Topology Real

/-- The key asymptotic bound: 2 * log x / x^(2/3) → 0 as x → ∞ -/
lemma log_div_pow_twoThirds_tendsto_zero :
  Tendsto (fun x : ℝ => (2 * log x) / x^(2/3 : ℝ)) atTop (𝓝 0) := by
  -- This follows from the general fact that log x grows slower than any positive power
  -- We use the standard result that log x / x^α → 0 for any α > 0
  have h_alpha_pos : (0 : ℝ) < 2/3 := by norm_num
  -- Use the standard Mathlib result about log vs polynomial growth
  have h_log_bound : Tendsto (fun x : ℝ => log x / x^(2/3 : ℝ)) atTop (𝓝 0) := by
    apply tendsto_log_div_rpow_atTop
    exact h_alpha_pos
  -- Scale by the constant factor 2
  have h_scale : Tendsto (fun x : ℝ => (2 * log x) / x^(2/3 : ℝ)) atTop (𝓝 0) := by
    simp only [mul_div_assoc]
    apply Tendsto.const_mul 2
    exact h_log_bound
  exact h_scale

/-- For any ε > 0, there exists N such that for all n ≥ N, 2 * log n / n^(2/3) < ε -/
lemma log_div_pow_twoThirds_eventually_lt (ε : ℝ) (hε : ε > 0) :
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (2 * log (n : ℝ)) / (n : ℝ)^(2/3 : ℝ) < ε := by
  -- Use the tendsto result to get eventual boundedness
  have h_tendsto := log_div_pow_twoThirds_tendsto_zero
  -- From the limit being 0, we can extract eventual boundedness
  have h_bound : ∀ᶠ x in atTop, (2 * log x) / x^(2/3 : ℝ) < ε := by
    rw [tendsto_nhds] at h_tendsto
    have h_mem : (0 : ℝ) ∈ Set.Iio ε := by
      rw [Set.mem_Iio]
      exact hε
    have h_open : IsOpen (Set.Iio ε) := isOpen_Iio
    exact h_tendsto (Set.Iio ε) h_open h_mem
  -- Convert the filter statement to a natural number bound
  rw [eventually_atTop] at h_bound
  obtain ⟨N_real, hN⟩ := h_bound
  -- Choose N large enough to ensure positivity and the bound
  use max 8 (Nat.ceil N_real)
  intro n hn
  have hn_real : (n : ℝ) ≥ N_real := by
    have h_max : (max 8 (Nat.ceil N_real) : ℝ) ≤ n := by
      simp only [Nat.cast_le]
      exact hn
    have h_ceil : (Nat.ceil N_real : ℝ) ≤ max 8 (Nat.ceil N_real) := by
      exact le_max_right 8 (Nat.ceil N_real)
    have h_le : N_real ≤ Nat.ceil N_real := Nat.le_ceil N_real
    linarith
  have hn_pos : (0 : ℝ) < n := by
    have h_eight : (8 : ℕ) ≤ n := by
      exact le_trans (le_max_left 8 (Nat.ceil N_real)) hn
    exact Nat.cast_pos.mpr (by linarith)
  -- For positive n ≥ 8, we have 2 * log n / n^(2/3) > 0 for large n
  have h_pos : (0 : ℝ) ≤ (2 * log (n : ℝ)) / (n : ℝ)^(2/3 : ℝ) := by
    apply div_nonneg
    · apply mul_nonneg
      · norm_num
      · exact log_nonneg (by linarith [hn_pos] : 1 ≤ (n : ℝ))
    · exact rpow_nonneg (by linarith [hn_pos]) (2/3 : ℝ)
  -- Apply the bound
  exact hN (n : ℝ) hn_real

end PvsNP.Asymptotics
