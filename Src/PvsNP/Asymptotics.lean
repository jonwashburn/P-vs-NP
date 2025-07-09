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
  -- Use the fact that log x / x^α → 0 for any α > 0
  -- We can use the standard result and scale by 2
  have h_pos : (0 : ℝ) < 2/3 := by norm_num
  -- Recognition Science: The substrate-measurement scale separation is fundamental
  -- log grows slower than any positive power of x
  have h_base : Tendsto (fun x : ℝ => log x / x^(2/3 : ℝ)) atTop (𝓝 0) := by
    -- Use Mathlib's tendsto_log_div_rpow_atTop
    convert tendsto_log_div_rpow_atTop h_pos
    simp
  -- Scale by constant 2
  convert Tendsto.const_mul 2 h_base using 1
  ext x
  simp [mul_div_assoc]

/-- For any ε > 0, there exists N such that for all n ≥ N, 2 * log n / n^(2/3) < ε -/
lemma log_div_pow_twoThirds_eventually_lt (ε : ℝ) (hε : ε > 0) :
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (2 * Real.log n) / (n : ℝ)^(2/3 : ℝ) < ε := by
  -- Use the tendsto result
  have h_tendsto := log_div_pow_twoThirds_tendsto_zero
  -- Convert to eventually property
  rw [tendsto_atTop_nhds] at h_tendsto
  have h_eventually : ∀ᶠ x : ℝ in atTop, |2 * log x / x^(2/3 : ℝ) - 0| < ε := by
    apply h_tendsto
    simp [Metric.ball, dist]
    exact hε
  -- Extract concrete N
  simp at h_eventually
  rw [Filter.eventually_atTop] at h_eventually
  obtain ⟨N₀, hN₀⟩ := h_eventually
  -- Choose N large enough
  use max (Nat.ceil N₀) 2
  intro n hn
  have hn_pos : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro h_zero
    rw [h_zero] at hn
    simp at hn
  have h_n_ge_N₀ : (n : ℝ) ≥ N₀ := by
    calc (n : ℝ) ≥ max (Nat.ceil N₀) 2 := Nat.cast_le.mpr hn
    _ ≥ Nat.ceil N₀ := le_max_left _ _
    _ ≥ N₀ := Nat.le_ceil N₀
  -- Apply the bound
  have h_bound := hN₀ n h_n_ge_N₀
  -- For positive n, 2 * log n / n^(2/3) is positive when n > 1
  have h_n_gt_one : 1 < n := by
    calc 1 < 2 := by norm_num
    _ ≤ max (Nat.ceil N₀) 2 := le_max_right _ _
    _ ≤ n := hn
  have h_log_pos : 0 < log n := log_pos (Nat.one_lt_cast.mpr h_n_gt_one)
  have h_ratio_pos : 0 < 2 * log n / (n : ℝ)^(2/3 : ℝ) := by
    apply div_pos
    · exact mul_pos (by norm_num : (0 : ℝ) < 2) h_log_pos
    · exact rpow_pos_of_pos (Nat.cast_pos.mpr hn_pos) _
  rw [abs_of_pos h_ratio_pos] at h_bound
  simp at h_bound
  exact h_bound

end PvsNP.Asymptotics
