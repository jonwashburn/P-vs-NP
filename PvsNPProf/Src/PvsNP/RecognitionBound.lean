/-- Count of true bits in mask equals n/2 -/
theorem mask_count_ones (n : ℕ) (code : BalancedParityCode n) :
  (Finset.filter (fun i => code.mask i = true) Finset.univ).card = n / 2 := by
  -- The filter counts true values
  have : (Finset.filter (fun i => code.mask i = true) Finset.univ) =
         (Finset.filter (fun i => code.mask i) Finset.univ) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    -- For Bool, (b = true) ↔ b
    cases code.mask i with
    | false => simp
    | true => simp
  rw [this]
  exact code.balanced
