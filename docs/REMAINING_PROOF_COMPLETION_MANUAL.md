# Remaining Proof-Completion Manual (Phase 6C)

> **Audience:** Lean contributors familiar with mathlib.
> **Goal:** Remove every remaining `sorry` in the P≠NP Recognition-Science proof and reach a clean `lake build` with `#lint` = 0.

---
## Compile-Blocking Items

### CB-1  `all_foundations_from_meta`
*File:* `Src/PvsNP/RSFoundation.lean`

1. **Strategy**  
   Prove each of the eight foundations one-by-one under the `MetaPrinciple` hypothesis and package them into a tuple.
   * Foundations 1–6 already have *finite* toy models (Unit, Bool, etc.).  Keep those but **close the goal** with the `by` tactic ocean.
   * Replace the final `sorry` with:
     ```lean
     exact
       ⟨foundation1, foundation2, foundation3,
        foundation4, foundation5, foundation6,
        foundation7, foundation8⟩
     ```
     where each `foundationX` is the proof block currently commented.
2. **Lean tips**  
   * Use `simp` heavily for `% 1` equalities.  
   * For Foundation 8 positivity: `have : 0 < phi := by positivity`.  
   * If the tuple grows unwieldy, create helper lemmas `foundation7_unit` etc.

### CB-2  `zero_free_parameters`
*File:* `Src/PvsNP/RSFoundation.lean`

1. **Case Split**  
   ```lean
   by_cases h₁ : constant = 1; · exact Or.inl <| Or.inr <| Or.inr h₁
   by_cases h₂ : constant = phi; · exact Or.inl <| Or.inl h₂
   by_cases h₃ : constant = E_coh; · exact Or.inl <| Or.inr <| Or.inl h₃
   ```
2. **Positive constant fallback**  
   Replace the current placeholder with:
   ```lean
   have hpos : 0 < constant := by
     by_contra hnonpos
     have : constant ≤ 0 := le_of_not_gt hnonpos
     -- derive contradiction with Foundation3_PositiveCost …
     sorry
   ```
3. **φ-power representation**  
   Use `Real.archimedean` to find `n : ℤ` with `(phi^n) ≤ constant < phi^(n+1)` then rewrite to `Nat` using `Int.toNat_ofNat`.
   * Helpful lemmas: `exists_int_pow_nat` in mathlib, `Real.log_pow`.
   * Final line: `exact Or.inr ⟨n.toNat, by ...⟩`.

### CB-4  Formal bound in `computation_recognition_separation`

1. **Replace `h_bound : ... < ε` with an explicit inequality proof.**
2. Suggested helper lemma (place near top of file):
   ```lean
   lemma log_div_pow_twoThirds (ε : ℝ) (hε : ε > 0) :
     ∃ N : ℕ, ∀ n ≥ N, 2 * Real.log n / n^(2/3 : ℝ) < ε := by
     -- use `tendsto` & `eventually_lt_of_tendsto_lt` on
     -- `tendsto_mul` + `tendsto_log_div_pow` (already in mathlib)
     sorry
   ```
3. Inside the main theorem call the lemma with `have ⟨N, hN⟩ := log_div_pow_twoThirds ε hε` then finish with `exact hN _ h_large`.

---
## Code-Quality Tasks

### CQ-1  Move narrative comments
* Create `docs/FOUNDATION_DERIVATIONS.md` and paste long explanatory comment blocks there.
* In Lean files replace the prose with a one-line reference:  `-- See docs/FOUNDATION_DERIVATIONS.md §3`.

### CQ-2  Split large proofs
* Threshold: ≥ 100 logical lines.  
* Break `all_foundations_from_meta` into separate private lemmas `f1_discrete`, `f2_dual`, … then combine with `by` tuple.

### CQ-3  Final lint pass
* Add to root `.lean` file:
  ```lean
  set_option linter.unusedVariables false
  ```
* Run `lake env lean --lint Src`  
  Fix any remaining warnings.

---
## Optional Build Optimisation
* In CI workflow YAML:
  ```yaml
  - name: Fetch lake cache
    run: lake exe cache get
  ```

---
### Completion Checklist
* [ ] CB-1 proof finished
* [ ] CB-2 proof finished
* [ ] CB-3 already done ✓
* [ ] CB-4 bound formalised
* [ ] CQ-tasks completed
* [ ] `lake build` green + `#lint` zero warnings 