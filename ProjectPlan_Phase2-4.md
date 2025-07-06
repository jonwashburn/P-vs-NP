# Project Plan — Phases 2 → 4  
*Completion of the Recognition-Science Lean Proof of **P ≠ NP***

---
## Phase 2 — Balanced Parity & Asymptotic Analysis

### 2.1 `BalancedParity.lean` — Balanced–Parity Encoding
1. **Type-Level Encoding**  
   • Define `ParityBit : Type := Bool` and an inductive `BPString` ensuring equal `0`/`1` count.  
   • Prove `BPString` is a *free ℤ₂-module* of rank `n − 1` (one parity constraint).
2. **Embedding into `Fin n`**  
   • Construct an explicit bijection `encode : BPString n → { s : Fin (2^n) // parity s = 0 }`.  
   • Show `decode ∘ encode = id` (information preservation).
3. **Complexity Lemmas**  
   • `encoding_time ≤ O(n)` via tail-recursive bit scan.  
   • `recognition_time ≥ Ω(n)` by counting argument → *no sub-linear recognizer exists*.
4. **Interoperability Proofs**  
   • Map TM tape → balanced-parity string (for Layer 1).  
   • Map CA block → balanced-parity word (for Layer 2).

### 2.2 `AsymptoticAnalysis.lean` — Separation `n^{1/3} log n ≪ n`
1. **Real-Analysis Foundations**  
   • Import `Mathlib.Analysis.Asymptotics`. Prove monotonicity of `n ↦ n^{1/3} log n` for `n ≥ 8`.
2. **Main Limit Lemma**  
   `lemma lim_ratio : (n^{1/3} log n) / n → 0` as `n → ∞` using l'Hôpital twice.
3. **ε-Separation Theorem**  
   Given `ε > 0`, ∃ `N`, ∀ `n ≥ N`, `(n^{1/3} log n) / n < ε`.  
   This plugs directly into `Core.recognition_science_resolution` (lines ≃ 90).
4. **Bridging to Recognition Science**  
   Replace `sorry` in `core` with calls to `lim_ratio` to close asymptotic goals.

---
## Phase 3 — Proof Refinements & Final Compilation

1. **Close Remaining `sorry`s**  
   • RSFoundation (3 trivial physics lemmas).  
   • TuringMachine halting cases (2).  
   • CellularAutomaton reversibility & separation (4).
2. **Remove "no goals to be solved" placeholders** — ensure clean tactic flow.
3. **Linter Clean-Up**  
   • Enable `set_option linter.all true` and resolve warnings (unused vars, doc-strings for primes).
4. **100 % Compilation Target**  
   • `lake build` succeeds with **zero errors, zero unintentional warnings**.

---
## Phase 4 — Comprehensive Testing & Verification

### 4.1 Property-Based Testing (`Tests/`)
*Use `StdLean` + `LakeTest`*
1. **Random Balanced-Parity Generation**  
   Verify `decode ∘ encode = id` for 10 000 samples up to `n = 128`.
2. **TM Simulation Harness**  
   • Execute `bit_doubling_TM` on random tapes, compare against reference Python model.
3. **CA Block-Rule Checker**  
   • Exhaustive enumeration of 16-cell blocks (2¹⁶ ≈ 65 k) to verify reversibility.

### 4.2 Formal Verification Scripts
1. **`#eval` Benchmarks**  
   Measure run-time of encoding/decoding to show practical bounds.
2. **Meta-Proof Audits**  
   Use `#guard_hyp` to assert absence of unchecked goals in theorems.

### 4.3 Continuous-Integration (GitHub Actions)
1. **Matrix Build**: macOS | Ubuntu | Windows, Lean 4 v4.12 & v4.13-nightly.  
2. **Linter & Coverage**: fail CI on any new `sorry` or linter warning.

---
### Deliverable Check-List
- [ ] Phase 2 files compile & integrate with `Core`.  
- [ ] All `Core` asymptotic `sorry`s replaced.  
- [ ] Phase 3 removes *all* remaining `sorry`s.  
- [ ] Phase 4 pipeline green with 100 % test pass.

---
*Prepared ☑︎ for continued development in Cursor.* 