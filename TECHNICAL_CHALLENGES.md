# Technical Challenges & Road-Map

This document tracks the **mathematical / formalisation hurdles** still blocking complete elimination of the remaining sorries in the Lean4 P vs NP project.

_Current build:_ **compiles with 14 sorries** (see `SORRY_STATUS_REPORT.md`).

---

## 1. Balanced-Parity Code Lemmas  *(RecognitionBound.lean)*

| Lemma | Status | Notes |
|-------|--------|-------|
| `card_odds` | ❌ | NEW: Helper lemma to count odd numbers in Fin (4*m). Requires bijection proof. |
| `mask_count_ones` | ❌ | Depends on `card_odds`. Once that's proven, this follows easily. |
| `encoded_parity_correct` | ❌ | Requires detailed parity calculation after flipping bit 0. |
| `information_lower_bound` | ❌ | Current encoding (flip-bit-0) isn't strong enough; we either need a **stronger code** (e.g. flip every even index) **or** weaken the statement.  Decision pending. |

### Progress Update
- Added `card_odds` as a helper lemma with clear structure
- Identified the key bijection: `j ↦ ⟨2*j + 1, _⟩` from `Fin (2*m)` to odd numbers
- Need to complete the division property: `(2*k + 1) / 2 = k`

### Plan of Attack

1. Prove a **general helper**
   ```lean
   lemma card_odds (m : ℕ) :
     (Finset.univ.filter (fun (i : Fin (4*m)) => i.val % 2 = 1)).card = 2*m
   ```
   by building a bijection `j ↦ ⟨2*j + 1, _⟩` from `Fin (2*m)`.
2. Deduce `mask_count_ones` from `card_odds` and the `n = 4*m` hypothesis.
3. Finish `encoded_parity_correct` with `Nat.mod_two_eq_zero_or_one` & simple parity arithmetic.
4. Decide on a **balanced-parity scheme** that really yields indistinguishability; propose flipping all indices `≡ 0 (mod 4)` for bit 1.

---

## 2. Morton Encoding Arithmetic  *(SATEncoding.lean)*

| Lemma | Status | Blocking on |
|-------|--------|-------------|
| `morton_simple_inverse` | ❌ | Attempted detailed proof but hit arithmetic complexity. Needs `Nat.add_mul_mod_self_left` and related lemmas. |
| `morton_decode_encode` | ❌ | Bit-level proof; will reuse `Nat.shiftl`/`Nat.land` results from `Nat.Bits`. |

### Progress Update
- Attempted full arithmetic proof for `morton_simple_inverse`
- Key insight: need `x + 1024*y < 1024²` to apply modulo properties
- Blocked on complex rewrite chains with Lean's arithmetic

### Plan

* Provide small library `Helpers/BitInterleave.lean` encapsulating bit interleaving proofs.
* For the *simple* base-1024 variant, import `Mathlib.Tactic.Linarith` and finish with `Nat.mod_mul_left_div_self` type lemmas.

---

## 3. Cellular-Automaton Dynamics  *(SATEncoding.lean)*

Seven sorries all stem from the **abstract CA model** (`block_update`, `ca_run`) being skeletal.  We should:

1. Move the CA core to `CellularAutomaton/Core.lean`.
2. Prove locality (`block_update_affects_only_neighbors`) using pattern matching on coordinates.
3. Establish speed bound via induction on steps (`signal_speed`).
4. Use these to bound `sat_computation_complexity` and the downstream asymptotic theorems.

---

## 4. Definitional-Equality Glitch  *(Core.lean)*

We still rely on a small `sorry` where Lean fails to rewrite `@HasRecognitionComplexity.recognition` to `p.T_r`.

### Progress Update
- Tried multiple approaches: simp lemma, change tactic, direct rewrite
- This appears to be a fundamental Lean limitation with typeclass instances
- The workaround sorry is well-documented and isolated

---

## Summary of This Round

**Sorries: 13 → 14** (added `card_odds` helper)

Key achievements:
1. Identified precise helper lemmas needed for balanced parity
2. Made concrete progress on arithmetic proofs (even if not completed)
3. Better understanding of where Lean struggles (definitional equality, complex arithmetic)

## Next Immediate Steps

1. Complete `card_odds` by proving `(2*k + 1) / 2 = k` 
2. Use mathlib's `Nat.add_div_right` for the division
3. Consider simpler balanced parity encoding to avoid complex proofs 