# Next-Step Road-Map for P ≠ NP Lean Project

> **Status at this commit** – `lake build` succeeds with **14 sorries** and no dependency warnings.  The items below are the remaining blockers to a fully sorry-free build.

---

## SPRINT A  Balanced-Parity lemmas (file `RecognitionBound.lean`)

| Lemma | Goal | Hints / Library Facts |
|-------|------|-----------------------|
| `card_odds` | Prove that exactly `2*m` of the numbers `< 4*m` are odd | • `Finset.card_congr`  • bijection `j ↦ ⟨2*j+1,…⟩`  • `Nat.mod_eq_one_iff`  • `Function.Injective` |
| `mask_count_ones` | Deduce bit-mask population from `card_odds` | One-line `simp` after the helper above |
| `encoded_parity_correct` | Show parity bit in encoding is correct | Use `Nat.mod_two_eq_zero_or_one` + previous lemma |
| `information_lower_bound` | Prove leakage bound OR strengthen encoding | Choose: (a) flip indices `≡ 0 (mod 4)` or (b) weaken statement |

**Time-estimate:** 1-2 h of Lean proofs.

---

## SPRINT B  Morton-encoding arithmetic (file `SATEncoding.lean`)

1. Collect arithmetic lemmas in `Helpers/BitInterleave.lean`, e.g. `Nat.add_mul_mod_self_left`, `Nat.mod_mul_left_div_self`.
2. Finish
   ```lean
   lemma morton_simple_inverse (x y : ℕ)
       (h : x + 1024*y < 1024^2) :
     decodeSimple (encodeSimple x y) = (x, y)
   ```
3. Generalise to base `2^k` and prove `morton_decode_encode` with bit-splits (`Nat.shiftl`, `Nat.land`).

---

## SPRINT C  Cellular-Automaton dynamics skeleton

• Move CA core to `CellularAutomaton/Core.lean` ‑ definitions of neighbourhood and `block_update`.
• Lemmas:
  1. `block_update_affects_only_neighbors` (pattern-match proof)
  2. `signal_speed` (induction on steps)
• Use these to complete `sat_computation_complexity`.

---

## Immediate Git Workflow

```bash
# stage everything, including this roadmap
git add -A

# commit with explicit status note
git commit -m "docs: add sprint roadmap; build compiles with 14 sorries"

# push to the main collaboration branch (adjust if on feature branch)
git push origin main
```

After pushing, open a PR (or just push to `main` if that's the workflow) so collaborators can self-assign items from SPRINT A/B/C. 