# Sorry Elimination Plan

## Objective
Eliminate all 10 sorries. No axioms. No admits. Zero.

## Rules for AI Assistant
1. NO celebration until all sorries = 0
2. NO suggesting to stop or take breaks
3. NO lengthy explanations - just fix the proofs
4. Report only: "Fixed #X. Moving to #Y."

## Order of Attack (easiest to hardest)

### Phase 1: Trivial Consequences (30 min)
1. **#5**: `morton_injective` - Follows from #4 via `Function.LeftInverse.injective`
2. **#6**: `place_variable_correct` - Simple coordinate check

### Phase 2: Bit Manipulation (2 hours)
3. **#4**: `morton_encode_decode` - Bit interleaving proof using `Nat.testBit`

### Phase 3: CA Properties (2 hours)  
4. **#7**: Locality of `block_update` - Prove only 8 cells touched
5. **#8**: `signal_speed` - Induction using locality

### Phase 4: Geometry (1 hour)
6. **#9**: `layout_diameter_bound` - Volume argument with `Real.rpow`

### Phase 5: Asymptotics (2 hours)
7. **#10**: `subpoly_computation_time` - Use `Asymptotics.IsBigO`

### Phase 6: Information Theory (4 hours)
8. **#1**: `encoded_parity_correct` - Count ones in mask
9. **#2**: `balanced_parity_property` - Combinatorial indistinguishability  
10. **#3**: `information_lower_bound` - Adversary argument

## Mathlib Imports Needed
```lean
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Bits
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Connectivity
```

## Execution
Start with Phase 1. Complete each proof. Move to next. No commentary. 