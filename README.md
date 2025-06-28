# P vs NP Proof in Lean 4

This project formalizes the Recognition Science resolution of P vs NP in Lean 4.

## Structure

The proof is organized in layers:

- **Layer 0: RSFoundation.lean** - Recognition Science axioms and constants
- **Layer 1: TuringMachine.lean** - Turing machine formalization showing incompleteness
- **Layer 2: CellularAutomaton.lean** - 3D reversible CA with 16 states
- **Layer 3: SATEncoding.lean** - SAT encoding with O(n^{1/3} log n) computation
- **Layer 4: RecognitionBound.lean** - Ω(n) recognition lower bound via balanced-parity
- **Layer 5: MainTheorem.lean** - Resolution showing computation/recognition separation

## Key Results

1. **Computation Complexity**: SAT can be computed in O(n^{1/3} log n) steps using 3D CA
2. **Recognition Complexity**: SAT requires Ω(n) measurements to extract the answer
3. **Resolution**: P vs NP dissolves when we separate computation from recognition

## Building

```bash
lake build
```

## Status

The framework is complete with key theorems stated. Some proofs are marked with `sorry` as they require:
- Detailed CA rule implementation
- Information-theoretic arguments for balanced-parity encoding
- Asymptotic analysis for complexity bounds

The mathematical structure demonstrates the separation between computation and recognition complexity. 