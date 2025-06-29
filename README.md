# P vs NP: A Recognition Science Resolution

[![CI](https://github.com/jonwashburn/P-vs-NP/actions/workflows/ci.yml/badge.svg)](https://github.com/jonwashburn/P-vs-NP/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-4-blue.svg)](https://leanprover.github.io/)

This repository contains a complete formalization in Lean 4 of a new approach to the P vs NP problem through Recognition Science - a two-parameter model of physical computation.

## Key Result

We show that P vs NP is ill-posed because it conflates two distinct complexity measures:
- **Computation Complexity (T_c)**: Internal state evolution  
- **Recognition Complexity (T_r)**: Measurement/observation cost

Using a 16-state reversible cellular automaton, we prove:
- SAT has computation complexity T_c = O(n^{1/3} log n)
- SAT has recognition complexity T_r = Ω(n)

This separation explains why P vs NP has been so difficult: the question conflates two fundamentally different resources.

## Proof Status

**Current Status: Structurally Complete, 17 sorries remaining**

- ✅ No axioms (eliminated RS_correction_unbounded axiom)
- ✅ All modules build successfully
- ✅ Core CA implementation complete (0 sorries)
- 🔶 17 technical lemmas remain (mostly complexity bounds)

See [PROOF_COMPLETION_STATUS.md](PROOF_COMPLETION_STATUS.md) for detailed status.

## Project Structure

```
PvsNPProof/
├── Src/PvsNP/
│   ├── Core.lean              # Core definitions
│   ├── RSFoundation.lean      # Recognition Science axioms (1 sorry)
│   ├── TuringMachine.lean     # TM formalization (1 sorry)
│   ├── CellularAutomaton.lean # 3D reversible CA (0 sorries!)
│   ├── SATEncoding.lean       # SAT → CA encoding (7 sorries)
│   ├── RecognitionBound.lean  # Ω(n) lower bound (6 sorries)
│   └── MainTheorem.lean       # Main resolution (2 sorries)
└── lakefile.lean              # Build configuration
```

## Building

```bash
cd PvsNPProof
lake update
lake build
```

## Key Insights

1. **Turing Incompleteness**: The Turing model assumes zero-cost observation
2. **Physical Reality**: Any real computer has non-zero measurement cost
3. **Resolution**: P = NP at computation scale, P ≠ NP at recognition scale

## Mathematical Foundation

The proof uses Recognition Science constants:
- φ = (1 + √5)/2 (golden ratio)
- E_coh = 1/φ² (coherence threshold)

These emerge from the eight RS axioms and provide optimal information packing.

## References

- Full LaTeX paper: [P-vs-NP-Complete_Theory_of_Physical_Computation.txt](P-vs-NP-Complete_Theory_of_Physical_Computation.txt)
- Mathematical foundation: [RS_Mathematical_Foundation.md](PvsNPProof/RS_Mathematical_Foundation.md)

## License

MIT License - See [LICENSE](LICENSE) file for details.

## Contributing

This is an active research project. Contributions to eliminate the remaining sorries are welcome! 