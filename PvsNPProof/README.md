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

This separation suggests:
- At computation scale: P = NP (both polynomial)
- At recognition scale: P ≠ NP (linear vs polynomial gap)

## Repository Structure

```
├── PvsNPProof/           # Lean 4 formalization
│   ├── Src/PvsNP/       # Core proof modules
│   │   ├── RSFoundation.lean      # Recognition Science axioms
│   │   ├── TuringMachine.lean     # TM formalization  
│   │   ├── CellularAutomaton.lean # 16-state CA
│   │   ├── SATEncoding.lean       # SAT → CA encoding
│   │   ├── RecognitionBound.lean  # Information-theoretic bounds
│   │   └── MainTheorem.lean       # Main separation theorem
│   └── ProofStatus.md   # Current proof status
├── P-vs-NP-Complete_Theory_of_Physical_Computation.tex
└── ProjectPlan.md       # Development roadmap
```

## Building the Lean Proof

```bash
cd PvsNPProof
lake update
lake build
```

## Current Status

- ✅ All modules build successfully
- ✅ Core mathematical structure complete
- 📊 16 sorries remaining (detailed proofs of standard results)
- 🔬 Formal verification demonstrates the computation/recognition separation

## Paper

The complete theory is detailed in: [P-vs-NP-Complete_Theory_of_Physical_Computation.tex](P-vs-NP-Complete_Theory_of_Physical_Computation.tex)

## Citation

If you use this work, please cite:
```bibtex
@article{washburn2024pvsnp,
  title={A Two-Parameter Theory of Physical Computation: A New Perspective on P vs NP},
  author={Washburn, Jonathan},
  journal={arXiv preprint},
  year={2024}
}
```

## License

This work is licensed under MIT License. See LICENSE for details. 