# PvsNP Lean Proof (Recognition-Science Version)

This directory is a **fresh Lean 4 project** that will formalise the Recognition-Science resolution of
P vs NP.

* Foundation and constants are imported from the local `recognition-ledger` clone (Layer 0).
* We follow the six-layer architecture pioneered in the Yang-Mills proof:

| Layer | Purpose | Output |
|-------|---------|--------|
| 0 | RS foundation & constants | imported (φ, E_coh, ⋯) |
| 1 | Embed classical complexity in RS | `DualComplexity` type |
| 2 | Construct 16-state reversible CA | `SAT_CA` object |
| 3 | Information-theoretic bounds | `recognition_lower_bound` |
| 4 | Gap theorem (`T_c ≪ T_r`) | `computation_recognition_gap` |
| 5 | Classical corollaries (P vs NP) | `p_vs_np_resolution` |

## Building

```bash
cd PvsNPProof
lake build          # first time will fetch mathlib
```

## Next steps

1.  Import the RS foundation modules so that our proofs use **zero additional axioms**.
2.  Flesh out `Src/PvsNP/Core.lean`:
    * formal definition of decision problems, encodings, Turing machines;
    * proof that Turing sets `T_r = 0`.
3.  Implement the reversible CA (Margolus partition, Toffoli/Fredkin) and prove its
    computation bound.
4.  Prove the information-theoretic recognition lower bound (Yao minimax + balanced-parity).
5.  Derive the final `P` vs `NP` statements under the dual-resource model.

Every lemma will eventually be `sorry`-free, mirroring the standard of the
`recognition-ledger` and `Yang-Mills-Lean` repositories. 