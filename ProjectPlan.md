# Project Plan — Completing the Recognition-Science Lean Proof of P vs NP

Repository: <https://github.com/jonwashburn/P-vs-NP>

## 0. Global Milestones

| Phase | Goal | Success Criterion | Target Date |
|-------|------|------------------|-------------|
| M0 | Infrastructure solidified | `lake build` passes CI on GitHub Actions | **✓ done** |
| M1 | Layer-0 & Layer-1 `sorry`-free | `RSFoundation.lean`, `TuringMachine.lean` proven | T + 2 weeks |
| M2 | Layer-2 & Layer-3 verified | `CellularAutomaton.lean`, `SATEncoding.lean` proven | T + 6 weeks |
| M3 | Layer-4 information-theoretic bounds | `RecognitionBound.lean` proven | T + 8 weeks |
| M4 | Master theorem verified | `MainTheorem.lean` `sorry`-free; repo compiles with **zero** admits | T + 9 weeks |
| M5 | Paper/doc polish & arXiv release | LaTeX compiles w/out "??" refs; Zenodo DOI minted | T + 10 weeks |

`T` = today's date when the plan is accepted.

---

## 1. Detailed Task Breakdown

### Layer 0 — RS Foundation
1. Finish remaining lemmas in `RSFoundation.lean`
   * Prove `RS_correction_unbounded`.
   * Add auxiliary lemmas for `Real.log` monotonicity.
2. Document constants in code & LaTeX (`\newcommand{\Ecoh}{\ensuremath{E_{\text{coh}}}}`, etc.).

### Layer 1 — Classical Complexity in RS
1. `TuringMachine.lean`
   * Replace four `sorry`s: configuration encoding, step relation, halting correctness, and `classical_assumption` equivalence proof.
   * Provide small deterministic example TM (e.g.
at-doubling) as regression test.
2. Unit tests in `Test/Turing.lean`.

### Layer 2 — 16-State Reversible CA
1. `CellularAutomaton.lean`
   * Formalise block rule in `BlockRule.lean`.
   * Prove reversibility (bijection of state update).
   * Complete mass-conservation lemma.
2. Add `CAProperties.lean` – reusable reversible/block-CA framework.

### Layer 3 — SAT Encoding
1. `SATEncoding.lean`
   * Define syntax of 3-SAT formulae (`Literal`, `Clause`, `Formula`).
   * Morton-curve placement; prove injectivity.
   * Show CA evaluates SAT in `O(n^{1/3}\log n)` ticks (use `Asymptotics`).

### Layer 4 — Recognition Bounds
1. `RecognitionBound.lean`
   * Fully prove `information_lower_bound` & `recognition_lower_bound`.
   * Implement decision-tree model (may reuse upcoming `BooleanDecisionTree`).
   * Balanced-parity code indistinguishability helpers.

### Layer 5 — Master Theorem
1. `MainTheorem.lean`
   * Combine results to prove `P_eq_NP_computation` and `P_ne_NP_recognition`.
   * Show incompatibility of classical assumption with physical constraints.

---

## 2. Engineering & QA Checklist

| Category | Requirement |
|----------|-------------|
| CI | GitHub Action runs `lake build` and unit tests; badge in README |
| Style | Run `lake exe leanformat` pre-commit |
| Docs | Keep `RS_Mathematical_Foundation.md` in sync with code |
| Tests | All files in `Test/` compile with no `sorry` |

---

## 3. Paper Synchronisation Workflow

1. When a Lean theorem is proven, search LaTeX for the matching statement and replace "(proof omitted)" with `\leanref{…}` link.
2. CI runs `latexmk -pdf`; build fails on undefined refs or warnings.
3. Final submission includes `git rev-parse HEAD` hash in paper footer.

---

## 4. Resource Allocation

| Contributor | Focus Areas | Weekly Hours |
|-------------|-------------|--------------|
| Jonathan (PI) | Layer 4 & paper polish | 10 |
| Dev A | Layer 1 proof engineering | 8 |
| Dev B | CA formalisation | 8 |
| Dev C | SAT encoding & asymptotics | 6 |

---

## 5. Risk Register

| Risk | Mitigation |
|------|-----------|
| Gaps in big-O library | Import `mathlib4` PR #XYZ or add local lemmas |
| Decision-tree framework heavier than expected | Scope cut: prove lower bound just for balanced-parity instances |
| Timeline slip | Buffer one week before submission deadline |

---

This markdown file serves as a living roadmap and checklist; update milestones and checkboxes as tasks are completed.  Create GitHub issues or project boards to mirror these tasks so progress remains transparent. 