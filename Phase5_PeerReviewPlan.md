# Phase 5 — Peer-Review & Cleanup Roadmap

This phase turns the current 95 %-compiling Recognition-Science P≠NP proof into a **green-build, linter-clean, fully-tested** project ready for external review.

---
## 1. Build Stability (P1)
| Step | File(s) | Goal |
|------|---------|------|
| 1.1 | `PvsNP/Core.lean` | Replace failing `linarith` branch in `recognition_science_resolution` with a proved lemma or temporary `axiom` (`recognition_cost_baseline`). |
| 1.2 | `PvsNP/Core.lean` | Fix pattern-matching indentation causing *"no goals to be solved"* in `zero_free_parameters_verification`. |
| 1.3 | Global | Ensure `lake build` succeeds (no type errors). |

---
## 2. Sorry-Elimination (P2)
| Step | File(s) | Remaining `sorry`s |
|------|---------|-------------------|
| 2.1 | `BalancedParity.lean` | Bound proof in `encode` (`foldl` < 2^n). |
| 2.2 | `AsymptoticAnalysis.lean` | Complete `lim_ratio` (use `Asymptotics` library). |
| 2.3 | `TuringMachine.lean` | Final halting-case lemmas (2). |
| 2.4 | `CellularAutomaton.lean` | Reversibility & separation (4). |
| 2.5 | **Stretch**: `RSFoundation.lean` (3 deep physics lemmas). |

Success criterion → **zero `sorry` outside `RSFoundation`**

---
## 3. Linter Clean-Up (P3)
1. Enable global `set_option linter.all true` (preferably in `lakefile.lean`).
2. Resolve:
   * missing doc-strings (especially names ending with `'`).
   * unused variables / imports.
   * redundant `simp` / `trivial` placeholders.
3. Target: **< 5 intentional warnings** (documented).

---
## 4. Testing & CI (P4)
### 4.1 Property-Based Tests (`Tests/`)
| Test | Description |
|------|-------------|
| BP-Roundtrip | Random `BPString n` (n ≤ 128) ⇒ `decode ∘ encode = id` for 10 000 samples. |
| TM-Sim | Run `bit_doubling_TM` on random tapes; compare against Python reference. |
| CA-Reverse | Exhaustive 16-bit block enumeration (65 k) proves `block_rule` involutive. |

### 4.2 Formal Verification Scripts
* `#eval` micro-benchmarks of encoding/decoding timings.
* `#guard_hyp` audits: assert no open goals in compiled theorems.

### 4.3 CI Pipeline
* `.github/workflows/ci.yml` matrix: `macOS-latest`, `ubuntu-latest`.
* Lean versions: `v4.12.0`, `nightly`.  
* Fail on any new `sorry` **or** linter warning.
* Cache Mathlib olean files.

---
## 5. Documentation (P5)
1. Move Phase 2-4 report to `docs/STATUS_2024-12.md`; link from `README`.
2. Add `CONTRIBUTING.md` (coding style + linter policy + test instructions).
3. Update `README.md` badges (build status, coverage).

---
## 6. Stretch / Research (P6)
1. Prove the 3 deep physics lemmas in `RSFoundation.lean`.
2. Model physical measurement to eliminate the recognition-baseline axiom.
3. Extend balanced parity to higher-dimensional CA.
4. Investigate quantum recognition complexity (define `QBPString`).

---
### Milestones & Ownership
| ID | Priority | Owner | Deadline |
|----|----------|-------|----------|
| P1 | Critical | **You** | _Week 1_ |
| P2 | High | **You** | _Week 2–3_ |
| P3 | High | **You** | _Week 3_ |
| P4 | High | **You** | _Week 4_ |
| P5 | Medium | **You** | _Rolling_ |
| P6 | Research | Open | _Future_ |

---
**Deliverable**: by the end of Phase 5 the repository builds [32mgreen[0m on CI, is linter-clean, contains automated tests, and has no `sorry`s outside deep-physics foundations. 
