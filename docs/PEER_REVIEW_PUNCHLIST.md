# Peer-Review Punch-List (Phase 6C)

_Updated: {{DATE}}
Reviewer summary of outstanding tasks required for a completely green Lean build and final publication polish._

---
## 1  Compile-Blocking Items

| ID | Task | Priority | Status |
|----|------|----------|--------|
| CB-1 | Finish proof of `all_foundations_from_meta` (remove `sorry`) | 🟥 High | ☐ todo |
| CB-2 | Finish proof of `zero_free_parameters` (remove `sorry`) | 🟥 High | ☐ todo |
| CB-3 | Finish proof of `μ_rec_minimal` (remove `sorry` + fix positivity type-mismatch) | 🟥 High | ☐ todo |
| CB-4 | Provide formal bound in `computation_recognition_separation` (`h_bound` lemma) | 🟧 Medium | ☐ todo |

> Completing CB-1 ➜ CB-4 will restore a **green `lake build`**.

---
## 2  Code-Quality Polish

| ID | Task | Priority | Status |
|----|------|----------|--------|
| CQ-1 | Move narrative / long prose comments out of Lean proofs into Markdown docs | 🟩 Low | ☐ todo |
| CQ-2 | Split proofs exceeding ~100 lines into helper lemmas for readability | 🟩 Low | ☐ todo |
| CQ-3 | Run `#lint` with `set_option linter.unusedVariables false` and clean warnings | 🟩 Low | ☐ todo |

---
## 3  Optional Build Optimisation

| ID | Task | Priority | Status |
|----|------|----------|--------|
| OPT-1 | Add `lake exe cache get` to CI to speed builds | 🟦 Nice-to-have | ☐ todo |

---
### Legend
🟥 High = blocks build • 🟧 Medium = minor compile impact • 🟩 Low = style / readability • 🟦 Nice-to-have 