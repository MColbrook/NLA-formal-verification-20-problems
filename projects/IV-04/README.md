# Hardness of interval determinant ranges and solution hulls

Exact determinant ranges and complete solution hulls of rational regular tridiagonal interval systems are NP-hard; the determinant-threshold language is NP-complete, even with superdiagonal entries fixed at one.

Research audience: Researchers in verified numerical computation, interval linear algebra and computational complexity.

Assumptions and conventions:

- Inputs have binary-encoded rational ordered interval endpoints and actual real interval realizations; malformed-input and complete-decoding conventions are explicit.
- The hard restricted families are tridiagonal, every realization is nonsingular, and every superdiagonal entry is one.
- The hull task returns rational lower and upper endpoints for every coordinate, with point right-hand side -e_n and a nonempty bounded actual solution set. Exact-output hardness uses actual polynomial-time query and postprocessing programs.

Selected headline statements:

- **thm:iv-det** — Proves NP-completeness of the determinant-threshold language, NP-hardness on the regular fixed-superdiagonal restriction, and one-query NP-hardness of the exact minimum/maximum determinant output on that restriction. Lean declaration: `IV04.Paper.Computational.actual_paper_iv_det`.
- **thm:iv-hull** — Proves one-query NP-hardness of the literal complete coordinatewise solution-hull output on regular fixed-superdiagonal interval systems with right-hand side -e_n; a correct complete rational answer exists for every reduction input and every such answer decides the source NP language. Lean declaration: `Reference.IV04FullHullHardness.iv_hull_literal_np_hard`.

This grouped component covers IV-02 and IV-04. Exact-output hardness is not a claim about approximate interval arithmetic or an independently selected FP^NP upper-bound algorithm.

Only the exact declarations listed in [comparator.json](comparator.json) are selected for this component. The full independently compiled module graph retains the other recorded paper proofs; library coverage and a selected comparison are separate scopes. Every retained local module passed ordinary compilation.

IV-04 Solution imports its two primary determinant/hull proof roots only. Alternative auxiliary environments are retained and compiled independently with the all-local builder mode; they are not combined in one import closure. Mathematical statements are neither weakened nor renamed.

This component passed ordinary full-source Lean 4.35.0 compilation and read-only compiled axiom-dependency queries for every configured declaration, within propext, Classical.choice and Quot.sound. Historical Lean 4.33.1 receipts remain separate source-bound evidence. Official Comparator and NanoDa verification remain pending the authors' later submission; no Palomar acceptance or independent-kernel replay is claimed.

The source is the author-provided unpublished manuscript, section 14, SHA-256 `b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5`. The manuscript and book are not reproduced here. [formalization.yaml](formalization.yaml) records mathematical sources, prior formalizations, scope and AI involvement.

Human authors and responsible maintainers: Matthew J. Colbrook and George Stepaniants. Substantial OpenAI Codex assistance and agent review are disclosed; no independent human review is claimed. The owner authorized the new Apache-2.0 release with third-party notices preserved. See the repository [LICENSE](../../LICENSE), [NOTICE](../../NOTICE.md) and [component texts](../../LICENSES/).

This proof component belongs to the single root Palomar submission. Submit the collection once with the repository-root comparator.json and formalization.yaml; leave the project directory blank. This account does not require a separate registry entry.
