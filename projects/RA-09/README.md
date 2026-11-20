# Sharp Frobenius transfer bounds

Sharp Frobenius-norm relative-error transfer for nonnegative nondecreasing continuous functions with f(x)/x nonincreasing: factor one under positive-semidefinite order and factor two without order.

Research audience: Researchers in matrix-function approximation, eigenvalue inequalities and low-rank error bounds.

Assumptions and conventions:

- A and B are real positive-semidefinite matrices, rank B is at most k, and the first discarded eigenvalue of A is positive.
- The function is continuous, nonnegative and nondecreasing on the nonnegative axis, with f(x)/x nonincreasing for positive x; concavity and operator monotonicity are not premises.
- The output applies f on the same selected k-dimensional eigenspace of B and is zero on its orthogonal complement, including when f(0) is positive.

Selected headline statements:

- **raf-thm:ordered** — If B is below A in semidefinite order, an input norm-relative factor 1+epsilon transfers with the same factor for the selected transformed approximation. Lean declaration: `NLA.RA09.paper_ordered_matrix_norm_relative`.
- **raf-thm:ordered** — The ordered factor one is optimal, using actual matrix approximation errors and positive comparison tails. Lean declaration: `NLA.RA09.paper_ordered_sharpness`.
- **raf-thm:unordered** — Without semidefinite order, an input norm-relative factor 1+epsilon transfers with factor at most 1+2epsilon. Lean declaration: `NLA.RA09.paper_unordered_matrix_norm_relative`.
- **raf-thm:unordered** — The unordered factor two is optimal, even for operator-monotone power functions, with ratios tending to two. Lean declaration: `NLA.RA09.paper_unordered_sharpness`.

These are the selected norm-relative consequences and sharpness statements. Squared-excess forms, degenerate cutoff cases and operator-monotone integral proofs remain auxiliary results.

Only the exact declarations listed in [comparator.json](comparator.json) are selected for this component. The full independently compiled module graph retains the other recorded paper proofs; library coverage and a selected comparison are separate scopes. Every retained local module passed ordinary compilation.

This Solution imports all mapped proof roots. The all-local builder mode compiles every retained local module independently, keeping alternative proof environments separate where necessary.

This component passed ordinary full-source Lean 4.35.0 compilation and read-only compiled axiom-dependency queries for every configured declaration, within propext, Classical.choice and Quot.sound. Historical Lean 4.33.1 receipts remain separate source-bound evidence. Official Comparator and NanoDa verification remain pending the authors' later submission; no Palomar acceptance or independent-kernel replay is claimed.

The source is the author-provided unpublished manuscript, section 6, SHA-256 `b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5`. The manuscript and book are not reproduced here. [formalization.yaml](formalization.yaml) records mathematical sources, prior formalizations, scope and AI involvement.

Human authors and responsible maintainers: Matthew J. Colbrook and George Stepaniants. Substantial OpenAI Codex assistance and agent review are disclosed; no independent human review is claimed. The owner authorized the new Apache-2.0 release with third-party notices preserved. See the repository [LICENSE](../../LICENSE), [NOTICE](../../NOTICE.md) and [component texts](../../LICENSES/).

This proof component belongs to the single root Palomar submission. Submit the collection once with the repository-root comparator.json and formalization.yaml; leave the project directory blank. This account does not require a separate registry entry.
