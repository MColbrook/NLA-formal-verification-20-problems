# A geometric-mean norm counterexample

Two rational positive-definite input pairs of order two refute the geometric-mean norm inequality in the operator norm at s=t=1/2 and r=2, with both sums equal to identity and the same witness for every p>0.

Research audience: Researchers in matrix geometric means, operator inequalities and unitarily invariant norms.

Assumptions and conventions:

- There are two summands of order two; all four matrices are rational and positive definite, represented in complex matrices for genuine functional calculus.
- The exponents are s=t=1/2 and r=2; p is any positive real number, so sr=1 satisfies the conjectured parameter range.
- Both input sums equal I_2, making the proposed right side one; the norm used for the strict violation is the actual Euclidean operator norm.

Selected headline statements:

- **thm:mi21** — The displayed rational input pairs have the stated positivity and identity sums, and the actual sum of squared geometric means has operator norm strictly greater than the conjectured right-hand side for every p>0. Lean declaration: `NLA.MI21.Paper.paper_counterexample`.

One unitarily invariant norm suffices to refute the universal inequality; the statement does not assert failure for every such norm.

Only the exact declarations listed in [comparator.json](comparator.json) are selected for this component. The full independently compiled module graph retains the other recorded paper proofs; library coverage and a selected comparison are separate scopes. Every retained local module passed ordinary compilation.

This Solution imports all mapped proof roots. The all-local builder mode compiles every retained local module independently, keeping alternative proof environments separate where necessary.

This component passed ordinary full-source Lean 4.35.0 compilation and read-only compiled axiom-dependency queries for every configured declaration, within propext, Classical.choice and Quot.sound. Historical Lean 4.33.1 receipts remain separate source-bound evidence. Official Comparator and NanoDa verification remain pending the authors' later submission; no Palomar acceptance or independent-kernel replay is claimed.

The source is the author-provided unpublished manuscript, section 16, SHA-256 `b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5`. The manuscript and book are not reproduced here. [formalization.yaml](formalization.yaml) records mathematical sources, prior formalizations, scope and AI involvement.

Human authors and responsible maintainers: Matthew J. Colbrook and George Stepaniants. Substantial OpenAI Codex assistance and agent review are disclosed; no independent human review is claimed. The owner authorized the new Apache-2.0 release with third-party notices preserved. See the repository [LICENSE](../../LICENSE), [NOTICE](../../NOTICE.md) and [component texts](../../LICENSES/).

This proof component belongs to the single root Palomar submission. Submit the collection once with the repository-root comparator.json and formalization.yaml; leave the project directory blank. This account does not require a separate registry entry.
