# Differentiation and nonnegative spectral realizability

The normalized characteristic-polynomial derivative of an explicit nonnegative seven-by-seven matrix is not the characteristic polynomial of any nonnegative matrix, even after adjoining arbitrarily many zero roots.

Research audience: Researchers in the nonnegative inverse eigenvalue problem and spectral realizability.

Assumptions and conventions:

- The witness is diag(1/2,C_2,C_4), with C_j the directed j-cycle permutation matrix; nonnegativity is entrywise.
- The derivative is normalized by dividing the degree-seven characteristic derivative by seven. Arbitrary zero padding means every additional number r>=0 of zero roots.
- Realizability concerns the complete characteristic polynomial of an entrywise-nonnegative real matrix of the required order.

Selected headline statements:

- **thm:is03** — Proves that the literal normalized derivative, multiplied by any power z^r, cannot equal the characteristic polynomial of an entrywise-nonnegative real matrix of order 6+r. Lean declaration: `NLA.IS03.paper_counterexample`.

The zero-padding quantifier is part of the selected theorem; it is stronger than disproving realizability in order six alone.

Only the exact declarations listed in [comparator.json](comparator.json) are selected for this component. The full independently compiled module graph retains the other recorded paper proofs; library coverage and a selected comparison are separate scopes. Every retained local module passed ordinary compilation.

This Solution imports all mapped proof roots. The all-local builder mode compiles every retained local module independently, keeping alternative proof environments separate where necessary.

This component passed ordinary full-source Lean 4.35.0 compilation and read-only compiled axiom-dependency queries for every configured declaration, within propext, Classical.choice and Quot.sound. Historical Lean 4.33.1 receipts remain separate source-bound evidence. Official Comparator and NanoDa verification remain pending the authors' later submission; no Palomar acceptance or independent-kernel replay is claimed.

The source is the author-provided unpublished manuscript, section 10, SHA-256 `b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5`. The manuscript and book are not reproduced here. [formalization.yaml](formalization.yaml) records mathematical sources, prior formalizations, scope and AI involvement.

Human authors and responsible maintainers: Matthew J. Colbrook and George Stepaniants. Substantial OpenAI Codex assistance and agent review are disclosed; no independent human review is claimed. The owner authorized the new Apache-2.0 release with third-party notices preserved. See the repository [LICENSE](../../LICENSE), [NOTICE](../../NOTICE.md) and [component texts](../../LICENSES/).

This proof component belongs to the single root Palomar submission. Submit the collection once with the repository-root comparator.json and formalization.yaml; leave the project directory blank. This account does not require a separate registry entry.
