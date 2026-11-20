# A q-permanent subset-inequality counterexample

An explicit real positive-semidefinite four-by-four matrix of rank two violates the q-permanent subset inequality at q=7/8 for a singleton subset.

Research audience: Researchers in generalized permanents and matrix inequalities.

Assumptions and conventions:

- The witness is the exact matrix in the manuscript, with Gram factor having rows (13,0,13,13) and (1,1,-2,1).
- The q-permanent sums actual permutation products weighted by q to the inversion count, and the restricted sum uses the singleton containing paper index two.
- The matrix is positive semidefinite of rank two but need not be entrywise nonnegative; q is exactly 7/8.

Selected headline statements:

- **section 15, unnumbered theorem** — Proves the exact witness's positive semidefiniteness and rank two and the strict negative difference per_q(A)-R_{q,{2}}(A)=-3235575/16384 at q=7/8. Lean declaration: `NLA.MI19.Paper.paper_counterexample`.

The selected result is the explicit semidefinite witness. The positive-definite perturbation remark and the eighteen-moving-terms expansion are auxiliary library statements.

Only the exact declarations listed in [comparator.json](comparator.json) are selected for this component. The full independently compiled module graph retains the other recorded paper proofs; library coverage and a selected comparison are separate scopes. Every retained local module passed ordinary compilation.

This Solution imports all mapped proof roots. The all-local builder mode compiles every retained local module independently, keeping alternative proof environments separate where necessary.

This component passed ordinary full-source Lean 4.35.0 compilation and read-only compiled axiom-dependency queries for every configured declaration, within propext, Classical.choice and Quot.sound. Historical Lean 4.33.1 receipts remain separate source-bound evidence. Official Comparator and NanoDa verification remain pending the authors' later submission; no Palomar acceptance or independent-kernel replay is claimed.

The source is the author-provided unpublished manuscript, section 15, SHA-256 `b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5`. The manuscript and book are not reproduced here. [formalization.yaml](formalization.yaml) records mathematical sources, prior formalizations, scope and AI involvement.

Human authors and responsible maintainers: Matthew J. Colbrook and George Stepaniants. Substantial OpenAI Codex assistance and agent review are disclosed; no independent human review is claimed. The owner authorized the new Apache-2.0 release with third-party notices preserved. See the repository [LICENSE](../../LICENSE), [NOTICE](../../NOTICE.md) and [component texts](../../LICENSES/).

This proof component belongs to the single root Palomar submission. Submit the collection once with the repository-root comparator.json and formalization.yaml; leave the project directory blank. This account does not require a separate registry entry.
