# The rectangular Rowland–Wu identity

The Rowland-Wu polynomial identity holds for the top-left entry of the positive balanced Sinkhorn scaling of every strictly positive real rectangular matrix, including matrices with vanishing minors.

Research audience: Researchers in matrix scaling, algebraic identities and Sinkhorn algorithms.

Assumptions and conventions:

- The input is any strictly positive real m-by-n matrix with m,n>=1, and the entry is taken from its genuine positive diagonal scaling with row sums one and column sums m/n.
- The polynomial uses the specified Delta and Gamma minors and principal minors of the literal row/column transition matrix H, with empty determinants and products equal to one.
- No nonvanishing-minor hypothesis is imposed. Arbitrary prescribed margins are not an additional selected claim.

Selected headline statements:

- **thm:nm04-main** — The explicit sum over all subsets of equal-cardinality trailing row/column index pairs vanishes at the scaled top-left entry, with the paper's determinant coefficients and exact m^(-1) normalization. Lean declaration: `NLA.NM04.Paper.paper_rowland_wu_identity`.

The compared theorem is the rectangular identity. Its actual scaling existence/uniqueness and null-vector construction occur in the proof library.

Only the exact declarations listed in [comparator.json](comparator.json) are selected for this component. The full independently compiled module graph retains the other recorded paper proofs; library coverage and a selected comparison are separate scopes. Every retained local module passed ordinary compilation.

This Solution imports all mapped proof roots. The all-local builder mode compiles every retained local module independently, keeping alternative proof environments separate where necessary.

This component passed ordinary full-source Lean 4.35.0 compilation and read-only compiled axiom-dependency queries for every configured declaration, within propext, Classical.choice and Quot.sound. Historical Lean 4.33.1 receipts remain separate source-bound evidence. Official Comparator and NanoDa verification remain pending the authors' later submission; no Palomar acceptance or independent-kernel replay is claimed.

The source is the author-provided unpublished manuscript, section 11, SHA-256 `b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5`. The manuscript and book are not reproduced here. [formalization.yaml](formalization.yaml) records mathematical sources, prior formalizations, scope and AI involvement.

Human authors and responsible maintainers: Matthew J. Colbrook and George Stepaniants. Substantial OpenAI Codex assistance and agent review are disclosed; no independent human review is claimed. The owner authorized the new Apache-2.0 release with third-party notices preserved. See the repository [LICENSE](../../LICENSE), [NOTICE](../../NOTICE.md) and [component texts](../../LICENSES/).

This proof component belongs to the single root Palomar submission. Submit the collection once with the repository-root comparator.json and formalization.yaml; leave the project directory blank. This account does not require a separate registry entry.
