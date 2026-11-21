# Counterexamples to concave matrix-function transfer

The selected results give spectral error-transfer failure for a fixed six-dimensional matrix pair and exact Nyström nuclear-norm examples with arbitrarily large amplification of arbitrarily small positive input excess.

Research audience: Researchers using low-rank approximations of matrix functions and randomized sketching.

Assumptions and conventions:

- The spectral statement takes any real C and ordered spectral data dA for the fixed six-dimensional witnessMatrix, and compares the fixed second matrix witnessApproximation with the three-term spectral truncation.
- The nuclear statement requires a real positive-definite input, an injective sketch and the actual inverse-based Nyström formula. It quantifies every nonnegative real C and every positive bound epsilon_0 on the input excess.
- Both selected statements use spectral functional calculus, the fixed kink f(x)=min(x,1), and ordered spectral truncations. Admissibility of the scalar function is proved separately in the unselected theorem paper_scalar_function.

Selected headline statements:

- **rac-thm:spectral** — For the fixed six-dimensional pair witnessMatrix and witnessApproximation, every real C and ordered spectral data dA of witnessMatrix satisfy the input spectral error bound at epsilon=0, while the transformed spectral error exceeds the corresponding three-term function-truncation error. This selected declaration is a fixed-pair error-transfer failure. Lean declaration: `NLA.RA08.Paper.paper_spectral_failure`.
- **rac-thm:nuclear** — For every nonnegative real C and every epsilon_0 greater than zero, constructs an exact Nyström example with positive input excess below epsilon_0 and transformed nuclear excess exceeding C times that excess. Lean declaration: `NLA.RA08.Paper.verified_paper_nuclear_counterexample`.

The selected spectral conclusion consists of the fixed-pair error inequalities. The separate, unselected [paper_spectral_witness](PaperSolution.lean#L14) supplies existence of ordered spectral data, positive-definite input, positive-semidefinite approximation and order, an injective fixed sketch paperOmega, an invertible Gram determinant, and nystrom witnessMatrix paperOmega = witnessApproximation. The Nyström realization is supporting context from that companion theorem, rather than a conclusion of the compared paper_spectral_failure. Scalar admissibility is likewise supplied by the unselected [paper_scalar_function](PaperSolution.lean#L52). The selected nuclear theorem directly includes its Nyström sketch and construction. These selected statements do not assert probabilities under any sketch distribution. A strictly increasing function variant is unselected auxiliary material.

Only the exact declarations listed in [comparator.json](comparator.json) are selected for this component. The full independently compiled module graph retains the other recorded paper proofs; library coverage and a selected comparison are separate scopes. Every retained local module passed ordinary compilation.

This Solution imports all mapped proof roots. The all-local builder mode compiles every retained local module independently, keeping alternative proof environments separate where necessary.

This component passed ordinary full-source Lean 4.35.0 compilation and read-only compiled axiom-dependency queries for every configured declaration, within propext, Classical.choice and Quot.sound. Historical Lean 4.33.1 receipts remain separate source-bound evidence. Official Comparator and NanoDa verification remain pending the authors' later submission; no Palomar acceptance or independent-kernel replay is claimed.

The source is the author-provided unpublished manuscript, section 5, SHA-256 `b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5`. The manuscript and book are not reproduced here. [formalization.yaml](formalization.yaml) records mathematical sources, prior formalizations, scope and AI involvement.

Human authors and responsible maintainers: Matthew J. Colbrook and George Stepaniants. Substantial OpenAI Codex assistance and agent review are disclosed; no independent human review is claimed. The owner authorized the new Apache-2.0 release with third-party notices preserved. See the repository [LICENSE](../../LICENSE), [NOTICE](../../NOTICE.md) and [component texts](../../LICENSES/).

This proof component belongs to the single root Palomar submission. Submit the collection once with the repository-root comparator.json and formalization.yaml; leave the project directory blank. This account does not require a separate registry entry.
