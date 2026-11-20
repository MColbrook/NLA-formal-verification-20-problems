# Counterexamples to concave matrix-function transfer

Exact Nyström examples disprove concave matrix-function transfer in spectral norm and show arbitrarily large nuclear-norm amplification of arbitrarily small positive input excess.

Research audience: Researchers using low-rank approximations of matrix functions and randomized sketching.

Assumptions and conventions:

- The matrices are real positive definite, the sketches have full column rank, and the approximations use the actual inverse-based Nyström formula with positive-semidefinite order.
- The transformed errors use genuine spectral functional calculus and optimal rank truncations. The counterexample function is the nonnegative nondecreasing concave kink f(x)=min(x,1).
- The nuclear statement quantifies every proposed finite amplification factor C at least zero and every positive bound on the input excess.

Selected headline statements:

- **rac-thm:spectral** — The explicit six-dimensional Nyström witness has zero spectral input excess and strictly positive transformed excess, disproving even an exact-input spectral transfer guarantee. Lean declaration: `NLA.RA08.Paper.paper_spectral_failure`.
- **rac-thm:nuclear** — For every finite C and every epsilon_0 greater than zero, constructs an exact Nyström example with positive input excess below epsilon_0 and transformed nuclear excess exceeding C times that excess. Lean declaration: `NLA.RA08.Paper.verified_paper_nuclear_counterexample`.

The selected examples concern a guarantee for every admissible approximation, not their probability under a particular sketch distribution. A strictly increasing function variant is auxiliary material and is not selected here.

Only the exact declarations listed in [comparator.json](comparator.json) are selected for this component. The full independently compiled module graph retains the other recorded paper proofs; library coverage and a selected comparison are separate scopes. Every retained local module passed ordinary compilation.

This Solution imports all mapped proof roots. The all-local builder mode compiles every retained local module independently, keeping alternative proof environments separate where necessary.

This component passed ordinary full-source Lean 4.35.0 compilation and read-only compiled axiom-dependency queries for every configured declaration, within propext, Classical.choice and Quot.sound. Historical Lean 4.33.1 receipts remain separate source-bound evidence. Official Comparator and NanoDa verification remain pending the authors' later submission; no Palomar acceptance or independent-kernel replay is claimed.

The source is the author-provided unpublished manuscript, section 5, SHA-256 `b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5`. The manuscript and book are not reproduced here. [formalization.yaml](formalization.yaml) records mathematical sources, prior formalizations, scope and AI involvement.

Human authors and responsible maintainers: Matthew J. Colbrook and George Stepaniants. Substantial OpenAI Codex assistance and agent review are disclosed; no independent human review is claimed. The owner authorized the new Apache-2.0 release with third-party notices preserved. See the repository [LICENSE](../../LICENSE), [NOTICE](../../NOTICE.md) and [component texts](../../LICENSES/).

This proof component belongs to the single root Palomar submission. Submit the collection once with the repository-root comparator.json and formalization.yaml; leave the project directory blank. This account does not require a separate registry entry.
