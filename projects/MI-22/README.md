# A weighted log-majorization counterexample

The literal rational three-by-three matrices A=diag(256,1/256,1) and the printed integer B refute weighted singular-value log-majorisation at t=1/8, with certified operator-norm bounds above 10900 and below 10200.

Research audience: Researchers in matrix means, singular-value inequalities and certified spectral computation.

Assumptions and conventions:

- A=diag(256,1/256,1), B has rows (17,-4,0), (-4,16385,-8192), (0,-8192,4096), and t=1/8; both matrices are proved positive definite.
- The left product is A^(1/8)(A#_(1/8)B)B^(7/8), with the actual functional-calculus weighted geometric mean; the right product is AB.
- Log-majorisation compares actual ordered singular values. The first partial-product inequality already fails because the left operator norm exceeds the right.

Selected headline statements:

- **thm:mi22** — Proves the exact inputs' positive definiteness, left-product operator norm >10900, right-product operator norm <10200, and failure of the stated weighted singular-value log-majorisation at t=1/8. Lean declaration: `NLA.MI22.Paper.paper_counterexample`.
- **thm:mi22** — Uses that actual counterexample to refute the original universally quantified weighted log-majorisation conjecture. Lean declaration: `NLA.MI22.Paper.paper_conjecture_false`.

Rational eighth-root certificates and noncommutative error propagation prove inequalities for the genuine matrix roots; floating-point evidence is not a premise.

Only the exact declarations listed in [comparator.json](comparator.json) are selected for this component. The full independently compiled module graph retains the other recorded paper proofs; library coverage and a selected comparison are separate scopes. Every retained local module passed ordinary compilation.

This Solution imports all mapped proof roots. The all-local builder mode compiles every retained local module independently, keeping alternative proof environments separate where necessary.

This component passed ordinary full-source Lean 4.35.0 compilation and read-only compiled axiom-dependency queries for every configured declaration, within propext, Classical.choice and Quot.sound. Historical Lean 4.33.1 receipts remain separate source-bound evidence. Official Comparator and NanoDa verification remain pending the authors' later submission; no Palomar acceptance or independent-kernel replay is claimed.

The source is the author-provided unpublished manuscript, section 17, SHA-256 `b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5`. The manuscript and book are not reproduced here. [formalization.yaml](formalization.yaml) records mathematical sources, prior formalizations, scope and AI involvement.

Human authors and responsible maintainers: Matthew J. Colbrook and George Stepaniants. Substantial OpenAI Codex assistance and agent review are disclosed; no independent human review is claimed. The owner authorized the new Apache-2.0 release with third-party notices preserved. See the repository [LICENSE](../../LICENSE), [NOTICE](../../NOTICE.md) and [component texts](../../LICENSES/).

This proof component belongs to the single root Palomar submission. Submit the collection once with the repository-root comparator.json and formalization.yaml; leave the project directory blank. This account does not require a separate registry entry.
