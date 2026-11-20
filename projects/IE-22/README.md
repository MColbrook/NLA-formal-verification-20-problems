# The sharp universal row-deletion constant

The truncated-Gaussian constant is the sharp universal bound for adversarial row deletion among all deterministic real matrices with unit rows, with an explicit uniform squared-error rate and a matching high-aspect supremum limit.

Research audience: Researchers in deterministic frame design, robust linear systems and random-matrix extremal constants.

Assumptions and conventions:

- The retained fraction theta is fixed strictly between zero and one, and the matrix is any real m-by-n matrix with Euclidean unit rows.
- The normalized squared quantity is (n/m) times the least singular value squared after the worst deletion retaining floor(theta*m) rows; its definition allows zero or rank-deficient retained matrices.
- The rate estimate is uniform over every positive row count m for sufficiently large n. The matching supremum limit uses n tending to infinity and m/n tending to infinity.

Selected headline statements:

- **thm:row-universal** — Along every high-aspect sequence, the supremum over unit-row matrices of sqrt(n/m) times the worst retained-set least singular value tends to sqrt(h_theta), so no smaller eventual uniform constant works. Lean declaration: `NLA.IE22.Paper.paper_high_aspect_supremum_limit`.
- **thm:row-universal** — Bounds the normalized squared deletion quantity by h_theta plus a theta-dependent constant times n^(-1/6), uniformly over every row count and unit-row matrix for sufficiently large n. Lean declaration: `NLA.IE22.Paper.paper_universal_squared_rate`.

No distributional assumption is made on the universal upper-bound inputs. Random matrices supply sharpness through the separate IE-21 theorem and proof dependencies.

Only the exact declarations listed in [comparator.json](comparator.json) are selected for this component. The full independently compiled module graph retains the other recorded paper proofs; library coverage and a selected comparison are separate scopes. Every retained local module passed ordinary compilation.

This Solution imports all mapped proof roots. The all-local builder mode compiles every retained local module independently, keeping alternative proof environments separate where necessary.

This component passed ordinary full-source Lean 4.35.0 compilation and read-only compiled axiom-dependency queries for every configured declaration, within propext, Classical.choice and Quot.sound. Historical Lean 4.33.1 receipts remain separate source-bound evidence. Official Comparator and NanoDa verification remain pending the authors' later submission; no Palomar acceptance or independent-kernel replay is claimed.

The source is the author-provided unpublished manuscript, section 7, SHA-256 `b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5`. The manuscript and book are not reproduced here. [formalization.yaml](formalization.yaml) records mathematical sources, prior formalizations, scope and AI involvement.

Human authors and responsible maintainers: Matthew J. Colbrook and George Stepaniants. Substantial OpenAI Codex assistance and agent review are disclosed; no independent human review is claimed. The owner authorized the new Apache-2.0 release with third-party notices preserved. See the repository [LICENSE](../../LICENSE), [NOTICE](../../NOTICE.md) and [component texts](../../LICENSES/).

This proof component belongs to the single root Palomar submission. Submit the collection once with the repository-root comparator.json and formalization.yaml; leave the project directory blank. This account does not require a separate registry entry.
