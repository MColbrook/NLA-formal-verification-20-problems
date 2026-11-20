# Limit for random-row deletion

For independent spherical unit rows and any fixed retained fraction theta in (0,1), the worst retained-set least singular value has the sharp truncated-Gaussian limit whenever n tends to infinity and m/n tends to infinity.

Research audience: Researchers in random matrices, robust linear systems and randomized iterative methods.

Assumptions and conventions:

- The real m-by-n matrix has independent rows uniform on the unit sphere; every sequence with n tending to infinity and m/n tending to infinity is permitted.
- For fixed theta between zero and one, retain floor(theta*m) rows and minimize the variational least singular value over all such subsets.
- The limiting h_theta is E[G^2 1_{|G|<=a_theta}] for a standard Gaussian G and its unique symmetric theta-quantile a_theta.

Selected headline statements:

- **thm:row-random** — Proves joint convergence in probability of (n/m) times the squared worst-subset least singular value to h_theta, (n/m) times the squared operator norm to one, and their squared ratio to h_theta. Lean declaration: `NLA.IE21.Paper.paper_random_rows`.

No stronger growth condition on the aspect ratio and no fixed common probability space are assumed. The deterministic optimality result is the separate IE-22 component.

Only the exact declarations listed in [comparator.json](comparator.json) are selected for this component. The full independently compiled module graph retains the other recorded paper proofs; library coverage and a selected comparison are separate scopes. Every retained local module passed ordinary compilation.

This Solution imports all mapped proof roots. The all-local builder mode compiles every retained local module independently, keeping alternative proof environments separate where necessary.

This component passed ordinary full-source Lean 4.35.0 compilation and read-only compiled axiom-dependency queries for every configured declaration, within propext, Classical.choice and Quot.sound. Historical Lean 4.33.1 receipts remain separate source-bound evidence. Official Comparator and NanoDa verification remain pending the authors' later submission; no Palomar acceptance or independent-kernel replay is claimed.

The source is the author-provided unpublished manuscript, section 7, SHA-256 `b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5`. The manuscript and book are not reproduced here. [formalization.yaml](formalization.yaml) records mathematical sources, prior formalizations, scope and AI involvement.

Human authors and responsible maintainers: Matthew J. Colbrook and George Stepaniants. Substantial OpenAI Codex assistance and agent review are disclosed; no independent human review is claimed. The owner authorized the new Apache-2.0 release with third-party notices preserved. See the repository [LICENSE](../../LICENSE), [NOTICE](../../NOTICE.md) and [component texts](../../LICENSES/).

This proof component belongs to the single root Palomar submission. Submit the collection once with the repository-root comparator.json and formalization.yaml; leave the project directory blank. This account does not require a separate registry entry.
