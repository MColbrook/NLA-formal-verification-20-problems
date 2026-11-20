# Stable nonsynchronous equilibria on random cubic graphs

Uniform labelled simple cubic graphs typically have a nonsynchronised local minimum of the attractive Kuramoto energy, with every edge cosine above 1/32 and Hessian at least 1/320 on the mean-zero subspace.

Research audience: Researchers in synchronization dynamics, random regular graphs and probabilistic network models.

Assumptions and conventions:

- Graphs are uniform over labelled simple 3-regular graphs on every even order n>=4; the limit is along those even orders.
- The energy is the sum over unordered edges of 1-cos(theta_u-theta_v), on the phase torus with common rotations identified for stability.
- The quantitative Hessian inequality is tested on every mean-zero real vector and uses the ordinary Euclidean squared norm.

Selected headline statements:

- **md-main** — The probability that every torus local minimum is synchronised tends to zero; with probability tending to one there is a nonsynchronised critical local minimum with all edge cosines >1/32 and Hessian quadratic form >=(1/320) times the squared norm on the mean-zero subspace. Lean declaration: `Reference.MD06MainAssembly.Interface.actual_paper_md_main`.

Explicitly compared supporting statements:

- `Reference.MD06FiniteProbability.actual_cubic_sample_nonempty` — For every natural k, there exists a labelled simple 3-regular graph on 2(k+2) vertices. Hence every finite cubic-graph sample space used by the theorem is nonempty and carries the stated uniform probability distribution.

The graph distribution and quantitative stability are actual conclusions of the selected theorem; expansion, cycle probabilities and correction estimates are proved supporting results, not assumed probabilistic contracts.

Only the exact declarations listed in [comparator.json](comparator.json) are selected for this component. The full independently compiled module graph retains the other recorded paper proofs; library coverage and a selected comparison are separate scopes. Every retained local module passed ordinary compilation.

This Solution imports all mapped proof roots. The all-local builder mode compiles every retained local module independently, keeping alternative proof environments separate where necessary.

This component passed ordinary full-source Lean 4.35.0 compilation and read-only compiled axiom-dependency queries for every configured declaration, within propext, Classical.choice and Quot.sound. Historical Lean 4.33.1 receipts remain separate source-bound evidence. Official Comparator and NanoDa verification remain pending the authors' later submission; no Palomar acceptance or independent-kernel replay is claimed.

The source is the author-provided unpublished manuscript, section 13, SHA-256 `b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5`. The manuscript and book are not reproduced here. [formalization.yaml](formalization.yaml) records mathematical sources, prior formalizations, scope and AI involvement.

Human authors and responsible maintainers: Matthew J. Colbrook and George Stepaniants. Substantial OpenAI Codex assistance and agent review are disclosed; no independent human review is claimed. The owner authorized the new Apache-2.0 release with third-party notices preserved. See the repository [LICENSE](../../LICENSE), [NOTICE](../../NOTICE.md) and [component texts](../../LICENSES/).

This proof component belongs to the single root Palomar submission. Submit the collection once with the repository-root comparator.json and formalization.yaml; leave the project directory blank. This account does not require a separate registry entry.
