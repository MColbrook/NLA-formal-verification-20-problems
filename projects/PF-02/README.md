# Disconnected minimal PSD factorization spaces

For each real PSD factor size k at least three, there are full-rank nonnegative integer and strictly positive rational square matrices whose spaces of minimal real PSD factorizations modulo invertible congruence are disconnected.

Research audience: Researchers in semidefinite factorizations, extension complexity and the topology of factorization spaces.

Assumptions and conventions:

- For every integer k>=3 the witness order and ordinary real rank are N=k(k+1)/2, and the genuine minimal real PSD rank is k.
- The full real factorization space is quotiented by all invertible congruences with its actual quotient topology.
- Both an entrywise-nonnegative integer witness and an entrywise-strictly-positive rational witness are supplied, with their casts to real matrices explicit.

Selected headline statements:

- **thm:pf02-all** — Constructs, for every k>=3, the two arithmetic classes of N-by-N witnesses with ordinary rank N, minimal real PSD rank k and disconnected congruence orbit spaces. Lean declaration: `Reference.PF02UniformPositiveOrientation.paper_all_size_disconnected_witness`.

Disconnectedness concerns the whole minimal factorization quotient, not merely a selected family of displayed factorizations.

Only the exact declarations listed in [comparator.json](comparator.json) are selected for this component. The full independently compiled module graph retains the other recorded paper proofs; library coverage and a selected comparison are separate scopes. Every retained local module passed ordinary compilation.

This Solution imports all mapped proof roots. The all-local builder mode compiles every retained local module independently, keeping alternative proof environments separate where necessary.

This component passed ordinary full-source Lean 4.35.0 compilation and read-only compiled axiom-dependency queries for every configured declaration, within propext, Classical.choice and Quot.sound. Historical Lean 4.33.1 receipts remain separate source-bound evidence. Official Comparator and NanoDa verification remain pending the authors' later submission; no Palomar acceptance or independent-kernel replay is claimed.

The source is the author-provided unpublished manuscript, section 12, SHA-256 `b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5`. The manuscript and book are not reproduced here. [formalization.yaml](formalization.yaml) records mathematical sources, prior formalizations, scope and AI involvement.

Human authors and responsible maintainers: Matthew J. Colbrook and George Stepaniants. Substantial OpenAI Codex assistance and agent review are disclosed; no independent human review is claimed. The owner authorized the new Apache-2.0 release with third-party notices preserved. See the repository [LICENSE](../../LICENSE), [NOTICE](../../NOTICE.md) and [component texts](../../LICENSES/).

This proof component belongs to the single root Palomar submission. Submit the collection once with the repository-root comparator.json and formalization.yaml; leave the project directory blank. This account does not require a separate registry entry.
