# Prescribed polynomial growth from two real matrices

For every nonnegative real exponent gamma, two distinct real matrices have maximal length-n product norm bounded above and below by positive constants times n^gamma. Rational exponents admit dyadic entries.

Research audience: Researchers in matrix-product growth and the stability of linear switching systems.

Assumptions and conventions:

- The exponent gamma is any real number at least zero; the construction chooses its finite matrix dimension and two distinct generators.
- Two-sided Euclidean operator-norm bounds hold at every positive integer word length, and the actual nth-root growth limit is one.
- The dyadic refinement assumes gamma is rational; dyadic means an integer divided by a power of two.

Selected headline statements:

- **mfg-thm-main** — Constructs two distinct real matrices and positive constants whose maximal word norm grows as n^gamma for every positive integer n, for any prescribed real gamma at least zero, with joint spectral radius one. Lean declaration: `NLA.MF12.Paper.paper_main_realization`.
- **mfg-thm-main** — When gamma is rational and nonnegative, obtains the same all-length growth and radius conclusions using matrices with dyadic rational entries. Lean declaration: `NLA.MF12.Paper.paper_rational_realization`.

These are existence and dyadic-realization theorems; sharper constants in an informal construction are not additional compared claims.

Only the exact declarations listed in [comparator.json](comparator.json) are selected for this component. The full independently compiled module graph retains the other recorded paper proofs; library coverage and a selected comparison are separate scopes. Every retained local module passed ordinary compilation.

This Solution imports all mapped proof roots. The all-local builder mode compiles every retained local module independently, keeping alternative proof environments separate where necessary.

This component passed ordinary full-source Lean 4.35.0 compilation and read-only compiled axiom-dependency queries for every configured declaration, within propext, Classical.choice and Quot.sound. Historical Lean 4.33.1 receipts remain separate source-bound evidence. Official Comparator and NanoDa verification remain pending the authors' later submission; no Palomar acceptance or independent-kernel replay is claimed.

The source is the author-provided unpublished manuscript, section 3, SHA-256 `b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5`. The manuscript and book are not reproduced here. [formalization.yaml](formalization.yaml) records mathematical sources, prior formalizations, scope and AI involvement.

Human authors and responsible maintainers: Matthew J. Colbrook and George Stepaniants. Substantial OpenAI Codex assistance and agent review are disclosed; no independent human review is claimed. The owner authorized the new Apache-2.0 release with third-party notices preserved. See the repository [LICENSE](../../LICENSE), [NOTICE](../../NOTICE.md) and [component texts](../../LICENSES/).

This proof component belongs to the single root Palomar submission. Submit the collection once with the repository-root comparator.json and formalization.yaml; leave the project directory blank. This account does not require a separate registry entry.
