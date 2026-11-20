# Uniform matrix-product growth and Hölder continuity of the joint spectral radius

Uniform growth bounds for products from a bounded family of real matrices, exact nilpotence at zero joint spectral radius, and a uniform local 1/d-Hölder estimate for the joint spectral radius.

Research audience: Researchers studying switched linear systems, matrix semigroups and continuity of the joint spectral radius.

Assumptions and conventions:

- The growth assertions concern every nonempty bounded family of real d-by-d matrices, d at least one, with the Euclidean operator norm and actual length-n products.
- Positive-radius growth retains the explicit dimension-dependent constant and all positive word lengths; zero radius implies every word of length at least d is zero.
- The Hölder assertion concerns nonempty compact families inside a common spectral-norm ball of radius L greater than zero, measured by the Hausdorff distance. No irreducibility or finite-generator restriction is imposed.

Selected headline statements:

- **mfu-thm-growth** — For every positive word length n and joint spectral radius rho>0, the maximal product norm is at most theta_d*(L*n)^(d-1)*rho^(n-d+1), where L>0 bounds all generator norms, theta_1=1 and theta_d=d*(2*exp(1)*d^2/(d-1))^(d-1) for d>=2. Lean declaration: `NLA.MF05.Paper.paper_real_bounded_positive_radius_growth`.
- **mfu-thm-growth** — If the joint spectral radius is zero, every matrix word of length at least the ambient dimension is exactly zero. Lean declaration: `NLA.MF05.Paper.paper_real_bounded_zero_radius_nilpotent`.
- **mfu-thm-holder** — For two nonempty compact real matrix families in a common norm ball, bounds the difference of their joint spectral radii by d(2d+1)L^(1-1/d) times their spectral Hausdorff distance to power 1/d. Lean declaration: `NLA.MF05.Paper.paper_real_uniform_holder`.

This component selects the real-family headline statements. Complex-family versions and further norm constructions are auxiliary library results, not additional selected headline declarations.

Only the exact declarations listed in [comparator.json](comparator.json) are selected for this component. The full independently compiled module graph retains the other recorded paper proofs; library coverage and a selected comparison are separate scopes. Every retained local module passed ordinary compilation.

This Solution imports all mapped proof roots. The all-local builder mode compiles every retained local module independently, keeping alternative proof environments separate where necessary.

This component passed ordinary full-source Lean 4.35.0 compilation and read-only compiled axiom-dependency queries for every configured declaration, within propext, Classical.choice and Quot.sound. Historical Lean 4.33.1 receipts remain separate source-bound evidence. Official Comparator and NanoDa verification remain pending the authors' later submission; no Palomar acceptance or independent-kernel replay is claimed.

The source is the author-provided unpublished manuscript, section 2, SHA-256 `b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5`. The manuscript and book are not reproduced here. [formalization.yaml](formalization.yaml) records mathematical sources, prior formalizations, scope and AI involvement.

Human authors and responsible maintainers: Matthew J. Colbrook and George Stepaniants. Substantial OpenAI Codex assistance and agent review are disclosed; no independent human review is claimed. The owner authorized the new Apache-2.0 release with third-party notices preserved. See the repository [LICENSE](../../LICENSE), [NOTICE](../../NOTICE.md) and [component texts](../../LICENSES/).

This proof component belongs to the single root Palomar submission. Submit the collection once with the repository-root comparator.json and formalization.yaml; leave the project directory blank. This account does not require a separate registry entry.
