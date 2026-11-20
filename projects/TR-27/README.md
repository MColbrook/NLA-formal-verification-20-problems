# Delayed tensor-power rank savings

For every r at least three and m at least two, a smooth rational nondegenerate complex projective curve has a point of border rank two and rank r whose unrestricted k-factor Segre rank is r^k for every k from one to m.

Research audience: Algebraic geometers and researchers in tensor rank, secant varieties and algebraic complexity.

Assumptions and conventions:

- The parameters r and m are integers with r>=3 and m>=2; the construction lies in projective space of dimension D-1 with D=r^m+r.
- Ranks allow arbitrary complex coefficients; different curve points may be chosen independently in each of the k Segre factors, without regrouping.
- Border rank uses actual Zariski closure. Smoothness and rationality are certified for the whole curve, including the point at infinity, through explicit analytic chart and birational data.

Selected headline statements:

- **thm:tr27-main** — Constructs the same smooth rational nondegenerate curve and point with border rank two, rank r and tensor-power ranks r^k for all 1<=k<=m. In particular r=3,m=2 gives rank nine at the square in projective eleven-space, disproving the general-variety square-saving conjecture. Lean declaration: `NLA.TR27.Paper.paper_full_family`.

Explicitly compared supporting statements:

- `NLA.TR27.Paper.coordinateProjection_surjective` — For integers D>=2 and r>=3, the explicit linear coordinate projection onto the D-dimensional complex coordinate space is surjective. This supplies the quotient-coordinate equivalence used in the curve statement.
- `NLA.TR27.Paper.coordinateProjection_kernel` — For integers D>=2 and r>=3, the kernel of that explicit coordinate projection is exactly the chosen one-dimensional centre line. This identifies the actual quotient with the stated coordinate space.
- `NLA.TR27.Paper.imageHomogeneousMap_eq_zero_iff` — For integers D>=2 and r>=3 and every homogeneous parameter u in C^2, the explicit homogeneous image map is zero if and only if u is zero. Thus the projective curve map has no nonzero parameter at which all coordinates vanish.
- `NLA.TR27.Paper.tensor_reps_nonzero` — For any complex vector space W, every natural k and every k-tuple of projective points of W, the tensor product of their chosen nonzero representatives is nonzero. This makes the projective tensor point and its powers well defined, including k=0.

This is the arbitrary-parameter finite-delay theorem. The eventual-savings upper bound for each fixed curve is auxiliary material and is not a further selected declaration.

Only the exact declarations listed in [comparator.json](comparator.json) are selected for this component. The full independently compiled module graph retains the other recorded paper proofs; library coverage and a selected comparison are separate scopes. Every retained local module passed ordinary compilation.

This Solution imports all mapped proof roots. The all-local builder mode compiles every retained local module independently, keeping alternative proof environments separate where necessary.

This component passed ordinary full-source Lean 4.35.0 compilation and read-only compiled axiom-dependency queries for every configured declaration, within propext, Classical.choice and Quot.sound. Historical Lean 4.33.1 receipts remain separate source-bound evidence. Official Comparator and NanoDa verification remain pending the authors' later submission; no Palomar acceptance or independent-kernel replay is claimed.

The source is the author-provided unpublished manuscript, section 9, SHA-256 `b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5`. The manuscript and book are not reproduced here. [formalization.yaml](formalization.yaml) records mathematical sources, prior formalizations, scope and AI involvement.

Human authors and responsible maintainers: Matthew J. Colbrook and George Stepaniants. Substantial OpenAI Codex assistance and agent review are disclosed; no independent human review is claimed. The owner authorized the new Apache-2.0 release with third-party notices preserved. See the repository [LICENSE](../../LICENSE), [NOTICE](../../NOTICE.md) and [component texts](../../LICENSES/).

This proof component belongs to the single root Palomar submission. Submit the collection once with the repository-root comparator.json and formalization.yaml; leave the project directory blank. This account does not require a separate registry entry.
