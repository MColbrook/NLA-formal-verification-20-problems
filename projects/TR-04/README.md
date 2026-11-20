# A strict tensor-train approximation bound

A deterministic exact-arithmetic/SVD algorithm returns a tensor-train approximation within the prescribed ranks with squared error strictly below (d-1) times the optimum whenever the optimum is positive, and exact recovery otherwise.

Research audience: Researchers in tensor approximation algorithms and numerical multilinear algebra.

Assumptions and conventions:

- The input is a dense real tensor of order d at least three, every mode has size at least two, and the first prescribed rank is positive. The formal statement even allows zero remaining ranks.
- Feasibility means the actual consecutive unfolding-rank bounds. The optimum is the attained minimum squared Frobenius error over that feasible set.
- The model charges exact scalar arithmetic, comparisons and specified cubic-cost singular-subspace primitives; static shape/index/reference metadata is free. This is not a floating-point, bit-complexity or compiler guarantee.

Selected headline statements:

- **thm:tr04-main** — The concrete lexicographic algorithm returns a feasible tensor, uses at most the first mode size many genuine TT-SVD completions, achieves strict squared error below (d-1)E_* when E_*>0 and exact recovery when E_*=0, and has charged cost at most 1500 times the fifth power of the dense input size. Lean declaration: `Reference.LexTensorExecution.actual_lexicographic_paper_algorithm`.

Explicitly compared supporting statements:

- `Reference.LexicographicFeasibilityBridge.product_eq_rowCount` — For every pair of natural mode sizes m,n, the concrete flattened row count equals m*n. This certifies the finite-index cast in the actual two-mode row layout.
- `Reference.LexTensorCompletion.lexCard_eq_card` — For every finite list of natural mode sizes, the recursive mixed-radix cardinality equals the number of actual tensor mode indices. This certifies the concrete layout equivalence used by TT-SVD completion.

The selected statement is the algorithm theorem. The separate every-order limiting sharpness examples are auxiliary proof-library results, not additional selected headline declarations.

Only the exact declarations listed in [comparator.json](comparator.json) are selected for this component. The full independently compiled module graph retains the other recorded paper proofs; library coverage and a selected comparison are separate scopes. Every retained local module passed ordinary compilation.

TR-04 Solution imports its primary algorithm proof root only. Alternative auxiliary tensor-arithmetic environments are retained and compiled independently with the all-local builder mode; they are not combined in one import closure. Mathematical statements are neither weakened nor renamed.

This component passed ordinary full-source Lean 4.35.0 compilation and read-only compiled axiom-dependency queries for every configured declaration, within propext, Classical.choice and Quot.sound. Historical Lean 4.33.1 receipts remain separate source-bound evidence. Official Comparator and NanoDa verification remain pending the authors' later submission; no Palomar acceptance or independent-kernel replay is claimed.

The source is the author-provided unpublished manuscript, section 8, SHA-256 `b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5`. The manuscript and book are not reproduced here. [formalization.yaml](formalization.yaml) records mathematical sources, prior formalizations, scope and AI involvement.

Human authors and responsible maintainers: Matthew J. Colbrook and George Stepaniants. Substantial OpenAI Codex assistance and agent review are disclosed; no independent human review is claimed. The owner authorized the new Apache-2.0 release with third-party notices preserved. See the repository [LICENSE](../../LICENSE), [NOTICE](../../NOTICE.md) and [component texts](../../LICENSES/).

This proof component belongs to the single root Palomar submission. Submit the collection once with the repository-root comparator.json and formalization.yaml; leave the project directory blank. This account does not require a separate registry entry.
