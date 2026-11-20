# Numerical Linear Algebra, Explained: formal verification

Lean developments accompanying *Numerical Linear Algebra, Explained: Twenty Problem Resolutions*, by **Matthew J. Colbrook and George Stepaniants**.

**One Palomar submission covers all twenty problem resolutions.** Use the
repository-root Challenge, Solution, Comparator configuration, and metadata.
The single configuration retains all 34 component headline and supporting
declarations, together with any explicitly documented technical proof helpers
needed for exact definition comparison.
The seventeen component projects are proof libraries and provenance records;
they are not separate registration targets.

## Single submission interface

| File | Purpose |
| --- | --- |
| [Challenge.lean](Challenge.lean) | Self-contained mathematical statements and fixed definitions |
| [Solution.lean](Solution.lean) | Proved declarations in one combined Lean environment |
| [comparator.json](comparator.json) | The one public submission configuration |
| [formalization.yaml](formalization.yaml) | Collection-wide scope, sources, authorship, automation, and limitations |
| [lakefile.toml](lakefile.toml) | Root Lean project and pinned dependencies |

[SUBMISSION.md](SUBMISSION.md) gives the single form submission, commit/push
commands, and reproduction steps. The root entry in
[submission-index.json](submission-index.json) is the only registration target.
Its `components` section preserves the internal seventeen-project mapping.

## Mathematical accounts

Each component account explains its statements, assumptions, research audience,
and limitations.

| Problems | Mathematical account |
| --- | --- |
| [MF-05, MF-07](projects/MF-05/README.md) | Uniform matrix-product growth and Hölder continuity of the joint spectral radius |
| [MF-12](projects/MF-12/README.md) | Prescribed polynomial growth from two real matrices |
| [RA-02, RA-03](projects/RA-02/README.md) | Sharp random-pivoting losses for Cholesky and LU |
| [RA-08](projects/RA-08/README.md) | Counterexamples to concave matrix-function transfer |
| [RA-09](projects/RA-09/README.md) | Sharp Frobenius transfer bounds |
| [IE-21](projects/IE-21/README.md) | Limit for random-row deletion |
| [IE-22](projects/IE-22/README.md) | The sharp universal row-deletion constant |
| [TR-04](projects/TR-04/README.md) | A strict tensor-train approximation bound |
| [TR-27](projects/TR-27/README.md) | Delayed tensor-power rank savings |
| [IS-03](projects/IS-03/README.md) | Differentiation and nonnegative spectral realizability |
| [NM-04](projects/NM-04/README.md) | The rectangular Rowland–Wu identity |
| [PF-02](projects/PF-02/README.md) | Disconnected minimal PSD factorization spaces |
| [MD-06](projects/MD-06/README.md) | Stable nonsynchronous equilibria on random cubic graphs |
| [IV-02, IV-04](projects/IV-04/README.md) | Hardness of interval determinant ranges and solution hulls |
| [MI-19](projects/MI-19/README.md) | A q-permanent subset-inequality counterexample |
| [MI-21](projects/MI-21/README.md) | A geometric-mean norm counterexample |
| [MI-22](projects/MI-22/README.md) | A weighted log-majorization counterexample |

The author-provided unpublished manuscript has SHA-256
`b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5`.
Its text and the author's book are not bundled. The coverage ledgers record
53 named statements and 57 prose claim groups. Auxiliary proofs remain in the
component libraries, including alternative environments compiled independently.

The [combined definition index](docs/COMBINED-DEFINITIONS.md) links the retained
mathematical definitions to their original component statements and preserves
their original explanatory docstrings.

## Check the prepared snapshot

Use Python 3.11 or later, from the repository root:

~~~text
python -m pip install -r tools/requirements.txt
python scripts/build_entry_metadata.py --check
python scripts/build_combined_interface.py --check
python tools/check_source_coverage.py
python tools/check_submission.py
~~~

The original component snapshot passed ordinary Lean 4.35.0 compilation for
2,304 local modules and compiled axiom queries for all 34 selected declarations.
Those receipts concern the component environments. The combined interface has
separate fresh compilation and axiom evidence in
[verification/combined-build-status.json](verification/combined-build-status.json).
Component receipts cannot establish that all proofs coexist in one Solution.
Statement and fixed-definition agreement is recorded separately in
[verification/combined-correspondence.json](verification/combined-correspondence.json),
using the bundled Comparator comparison core without full proof export or kernel replay.

Challenges intentionally contain statement placeholders. Proved Solution
closures may use only `propext`, `Classical.choice`, and `Quot.sound`.
Ordinary builds and saved axiom reports are distinct from official Palomar
and independent NanoDa verification, which remain pending submission.
No GitHub push, Palomar submission, or registration has been performed here.

The current port pins Lean 4.35.0 and canonical Mathlib, with no LeanCert
dependency. Historical archives preserve earlier LeanCert-assisted work.
The unchanged original sources, compatibility edits, and component build
records remain in [archives/](archives/), [patches/compatibility/](patches/compatibility/),
[audit/](audit/), and [verification/](verification/).

## Provenance and licence

The development includes attributed prior formalizations and substantial OpenAI
Codex assistance. Source-correspondence and proof-scope reviews were agent
reviews; no independent human refereeing or Palomar acceptance is claimed.
The named human authors and maintainers take responsibility for this release.
See [formalization.yaml](formalization.yaml), [NOTICE.md](NOTICE.md), and
[docs/LICENSING-AND-PROVENANCE.md](docs/LICENSING-AND-PROVENANCE.md).

Released under [Apache-2.0](LICENSE), with third-party terms and notices preserved
in [LICENSES/](LICENSES/). [CITATION.cff](CITATION.cff) supplies citation metadata.

<!-- BEGIN COMBINED MATHEMATICAL ACCOUNT -->
## Mathematical statements and assumptions

The following accounts describe every selected headline and supporting declaration
in the single root Comparator configuration. Each subsection records the relevant
hypotheses, conventions, audience, and scope limitations.

### MF-05, MF-07: Uniform matrix-product growth and Hölder continuity of the joint spectral radius

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

### MF-12: Prescribed polynomial growth from two real matrices

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

### RA-02, RA-03: Sharp random-pivoting losses for Cholesky and LU

The sharp worst-case expected loss after r random pivots is 2^r for Cholesky trace residual and 4^r for LU squared Frobenius residual, relative to the corresponding optimal rank-r error.

Research audience: Researchers in randomized numerical linear algebra and low-rank matrix approximation.

Assumptions and conventions:

- The pivot laws and residual updates are the actual randomized algorithms, including zero-pivot and absorbing-zero cases.
- Cholesky inputs are complex positive semidefinite matrices; LU inputs may be arbitrary rectangular complex matrices. Ratios require positive optimal rank-r error.
- The same suprema hold on the stated subclass of real positive-definite entrywise-positive inputs. The rank parameter includes every positive integer r.

Selected headline statements:

- **rap-cor:sup** — Identifies the exact four least upper bounds: 2^r for the Cholesky loss and 4^r for the LU loss, both over the full admissible classes and over the real positive-definite entrywise-positive sharpness subclasses. Lean declaration: `NLA.RA02.Paper.paper_sup_worst_case_constants`.

This grouped component covers RA-02 and RA-03. Unit-diagonal restrictions and finite rational certificates are separate auxiliary library material, not extra conclusions of the selected supremum theorem.

### RA-08: Counterexamples to concave matrix-function transfer

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

### RA-09: Sharp Frobenius transfer bounds

Sharp Frobenius-norm relative-error transfer for nonnegative nondecreasing continuous functions with f(x)/x nonincreasing: factor one under positive-semidefinite order and factor two without order.

Research audience: Researchers in matrix-function approximation, eigenvalue inequalities and low-rank error bounds.

Assumptions and conventions:

- A and B are real positive-semidefinite matrices, rank B is at most k, and the first discarded eigenvalue of A is positive.
- The function is continuous, nonnegative and nondecreasing on the nonnegative axis, with f(x)/x nonincreasing for positive x; concavity and operator monotonicity are not premises.
- The output applies f on the same selected k-dimensional eigenspace of B and is zero on its orthogonal complement, including when f(0) is positive.

Selected headline statements:

- **raf-thm:ordered** — If B is below A in semidefinite order, an input norm-relative factor 1+epsilon transfers with the same factor for the selected transformed approximation. Lean declaration: `NLA.RA09.paper_ordered_matrix_norm_relative`.
- **raf-thm:ordered** — The ordered factor one is optimal, using actual matrix approximation errors and positive comparison tails. Lean declaration: `NLA.RA09.paper_ordered_sharpness`.
- **raf-thm:unordered** — Without semidefinite order, an input norm-relative factor 1+epsilon transfers with factor at most 1+2epsilon. Lean declaration: `NLA.RA09.paper_unordered_matrix_norm_relative`.
- **raf-thm:unordered** — The unordered factor two is optimal, even for operator-monotone power functions, with ratios tending to two. Lean declaration: `NLA.RA09.paper_unordered_sharpness`.

These are the selected norm-relative consequences and sharpness statements. Squared-excess forms, degenerate cutoff cases and operator-monotone integral proofs remain auxiliary results.

### IE-21: Limit for random-row deletion

For independent spherical unit rows and any fixed retained fraction theta in (0,1), the worst retained-set least singular value has the sharp truncated-Gaussian limit whenever n tends to infinity and m/n tends to infinity.

Research audience: Researchers in random matrices, robust linear systems and randomized iterative methods.

Assumptions and conventions:

- The real m-by-n matrix has independent rows uniform on the unit sphere; every sequence with n tending to infinity and m/n tending to infinity is permitted.
- For fixed theta between zero and one, retain floor(theta*m) rows and minimize the variational least singular value over all such subsets.
- The limiting h_theta is E[G^2 1_{|G|<=a_theta}] for a standard Gaussian G and its unique symmetric theta-quantile a_theta.

Selected headline statements:

- **thm:row-random** — Proves joint convergence in probability of (n/m) times the squared worst-subset least singular value to h_theta, (n/m) times the squared operator norm to one, and their squared ratio to h_theta. Lean declaration: `NLA.IE21.Paper.paper_random_rows`.

No stronger growth condition on the aspect ratio and no fixed common probability space are assumed. The deterministic optimality result is the separate IE-22 component.

### IE-22: The sharp universal row-deletion constant

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

### TR-04: A strict tensor-train approximation bound

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

### TR-27: Delayed tensor-power rank savings

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

### IS-03: Differentiation and nonnegative spectral realizability

The normalized characteristic-polynomial derivative of an explicit nonnegative seven-by-seven matrix is not the characteristic polynomial of any nonnegative matrix, even after adjoining arbitrarily many zero roots.

Research audience: Researchers in the nonnegative inverse eigenvalue problem and spectral realizability.

Assumptions and conventions:

- The witness is diag(1/2,C_2,C_4), with C_j the directed j-cycle permutation matrix; nonnegativity is entrywise.
- The derivative is normalized by dividing the degree-seven characteristic derivative by seven. Arbitrary zero padding means every additional number r>=0 of zero roots.
- Realizability concerns the complete characteristic polynomial of an entrywise-nonnegative real matrix of the required order.

Selected headline statements:

- **thm:is03** — Proves that the literal normalized derivative, multiplied by any power z^r, cannot equal the characteristic polynomial of an entrywise-nonnegative real matrix of order 6+r. Lean declaration: `NLA.IS03.paper_counterexample`.

The zero-padding quantifier is part of the selected theorem; it is stronger than disproving realizability in order six alone.

### NM-04: The rectangular Rowland–Wu identity

The Rowland-Wu polynomial identity holds for the top-left entry of the positive balanced Sinkhorn scaling of every strictly positive real rectangular matrix, including matrices with vanishing minors.

Research audience: Researchers in matrix scaling, algebraic identities and Sinkhorn algorithms.

Assumptions and conventions:

- The input is any strictly positive real m-by-n matrix with m,n>=1, and the entry is taken from its genuine positive diagonal scaling with row sums one and column sums m/n.
- The polynomial uses the specified Delta and Gamma minors and principal minors of the literal row/column transition matrix H, with empty determinants and products equal to one.
- No nonvanishing-minor hypothesis is imposed. Arbitrary prescribed margins are not an additional selected claim.

Selected headline statements:

- **thm:nm04-main** — The explicit sum over all subsets of equal-cardinality trailing row/column index pairs vanishes at the scaled top-left entry, with the paper's determinant coefficients and exact m^(-1) normalization. Lean declaration: `NLA.NM04.Paper.paper_rowland_wu_identity`.

The compared theorem is the rectangular identity. Its actual scaling existence/uniqueness and null-vector construction occur in the proof library.

### PF-02: Disconnected minimal PSD factorization spaces

For each real PSD factor size k at least three, there are full-rank nonnegative integer and strictly positive rational square matrices whose spaces of minimal real PSD factorizations modulo invertible congruence are disconnected.

Research audience: Researchers in semidefinite factorizations, extension complexity and the topology of factorization spaces.

Assumptions and conventions:

- For every integer k>=3 the witness order and ordinary real rank are N=k(k+1)/2, and the genuine minimal real PSD rank is k.
- The full real factorization space is quotiented by all invertible congruences with its actual quotient topology.
- Both an entrywise-nonnegative integer witness and an entrywise-strictly-positive rational witness are supplied, with their casts to real matrices explicit.

Selected headline statements:

- **thm:pf02-all** — Constructs, for every k>=3, the two arithmetic classes of N-by-N witnesses with ordinary rank N, minimal real PSD rank k and disconnected congruence orbit spaces. Lean declaration: `Reference.PF02UniformPositiveOrientation.paper_all_size_disconnected_witness`.

Disconnectedness concerns the whole minimal factorization quotient, not merely a selected family of displayed factorizations.

### MD-06: Stable nonsynchronous equilibria on random cubic graphs

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

### IV-02, IV-04: Hardness of interval determinant ranges and solution hulls

Exact determinant ranges and complete solution hulls of rational regular tridiagonal interval systems are NP-hard; the determinant-threshold language is NP-complete, even with superdiagonal entries fixed at one.

Research audience: Researchers in verified numerical computation, interval linear algebra and computational complexity.

Assumptions and conventions:

- Inputs have binary-encoded rational ordered interval endpoints and actual real interval realizations; malformed-input and complete-decoding conventions are explicit.
- The hard restricted families are tridiagonal, every realization is nonsingular, and every superdiagonal entry is one.
- The hull task returns rational lower and upper endpoints for every coordinate, with point right-hand side -e_n and a nonempty bounded actual solution set. Exact-output hardness uses actual polynomial-time query and postprocessing programs.

Selected headline statements:

- **thm:iv-det** — Proves NP-completeness of the determinant-threshold language, NP-hardness on the regular fixed-superdiagonal restriction, and one-query NP-hardness of the exact minimum/maximum determinant output on that restriction. Lean declaration: `IV04.Paper.Computational.actual_paper_iv_det`.
- **thm:iv-hull** — Proves one-query NP-hardness of the literal complete coordinatewise solution-hull output on regular fixed-superdiagonal interval systems with right-hand side -e_n; a correct complete rational answer exists for every reduction input and every such answer decides the source NP language. Lean declaration: `Reference.IV04FullHullHardness.iv_hull_literal_np_hard`.

This grouped component covers IV-02 and IV-04. Exact-output hardness is not a claim about approximate interval arithmetic or an independently selected FP^NP upper-bound algorithm.

### MI-19: A q-permanent subset-inequality counterexample

An explicit real positive-semidefinite four-by-four matrix of rank two violates the q-permanent subset inequality at q=7/8 for a singleton subset.

Research audience: Researchers in generalized permanents and matrix inequalities.

Assumptions and conventions:

- The witness is the exact matrix in the manuscript, with Gram factor having rows (13,0,13,13) and (1,1,-2,1).
- The q-permanent sums actual permutation products weighted by q to the inversion count, and the restricted sum uses the singleton containing paper index two.
- The matrix is positive semidefinite of rank two but need not be entrywise nonnegative; q is exactly 7/8.

Selected headline statements:

- **section 15, unnumbered theorem** — Proves the exact witness's positive semidefiniteness and rank two and the strict negative difference per_q(A)-R_{q,{2}}(A)=-3235575/16384 at q=7/8. Lean declaration: `NLA.MI19.Paper.paper_counterexample`.

The selected result is the explicit semidefinite witness. The positive-definite perturbation remark and the eighteen-moving-terms expansion are auxiliary library statements.

### MI-21: A geometric-mean norm counterexample

Two rational positive-definite input pairs of order two refute the geometric-mean norm inequality in the operator norm at s=t=1/2 and r=2, with both sums equal to identity and the same witness for every p>0.

Research audience: Researchers in matrix geometric means, operator inequalities and unitarily invariant norms.

Assumptions and conventions:

- There are two summands of order two; all four matrices are rational and positive definite, represented in complex matrices for genuine functional calculus.
- The exponents are s=t=1/2 and r=2; p is any positive real number, so sr=1 satisfies the conjectured parameter range.
- Both input sums equal I_2, making the proposed right side one; the norm used for the strict violation is the actual Euclidean operator norm.

Selected headline statements:

- **thm:mi21** — The displayed rational input pairs have the stated positivity and identity sums, and the actual sum of squared geometric means has operator norm strictly greater than the conjectured right-hand side for every p>0. Lean declaration: `NLA.MI21.Paper.paper_counterexample`.

One unitarily invariant norm suffices to refute the universal inequality; the statement does not assert failure for every such norm.

### MI-22: A weighted log-majorization counterexample

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

### Technical supporting theorems

These compiler-generated proof declarations support the fixed mathematical definitions.
Their types are compared explicitly and their genuine Solution proofs are included in
the axiom check. They do not add manuscript headline results.

#### NLA.MI22.singularValue._proof_1

Finite-dimensionality of every complex Euclidean coordinate space, required by the fixed singularValue definition.

Source: [projects/MI-22/NLA/MI22/Definitions.lean](projects/MI-22/NLA/MI22/Definitions.lean#L46), module `NLA.MI22.Definitions`. Generated while elaborating `NLA.MI22.singularValue`.

Normalized compiled type (Lean expression debug form):

```lean
forall {n : Nat}, Module.Finite.{0, 0} Complex (WithLp.{0} (OfNat.ofNat.{0} ENNReal 2 (instOfNatAtLeastTwo.{0} ENNReal 2 (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne)) PiLp.innerProductSpace._proof_1)) ((Fin n) -> Complex)) (Ring.toSemiring.{0} Complex (DivisionRing.toRing.{0} Complex (Field.toDivisionRing.{0} Complex (NormedField.toField.{0} Complex (DenselyNormedField.toNormedField.{0} Complex (RCLike.toDenselyNormedField.{0} Complex Complex.instRCLike)))))) (AddCommGroup.toAddCommMonoid.{0} (WithLp.{0} (OfNat.ofNat.{0} ENNReal 2 (instOfNatAtLeastTwo.{0} ENNReal 2 (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne)) PiLp.innerProductSpace._proof_1)) ((Fin n) -> Complex)) (WithLp.instAddCommGroup.{0} (OfNat.ofNat.{0} ENNReal 2 (instOfNatAtLeastTwo.{0} ENNReal 2 (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne)) PiLp.innerProductSpace._proof_1)) ((Fin n) -> Complex) (Pi.addCommGroup.{0, 0} (Fin n) (fun (x._@.Mathlib.Analysis.InnerProductSpace.PiL2.209079104._hygCtx._hyg.45 : Fin n) => Complex) (fun (i : Fin n) => SeminormedAddCommGroup.toAddCommGroup.{0} Complex (NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup))))) (WithLp.instModule.{0, 0} (OfNat.ofNat.{0} ENNReal 2 (instOfNatAtLeastTwo.{0} ENNReal 2 (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne)) PiLp.innerProductSpace._proof_1)) Complex ((Fin n) -> Complex) (Ring.toSemiring.{0} Complex (DivisionRing.toRing.{0} Complex (Field.toDivisionRing.{0} Complex (NormedField.toField.{0} Complex (DenselyNormedField.toNormedField.{0} Complex (RCLike.toDenselyNormedField.{0} Complex Complex.instRCLike)))))) (Pi.addCommGroup.{0, 0} (Fin n) (fun (x._@.Mathlib.Analysis.InnerProductSpace.PiL2.209079104._hygCtx._hyg.45 : Fin n) => Complex) (fun (i : Fin n) => SeminormedAddCommGroup.toAddCommGroup.{0} Complex (NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup))) (Pi.module.{0, 0, 0} (Fin n) (fun (x._@.Mathlib.Analysis.InnerProductSpace.PiL2.209079104._hygCtx._hyg.45 : Fin n) => Complex) Complex (CommSemiring.toSemiring.{0} Complex (Semifield.toCommSemiring.{0} Complex (Field.toSemifield.{0} Complex (NormedField.toField.{0} Complex (DenselyNormedField.toNormedField.{0} Complex (RCLike.toDenselyNormedField.{0} Complex Complex.instRCLike)))))) (fun (i : Fin n) => AddCommGroup.toAddCommMonoid.{0} Complex (SeminormedAddCommGroup.toAddCommGroup.{0} Complex (NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup))) (fun (i : Fin n) => NormedSpace.toModule.{0, 0} Complex Complex (DenselyNormedField.toNormedField.{0} Complex (RCLike.toDenselyNormedField.{0} Complex Complex.instRCLike)) (NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup) (InnerProductSpace.toNormedSpace.{0, 0} Complex Complex Complex.instRCLike (NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup) (RCLike.innerProductSpace.{0} Complex Complex.instRCLike)))))
```

#### Complexity.NTM.trace._proof_6

For i in Fin T, the bound i.val + 1 < T + 1 needed to advance the finite computation trace.

Source: [projects/IV-04/NLA/IV04/Complexitylib/Models/TuringMachine.lean](projects/IV-04/NLA/IV04/Complexitylib/Models/TuringMachine.lean#L676), module `NLA.IV04.Complexitylib.Models.TuringMachine`. Generated while elaborating `Complexity.NTM.trace`.

Normalized compiled type (Lean expression debug form):

```lean
forall (T : Nat) (i : Fin T), LT.lt.{0} Nat instLTNat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Fin.val T i) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) T (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
```

#### NLA.TR27.Paper.pivotIndex._proof_2

The bound 1 < D + 1 under 2 <= D, required for the coordinate pivot index.

Source: [projects/TR-27/NLA/TR27/PaperCoordinateDefinitions.lean](projects/TR-27/NLA/TR27/PaperCoordinateDefinitions.lean#L15), module `NLA.TR27.PaperCoordinateDefinitions`. Generated while elaborating `NLA.TR27.Paper.pivotIndex`.

Normalized compiled type (Lean expression debug form):

```lean
forall (D : Nat), (LE.le.{0} Nat instLENat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) D) -> (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) D (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
```

#### NLA.TR27.Paper.recoveryIndex._proof_2

The bound j.val + 1 < D for j in Fin 4 and 5 <= D, required by recoveryIndex.

Source: [projects/TR-27/NLA/TR27/PaperRationalDefinitions.lean](projects/TR-27/NLA/TR27/PaperRationalDefinitions.lean#L22), module `NLA.TR27.PaperRationalDefinitions`. Generated while elaborating `NLA.TR27.Paper.recoveryIndex`.

Normalized compiled type (Lean expression debug form):

```lean
forall (D : Nat), (LE.le.{0} Nat instLENat (OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)) D) -> (forall (j : Fin (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))), LT.lt.{0} Nat instLTNat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Fin.val (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4)) j) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) D)
```

#### NLA.TR27.Paper.recoveryOpenPoints._proof_2

The implication 5 <= D -> 2 <= D used by the coordinate pivot in recoveryOpenPoints.

Source: [projects/TR-27/NLA/TR27/PaperRationalGeometryDefinitions.lean](projects/TR-27/NLA/TR27/PaperRationalGeometryDefinitions.lean#L15), module `NLA.TR27.PaperRationalGeometryDefinitions`. Generated while elaborating `NLA.TR27.Paper.recoveryOpenPoints`.

Normalized compiled type (Lean expression debug form):

```lean
forall (D : Nat), Nat -> (LE.le.{0} Nat instLENat (OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)) D) -> (LE.le.{0} Nat instLENat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) D)
```

#### Reference.LexTensorCompletion.lexIndex._proof_5

The right inverse law of the lexicographic index equivalence for the empty mode list.

Source: [projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean](projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L206), module `NLA.TR04.LexicographicTensorReplayR3.PureDefinitions`. Generated while elaborating `Reference.LexTensorCompletion.lexIndex`.

Normalized compiled type (Lean expression debug form):

```lean
forall (j : Fin (Reference.LexTensorCompletion.lexCard (List.nil.{0} Nat))), Eq.{1} (Fin (Reference.LexTensorCompletion.lexCard (List.nil.{0} Nat))) ((fun (x._@.NLA.TR04.LexicographicTensorReplayR3.PureDefinitions.1639430859._hygCtx._hyg.42 : Reference.LexTensorCompletion.ModeIndex (List.nil.{0} Nat)) => Fin.mk (Reference.LexTensorCompletion.lexCard (List.nil.{0} Nat)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) Reference.LexTensorCompletion.lexIndex._proof_2) ((fun (x._@.NLA.TR04.LexicographicTensorReplayR3.PureDefinitions.1639430859._hygCtx._hyg.50 : Fin (Reference.LexTensorCompletion.lexCard (List.nil.{0} Nat))) => PUnit.unit.{1}) j)) j
```

#### Reference.LexTensorCompletion.lexIndex._proof_2

The bound 0 < lexCard [], making zero a valid finite index for the empty mode list.

Source: [projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean](projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L206), module `NLA.TR04.LexicographicTensorReplayR3.PureDefinitions`. Generated while elaborating `Reference.LexTensorCompletion.lexIndex`.

Normalized compiled type (Lean expression debug form):

```lean
LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (Reference.LexTensorCompletion.lexCard (List.nil.{0} Nat))
```

#### NLA.IE21.matrixMap._proof_6

Joint continuity of real scalar multiplication on the Euclidean domain required by the fixed matrixMap construction.

Source: [projects/IE-21/NLA/IE21/Definitions.lean](projects/IE-21/NLA/IE21/Definitions.lean#L60), module `NLA.IE21.Definitions`. Generated while elaborating `NLA.IE21.matrixMap`.

Normalized compiled type (Lean expression debug form):

```lean
forall {n : Nat}, ContinuousSMul.{0, 0} Real (EuclideanSpace.{0, 0} Real (Fin n)) (SMulZeroClass.toSMul.{0, 0} Real (EuclideanSpace.{0, 0} Real (Fin n)) (AddZero.toZero.{0} (EuclideanSpace.{0, 0} Real (Fin n)) (AddZeroClass.toAddZero.{0} (EuclideanSpace.{0, 0} Real (Fin n)) (AddMonoid.toAddZeroClass.{0} (EuclideanSpace.{0, 0} Real (Fin n)) (SubNegMonoid.toAddMonoid.{0} (EuclideanSpace.{0, 0} Real (Fin n)) (AddGroup.toSubNegMonoid.{0} (EuclideanSpace.{0, 0} Real (Fin n)) (AddCommGroup.toAddGroup.{0} (EuclideanSpace.{0, 0} Real (Fin n)) (WithLp.instAddCommGroup.{0} (OfNat.ofNat.{0} ENNReal 2 (instOfNatAtLeastTwo.{0} ENNReal 2 (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne)) PiLp.innerProductSpace._proof_1)) ((Fin n) -> Real) (Pi.addCommGroup.{0, 0} (Fin n) (fun (x._@.Mathlib.Analysis.InnerProductSpace.PiL2.209079104._hygCtx._hyg.45 : Fin n) => Real) (fun (i : Fin n) => Real.instAddCommGroup))))))))) (DistribSMul.toSMulZeroClass.{0, 0} Real (EuclideanSpace.{0, 0} Real (Fin n)) (AddMonoid.toAddZeroClass.{0} (EuclideanSpace.{0, 0} Real (Fin n)) (SubNegMonoid.toAddMonoid.{0} (EuclideanSpace.{0, 0} Real (Fin n)) (AddGroup.toSubNegMonoid.{0} (EuclideanSpace.{0, 0} Real (Fin n)) (AddCommGroup.toAddGroup.{0} (EuclideanSpace.{0, 0} Real (Fin n)) (WithLp.instAddCommGroup.{0} (OfNat.ofNat.{0} ENNReal 2 (instOfNatAtLeastTwo.{0} ENNReal 2 (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne)) PiLp.innerProductSpace._proof_1)) ((Fin n) -> Real) (Pi.addCommGroup.{0, 0} (Fin n) (fun (x._@.Mathlib.Analysis.InnerProductSpace.PiL2.209079104._hygCtx._hyg.45 : Fin n) => Real) (fun (i : Fin n) => Real.instAddCommGroup))))))) (DistribMulAction.toDistribSMul.{0, 0} Real (EuclideanSpace.{0, 0} Real (Fin n)) (Semiring.toMonoid.{0} Real (CommSemiring.toSemiring.{0} Real (Semifield.toCommSemiring.{0} Real (Field.toSemifield.{0} Real (NormedField.toField.{0} Real Real.normedField))))) (SubNegMonoid.toAddMonoid.{0} (EuclideanSpace.{0, 0} Real (Fin n)) (AddGroup.toSubNegMonoid.{0} (EuclideanSpace.{0, 0} Real (Fin n)) (AddCommGroup.toAddGroup.{0} (EuclideanSpace.{0, 0} Real (Fin n)) (WithLp.instAddCommGroup.{0} (OfNat.ofNat.{0} ENNReal 2 (instOfNatAtLeastTwo.{0} ENNReal 2 (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne)) PiLp.innerProductSpace._proof_1)) ((Fin n) -> Real) (Pi.addCommGroup.{0, 0} (Fin n) (fun (x._@.Mathlib.Analysis.InnerProductSpace.PiL2.209079104._hygCtx._hyg.45 : Fin n) => Real) (fun (i : Fin n) => Real.instAddCommGroup)))))) (Module.toDistribMulAction.{0, 0} Real (EuclideanSpace.{0, 0} Real (Fin n)) (CommSemiring.toSemiring.{0} Real (Semifield.toCommSemiring.{0} Real (Field.toSemifield.{0} Real (NormedField.toField.{0} Real Real.normedField)))) (AddCommGroup.toAddCommMonoid.{0} (EuclideanSpace.{0, 0} Real (Fin n)) (WithLp.instAddCommGroup.{0} (OfNat.ofNat.{0} ENNReal 2 (instOfNatAtLeastTwo.{0} ENNReal 2 (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne)) PiLp.innerProductSpace._proof_1)) ((Fin n) -> Real) (Pi.addCommGroup.{0, 0} (Fin n) (fun (x._@.Mathlib.Analysis.InnerProductSpace.PiL2.209079104._hygCtx._hyg.45 : Fin n) => Real) (fun (i : Fin n) => Real.instAddCommGroup)))) (WithLp.instModule.{0, 0} (OfNat.ofNat.{0} ENNReal 2 (instOfNatAtLeastTwo.{0} ENNReal 2 (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne)) PiLp.innerProductSpace._proof_1)) Real ((Fin n) -> Real) (CommSemiring.toSemiring.{0} Real (Semifield.toCommSemiring.{0} Real (Field.toSemifield.{0} Real (NormedField.toField.{0} Real Real.normedField)))) (Pi.addCommGroup.{0, 0} (Fin n) (fun (x._@.Mathlib.Analysis.InnerProductSpace.PiL2.209079104._hygCtx._hyg.45 : Fin n) => Real) (fun (i : Fin n) => Real.instAddCommGroup)) (Pi.Function.module.{0, 0, 0} (Fin n) Real Real (CommSemiring.toSemiring.{0} Real (Semifield.toCommSemiring.{0} Real (Field.toSemifield.{0} Real (NormedField.toField.{0} Real Real.normedField)))) (Semiring.toAddCommMonoid.{0} Real (Ring.toSemiring.{0} Real Real.instRing)) (Semiring.toModule.{0} Real (CommSemiring.toSemiring.{0} Real (Semifield.toCommSemiring.{0} Real (Field.toSemifield.{0} Real (NormedField.toField.{0} Real Real.normedField))))))))))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real (SeminormedRing.toPseudoMetricSpace.{0} Real (SeminormedCommRing.toSeminormedRing.{0} Real (NormedCommRing.toSeminormedCommRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))))) (PiLp.topologicalSpace.{0, 0} (OfNat.ofNat.{0} ENNReal 2 (instOfNatAtLeastTwo.{0} ENNReal 2 (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne)) PiLp.innerProductSpace._proof_1)) (Fin n) (fun (x._@.Mathlib.Analysis.InnerProductSpace.PiL2.209079104._hygCtx._hyg.45 : Fin n) => Real) (fun (i : Fin n) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
```

#### NLA.IE21.matrixMap._proof_4

Continuity of multiplication by each fixed real scalar on the Euclidean codomain required by matrixMap.

Source: [projects/IE-21/NLA/IE21/Definitions.lean](projects/IE-21/NLA/IE21/Definitions.lean#L60), module `NLA.IE21.Definitions`. Generated while elaborating `NLA.IE21.matrixMap`.

Normalized compiled type (Lean expression debug form):

```lean
forall {m : Nat}, ContinuousConstSMul.{0, 0} Real (EuclideanSpace.{0, 0} Real (Fin m)) (PiLp.topologicalSpace.{0, 0} (OfNat.ofNat.{0} ENNReal 2 (instOfNatAtLeastTwo.{0} ENNReal 2 (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne)) PiLp.innerProductSpace._proof_1)) (Fin m) (fun (x._@.Mathlib.Analysis.InnerProductSpace.PiL2.209079104._hygCtx._hyg.45 : Fin m) => Real) (fun (i : Fin m) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) (SMulZeroClass.toSMul.{0, 0} Real (EuclideanSpace.{0, 0} Real (Fin m)) (AddZero.toZero.{0} (EuclideanSpace.{0, 0} Real (Fin m)) (AddZeroClass.toAddZero.{0} (EuclideanSpace.{0, 0} Real (Fin m)) (AddMonoid.toAddZeroClass.{0} (EuclideanSpace.{0, 0} Real (Fin m)) (AddCommMonoid.toAddMonoid.{0} (EuclideanSpace.{0, 0} Real (Fin m)) (AddCommGroup.toAddCommMonoid.{0} (EuclideanSpace.{0, 0} Real (Fin m)) (WithLp.instAddCommGroup.{0} (OfNat.ofNat.{0} ENNReal 2 (instOfNatAtLeastTwo.{0} ENNReal 2 (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne)) PiLp.innerProductSpace._proof_1)) ((Fin m) -> Real) (Pi.addCommGroup.{0, 0} (Fin m) (fun (x._@.Mathlib.Analysis.InnerProductSpace.PiL2.209079104._hygCtx._hyg.45 : Fin m) => Real) (fun (i : Fin m) => Real.instAddCommGroup)))))))) (DistribSMul.toSMulZeroClass.{0, 0} Real (EuclideanSpace.{0, 0} Real (Fin m)) (AddMonoid.toAddZeroClass.{0} (EuclideanSpace.{0, 0} Real (Fin m)) (AddCommMonoid.toAddMonoid.{0} (EuclideanSpace.{0, 0} Real (Fin m)) (AddCommGroup.toAddCommMonoid.{0} (EuclideanSpace.{0, 0} Real (Fin m)) (WithLp.instAddCommGroup.{0} (OfNat.ofNat.{0} ENNReal 2 (instOfNatAtLeastTwo.{0} ENNReal 2 (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne)) PiLp.innerProductSpace._proof_1)) ((Fin m) -> Real) (Pi.addCommGroup.{0, 0} (Fin m) (fun (x._@.Mathlib.Analysis.InnerProductSpace.PiL2.209079104._hygCtx._hyg.45 : Fin m) => Real) (fun (i : Fin m) => Real.instAddCommGroup)))))) (DistribMulAction.toDistribSMul.{0, 0} Real (EuclideanSpace.{0, 0} Real (Fin m)) (Semiring.toMonoid.{0} Real (CommSemiring.toSemiring.{0} Real (Semifield.toCommSemiring.{0} Real (Field.toSemifield.{0} Real (NormedField.toField.{0} Real (NontriviallyNormedField.toNormedField.{0} Real (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))) (AddCommMonoid.toAddMonoid.{0} (EuclideanSpace.{0, 0} Real (Fin m)) (AddCommGroup.toAddCommMonoid.{0} (EuclideanSpace.{0, 0} Real (Fin m)) (WithLp.instAddCommGroup.{0} (OfNat.ofNat.{0} ENNReal 2 (instOfNatAtLeastTwo.{0} ENNReal 2 (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne)) PiLp.innerProductSpace._proof_1)) ((Fin m) -> Real) (Pi.addCommGroup.{0, 0} (Fin m) (fun (x._@.Mathlib.Analysis.InnerProductSpace.PiL2.209079104._hygCtx._hyg.45 : Fin m) => Real) (fun (i : Fin m) => Real.instAddCommGroup))))) (Module.toDistribMulAction.{0, 0} Real (EuclideanSpace.{0, 0} Real (Fin m)) (CommSemiring.toSemiring.{0} Real (Semifield.toCommSemiring.{0} Real (Field.toSemifield.{0} Real (NormedField.toField.{0} Real (NontriviallyNormedField.toNormedField.{0} Real (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))) (AddCommGroup.toAddCommMonoid.{0} (EuclideanSpace.{0, 0} Real (Fin m)) (WithLp.instAddCommGroup.{0} (OfNat.ofNat.{0} ENNReal 2 (instOfNatAtLeastTwo.{0} ENNReal 2 (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne)) PiLp.innerProductSpace._proof_1)) ((Fin m) -> Real) (Pi.addCommGroup.{0, 0} (Fin m) (fun (x._@.Mathlib.Analysis.InnerProductSpace.PiL2.209079104._hygCtx._hyg.45 : Fin m) => Real) (fun (i : Fin m) => Real.instAddCommGroup)))) (WithLp.instModule.{0, 0} (OfNat.ofNat.{0} ENNReal 2 (instOfNatAtLeastTwo.{0} ENNReal 2 (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne)) PiLp.innerProductSpace._proof_1)) Real ((Fin m) -> Real) (CommSemiring.toSemiring.{0} Real (Semifield.toCommSemiring.{0} Real (Field.toSemifield.{0} Real (NormedField.toField.{0} Real (DenselyNormedField.toNormedField.{0} Real (RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))) (Pi.addCommGroup.{0, 0} (Fin m) (fun (x._@.Mathlib.Analysis.InnerProductSpace.PiL2.209079104._hygCtx._hyg.45 : Fin m) => Real) (fun (i : Fin m) => Ring.toAddCommGroup.{0} Real (DivisionRing.toRing.{0} Real (Field.toDivisionRing.{0} Real (NormedField.toField.{0} Real (DenselyNormedField.toNormedField.{0} Real (RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))) (Pi.Function.module.{0, 0, 0} (Fin m) Real Real (CommSemiring.toSemiring.{0} Real (Semifield.toCommSemiring.{0} Real (Field.toSemifield.{0} Real (NormedField.toField.{0} Real (DenselyNormedField.toNormedField.{0} Real (RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))) (Semiring.toAddCommMonoid.{0} Real (Ring.toSemiring.{0} Real (DivisionRing.toRing.{0} Real (Field.toDivisionRing.{0} Real (NormedField.toField.{0} Real (DenselyNormedField.toNormedField.{0} Real (RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))) (Semiring.toModule.{0} Real (CommSemiring.toSemiring.{0} Real (Semifield.toCommSemiring.{0} Real (Field.toSemifield.{0} Real (NormedField.toField.{0} Real (DenselyNormedField.toNormedField.{0} Real (RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))))))))))
```

<!-- END COMBINED MATHEMATICAL ACCOUNT -->
