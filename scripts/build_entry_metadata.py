#!/usr/bin/env python3
"""Generate truthful component accounts for one root submission; never invoke Lean or kernels.

Run from any directory after staging interfaces:
    python scripts/build_entry_metadata.py
    python scripts/build_entry_metadata.py --check

Requires the pinned PyYAML dependency in tools/requirements.txt. The unchanged
vendored official metadata validator checks all written metadata. New comparator
helpers require explicit mathematical roles in audit/entry-interfaces.json;
unknown names fail instead of silently disappearing from the informal account.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import posixpath
import re
from pathlib import Path
import sys

import yaml

ROOT = Path(__file__).resolve().parents[1]
MANUSCRIPT = "b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5"
AUTHORS = ["Matthew J. Colbrook", "George Stepaniants"]
VERIFICATION_STATUS = (
    "This entry passed ordinary full-source Lean 4.35.0 compilation and read-only "
    "compiled axiom-dependency queries for every configured declaration, within "
    "propext, Classical.choice and Quot.sound. Historical Lean 4.33.1 receipts "
    "remain separate source-bound evidence. Official Comparator and NanoDa "
    "verification remain pending the authors' later submission; no Palomar "
    "acceptance or independent-kernel replay is claimed."
)

# Curated from the author-provided source and its current statement ledger.
# 'claims' follows the primary target order, one account for each exact name.
SPECS = {
    "MF-05": {
        "summary": "Uniform growth bounds for products from a bounded family of real matrices, exact nilpotence at zero joint spectral radius, and a uniform local 1/d-Hölder estimate for the joint spectral radius.",
        "assumptions": [
            "The growth assertions concern every nonempty bounded family of real d-by-d matrices, d at least one, with the Euclidean operator norm and actual length-n products.",
            "Positive-radius growth retains the explicit dimension-dependent constant and all positive word lengths; zero radius implies every word of length at least d is zero.",
            "The Hölder assertion concerns nonempty compact families inside a common spectral-norm ball of radius L greater than zero, measured by the Hausdorff distance. No irreducibility or finite-generator restriction is imposed."
        ],
        "claims": [
            "For every positive word length n and joint spectral radius rho>0, the maximal product norm is at most theta_d*(L*n)^(d-1)*rho^(n-d+1), where L>0 bounds all generator norms, theta_1=1 and theta_d=d*(2*exp(1)*d^2/(d-1))^(d-1) for d>=2.",
            "If the joint spectral radius is zero, every matrix word of length at least the ambient dimension is exactly zero.",
            "For two nonempty compact real matrix families in a common norm ball, bounds the difference of their joint spectral radii by d(2d+1)L^(1-1/d) times their spectral Hausdorff distance to power 1/d."
        ],
        "audience": "Researchers studying switched linear systems, matrix semigroups and continuity of the joint spectral radius.",
        "arxiv": ["math.NA", "math.FA"], "msc": ["15A60"], "section": 2,
        "scope_note": "This entry selects the real-family headline statements. Complex-family versions and further norm constructions are auxiliary library results, not additional selected headline declarations."
    },
    "MF-12": {
        "summary": "For every nonnegative real exponent gamma, two distinct real matrices have maximal length-n product norm bounded above and below by positive constants times n^gamma. Rational exponents admit dyadic entries.",
        "assumptions": [
            "The exponent gamma is any real number at least zero; the construction chooses its finite matrix dimension and two distinct generators.",
            "Two-sided Euclidean operator-norm bounds hold at every positive integer word length, and the actual nth-root growth limit is one.",
            "The dyadic refinement assumes gamma is rational; dyadic means an integer divided by a power of two."
        ],
        "claims": [
            "Constructs two distinct real matrices and positive constants whose maximal word norm grows as n^gamma for every positive integer n, for any prescribed real gamma at least zero, with joint spectral radius one.",
            "When gamma is rational and nonnegative, obtains the same all-length growth and radius conclusions using matrices with dyadic rational entries."
        ],
        "audience": "Researchers in matrix-product growth and the stability of linear switching systems.",
        "arxiv": ["math.NA", "math.FA"], "msc": ["15A60"], "section": 3,
        "scope_note": "These are existence and dyadic-realization theorems; sharper constants in an informal construction are not additional compared claims."
    },
    "RA-02": {
        "summary": "The sharp worst-case expected loss after r random pivots is 2^r for Cholesky trace residual and 4^r for LU squared Frobenius residual, relative to the corresponding optimal rank-r error.",
        "assumptions": [
            "The pivot laws and residual updates are the actual randomized algorithms, including zero-pivot and absorbing-zero cases.",
            "Cholesky inputs are complex positive semidefinite matrices; LU inputs may be arbitrary rectangular complex matrices. Ratios require positive optimal rank-r error.",
            "The same suprema hold on the stated subclass of real positive-definite entrywise-positive inputs. The rank parameter includes every positive integer r."
        ],
        "claims": [
            "Identifies the exact four least upper bounds: 2^r for the Cholesky loss and 4^r for the LU loss, both over the full admissible classes and over the real positive-definite entrywise-positive sharpness subclasses."
        ],
        "audience": "Researchers in randomized numerical linear algebra and low-rank matrix approximation.",
        "arxiv": ["math.NA"], "msc": ["15A23", "65F55"], "section": 4,
        "scope_note": "This grouped entry covers RA-02 and RA-03. Unit-diagonal restrictions and finite rational certificates are separate auxiliary library material, not extra conclusions of the selected supremum theorem."
    },
    "RA-08": {
        "summary": "The selected results give spectral error-transfer failure for a fixed six-dimensional matrix pair and exact Nyström nuclear-norm examples with arbitrarily large amplification of arbitrarily small positive input excess.",
        "assumptions": [
            "The spectral statement takes any real C and ordered spectral data dA for the fixed six-dimensional witnessMatrix, and compares the fixed second matrix witnessApproximation with the three-term spectral truncation.",
            "The nuclear statement requires a real positive-definite input, an injective sketch and the actual inverse-based Nyström formula. It quantifies every nonnegative real C and every positive bound epsilon_0 on the input excess.",
            "Both selected statements use spectral functional calculus, the fixed kink f(x)=min(x,1), and ordered spectral truncations. Admissibility of the scalar function is proved separately in the unselected theorem paper_scalar_function."
        ],
        "claims": [
            "For the fixed six-dimensional pair witnessMatrix and witnessApproximation, every real C and ordered spectral data dA of witnessMatrix satisfy the input spectral error bound at epsilon=0, while the transformed spectral error exceeds the corresponding three-term function-truncation error. This selected declaration is a fixed-pair error-transfer failure.",
            "For every nonnegative real C and every epsilon_0 greater than zero, constructs an exact Nyström example with positive input excess below epsilon_0 and transformed nuclear excess exceeding C times that excess."
        ],
        "audience": "Researchers using low-rank approximations of matrix functions and randomized sketching.",
        "arxiv": [
            "math.NA",
            "math.FA"
        ],
        "msc": [
            "15A45",
            "15A60"
        ],
        "section": 5,
        "scope_note": "The selected spectral conclusion consists of the fixed-pair error inequalities. The separate, unselected [paper_spectral_witness](PaperSolution.lean#L14) supplies existence of ordered spectral data, positive-definite input, positive-semidefinite approximation and order, an injective fixed sketch paperOmega, an invertible Gram determinant, and nystrom witnessMatrix paperOmega = witnessApproximation. The Nyström realization is supporting context from that companion theorem, rather than a conclusion of the compared paper_spectral_failure. Scalar admissibility is likewise supplied by the unselected [paper_scalar_function](PaperSolution.lean#L52). The selected nuclear theorem directly includes its Nyström sketch and construction. These selected statements do not assert probabilities under any sketch distribution. A strictly increasing function variant is unselected auxiliary material."
    },
    "RA-09": {
        "summary": "Sharp Frobenius-norm relative-error transfer for nonnegative nondecreasing continuous functions with f(x)/x nonincreasing: factor one under positive-semidefinite order and factor two without order.",
        "assumptions": [
            "A and B are real positive-semidefinite matrices, rank B is at most k, and the first discarded eigenvalue of A is positive.",
            "The function is continuous, nonnegative and nondecreasing on the nonnegative axis, with f(x)/x nonincreasing for positive x; concavity and operator monotonicity are not premises.",
            "The output applies f on the same selected k-dimensional eigenspace of B and is zero on its orthogonal complement, including when f(0) is positive."
        ],
        "claims": [
            "If B is below A in semidefinite order, an input norm-relative factor 1+epsilon transfers with the same factor for the selected transformed approximation.",
            "The ordered factor one is optimal, using actual matrix approximation errors and positive comparison tails.",
            "Without semidefinite order, an input norm-relative factor 1+epsilon transfers with factor at most 1+2epsilon.",
            "The unordered factor two is optimal, even for operator-monotone power functions, with ratios tending to two."
        ],
        "audience": "Researchers in matrix-function approximation, eigenvalue inequalities and low-rank error bounds.",
        "arxiv": ["math.NA", "math.FA"], "msc": ["15A45", "15A60"], "section": 6,
        "scope_note": "These are the selected norm-relative consequences and sharpness statements. Squared-excess forms, degenerate cutoff cases and operator-monotone integral proofs remain auxiliary results."
    },
    "IE-21": {
        "summary": "For independent spherical unit rows and any fixed retained fraction theta in (0,1), the worst retained-set least singular value has the sharp truncated-Gaussian limit whenever n tends to infinity and m/n tends to infinity.",
        "assumptions": [
            "The real m-by-n matrix has independent rows uniform on the unit sphere; every sequence with n tending to infinity and m/n tending to infinity is permitted.",
            "For fixed theta between zero and one, retain floor(theta*m) rows and minimize the variational least singular value over all such subsets.",
            "The limiting h_theta is E[G^2 1_{|G|<=a_theta}] for a standard Gaussian G and its unique symmetric theta-quantile a_theta."
        ],
        "claims": [
            "Proves joint convergence in probability of (n/m) times the squared worst-subset least singular value to h_theta, (n/m) times the squared operator norm to one, and their squared ratio to h_theta."
        ],
        "audience": "Researchers in random matrices, robust linear systems and randomized iterative methods.",
        "arxiv": ["math.NA", "math.PR"], "msc": ["15A18", "60B20", "65F10"], "section": 7,
        "scope_note": "No stronger growth condition on the aspect ratio and no fixed common probability space are assumed. The deterministic optimality result is the separate IE-22 entry."
    },
    "IE-22": {
        "summary": "The truncated-Gaussian constant is the sharp universal bound for adversarial row deletion among all deterministic real matrices with unit rows, with an explicit uniform squared-error rate and a matching high-aspect supremum limit.",
        "assumptions": [
            "The retained fraction theta is fixed strictly between zero and one, and the matrix is any real m-by-n matrix with Euclidean unit rows.",
            "The normalized squared quantity is (n/m) times the least singular value squared after the worst deletion retaining floor(theta*m) rows; its definition allows zero or rank-deficient retained matrices.",
            "The rate estimate is uniform over every positive row count m for sufficiently large n. The matching supremum limit uses n tending to infinity and m/n tending to infinity."
        ],
        "claims": [
            "Along every high-aspect sequence, the supremum over unit-row matrices of sqrt(n/m) times the worst retained-set least singular value tends to sqrt(h_theta), so no smaller eventual uniform constant works.",
            "Bounds the normalized squared deletion quantity by h_theta plus a theta-dependent constant times n^(-1/6), uniformly over every row count and unit-row matrix for sufficiently large n."
        ],
        "audience": "Researchers in deterministic frame design, robust linear systems and random-matrix extremal constants.",
        "arxiv": ["math.NA", "math.PR"], "msc": ["15A18", "60B20", "65F10"], "section": 7,
        "scope_note": "No distributional assumption is made on the universal upper-bound inputs. Random matrices supply sharpness through the separate IE-21 theorem and proof dependencies."
    },
    "TR-04": {
        "summary": "A deterministic exact-arithmetic/SVD algorithm returns a tensor-train approximation within the prescribed ranks with squared error strictly below (d-1) times the optimum whenever the optimum is positive, and exact recovery otherwise.",
        "assumptions": [
            "The input is a dense real tensor of order d at least three, every mode has size at least two, and the first prescribed rank is positive. The formal statement even allows zero remaining ranks.",
            "Feasibility means the actual consecutive unfolding-rank bounds. The optimum is the attained minimum squared Frobenius error over that feasible set.",
            "The model charges exact scalar arithmetic, comparisons and specified cubic-cost singular-subspace primitives; static shape/index/reference metadata is free. This is not a floating-point, bit-complexity or compiler guarantee."
        ],
        "claims": [
            "The concrete lexicographic algorithm returns a feasible tensor, uses at most the first mode size many genuine TT-SVD completions, achieves strict squared error below (d-1)E_* when E_*>0 and exact recovery when E_*=0, and has charged cost at most 1500 times the fifth power of the dense input size."
        ],
        "audience": "Researchers in tensor approximation algorithms and numerical multilinear algebra.",
        "arxiv": ["math.NA"], "msc": ["15A69", "65F55"], "section": 8,
        "scope_note": "The selected statement is the algorithm theorem. The separate every-order limiting sharpness examples are auxiliary proof-library results, not additional selected headline declarations."
    },
    "TR-27": {
        "summary": "For every r at least three and m at least two, a smooth rational nondegenerate complex projective curve has a point of border rank two and rank r whose unrestricted k-factor Segre rank is r^k for every k from one to m.",
        "assumptions": [
            "The parameters r and m are integers with r>=3 and m>=2; the construction lies in projective space of dimension D-1 with D=r^m+r.",
            "Ranks allow arbitrary complex coefficients; different curve points may be chosen independently in each of the k Segre factors, without regrouping.",
            "Border rank uses actual Zariski closure. Smoothness and rationality are certified for the whole curve, including the point at infinity, through explicit analytic chart and birational data."
        ],
        "claims": [
            "Constructs the same smooth rational nondegenerate curve and point with border rank two, rank r and tensor-power ranks r^k for all 1<=k<=m. In particular r=3,m=2 gives rank nine at the square in projective eleven-space, disproving the general-variety square-saving conjecture."
        ],
        "audience": "Algebraic geometers and researchers in tensor rank, secant varieties and algebraic complexity.",
        "arxiv": ["math.AG"], "msc": ["15A69"], "section": 9,
        "scope_note": "This is the arbitrary-parameter finite-delay theorem. The eventual-savings upper bound for each fixed curve is auxiliary material and is not a further selected declaration."
    },
    "IS-03": {
        "summary": "The normalized characteristic-polynomial derivative of an explicit nonnegative seven-by-seven matrix is not the characteristic polynomial of any nonnegative matrix, even after adjoining arbitrarily many zero roots.",
        "assumptions": [
            "The witness is diag(1/2,C_2,C_4), with C_j the directed j-cycle permutation matrix; nonnegativity is entrywise.",
            "The derivative is normalized by dividing the degree-seven characteristic derivative by seven. Arbitrary zero padding means every additional number r>=0 of zero roots.",
            "Realizability concerns the complete characteristic polynomial of an entrywise-nonnegative real matrix of the required order."
        ],
        "claims": [
            "Proves that the literal normalized derivative, multiplied by any power z^r, cannot equal the characteristic polynomial of an entrywise-nonnegative real matrix of order 6+r."
        ],
        "audience": "Researchers in the nonnegative inverse eigenvalue problem and spectral realizability.",
        "arxiv": ["math.RA"], "msc": ["15A18"], "section": 10,
        "scope_note": "The zero-padding quantifier is part of the selected theorem; it is stronger than disproving realizability in order six alone."
    },
    "NM-04": {
        "summary": "The Rowland-Wu polynomial identity holds for the top-left entry of the positive balanced Sinkhorn scaling of every strictly positive real rectangular matrix, including matrices with vanishing minors.",
        "assumptions": [
            "The input is any strictly positive real m-by-n matrix with m,n>=1, and the entry is taken from its genuine positive diagonal scaling with row sums one and column sums m/n.",
            "The polynomial uses the specified Delta and Gamma minors and principal minors of the literal row/column transition matrix H, with empty determinants and products equal to one.",
            "No nonvanishing-minor hypothesis is imposed. Arbitrary prescribed margins are not an additional selected claim."
        ],
        "claims": [
            "The explicit sum over all subsets of equal-cardinality trailing row/column index pairs vanishes at the scaled top-left entry, with the paper's determinant coefficients and exact m^(-1) normalization."
        ],
        "audience": "Researchers in matrix scaling, algebraic identities and Sinkhorn algorithms.",
        "arxiv": ["math.NA", "math.CO"], "msc": ["15A15", "15A23"], "section": 11,
        "scope_note": "The compared theorem is the rectangular identity. Its actual scaling existence/uniqueness and null-vector construction occur in the proof library."
    },
    "PF-02": {
        "summary": "For each real PSD factor size k at least three, there are full-rank nonnegative integer and strictly positive rational square matrices whose spaces of minimal real PSD factorizations modulo invertible congruence are disconnected.",
        "assumptions": [
            "For every integer k>=3 the witness order and ordinary real rank are N=k(k+1)/2, and the genuine minimal real PSD rank is k.",
            "The full real factorization space is quotiented by all invertible congruences with its actual quotient topology.",
            "Both an entrywise-nonnegative integer witness and an entrywise-strictly-positive rational witness are supplied, with their casts to real matrices explicit."
        ],
        "claims": [
            "Constructs, for every k>=3, the two arithmetic classes of N-by-N witnesses with ordinary rank N, minimal real PSD rank k and disconnected congruence orbit spaces."
        ],
        "audience": "Researchers in semidefinite factorizations, extension complexity and the topology of factorization spaces.",
        "arxiv": ["math.OC", "math.CO"], "msc": ["15A23", "15B48"], "section": 12,
        "scope_note": "Disconnectedness concerns the whole minimal factorization quotient, not merely a selected family of displayed factorizations."
    },
    "MD-06": {
        "summary": "Uniform labelled simple cubic graphs typically have a nonsynchronised local minimum of the attractive Kuramoto energy, with every edge cosine above 1/32 and Hessian at least 1/320 on the mean-zero subspace.",
        "assumptions": [
            "Graphs are uniform over labelled simple 3-regular graphs on every even order n>=4; the limit is along those even orders.",
            "The energy is the sum over unordered edges of 1-cos(theta_u-theta_v), on the phase torus with common rotations identified for stability.",
            "The quantitative Hessian inequality is tested on every mean-zero real vector and uses the ordinary Euclidean squared norm."
        ],
        "claims": [
            "The probability that every torus local minimum is synchronised tends to zero; with probability tending to one there is a nonsynchronised critical local minimum with all edge cosines >1/32 and Hessian quadratic form >=(1/320) times the squared norm on the mean-zero subspace."
        ],
        "audience": "Researchers in synchronization dynamics, random regular graphs and probabilistic network models.",
        "arxiv": ["math.PR", "math.DS"], "msc": ["05C80"], "section": 13,
        "scope_note": "The graph distribution and quantitative stability are actual conclusions of the selected theorem; expansion, cycle probabilities and correction estimates are proved supporting results, not assumed probabilistic contracts."
    },
    "IV-04": {
        "summary": "Exact determinant ranges and complete solution hulls of rational regular tridiagonal interval systems are NP-hard; the determinant-threshold language is NP-complete, even with superdiagonal entries fixed at one.",
        "assumptions": [
            "Inputs have binary-encoded rational ordered interval endpoints and actual real interval realizations; malformed-input and complete-decoding conventions are explicit.",
            "The hard restricted families are tridiagonal, every realization is nonsingular, and every superdiagonal entry is one.",
            "The hull task returns rational lower and upper endpoints for every coordinate, with point right-hand side -e_n and a nonempty bounded actual solution set. Exact-output hardness uses actual polynomial-time query and postprocessing programs."
        ],
        "claims": [
            "Proves NP-completeness of the determinant-threshold language, NP-hardness on the regular fixed-superdiagonal restriction, and one-query NP-hardness of the exact minimum/maximum determinant output on that restriction.",
            "Proves one-query NP-hardness of the literal complete coordinatewise solution-hull output on regular fixed-superdiagonal interval systems with right-hand side -e_n; a correct complete rational answer exists for every reduction input and every such answer decides the source NP language."
        ],
        "audience": "Researchers in verified numerical computation, interval linear algebra and computational complexity.",
        "arxiv": ["math.NA", "cs.CC"], "msc": ["68Q25", "15A15"], "section": 14,
        "scope_note": "This grouped entry covers IV-02 and IV-04. Exact-output hardness is not a claim about approximate interval arithmetic or an independently selected FP^NP upper-bound algorithm."
    },
    "MI-19": {
        "summary": "An explicit real positive-semidefinite four-by-four matrix of rank two violates the q-permanent subset inequality at q=7/8 for a singleton subset.",
        "assumptions": [
            "The witness is the exact matrix in the manuscript, with Gram factor having rows (13,0,13,13) and (1,1,-2,1).",
            "The q-permanent sums actual permutation products weighted by q to the inversion count, and the restricted sum uses the singleton containing paper index two.",
            "The matrix is positive semidefinite of rank two but need not be entrywise nonnegative; q is exactly 7/8."
        ],
        "claims": [
            "Proves the exact witness's positive semidefiniteness and rank two and the strict negative difference per_q(A)-R_{q,{2}}(A)=-3235575/16384 at q=7/8."
        ],
        "audience": "Researchers in generalized permanents and matrix inequalities.",
        "arxiv": ["math.CO", "math.RA"], "msc": ["15A15", "15A45"], "section": 15,
        "scope_note": "The selected result is the explicit semidefinite witness. The positive-definite perturbation remark and the eighteen-moving-terms expansion are auxiliary library statements."
    },
    "MI-21": {
        "summary": "Two rational positive-definite input pairs of order two refute the geometric-mean norm inequality in the operator norm at s=t=1/2 and r=2, with both sums equal to identity and the same witness for every p>0.",
        "assumptions": [
            "There are two summands of order two; all four matrices are rational and positive definite, represented in complex matrices for genuine functional calculus.",
            "The exponents are s=t=1/2 and r=2; p is any positive real number, so sr=1 satisfies the conjectured parameter range.",
            "Both input sums equal I_2, making the proposed right side one; the norm used for the strict violation is the actual Euclidean operator norm."
        ],
        "claims": [
            "The displayed rational input pairs have the stated positivity and identity sums, and the actual sum of squared geometric means has operator norm strictly greater than the conjectured right-hand side for every p>0."
        ],
        "audience": "Researchers in matrix geometric means, operator inequalities and unitarily invariant norms.",
        "arxiv": ["math.FA"], "msc": ["15A45", "15A60"], "section": 16,
        "scope_note": "One unitarily invariant norm suffices to refute the universal inequality; the statement does not assert failure for every such norm."
    },
    "MI-22": {
        "summary": "The literal rational three-by-three matrices A=diag(256,1/256,1) and the printed integer B refute weighted singular-value log-majorisation at t=1/8, with certified operator-norm bounds above 10900 and below 10200.",
        "assumptions": [
            "A=diag(256,1/256,1), B has rows (17,-4,0), (-4,16385,-8192), (0,-8192,4096), and t=1/8; both matrices are proved positive definite.",
            "The left product is A^(1/8)(A#_(1/8)B)B^(7/8), with the actual functional-calculus weighted geometric mean; the right product is AB.",
            "Log-majorisation compares actual ordered singular values. The first partial-product inequality already fails because the left operator norm exceeds the right."
        ],
        "claims": [
            "Proves the exact inputs' positive definiteness, left-product operator norm >10900, right-product operator norm <10200, and failure of the stated weighted singular-value log-majorisation at t=1/8.",
            "Uses that actual counterexample to refute the original universally quantified weighted log-majorisation conjecture."
        ],
        "audience": "Researchers in matrix means, singular-value inequalities and certified spectral computation.",
        "arxiv": ["math.FA", "math.NA"], "msc": ["15A45", "15A60"], "section": 17,
        "scope_note": "Rational eighth-root certificates and noncommutative error propagation prove inequalities for the genuine matrix roots; floating-point evidence is not a premise."
    }
}


HELPER_ACCOUNTS = {
    "NLA.TR27.Paper.coordinateProjection_surjective": "For integers D>=2 and r>=3, the explicit linear coordinate projection onto the D-dimensional complex coordinate space is surjective. This supplies the quotient-coordinate equivalence used in the curve statement.",
    "NLA.TR27.Paper.coordinateProjection_kernel": "For integers D>=2 and r>=3, the kernel of that explicit coordinate projection is exactly the chosen one-dimensional centre line. This identifies the actual quotient with the stated coordinate space.",
    "NLA.TR27.Paper.imageHomogeneousMap_eq_zero_iff": "For integers D>=2 and r>=3 and every homogeneous parameter u in C^2, the explicit homogeneous image map is zero if and only if u is zero. Thus the projective curve map has no nonzero parameter at which all coordinates vanish.",
    "NLA.TR27.Paper.tensor_reps_nonzero": "For any complex vector space W, every natural k and every k-tuple of projective points of W, the tensor product of their chosen nonzero representatives is nonzero. This makes the projective tensor point and its powers well defined, including k=0.",
    "Reference.LexicographicFeasibilityBridge.product_eq_rowCount": "For every pair of natural mode sizes m,n, the concrete flattened row count equals m*n. This certifies the finite-index cast in the actual two-mode row layout.",
    "Reference.LexTensorCompletion.lexCard_eq_card": "For every finite list of natural mode sizes, the recursive mixed-radix cardinality equals the number of actual tensor mode indices. This certifies the concrete layout equivalence used by TT-SVD completion.",
    "Reference.MD06FiniteProbability.actual_cubic_sample_nonempty": "For every natural k, there exists a labelled simple 3-regular graph on 2(k+2) vertices. Hence every finite cubic-graph sample space used by the theorem is nonempty and carries the stated uniform probability distribution."
}


def load_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def digest(data):
    return hashlib.sha256(data).hexdigest()


def helper_accounts(audit):
    roles = {}
    raw = audit.get("supporting_theorem_roles", {})
    if isinstance(raw, dict):
        for name, role in raw.items():
            if isinstance(role, str) and role.strip():
                roles[name] = role.strip()
            elif isinstance(role, dict):
                value = role.get("description") or role.get("role") or role.get("statement")
                if isinstance(value, str) and value.strip():
                    roles[name] = value.strip()
    list_roles = raw if isinstance(raw, list) else []
    for item in [*list_roles, *audit.get("supporting_theorems", [])]:
        if isinstance(item, dict):
            name = item.get("name") or item.get("theorem_name")
            role = item.get("description") or item.get("role") or item.get("statement")
            if name and isinstance(role, str) and role.strip():
                roles[name] = role.strip()
    roles.update(HELPER_ACCOUNTS)
    return roles


def entry_material(entry, primary, root_metadata, audit):
    identifier = entry["id"]
    spec = SPECS[identifier]
    project = ROOT / entry["project_path"]
    primary_names = [name for target in primary["targets"] for name in target["theorem_names"]]
    if len(primary_names) != len(spec["claims"]):
        raise ValueError(f"Curated claim count no longer matches primary targets for {identifier}")
    primary_descriptions = dict(zip(primary_names, spec["claims"]))
    target_for_name = {name: target for target in primary["targets"] for name in target["theorem_names"]}
    config_path = ROOT / entry["comparator_config_path"]
    config = load_json(config_path) if config_path.exists() else None
    selected = list(config["theorem_names"]) if config else primary_names
    if len(set(selected)) != len(selected):
        raise ValueError(f"Repeated compared declaration in {identifier}")
    if not set(primary_names).issubset(selected):
        raise ValueError(f"Comparator lost a curated primary declaration in {identifier}")
    roles = helper_accounts(audit)
    unknown = [name for name in selected if name not in primary_descriptions and name not in roles]
    if unknown:
        raise ValueError(f"No plain-language account for compared helper(s) in {identifier}: {unknown}")
    helpers = [name for name in selected if name not in primary_descriptions]
    descriptions = {**primary_descriptions, **roles}
    metadata = copy.deepcopy(root_metadata)
    metadata["project"]["name"] = entry["title"]
    metadata["project"]["description"] = spec["summary"] + " " + spec["scope_note"]
    metadata["project"]["authors"] = list(AUTHORS)
    metadata["project"]["responsible_maintainers"] = list(AUTHORS)
    metadata["project"]["license"] = "Apache-2.0"
    metadata["classification"] = {"arxiv": spec["arxiv"], "msc2020": spec["msc"]}
    labels = list(dict.fromkeys(target.get("manuscript_label") or f"Section {spec['section']}, unnumbered {identifier} theorem" for target in primary["targets"]))
    metadata["sources"][0]["location"] = f"Author-provided unpublished manuscript, section {spec['section']}; " + ", ".join(labels)
    metadata["sources"][0]["note"] = (
        f"Exact source SHA-256: {MANUSCRIPT}. The manuscript was provided by the authors; "
        "its text is not bundled and no public paper URL or DOI is asserted. This entry "
        "formalizes only the selected declarations described here. Original mathematical "
        "attributions and the distinct source problem collection remain in the retained provenance."
    )
    # Source problem URLs are bibliographic, not invented identifiers for the new repository.
    metadata["sources"][1]["note"] = (
        "Original problem collection and historical literature context for "
        + ", ".join(entry["problem_ids"])
        + ". Prior Lean code is identified separately under related_formalizations; "
        "no new novelty or exhaustive literature-search claim is made."
    )
    metadata["status"] = {
        "scope": spec["summary"] + " " + spec["scope_note"] + " Only declarations in this project's comparator.json are selected for this entry. " + VERIFICATION_STATUS,
        "axioms": ["propext", "Classical.choice", "Quot.sound"]
    }
    metadata["fidelity"]["divergences"] = " ".join(spec["assumptions"]) + " " + spec["scope_note"] + " " + VERIFICATION_STATUS
    metadata["review"]["status"] = "agent-reviewed"
    metadata["review"]["notes"] = (
        "Historical source correspondence and proof-scope reviews were performed by AI agents. "
        "Their original Lean 4.33.1 receipts are historical source-bound evidence. " + VERIFICATION_STATUS
        + " No independent human refereeing or upstream author endorsement is claimed."
    )
    if helpers:
        metadata["project"]["description"] += " The comparison also includes explicitly identified supporting statements for the dependent semantic constructions."
    metadata["entry_scope"] = {
        "problem_ids": entry["problem_ids"], "manuscript_section": spec["section"],
        "manuscript_labels": labels, "research_audience": spec["audience"],
        "assumptions": spec["assumptions"], "primary_theorem_names": primary_names,
        "supporting_theorem_names": helpers, "compared_theorem_names": selected,
        "selection_basis": "comparator.json" if config else "primary-entry-targets.json; comparator assembly outstanding",
        "auxiliary_proof_scope": (
            "The full independently compiled module graph retains the auxiliary proofs for the 53 named-statement "
            "and 57 prose-group source inventory. Every retained local module passed ordinary compilation; "
            "alternative proof environments are kept separate. Their presence is distinct from which "
            "declarations are selected and compared in this entry."
        )
    }
    metadata["entry_scope"]["compilation_model"] = (
        "TR-04 Solution imports the primary algorithm proof root only; alternative auxiliary tensor-arithmetic environments are compiled independently through the all-local builder mode."
        if identifier == "TR-04" else
        "IV-04 Solution imports the two primary determinant/hull proof roots only; alternative auxiliary environments are compiled independently through the all-local builder mode."
        if identifier == "IV-04" else
        "Solution imports all mapped proof roots; the all-local builder mode also compiles every retained local module independently."
    )
    metadata["alignment"] = {"namespace": "Multiple original namespaces retained", "statements": []}
    for name in selected:
        target = target_for_name.get(name)
        source = (target.get("manuscript_label") if target else None) or (f"Section {spec['section']}, unnumbered {identifier} theorem" if target else "Supporting statement for the selected semantic construction")
        metadata["alignment"]["statements"].append({
            "source": source, "lean": name, "module": config.get("challenge_module", "Challenge") if config else "Challenge",
            "status": "ordinary source build and compiled axiom-dependency query passed; official comparison pending",
            "note": descriptions[name] + (" Explicit supporting declaration rather than a separate manuscript headline." if name in helpers else "")
        })
    metadata["paper_verification"] = {
        "manuscript_sha256": MANUSCRIPT, "entry_problem_ids": entry["problem_ids"],
        "selected_primary_declarations": len(primary_names), "selected_supporting_declarations": len(helpers),
        "current_port_status": "ordinary full-source Lean 4.35.0 compilation and compiled selected-axiom queries passed; official verification pending",
        "ordinary_build_receipt": "../../verification/build-status.json",
        "selected_axiom_report": f"../../verification/selected-axioms/{identifier}/selected-axioms.json",
        "submission_status": "Internal component of the single root Palomar submission"
    }
    metadata["licensing"]["notices"] = "../../NOTICE.md; ../../LICENSES/; ../../docs/LICENSING-AND-PROVENANCE.md"
    metadata_text = "# Generated by scripts/build_entry_metadata.py; edit its curated accounts, then regenerate.\n" + yaml.safe_dump(metadata, allow_unicode=True, sort_keys=False, width=100)
    body = [f"# {entry['title']}", "", spec["summary"], "", "Research audience: " + spec["audience"], "", "Assumptions and conventions:", ""]
    body.extend("- " + text for text in spec["assumptions"])
    body.extend(["", "Selected headline statements:", ""])
    for name in primary_names:
        target = target_for_name[name]
        label = target.get("manuscript_label") or f"section {spec['section']}, unnumbered theorem"
        body.extend([f"- **{label}** — {descriptions[name]} Lean declaration: \x60{name}\x60."])
    if helpers:
        body.extend(["", "Explicitly compared supporting statements:", ""])
        for name in helpers:
            body.append(f"- \x60{name}\x60 — {descriptions[name]}")
    body.extend(["", spec["scope_note"], "", "Only the exact declarations listed in [comparator.json](comparator.json) are selected for this entry. The full independently compiled module graph retains the other recorded paper proofs; library coverage and a selected comparison are separate scopes. Every retained local module passed ordinary compilation.", "", VERIFICATION_STATUS, "", "The source is the author-provided unpublished manuscript, section " + str(spec["section"]) + ", SHA-256 \x60" + MANUSCRIPT + "\x60. The manuscript and book are not reproduced here. [formalization.yaml](formalization.yaml) records mathematical sources, prior formalizations, scope and AI involvement.", "", "Human authors and responsible maintainers: Matthew J. Colbrook and George Stepaniants. Substantial OpenAI Codex assistance and agent review are disclosed; no independent human review is claimed. The owner authorized the new Apache-2.0 release with third-party notices preserved. See the repository [LICENSE](../../LICENSE), [NOTICE](../../NOTICE.md) and [component texts](../../LICENSES/).", "", "This proof component belongs to the single root Palomar submission. Submit the collection once with the repository-root comparator.json and formalization.yaml; leave the project directory blank. This account does not require a separate registry entry.", ""])
    compilation_note = (
        "TR-04 Solution imports its primary algorithm proof root only. Alternative auxiliary tensor-arithmetic environments are retained and compiled independently with the all-local builder mode; they are not combined in one import closure. Mathematical statements are neither weakened nor renamed."
        if identifier == "TR-04" else
        "IV-04 Solution imports its two primary determinant/hull proof roots only. Alternative auxiliary environments are retained and compiled independently with the all-local builder mode; they are not combined in one import closure. Mathematical statements are neither weakened nor renamed."
        if identifier == "IV-04" else
        "This Solution imports all mapped proof roots. The all-local builder mode compiles every retained local module independently, keeping alternative proof environments separate where necessary."
    )
    body[body.index(VERIFICATION_STATUS):body.index(VERIFICATION_STATUS)] = [compilation_note, ""]
    readme = "\n".join(body)
    for old, new in (
        ("This entry", "This component"),
        ("this entry", "this component"),
        ("selected for this entry", "selected for this component"),
        ("separate IE-22 entry", "separate IE-22 component"),
        ("grouped entry", "grouped component"),
    ):
        metadata_text = metadata_text.replace(old, new)
        readme = readme.replace(old, new)
    return metadata_text, readme, {"id": identifier, "primary_theorem_names": primary_names, "supporting_theorem_names": helpers, "selected_theorem_names": selected, "source_labels": labels}



ACCOUNT_BEGIN = "<!-- BEGIN COMBINED MATHEMATICAL ACCOUNT -->"
ACCOUNT_END = "<!-- END COMBINED MATHEMATICAL ACCOUNT -->"


def lifted_component_links(text, project_path):
    """Preserve relative link destinations when moving component prose to root."""
    def replace(match):
        target = match[2]
        if target.startswith("/") or re.match(r"^[A-Za-z][A-Za-z0-9+.-]*:", target):
            return match[0]
        if target.startswith("#"):
            target = project_path + "/README.md" + target
        else:
            target = posixpath.normpath(project_path + "/" + target)
        return match[1] + target + match[3]
    return re.sub(r"(!?\[[^\]\n]*\]\()([^\s)]+)(\))", replace, text)



def technical_supporting_theorems():
    filename = ROOT / "audit/combined-supporting-theorems.json"
    if not filename.exists():
        return []
    data = load_json(filename)
    if data.get("schema_version") != 1 or not isinstance(data.get("theorems"), list):
        raise ValueError("Malformed technical supporting-theorem manifest")
    rows = data["theorems"]
    for row in rows:
        if any(not isinstance(row.get(key), str) or not row[key].strip() for key in ("name", "type_lean", "source_path", "source_module", "purpose")):
            raise ValueError("Each technical supporting theorem needs its type, source and purpose")
    return rows

def combined_account_block(accounts):
    parts = [
        ACCOUNT_BEGIN,
        "## Mathematical statements and assumptions",
        "",
        "The following accounts describe every selected headline and supporting declaration",
        "in the single root Comparator configuration. Each subsection records the relevant",
        "hypotheses, conventions, audience, and scope limitations.",
    ]
    selected = []
    for entry, readme, details in accounts:
        body = readme.split("\n", 1)[1].lstrip()
        marker = "\nOnly the exact declarations listed"
        if marker not in body:
            raise ValueError("Cannot locate mathematical account boundary for " + entry["id"])
        mathematical = body.split(marker, 1)[0].rstrip()
        mathematical = lifted_component_links(mathematical, entry["project_path"])
        parts.extend(["", "### " + ", ".join(entry["problem_ids"]) + ": " + entry["title"], "", mathematical])
        selected.extend(details["selected_theorem_names"])
    if len(selected) != 34:
        raise ValueError("Combined root account must retain all 34 base declarations")
    technical = technical_supporting_theorems()
    if technical:
        parts.extend(["", "### Technical supporting theorems", "",
            "These supporting proof declarations have explicit source names in the Challenge and support the fixed mathematical definitions.",
            "Their types are compared explicitly and their genuine Solution proofs are included in",
            "the axiom check. They do not add manuscript headline results."])
        fence = chr(96) * 3
        for item in technical:
            source = item["source_path"]
            target = source
            if type(item.get("source_line")) is int and item["source_line"] > 0:
                target += "#L" + str(item["source_line"])
            origin = "Source: [" + source + "](" + target + "), module " + chr(96) + item["source_module"] + chr(96) + "."
            if isinstance(item.get("owner_declaration"), str) and item["owner_declaration"]:
                origin += " Generated while elaborating " + chr(96) + item["owner_declaration"] + chr(96) + "."
            parts.extend(["", "#### " + item["name"], "", item["purpose"], "", origin,
                "", "Normalized compiled type (Lean expression debug form):", "", fence + "lean", item["type_lean"], fence])
            selected.append(item["name"])
    parts.extend(["", ACCOUNT_END])
    block = "\n".join(parts)
    missing = [name for name in selected if name not in block]
    if missing:
        raise ValueError("Combined root account lacks selected declarations: " + repr(missing))
    return block


def update_root_account(block, check):
    filename = ROOT / "README.md"
    text = filename.read_text(encoding="utf-8")
    if text.count(ACCOUNT_BEGIN) != text.count(ACCOUNT_END) or text.count(ACCOUNT_BEGIN) > 1:
        raise ValueError("Malformed combined mathematical account markers")
    if ACCOUNT_BEGIN in text:
        start = text.index(ACCOUNT_BEGIN)
        end = text.index(ACCOUNT_END, start) + len(ACCOUNT_END)
        current = text[start:end]
        if check:
            if current != block:
                raise ValueError("Generated mathematical account is stale: README.md")
        else:
            filename.write_text(text[:start] + block + text[end:], encoding="utf-8", newline="\n")
    elif check:
        raise ValueError("Missing generated mathematical account in README.md")
    else:
        separator = "" if text.endswith("\n\n") else ("\n" if text.endswith("\n") else "\n\n")
        filename.write_text(text + separator + block + "\n", encoding="utf-8", newline="\n")
    return {"path": "README.md", "base_compared_declarations": 34, "technical_supporting_theorems": len(technical_supporting_theorems()), "compared_declarations": 34 + len(technical_supporting_theorems()),
            "sha256": digest(block.encode("utf-8")), "bytes": len(block.encode("utf-8"))}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Check generated files without changing them")
    args = parser.parse_args()
    index = load_json(ROOT / "submission-index.json")
    components = index.get("components", index["entries"])
    primary = {entry["id"]: entry for entry in load_json(ROOT / "primary-entry-targets.json")["entries"]}
    interfaces_path = ROOT / "audit" / "entry-interfaces.json"
    interfaces = {entry["id"]: entry for entry in load_json(interfaces_path).get("entries", [])} if interfaces_path.exists() else {}
    root_metadata = yaml.safe_load((ROOT / "formalization.yaml").read_text(encoding="utf-8"))
    if root_metadata["project"]["authors"] != AUTHORS or root_metadata["project"]["responsible_maintainers"] != AUTHORS:
        raise ValueError("Root human authors/maintainers changed; review before generating")
    if root_metadata["project"]["license"] != "Apache-2.0":
        raise ValueError("Root licence changed; review before generating")
    report = {"schema_version": 1, "generator": "scripts/build_entry_metadata.py", "manuscript_sha256": MANUSCRIPT, "entries": [], "lean_or_kernel_execution": False}
    accounts = []
    for entry in components:
        if entry["id"] not in SPECS:
            raise ValueError("No curated account for " + entry["id"])
        metadata, readme, details = entry_material(entry, primary[entry["id"]], root_metadata, interfaces.get(entry["id"], {}))
        for rel, text in [(entry["formalization_metadata_path"], metadata), (entry["project_path"] + "/README.md", readme)]:
            filename = ROOT / rel
            if args.check:
                if not filename.is_file() or filename.read_text(encoding="utf-8") != text:
                    raise ValueError("Generated metadata/account is stale: " + rel)
            else:
                filename.parent.mkdir(parents=True, exist_ok=True)
                filename.write_text(text, encoding="utf-8", newline="\n")
        report["entries"].append(details)
        accounts.append((entry, readme, details))
    report["technical_supporting_theorems"] = technical_supporting_theorems()
    report["root_mathematical_account"] = update_root_account(combined_account_block(accounts), args.check)
    # Official validator only parses metadata and taxonomies; no build/replay APIs.
    sys.path.insert(0, str(ROOT / "tools" / "palomar_contract"))
    from scripts.submission_contract import load_formalization_metadata
    report["metadata_validation"] = []
    for filename in [ROOT / "formalization.yaml", *[ROOT / entry["formalization_metadata_path"] for entry in components]]:
        try:
            validated = load_formalization_metadata(filename)
        except Exception as error:
            raise ValueError(f"Official metadata validation failed for {filename.relative_to(ROOT).as_posix()}: {error}") from error
        report["metadata_validation"].append({"path": filename.relative_to(ROOT).as_posix(), "status": "pass", "sha256": digest(filename.read_bytes()), "bytes": filename.stat().st_size})
    report["status"] = "pass; generated accounts match exact selected names and official metadata validation passed"
    if not args.check:
        (ROOT / "audit" / "entry-metadata-generation.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "submission_count": 1, "component_accounts": len(report["entries"]), "metadata_files_validated": len(report["metadata_validation"]), "base_compared_statements_documented": sum(len(entry["selected_theorem_names"]) for entry in report["entries"]), "technical_supporting_theorems": len(report["technical_supporting_theorems"]), "compared_statements_documented": sum(len(entry["selected_theorem_names"]) for entry in report["entries"]) + len(report["technical_supporting_theorems"]), "lean_or_kernel_execution": False}, indent=2))


if __name__ == "__main__":
    main()
