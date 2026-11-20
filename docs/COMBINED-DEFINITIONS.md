# Combined statement definitions and declarations

This index links every retained declaration to its preserved component source. The source definitions and selected theorem types remain in the root Challenge. Documentation blocks below are copied verbatim from the original component interfaces; no new mathematical interpretation is supplied for undocumented declarations. The component README files provide the informal accounts, hypotheses and limitations.

Indexed original declarations: 458. Original documentation blocks: 155. Explicit supporting theorem anchors: 9.

## MF-05

### NLA.MF05.Paper.RealSquare

[abbrev in preserved source](../projects/MF-05/Challenge.lean#L550)

### NLA.MF05.Paper.realSpectralNorm

[def in preserved source](../projects/MF-05/Challenge.lean#L556)

### NLA.MF05.Paper.realMatrixProduct

[def in preserved source](../projects/MF-05/Challenge.lean#L559)

### NLA.MF05.Paper.realWordNorms

[def in preserved source](../projects/MF-05/Challenge.lean#L560)

### NLA.MF05.Paper.realFamilyGrowth

[def in preserved source](../projects/MF-05/Challenge.lean#L563)

### NLA.MF05.Paper.realRootGrowth

[def in preserved source](../projects/MF-05/Challenge.lean#L564)

### NLA.MF05.Paper.realRadius

[def in preserved source](../projects/MF-05/Challenge.lean#L566)

### NLA.MF05.Paper.realPointDistance

[def in preserved source](../projects/MF-05/Challenge.lean#L569)

### NLA.MF05.Paper.realDirectedDistance

[def in preserved source](../projects/MF-05/Challenge.lean#L571)

### NLA.MF05.Paper.realHausdorff

[def in preserved source](../projects/MF-05/Challenge.lean#L573)

### NLA.MF05.Paper.theta

[def in preserved source](../projects/MF-05/Challenge.lean#L590)

### NLA.MF05.Paper.paper_real_bounded_positive_radius_growth

[theorem in preserved source](../projects/MF-05/Challenge.lean#L609)

### NLA.MF05.Paper.paper_real_bounded_zero_radius_nilpotent

[theorem in preserved source](../projects/MF-05/Challenge.lean#L617)

### NLA.MF05.Paper.paper_real_uniform_holder

[theorem in preserved source](../projects/MF-05/Challenge.lean#L639)

## MF-12

### NLA.MF12.Square

[abbrev in preserved source](../projects/MF-12/Challenge.lean#L42)

### NLA.MF12.spectralNorm

[def in preserved source](../projects/MF-12/Challenge.lean#L46)

```lean
/-- The genuine induced Euclidean operator norm, not an entrywise matrix norm. -/
```

### NLA.MF12.matrixProduct

[def in preserved source](../projects/MF-12/Challenge.lean#L50)

```lean
/-- Chronological convention: later factors act on the left. -/
```

### NLA.MF12.wordNorms

[def in preserved source](../projects/MF-12/Challenge.lean#L53)

```lean
/-- All genuine length-n family products. Repeated factors are unrestricted. -/
```

### NLA.MF12.familyGrowth

[def in preserved source](../projects/MF-12/Challenge.lean#L58)

```lean
/-- The finite maximum is a separate exported attainment obligation. -/
```

### NLA.MF12.pairFamily

[def in preserved source](../projects/MF-12/Challenge.lean#L60)

### NLA.MF12.Paper.IsDyadic

[def in preserved source](../projects/MF-12/Challenge.lean#L174)

```lean
/-- An actual integer divided by a nonnegative power of two. -/
```

### NLA.MF12.Paper.paperDimension

[def in preserved source](../projects/MF-12/Challenge.lean#L193)

```lean
/-- The dimension claimed in the manuscript, including exponent zero. -/
```

### NLA.MF12.Paper.Realizes

[def in preserved source](../projects/MF-12/Challenge.lean#L198)

```lean
/-- Two distinct actual matrices, bounds at every positive length, and the
    actual maximal-product nth-root limit. -/
```

### NLA.MF12.Paper.paper_main_realization

[theorem in preserved source](../projects/MF-12/Challenge.lean#L219)

### NLA.MF12.Paper.paper_rational_realization

[theorem in preserved source](../projects/MF-12/Challenge.lean#L225)

## RA-02

### NLA.RA02.Square

[abbrev in preserved source](../projects/RA-02/Challenge.lean#L42)

### NLA.RA02.History

[abbrev in preserved source](../projects/RA-02/Challenge.lean#L43)

### NLA.RA02.realTrace

[def in preserved source](../projects/RA-02/Challenge.lean#L45)

### NLA.RA02.choleskyStep

[def in preserved source](../projects/RA-02/Challenge.lean#L55)

```lean
/-- Zero-diagonal choices are harmless totalization. Their probability is zero
for a nonzero PSD residual. The nonzero case is the original complex update. -/
```

### NLA.RA02.pivotMass

[def in preserved source](../projects/RA-02/Challenge.lean#L60)

```lean
/-- On a zero PSD residual use uniform dummy labels; all residuals stay zero.
The n=0 value is only totalization: normalization is asserted for n>=1. -/
```

### NLA.RA02.pathResidual

[def in preserved source](../projects/RA-02/Challenge.lean#L64)

```lean
/-- Chronological residual, including all zero-probability paths. -/
```

### NLA.RA02.pathWeight

[def in preserved source](../projects/RA-02/Challenge.lean#L69)

```lean
/-- Product of actual conditional masses; no independence assumption. -/
```

### NLA.RA02.pathContribution

[def in preserved source](../projects/RA-02/Challenge.lean#L73)

### NLA.RA02.expectedTrace

[def in preserved source](../projects/RA-02/Challenge.lean#L77)

```lean
/-- Full finite expectation. Every ordered label sequence is included. -/
```

### NLA.RA02.orderedEigenvalues

[def in preserved source](../projects/RA-02/Challenge.lean#L82)

```lean
/-- Mathlib's genuinely decreasing eigenvalues. The finite-index transport
uses only card(Fin n)=n; the separately reindexed eigenvalues is not used. -/
```

### NLA.RA02.rankTail

[def in preserved source](../projects/RA-02/Challenge.lean#L86)

```lean
/-- Zero-based i>=r is the original one-based j>r tail. -/
```

### NLA.RA03.frobeniusSq

[def in preserved source](../projects/RA-02/Challenge.lean#L199)

```lean
/-- The squared Frobenius norm, written as the exact sum of squared complex moduli. -/
```

### NLA.RA03.Pivot

[abbrev in preserved source](../projects/RA-02/Challenge.lean#L204)

```lean
/-- `none` is the absorbing label used only after the residual is zero.
Each `some (i,j)` selects a row and a column together. -/
```

### NLA.RA03.pivotMass

[def in preserved source](../projects/RA-02/Challenge.lean#L208)

```lean
/-- The exact conditional pivot probabilities. The zero residual assigns
probability one to `none`; otherwise only entry labels have nonzero mass. -/
```

### NLA.RA03.pivotResidual

[def in preserved source](../projects/RA-02/Challenge.lean#L214)

```lean
/-- The canonical rank-one cross update. A zero entry is given an identity
update solely to totalize the function; its selection probability is zero. -/
```

### NLA.RA03.nextResidual

[def in preserved source](../projects/RA-02/Challenge.lean#L221)

```lean
/-- The next residual for a transition label. The `none` transition has
positive mass exactly at the zero matrix, where it keeps the residual zero. -/
```

### NLA.RA03.historyResidual

[def in preserved source](../projects/RA-02/Challenge.lean#L227)

```lean
/-- The terminal residual along an ordered history of `k` transitions. -/
```

### NLA.RA03.historyMass

[def in preserved source](../projects/RA-02/Challenge.lean#L235)

```lean
/-- The joint probability of a history is the product of the conditional
probabilities along its actual residuals. No independence of row and column
choices, or of successive pivot choices, is assumed. -/
```

### NLA.RA03.expectedError

[def in preserved source](../projects/RA-02/Challenge.lean#L243)

```lean
/-- The actual finite expectation after exactly `k` transitions. Absorption
implements the canonical instruction to keep all later residuals zero. -/
```

### NLA.RA02.Paper.rectangularBestRankErrorSquared

[def in preserved source](../projects/RA-02/Challenge.lean#L310)

```lean
/-- Infimum of actual squared Frobenius errors over complex rectangular
matrices of rank at most r. No spectral approximation theorem is assumed. -/
```

### NLA.RA02.Paper.luRatios

[def in preserved source](../projects/RA-02/Challenge.lean#L329)

```lean
/-- Actual LU ratios over all complex rectangular matrix inputs with positive
best rank-r squared Frobenius error. No dimension or nonsingularity condition. -/
```

### NLA.RA02.Paper.realPositiveLURatios

[def in preserved source](../projects/RA-02/Challenge.lean#L335)

```lean
/-- The same ratios restricted to real positive-definite, entrywise-positive inputs. -/
```

### NLA.RA02.Paper.choleskyRatios

[def in preserved source](../projects/RA-02/Challenge.lean#L356)

```lean
/-- Ratios for arbitrary complex PSD inputs with a positive rank-r tail. -/
```

### NLA.RA02.Paper.realPositiveCholeskyRatios

[def in preserved source](../projects/RA-02/Challenge.lean#L362)

```lean
/-- Restriction to real, positive-definite, entrywise-positive inputs. -/
```

### NLA.RA02.Paper.paper_sup_worst_case_constants

[theorem in preserved source](../projects/RA-02/Challenge.lean#L548)

## RA-08

### NLA.RA08.RealMatrix

[abbrev in preserved source](../projects/RA-08/Challenge.lean#L40)

### NLA.RA08.spectralNorm

[def in preserved source](../projects/RA-08/Challenge.lean#L44)

```lean
/-- The actual operator norm for the matrix acting on real Euclidean space.
This is not the default norm on a matrix or on a function space. -/
```

### NLA.RA08.OrderedSpectralData

[structure in preserved source](../projects/RA-08/Challenge.lean#L59)

```lean
/-- An arbitrary complete ordered orthonormal eigendecomposition of the
actual matrix. Over the reals a unitary matrix is an orthogonal matrix.
Both the nonnegative eigenvalues and every permitted choice of eigenvectors
are quantified in the conjecture; no preferred choice is built in.
Reconstruction, not a claimed numerical spectrum, is part of the data. -/
```

### NLA.RA08.spectralCombination

[def in preserved source](../projects/RA-08/Challenge.lean#L69)

```lean
/-- Apply arbitrary scalar values in the selected eigenbasis. -/
```

### NLA.RA08.truncation

[def in preserved source](../projects/RA-08/Challenge.lean#L75)

```lean
/-- Canonical rank-`k` eigenvalue truncation, zero-based indices `i < k`. -/
```

### NLA.RA08.functionalCalculus

[def in preserved source](../projects/RA-08/Challenge.lean#L80)

```lean
/-- Genuine real continuous functional calculus in the real matrix algebra. -/
```

### NLA.RA08.functionTruncation

[def in preserved source](../projects/RA-08/Challenge.lean#L86)

```lean
/-- The function truncation uses the SAME selected eigenvectors as `truncation`.
It is neither `f (X_k)` nor an independently rotated spectral truncation of `f X`.
In particular the discarded entries are zero even when `f 0` is positive. -/
```

### NLA.RA08.witnessFunction

[def in preserved source](../projects/RA-08/Challenge.lean#L106)

```lean
/-- Colbrook's unchanged kink function, restricted to the half-line in the problem. -/
```

### NLA.RA08.witnessT

[def in preserved source](../projects/RA-08/Challenge.lean#L108)

### NLA.RA08.witnessA

[def in preserved source](../projects/RA-08/Challenge.lean#L110)

### NLA.RA08.witnessB

[def in preserved source](../projects/RA-08/Challenge.lean#L112)

### NLA.RA08.witnessF

[def in preserved source](../projects/RA-08/Challenge.lean#L120)

```lean
/-- The unchanged rank-three orthogonal projection, written with the single
common denominator `65 * 81`. The source gives the equivalent `U Uᵀ` block form. -/
```

### NLA.RA08.witnessApproximation

[def in preserved source](../projects/RA-08/Challenge.lean#L129)

### NLA.RA08.witnessMatrix

[def in preserved source](../projects/RA-08/Challenge.lean#L132)

### NLA.RA08.Paper.nystrom

[def in preserved source](../projects/RA-08/Challenge.lean#L194)

### NLA.RA08.Paper.paper_spectral_failure

[theorem in preserved source](../projects/RA-08/Challenge.lean#L212)

### NLA.RA08.Paper.nuclearNorm

[def in preserved source](../projects/RA-08/Challenge.lean#L270)

```lean
/-- The actual nuclear norm: the trace of the positive square root of AᵀA. -/
```

### NLA.RA08.Paper.NuclearTransferFailure

[def in preserved source](../projects/RA-08/Challenge.lean#L433)

```lean
/-- The printed nuclear theorem, with actual Nyström and actual ordered truncations. -/
```

### NLA.RA08.Paper.verified_paper_nuclear_counterexample

[theorem in preserved source](../projects/RA-08/Challenge.lean#L458)

## RA-09

### NLA.RA09.RealMatrix

[abbrev in preserved source](../projects/RA-09/Challenge.lean#L40)

### NLA.RA09.frobeniusSquared

[def in preserved source](../projects/RA-09/Challenge.lean#L43)

```lean
/-- Finite real entry squares; equality with actual Frobenius norm squared is an obligation. -/
```

### NLA.RA09.frobeniusNorm

[def in preserved source](../projects/RA-09/Challenge.lean#L49)

```lean
/-- The actual Mathlib Frobenius norm, with its instance isolated from CFC. -/
```

### NLA.RA09.OrderedSpectralData

[structure in preserved source](../projects/RA-09/Challenge.lean#L58)

```lean
/-- Every allowed ordered orthonormal decomposition of the actual matrix. -/
```

### NLA.RA09.spectralCombination

[def in preserved source](../projects/RA-09/Challenge.lean#L67)

### NLA.RA09.functionalCalculus

[def in preserved source](../projects/RA-09/Challenge.lean#L77)

```lean
/-- Genuine Mathlib real functional calculus, not a stipulated spectral formula. -/
```

### NLA.RA09.functionTruncation

[def in preserved source](../projects/RA-09/Challenge.lean#L81)

```lean
/-- SAME basis as the original truncation; discarded entries stay zero even when f(0)>0. -/
```

### NLA.RA09.spectralTail

[def in preserved source](../projects/RA-09/Challenge.lean#L85)

### NLA.RA09.functionTail

[def in preserved source](../projects/RA-09/Challenge.lean#L88)

### NLA.RA09.PaperAdmissibleFunction

[def in preserved source](../projects/RA-09/Challenge.lean#L134)

### NLA.RA09.UnorderedSharpnessWitness

[def in preserved source](../projects/RA-09/Challenge.lean#L151)

### NLA.RA09.paper_ordered_matrix_norm_relative

[theorem in preserved source](../projects/RA-09/Challenge.lean#L206)

### NLA.RA09.paper_unordered_matrix_norm_relative

[theorem in preserved source](../projects/RA-09/Challenge.lean#L216)

### NLA.RA09.paper_ordered_sharpness

[theorem in preserved source](../projects/RA-09/Challenge.lean#L226)

### NLA.RA09.paper_unordered_sharpness

[theorem in preserved source](../projects/RA-09/Challenge.lean#L235)

## IE-21

### NLA.IE21.Space

[abbrev in preserved source](../projects/IE-21/Challenge.lean#L39)

### NLA.IE21.Mat

[abbrev in preserved source](../projects/IE-21/Challenge.lean#L40)

### NLA.IE21.Sphere

[abbrev in preserved source](../projects/IE-21/Challenge.lean#L41)

### NLA.IE21.matrixMeasurableSpace

[instance in preserved source](../projects/IE-21/Challenge.lean#L43)

### NLA.IE21.matrixBorelSpace

[instance in preserved source](../projects/IE-21/Challenge.lean#L46)

### NLA.IE21.surfaceMeasure

[def in preserved source](../projects/IE-21/Challenge.lean#L50)

```lean
/-- Actual Euclidean surface measure, obtained from Euclidean Lebesgue measure. -/
```

### NLA.IE21.surfaceLaw

[def in preserved source](../projects/IE-21/Challenge.lean#L54)

```lean
/-- Normalization is literal inverse total mass, with no probability axiom. -/
```

### NLA.IE21.sphereLaw

[def in preserved source](../projects/IE-21/Challenge.lean#L58)

```lean
/-- Ambient-space law of a uniform unit vector. -/
```

### NLA.IE21.matrixRow

[def in preserved source](../projects/IE-21/Challenge.lean#L64)

### NLA.IE21.matrixMap

[def in preserved source](../projects/IE-21/Challenge.lean#L71)

### NLA.IE21.operatorNorm

[def in preserved source](../projects/IE-21/Challenge.lean#L74)

### NLA.IE21.retainedRows

[def in preserved source](../projects/IE-21/Challenge.lean#L76)

### NLA.IE21.retainedMatrix

[def in preserved source](../projects/IE-21/Challenge.lean#L78)

### NLA.IE21.retainedNorm

[def in preserved source](../projects/IE-21/Challenge.lean#L81)

### NLA.IE21.deletionSingular

[def in preserved source](../projects/IE-21/Challenge.lean#L86)

```lean
/-- Infimum over the exact canonical pairs. Mandatory attainment and lower-bound
theorems rule out reliance on any empty-set/default behavior of real `sInf`. -/
```

### NLA.IE21.normalizedDeletion

[def in preserved source](../projects/IE-21/Challenge.lean#L99)

### NLA.IE21.normalizedOperator

[def in preserved source](../projects/IE-21/Challenge.lean#L102)

### NLA.IE21.deletionRatio

[def in preserved source](../projects/IE-21/Challenge.lean#L105)

### NLA.IE21.gaussianCutoff

[def in preserved source](../projects/IE-21/Challenge.lean#L112)

### NLA.IE21.gaussianTrim

[def in preserved source](../projects/IE-21/Challenge.lean#L116)

```lean
/-- Exact canonical Gaussian integral; its quantile semantics must be proved. -/
```

### NLA.IE21.IndependentSphereRows

[def in preserved source](../projects/IE-21/Challenge.lean#L153)

```lean
/-- Independent rows with the actual normalized surface law on any probability space. -/
```

### NLA.IE21.Paper.paper_random_rows

[theorem in preserved source](../projects/IE-21/Challenge.lean#L175)

## IE-22

### NLA.IE22.UnitRows

[def in preserved source](../projects/IE-22/Challenge.lean#L183)

```lean
/-- Literal unit Euclidean row condition. -/
```

### NLA.IE22.normalizedSingular

[def in preserved source](../projects/IE-22/Challenge.lean#L187)

```lean
/-- The canonical unsquared, normalized singular statistic. -/
```

### NLA.IE22.unitRowValues

[def in preserved source](../projects/IE-22/Challenge.lean#L190)

### NLA.IE22.extremalValue

[def in preserved source](../projects/IE-22/Challenge.lean#L194)

```lean
/-- Literal canonical supremum M; nonempty/finite/attained semantics are compulsory. -/
```

### NLA.IE22.sharpConstant

[def in preserved source](../projects/IE-22/Challenge.lean#L196)

### NLA.IE22.errorSchedule

[def in preserved source](../projects/IE-22/Challenge.lean#L241)

### NLA.IE22.Paper.paper_high_aspect_supremum_limit

[theorem in preserved source](../projects/IE-22/Challenge.lean#L259)

### NLA.IE22.Paper.paper_universal_squared_rate

[theorem in preserved source](../projects/IE-22/Challenge.lean#L266)

## TR-04

### Reference.RealSVDPackage.Rect

[abbrev in preserved source](../projects/TR-04/Challenge.lean#L20)

### Reference.RealSVDPackage.Square

[abbrev in preserved source](../projects/TR-04/Challenge.lean#L21)

### Reference.RealSVDPackage.EuclideanVector

[abbrev in preserved source](../projects/TR-04/Challenge.lean#L22)

### Reference.RealSVDPackage.euclideanLin

[def in preserved source](../projects/TR-04/Challenge.lean#L23)

### Reference.RealSVDPackage.singularValue

[def in preserved source](../projects/TR-04/Challenge.lean#L25)

### Reference.RealSVDPackage.basisMatrix

[def in preserved source](../projects/TR-04/Challenge.lean#L27)

### Reference.RealOptimalityEquality.leftBasis

[def in preserved source](../projects/TR-04/Challenge.lean#L42)

### Reference.RealOptimalityEquality.leftVectorMatrix

[def in preserved source](../projects/TR-04/Challenge.lean#L46)

### Reference.RecursiveTensorCompletion.ModeIndex

[def in preserved source](../projects/TR-04/Challenge.lean#L60)

### Reference.RecursiveTensorCompletion.modeIndexFintype

[instance in preserved source](../projects/TR-04/Challenge.lean#L63)

### Reference.RecursiveTensorCompletion.modeIndexDecidableEq

[instance in preserved source](../projects/TR-04/Challenge.lean#L69)

### Reference.RecursiveTensorCompletion.Tensor

[abbrev in preserved source](../projects/TR-04/Challenge.lean#L75)

### Reference.RecursiveTensorCompletion.tensorFrobeniusSq

[def in preserved source](../projects/TR-04/Challenge.lean#L76)

### Reference.RecursiveTensorCompletion.rowCount

[def in preserved source](../projects/TR-04/Challenge.lean#L78)

### Reference.RecursiveTensorCompletion.rowEquiv

[def in preserved source](../projects/TR-04/Challenge.lean#L79)

### Reference.RecursiveTensorCompletion.merge

[def in preserved source](../projects/TR-04/Challenge.lean#L81)

### Reference.RecursiveTensorCompletion.feasible

[def in preserved source](../projects/TR-04/Challenge.lean#L83)

### Reference.LexicographicFeasibilityBridge.product_eq_rowCount

[theorem in preserved source](../projects/TR-04/Challenge.lean#L100)

### Reference.LexicographicFeasibilityBridge.rowEquivLex

[def in preserved source](../projects/TR-04/Challenge.lean#L101)

### Reference.TensorCandidateSelection.error

[def in preserved source](../projects/TR-04/Challenge.lean#L116)

### Reference.TensorOptimumAttainment.feasibleSet

[def in preserved source](../projects/TR-04/Challenge.lean#L128)

### Reference.TensorOptimumAttainment.optimalError

[def in preserved source](../projects/TR-04/Challenge.lean#L130)

### Reference.LexTensorArithmeticExecution.Event

[inductive in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L38)

### Reference.LexTensorArithmeticExecution.eventCharge

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L61)

### Reference.LexTensorArithmeticExecution.Run

[structure in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L65)

### Reference.LexTensorArithmeticExecution.pureRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L69)

### Reference.LexTensorArithmeticExecution.bindRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L71)

### Unnamed instance in Reference.LexTensorArithmeticExecution (source line 75)

[instance in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L75)

### Reference.LexTensorArithmeticExecution.readReal

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L79)

### Reference.LexTensorArithmeticExecution.zeroReal

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L81)

### Reference.LexTensorArithmeticExecution.addReal

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L83)

### Reference.LexTensorArithmeticExecution.subReal

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L85)

### Reference.LexTensorArithmeticExecution.mulReal

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L87)

### Reference.LexTensorArithmeticExecution.lessReal

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L89)

### Reference.LexTensorArithmeticExecution.leftSubspace

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L91)

### Reference.LexTensorCompletion.ModeIndex

[abbrev in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L107)

### Reference.LexTensorCompletion.Tensor

[abbrev in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L109)

### Reference.LexTensorCompletion.tensorFrobeniusSq

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L111)

### Reference.LexTensorCompletion.rowCount

[abbrev in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L113)

### Reference.LexTensorCompletion.rowEquiv

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L115)

### Reference.LexTensorCompletion.merge

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L117)

### Reference.LexTensorCompletion.unmerge

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L120)

### Reference.LexTensorCompletion.feasible

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L126)

### Reference.LexOrderedIndex.indexList

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L141)

### Reference.LexOrderedIndex.mem_indexList

[theorem in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L144)

### Reference.LexOrderedIndex.nodup_indexList

[theorem in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L147)

### Reference.LexOrderedIndex.predicateListEquiv

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L150)

### Reference.LexOrderedIndex.listEnum

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L157)

### Reference.LexOrderedIndex.indexList_length

[theorem in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L161)

### Reference.LexOrderedIndex.indexEnum

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L166)

### Reference.LexTensorArithmeticExecution.vectorRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L181)

### Reference.LexTensorArithmeticExecution.dotRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L186)

### Reference.LexTensorArithmeticExecution.matrixMulRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L193)

### Reference.LexTensorCompletion.lexCard

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L202)

### Reference.LexTensorCompletion.lexIndex

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L206)

### Reference.LexTensorCompletion.lexCard_eq_card

[theorem in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L214)

### Reference.LexTensorCompletion.concreteLayout

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L221)

### Reference.LexOrderedCyclicBoundary.EIndex

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L238)

### Reference.LexOrderedCyclicBoundary.HIndex

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L241)

### Reference.LexOrderedCyclicBoundary.eFinite

[instance in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L244)

### Reference.LexOrderedCyclicBoundary.hFinite

[instance in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L248)

### Reference.LexOrderedCyclicBoundary.eCount

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L252)

### Reference.LexOrderedCyclicBoundary.hCount

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L254)

### Reference.LexOrderedCyclicBoundary.boundaryOrdinal

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L256)

### Reference.LexOrderedCyclicBoundary.inWindow

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L258)

### Reference.LexOrderedCyclicBoundary.windowSelected

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L260)

### Reference.LexOrderedCyclicBoundary.selected

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L265)

### Reference.LexOrderedCyclicBoundary.indicatorFrame

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L274)

### Reference.LexOrderedCyclicBoundary.candidateFrame

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L286)

### Reference.LexTensorCompletion.denseTensor

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L301)

### Reference.LexTensorCompletion.svdFrame

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L305)

### Reference.LexTensorCompletion.ttSVD

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L309)

### Reference.LexTensorCompletion.completeFrame

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L320)

### Reference.LexOrderedCyclicBoundary.tensorBoundary

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L359)

### Reference.LexOrderedCyclicBoundary.tensorBoundaryCount

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L362)

### Reference.LexOrderedCyclicBoundary.tensorRetainedBoundary

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L365)

### Reference.LexOrderedCyclicBoundary.tensorCandidateFrame

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L368)

### Reference.LexOrderedCyclicBoundary.cyclicCompletion

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L372)

### Reference.LexOrderedTensorSolver.error

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L388)

### Reference.LexOrderedTensorSolver.firstMinimum

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L390)

### Reference.LexOrderedTensorSolver.leadingCompletion

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L395)

### Reference.LexOrderedTensorSolver.columnSpaceCompletion

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L398)

### Reference.LexOrderedTensorSolver.candidates

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L401)

### Reference.LexOrderedTensorSolver.solver

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L410)

### Reference.LexTensorExecution.Event

[inductive in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L426)

### Reference.LexTensorExecution.eventCharge

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L454)

### Reference.LexTensorExecution.Run

[structure in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L459)

### Reference.LexTensorExecution.pureRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L463)

### Reference.LexTensorExecution.bindRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L465)

### Reference.LexTensorExecution.liftRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L469)

### Reference.LexTensorExecution.spectralRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L472)

### Reference.LexTensorExecution.equalRealRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L475)

### Reference.LexTensorExecution.equalNatRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L477)

### Reference.LexTensorExecution.lessNatRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L479)

### Reference.LexTensorExecution.addNatRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L481)

### Reference.LexTensorExecution.subNatRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L483)

### Reference.LexTensorExecution.modNatRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L485)

### Reference.LexTensorExecution.branchRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L487)

### Reference.LexTensorExecution.charge

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L489)

### Reference.LexTensorExecution.filterRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L491)

### Reference.LexTensorExecution.ordinalRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L497)

### Reference.LexTensorExecution.readRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L512)

### Reference.LexTensorExecution.lessRealRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L514)

### Reference.LexTensorExecution.equalScanRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L516)

### Reference.LexTensorExecution.aboveScanRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L519)

### Reference.LexTensorExecution.windowMaskRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L522)

### Reference.LexTensorExecution.windowScanRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L537)

### Reference.LexTensorExecution.frameFromListRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L541)

### Reference.LexTensorArithmeticExecution.rowErrorRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L598)

### Reference.LexTensorArithmeticExecution.matrixErrorRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L606)

### Reference.LexTensorArithmeticExecution.tensorErrorRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L611)

### Reference.LexTensorArithmeticExecution.minimumRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L625)

### Reference.LexTensorArithmeticExecution.copyMatrixRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L651)

### Reference.LexTensorArithmeticExecution.tensorCopyRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L654)

### Reference.LexTensorArithmeticExecution.tensorMulRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L658)

### Reference.LexTensorArithmeticExecution.frameRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L662)

### Reference.LexTensorArithmeticExecution.ttRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L678)

### Reference.LexTensorArithmeticExecution.completionRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L691)

### Reference.LexTensorExecution.cyclicExecutionRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L731)

### Reference.LexTensorExecution.listMapRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L765)

### Reference.LexTensorExecution.prefixFrameRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L769)

### Reference.LexTensorExecution.prefixCompletionRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L774)

### Reference.LexTensorExecution.sigmaAtRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L778)

### Reference.LexTensorExecution.candidateDataRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L788)

### Reference.LexTensorExecution.candidatesExecutionRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L811)

### Reference.LexTensorExecution.solverExecutionRun

[def in preserved source](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L815)

### Reference.LexTensorExecution.actual_lexicographic_paper_algorithm

[theorem in preserved source](../projects/TR-04/Challenge.lean#L603)

## TR-27

### NLA.TR27.ProjectiveVariety

[structure in preserved source](../projects/TR-27/Challenge.lean#L40)

### NLA.TR27.ProjectiveVariety.cone

[def in preserved source](../projects/TR-27/Challenge.lean#L50)

### NLA.TR27.ProjectiveVariety.points

[def in preserved source](../projects/TR-27/Challenge.lean#L55)

### NLA.TR27.ProjectiveVariety.Admissible

[def in preserved source](../projects/TR-27/Challenge.lean#L60)

### NLA.TR27.ProjectiveVariety.zariskiClosure

[def in preserved source](../projects/TR-27/Challenge.lean#L69)

### NLA.TR27.ProjectiveVariety.IsClosed

[def in preserved source](../projects/TR-27/Challenge.lean#L75)

### NLA.TR27.ProjectiveVariety.IsIrreducible

[def in preserved source](../projects/TR-27/Challenge.lean#L80)

### NLA.TR27.ProjectiveRankAtMost

[def in preserved source](../projects/TR-27/Challenge.lean#L93)

### NLA.TR27.projectiveRank

[def in preserved source](../projects/TR-27/Challenge.lean#L99)

### NLA.TR27.borderRank

[def in preserved source](../projects/TR-27/Challenge.lean#L102)

### NLA.TR27.Represents

[def in preserved source](../projects/TR-27/Challenge.lean#L106)

### NLA.TR27.Paper.CurveSpace

[abbrev in preserved source](../projects/TR-27/Challenge.lean#L130)

### NLA.TR27.Paper.curveVector

[def in preserved source](../projects/TR-27/Challenge.lean#L133)

### NLA.TR27.Paper.tangentVector

[def in preserved source](../projects/TR-27/Challenge.lean#L137)

### NLA.TR27.Paper.coordinateProjectiveTopology

[def in preserved source](../projects/TR-27/Challenge.lean#L158)

### NLA.TR27.Paper.projectiveCoordinateRatio

[def in preserved source](../projects/TR-27/Challenge.lean#L177)

### NLA.TR27.Paper.projectionCenter

[def in preserved source](../projects/TR-27/Challenge.lean#L194)

### NLA.TR27.Paper.centerLine

[def in preserved source](../projects/TR-27/Challenge.lean#L197)

### NLA.TR27.Paper.QuotientSpace

[abbrev in preserved source](../projects/TR-27/Challenge.lean#L200)

### NLA.TR27.Paper.quotientProjection

[def in preserved source](../projects/TR-27/Challenge.lean#L202)

### NLA.TR27.Paper.quotientCurve

[def in preserved source](../projects/TR-27/Challenge.lean#L205)

### NLA.TR27.Paper.quotientTangent

[def in preserved source](../projects/TR-27/Challenge.lean#L208)

### NLA.TR27.Paper.quotientPoints

[def in preserved source](../projects/TR-27/Challenge.lean#L211)

### NLA.TR27.Paper.chosenParameters

[def in preserved source](../projects/TR-27/Challenge.lean#L214)

### NLA.TR27.Paper.familyDegree

[def in preserved source](../projects/TR-27/Challenge.lean#L216)

### NLA.TR27.Paper.chosenPowerSum

[def in preserved source](../projects/TR-27/Challenge.lean#L233)

### NLA.TR27.Paper.chosenPivot

[def in preserved source](../projects/TR-27/Challenge.lean#L234)

### NLA.TR27.Paper.pivotIndex

[def in preserved source](../projects/TR-27/Challenge.lean#L253)

### NLA.TR27.Paper.retainedIndex

[def in preserved source](../projects/TR-27/Challenge.lean#L256)

### NLA.TR27.Paper.coordinateProjection

[def in preserved source](../projects/TR-27/Challenge.lean#L259)

### NLA.TR27.Paper.ImageCoordinatePolynomial

[abbrev in preserved source](../projects/TR-27/Challenge.lean#L283)

### NLA.TR27.Paper.CurveParameterPolynomial

[abbrev in preserved source](../projects/TR-27/Challenge.lean#L284)

### NLA.TR27.Paper.imageHomogeneousCoordinate

[def in preserved source](../projects/TR-27/Challenge.lean#L286)

### NLA.TR27.Paper.imageSubstitution

[def in preserved source](../projects/TR-27/Challenge.lean#L293)

### NLA.TR27.Paper.imageHomogeneousMap

[def in preserved source](../projects/TR-27/Challenge.lean#L297)

### NLA.TR27.Paper.imageIdeal

[def in preserved source](../projects/TR-27/Challenge.lean#L300)

### NLA.TR27.Paper.coordinateImagePoints

[def in preserved source](../projects/TR-27/Challenge.lean#L322)

### NLA.TR27.Paper.HasProjectiveAnalyticGraph

[def in preserved source](../projects/TR-27/Challenge.lean#L328)

### NLA.TR27.Paper.coordinateProjection_surjective

[theorem in preserved source](../projects/TR-27/Challenge.lean#L353)

### NLA.TR27.Paper.coordinateProjection_kernel

[theorem in preserved source](../projects/TR-27/Challenge.lean#L355)

### NLA.TR27.Paper.quotientCoordinateEquiv

[def in preserved source](../projects/TR-27/Challenge.lean#L357)

### NLA.TR27.Paper.imageHomogeneousMap_eq_zero_iff

[theorem in preserved source](../projects/TR-27/Challenge.lean#L381)

### NLA.TR27.Paper.projectiveCurveMap

[def in preserved source](../projects/TR-27/Challenge.lean#L400)

### NLA.TR27.Paper.recoveryMomentA

[def in preserved source](../projects/TR-27/Challenge.lean#L419)

### NLA.TR27.Paper.recoveryMomentB

[def in preserved source](../projects/TR-27/Challenge.lean#L422)

### NLA.TR27.Paper.recoveryMomentC

[def in preserved source](../projects/TR-27/Challenge.lean#L425)

### NLA.TR27.Paper.recoveryIndex

[def in preserved source](../projects/TR-27/Challenge.lean#L429)

### NLA.TR27.Paper.recoveryDenominator

[def in preserved source](../projects/TR-27/Challenge.lean#L431)

### NLA.TR27.Paper.recoveryNumerator

[def in preserved source](../projects/TR-27/Challenge.lean#L436)

### NLA.TR27.Paper.recoveryPolynomial

[def in preserved source](../projects/TR-27/Challenge.lean#L441)

### NLA.TR27.Paper.rationalRecovery

[def in preserved source](../projects/TR-27/Challenge.lean#L446)

### NLA.TR27.Paper.recoveryOpenPoints

[def in preserved source](../projects/TR-27/Challenge.lean#L467)

### NLA.TR27.Paper.tensor_reps_nonzero

[theorem in preserved source](../projects/TR-27/Challenge.lean#L490)

### NLA.TR27.Paper.tensorPoint

[def in preserved source](../projects/TR-27/Challenge.lean#L492)

### NLA.TR27.Paper.powerPoint

[def in preserved source](../projects/TR-27/Challenge.lean#L495)

### NLA.TR27.Paper.productPoints

[def in preserved source](../projects/TR-27/Challenge.lean#L499)

### NLA.TR27.Paper.paper_full_family

[theorem in preserved source](../projects/TR-27/Challenge.lean#L521)

## IS-03

### NLA.IS03.RealMatrix

[abbrev in preserved source](../projects/IS-03/Challenge.lean#L38)

```lean
/-- Actual real square matrices of the indicated finite order. -/
```

### NLA.IS03.EntrywiseNonnegative

[def in preserved source](../projects/IS-03/Challenge.lean#L41)

```lean
/-- Entrywise nonnegativity; it is not positive-semidefinite order. -/
```

### NLA.IS03.normalizedDerivative

[def in preserved source](../projects/IS-03/Challenge.lean#L45)

```lean
/-- The actual formal derivative, scaled by the reciprocal of the matrix order. -/
```

### NLA.IS03.witnessMatrix

[def in preserved source](../projects/IS-03/Challenge.lean#L55)

```lean
/-- Colbrook's unchanged block matrix diag(1/2, C₂, C₄). -/
```

### NLA.IS03.paper_counterexample

[theorem in preserved source](../projects/IS-03/Challenge.lean#L91)

## NM-04

### NLA.NM04.MinorIndex

[abbrev in preserved source](../projects/NM-04/Challenge.lean#L48)

```lean
/-- A pair of actual finite subsets with equal cardinalities. -/
```

### NLA.NM04.position

[def in preserved source](../projects/NM-04/Challenge.lean#L55)

```lean
/-- One-based position in the increasing order. Only member positions enter signs. -/
```

### NLA.NM04.minorMatrix

[def in preserved source](../projects/NM-04/Challenge.lean#L59)

```lean
/-- The two maps enumerate the selected rows and columns in increasing order. -/
```

### NLA.NM04.minor

[def in preserved source](../projects/NM-04/Challenge.lean#L65)

### NLA.NM04.RaisingSupport

[def in preserved source](../projects/NM-04/Challenge.lean#L85)

```lean
/-- Literal singleton supports from the canonical four off-diagonal cases. -/
```

### NLA.NM04.LoweringSupport

[def in preserved source](../projects/NM-04/Challenge.lean#L90)

### NLA.NM04.ColumnExchangeSupport

[def in preserved source](../projects/NM-04/Challenge.lean#L95)

### NLA.NM04.RowExchangeSupport

[def in preserved source](../projects/NM-04/Challenge.lean#L100)

### NLA.NM04.raisingCoefficient

[def in preserved source](../projects/NM-04/Challenge.lean#L105)

### NLA.NM04.loweringCoefficient

[def in preserved source](../projects/NM-04/Challenge.lean#L110)

### NLA.NM04.columnExchangeCoefficient

[def in preserved source](../projects/NM-04/Challenge.lean#L115)

### NLA.NM04.rowExchangeCoefficient

[def in preserved source](../projects/NM-04/Challenge.lean#L120)

### NLA.NM04.Rect

[abbrev in preserved source](../projects/NM-04/Challenge.lean#L146)

### NLA.NM04.Tail

[abbrev in preserved source](../projects/NM-04/Challenge.lean#L149)

```lean
/-- Original labels 2,...,m, stored as their zero-based `Fin m` indices. -/
```

### NLA.NM04.Index

[abbrev in preserved source](../projects/NM-04/Challenge.lean#L150)

### NLA.NM04.firstIndex

[def in preserved source](../projects/NM-04/Challenge.lean#L152)

### NLA.NM04.tailMatrix

[def in preserved source](../projects/NM-04/Challenge.lean#L154)

### NLA.NM04.delta

[def in preserved source](../projects/NM-04/Challenge.lean#L158)

```lean
/-- First index followed by increasing tail indices is the source's increasing order. -/
```

### NLA.NM04.gamma

[def in preserved source](../projects/NM-04/Challenge.lean#L164)

### NLA.NM04.H

[def in preserved source](../projects/NM-04/Challenge.lean#L169)

```lean
/-- Integer arithmetic, including the negative diagonal and lowering coefficient. -/
```

### NLA.NM04.HReal

[def in preserved source](../projects/NM-04/Challenge.lean#L175)

### NLA.NM04.Positive

[def in preserved source](../projects/NM-04/Challenge.lean#L186)

### NLA.NM04.Balanced

[def in preserved source](../projects/NM-04/Challenge.lean#L188)

### NLA.NM04.diagonalScale

[def in preserved source](../projects/NM-04/Challenge.lean#L192)

```lean
/-- Entrywise form of multiplication by the actual two diagonal matrices. -/
```

### NLA.NM04.ScaledBalanced

[def in preserved source](../projects/NM-04/Challenge.lean#L195)

### NLA.NM04.sinkhorn

[def in preserved source](../projects/NM-04/Challenge.lean#L201)

```lean
/-- Total choice only. Existence, uniqueness and exclusion of the fallback on
    positive inputs are separate contracts and are not assumptions of this definition. -/
```

### NLA.NM04.Paper.paper_rowland_wu_identity

[theorem in preserved source](../projects/NM-04/Challenge.lean#L254)

## PF-02

### NLA.PF02.Mat

[abbrev in preserved source](../projects/PF-02/Challenge.lean#L172)

### NLA.PF02.FactorTuple

[abbrev in preserved source](../projects/PF-02/Challenge.lean#L173)

### NLA.PF02.IsFactorization

[def in preserved source](../projects/PF-02/Challenge.lean#L176)

```lean
/-- Every row and column factor is genuinely real positive semidefinite. -/
```

### NLA.PF02.Factorization

[abbrev in preserved source](../projects/PF-02/Challenge.lean#L181)

```lean
/-- The full factorization space with its inherited finite-dimensional Euclidean topology. -/
```

### NLA.PF02.IsPSDRank

[def in preserved source](../projects/PF-02/Challenge.lean#L185)

```lean
/-- The actual minimum among all positive integer factor sizes, including attainment. -/
```

### NLA.PF02.Congruent

[def in preserved source](../projects/PF-02/Challenge.lean#L189)

```lean
/-- A single genuine invertible change of basis, on all row and column factors. -/
```

### NLA.PF02.OrbitSpace

[abbrev in preserved source](../projects/PF-02/Challenge.lean#L195)

```lean
/-- Quotient topology on actual congruence orbits; the public orbit theorem checks exact equality. -/
```

### Reference.PF02UniformPositiveOrientation.paper_all_size_disconnected_witness

[theorem in preserved source](../projects/PF-02/Challenge.lean#L612)

## MD-06

### Reference.MD06Actual.Phase

[abbrev in preserved source](../projects/MD-06/Challenge.lean#L19)

### Reference.MD06Actual.Energy

[def in preserved source](../projects/MD-06/Challenge.lean#L21)

### Reference.MD06Actual.Synchronized

[def in preserved source](../projects/MD-06/Challenge.lean#L25)

### Reference.MD06Actual.Gradient

[def in preserved source](../projects/MD-06/Challenge.lean#L27)

### Reference.MD06Actual.HessianQuadratic

[def in preserved source](../projects/MD-06/Challenge.lean#L31)

### Reference.MD06FiniteProbability.Size

[abbrev in preserved source](../projects/MD-06/Challenge.lean#L53)

### Reference.MD06FiniteProbability.CubicSample

[abbrev in preserved source](../projects/MD-06/Challenge.lean#L55)

### Reference.MD06FiniteProbability.sampleFintype

[instance in preserved source](../projects/MD-06/Challenge.lean#L58)

### Reference.MD06FiniteProbability.actual_cubic_sample_nonempty

[theorem in preserved source](../projects/MD-06/Challenge.lean#L78)

### Reference.MD06FiniteProbability.sampleNonempty

[instance in preserved source](../projects/MD-06/Challenge.lean#L79)

### Reference.MD06FiniteProbability.UniformCubic

[def in preserved source](../projects/MD-06/Challenge.lean#L82)

### Reference.MD06MainAssembly.Interface.actual_paper_md_main

[theorem in preserved source](../projects/MD-06/Challenge.lean#L115)

## IV-04

### Complexity.delimit

[def in preserved source](../projects/IV-04/Challenge.lean#L34)

```lean
/-- Frame a binary string as a self-delimiting block: each payload bit is doubled
    (`false ↦ [false, false]`, `true ↦ [true, true]`) and the block is terminated by the
    separator `[false, true]`, which no run of doubled bits can produce. -/
```

### Complexity.pair

[def in preserved source](../projects/IV-04/Challenge.lean#L50)

```lean
/-- Encode a pair of binary strings as a single binary string.
    Each bit of `x` is doubled (`false ↦ [false, false]`, `true ↦ [true, true]`),
    followed by the separator `[false, true]`, followed by `y` verbatim.
    The output has length `2|x| + 2 + |y|` (`pair_length`) and the encoding is
    injective (`pair_inj`). Machine-level cost is recorded elsewhere: `pair` of
    two `FP` functions is in `FP` (`mem_FP_pair`), and `x ↦ pair (f x) x` has
    an explicit bound (`TM.pairWithInputTM_computesInTime`); no linear-time
    bound for `pair` itself is stated. -/
```

### IV04.Paper.Computational.firstBit

[def in preserved source](../projects/IV-04/Challenge.lean#L60)

```lean
/-- The first output bit, with false for an empty word. -/
```

### IV04.Paper.Mat

[abbrev in preserved source](../projects/IV-04/Challenge.lean#L70)

```lean
/-- Real square matrices of order n. -/
```

### IV04.Paper.naturalCode

[def in preserved source](../projects/IV-04/Challenge.lean#L80)

```lean
/-- Unary length followed by the canonical least-significant-first payload. -/
```

### IV04.Paper.readUnary

[def in preserved source](../projects/IV-04/Challenge.lean#L83)

```lean
/-- Read true bits up to a false terminator, returning their count and the unused suffix. -/
```

### IV04.Paper.readNatural

[def in preserved source](../projects/IV-04/Challenge.lean#L90)

```lean
/-- Read a unary payload length and that many least-significant-first binary digits. -/
```

### IV04.Paper.rationalCode

[def in preserved source](../projects/IV-04/Challenge.lean#L96)

```lean
/-- Encode a rational by its sign, absolute numerator and positive denominator. -/
```

### IV04.Paper.readRational

[def in preserved source](../projects/IV-04/Challenge.lean#L99)

```lean
/-- Read sign, numerator and denominator fields using rational division, with the unused suffix. -/
```

### Complexity.Γ

[inductive in preserved source](../projects/IV-04/Challenge.lean#L115)

```lean
/-- The tape alphabet Γ = {0, 1, □, ▷}. -/
```

### Unnamed instance in Complexity (source line 118)

[instance in preserved source](../projects/IV-04/Challenge.lean#L118)

### Unnamed instance in Complexity (source line 121)

[instance in preserved source](../projects/IV-04/Challenge.lean#L121)

### Complexity.Γw

[inductive in preserved source](../projects/IV-04/Challenge.lean#L124)

```lean
/-- The writable alphabet Γw = {0, 1, □}. The start symbol `▷` cannot be written by a
    transition function — this is enforced structurally by using `Γw` in the output of `δ`. -/
```

### Unnamed instance in Complexity (source line 127)

[instance in preserved source](../projects/IV-04/Challenge.lean#L127)

### Complexity.Γw.toΓ

[def in preserved source](../projects/IV-04/Challenge.lean#L131)

```lean
/-- Embed a writable symbol into the full alphabet. -/
```

### Unnamed instance in Complexity (source line 135)

[instance in preserved source](../projects/IV-04/Challenge.lean#L135)

### Complexity.Γ.ofBool

[def in preserved source](../projects/IV-04/Challenge.lean#L137)

```lean
/-- Convert a boolean to an alphabet symbol. -/
```

### Complexity.Dir3

[inductive in preserved source](../projects/IV-04/Challenge.lean#L141)

```lean
/-- Three-way tape head direction: left, right, or stay. -/
```

### Unnamed instance in Complexity (source line 144)

[instance in preserved source](../projects/IV-04/Challenge.lean#L144)

### Complexity.Tape

[structure in preserved source](../projects/IV-04/Challenge.lean#L158)

```lean
/-- A one-sided infinite tape: a head position and the contents of every cell.
    Cell 0 is the leftmost cell. The head cannot move left of cell 0 (moving
    left at position 0 is a no-op via `Nat` subtraction), and writing at cell 0
    is a no-op.

    The structure itself allows any symbol in any cell. The left-end marker `▷`
    at cell 0 is an invariant of the semantics, not of the type: `Tape.init`
    places it, machines write only symbols of `Γw` (never `▷`), and writes at
    cell 0 are ignored, so every tape reachable from an initial configuration
    satisfies `Tape.StartInvariant`. Statements about arbitrary tapes that need
    the marker must assume that invariant. -/
```

### Complexity.Tape.read

[def in preserved source](../projects/IV-04/Challenge.lean#L164)

```lean
/-- Read the symbol under the head. -/
```

### Complexity.Tape.write

[def in preserved source](../projects/IV-04/Challenge.lean#L167)

```lean
/-- Write a symbol at the head position. Writing at cell 0 is a no-op,
    preserving the start symbol `▷`. -/
```

### Complexity.Tape.move

[def in preserved source](../projects/IV-04/Challenge.lean#L172)

```lean
/-- Move the head according to a three-way direction.
    Moving left at position 0 stays at 0 (`Nat` subtraction saturates). -/
```

### Complexity.Tape.HasOutput

[def in preserved source](../projects/IV-04/Challenge.lean#L180)

```lean
/-- The tape contains output `y : List Bool` starting at cell 1:
    cells 1 through |y| match `y`, and cell |y| + 1 is blank.
    Output is the binary string written on the output tape after `▷`. -/
```

### Complexity.Tape.decidableHasOutput

[instance in preserved source](../projects/IV-04/Challenge.lean#L184)

### Complexity.Tape.writeAndMove

[abbrev in preserved source](../projects/IV-04/Challenge.lean#L190)

```lean
/-- Write a symbol and move in one step. -/
```

### Complexity.Tape.init

[def in preserved source](../projects/IV-04/Challenge.lean#L195)

```lean
/-- Initialize a tape: `▷` at cell 0, `contents` at cells 1, 2, ..., `□` elsewhere.
    Head starts at position 0 (on `▷`). -/
```

### Complexity.Language

[abbrev in preserved source](../projects/IV-04/Challenge.lean#L201)

```lean
/-- A language is a set of binary strings. -/
```

### Complexity.Cfg

[structure in preserved source](../projects/IV-04/Challenge.lean#L204)

```lean
/-- A configuration of a Turing machine with `n` work tapes:
    a read-only input tape, `n` read-write work tapes, and a read-write output tape. -/
```

### Complexity.Cfg.init

[abbrev in preserved source](../projects/IV-04/Challenge.lean#L211)

```lean
/-- Initial configuration for any TM: input on the input tape, all tapes start with `▷`. -/
```

### Complexity.Cfg.isHalted

[abbrev in preserved source](../projects/IV-04/Challenge.lean#L217)

```lean
/-- A configuration is halted when its state equals the halt state. -/
```

### Complexity.TM

[structure in preserved source](../projects/IV-04/Challenge.lean#L225)

```lean
/-- A deterministic Turing machine with `n` work tapes.

    The machine has a read-only input tape, `n` read-write work tapes, and a read-write
    output tape. The transition function reads `Γ` from all tape heads but writes only
    `Γw` (excluding `▷`) to work and output tapes. `Q` is finite. -/
```

### Complexity.NTM

[structure in preserved source](../projects/IV-04/Challenge.lean#L243)

```lean
/-- A nondeterministic Turing machine with two transition functions.

    The same structure is used for probabilistic TMs — only the acceptance
    criterion differs (existential for NTM, counting for PTM). `Q` is finite. -/
```

### Complexity.TM.step

[def in preserved source](../projects/IV-04/Challenge.lean#L260)

```lean
/-- Step a deterministic TM by one step. Returns `none` if halted. -/
```

### Complexity.TM.initCfg

[abbrev in preserved source](../projects/IV-04/Challenge.lean#L271)

```lean
/-- Initial configuration: input on the input tape, all tapes start with `▷`. -/
```

### Complexity.TM.halted

[abbrev in preserved source](../projects/IV-04/Challenge.lean#L274)

```lean
/-- A configuration is halted when its state is `qhalt`. -/
```

### Complexity.TM.reachesIn

[inductive in preserved source](../projects/IV-04/Challenge.lean#L277)

```lean
/-- Reachability in exactly `t` steps. -/
```

### Complexity.TM.ComputesInTime

[def in preserved source](../projects/IV-04/Challenge.lean#L283)

```lean
/-- DTM computes function `f` in time `T(n)`:
    for every input `x`, the machine halts within `T(|x|)` steps with `f(x)`
    written on the output tape. -/
```

### Complexity.NTM.trace

[def in preserved source](../projects/IV-04/Challenge.lean#L291)

```lean
/-- Execute an NTM for `T` steps with a fixed choice sequence.
    Stops early if the machine reaches `qhalt`. -/
```

### Complexity.NTM.initCfg

[abbrev in preserved source](../projects/IV-04/Challenge.lean#L307)

```lean
/-- Initial configuration: input on the input tape, all tapes start with `▷`. -/
```

### Complexity.NTM.halted

[abbrev in preserved source](../projects/IV-04/Challenge.lean#L310)

```lean
/-- A configuration is halted when its state is `qhalt`. -/
```

### Complexity.NTM.AcceptsInTime

[def in preserved source](../projects/IV-04/Challenge.lean#L314)

```lean
/-- NTM accepts `x` within `T` steps: there exists a choice sequence of length `T`
    leading to `qhalt` with output cell 1 = `1`. -/
```

### Complexity.NTM.AllPathsHaltIn

[def in preserved source](../projects/IV-04/Challenge.lean#L321)

```lean
/-- All computation paths of the NTM halt within `T(|x|)` steps, for every
    input `x` and every choice sequence. This is the core time-boundedness
    condition shared by `DecidesInTime`, `BPTIME`, and `NTM.IsPPT`. -/
```

### Complexity.NTM.DecidesInTime

[def in preserved source](../projects/IV-04/Challenge.lean#L327)

```lean
/-- NTM decides `L` within time bound `T(n)`:
    all computation paths halt within `T(|x|)` steps, and accepting paths exist
    iff `x ∈ L` (AB Definition 2.1). -/
```

### Complexity.BigO

[def in preserved source](../projects/IV-04/Challenge.lean#L343)

```lean
/-- `f` grows at most as fast as `g` asymptotically: `f(n) = O(g(n))` as `n → ∞`.
    Lifts Mathlib's `Asymptotics.IsBigO` to `ℕ → ℕ` functions, avoiding
    repeated `Nat.cast` coercions in complexity class definitions.

    Unfolding: `f =O g ↔ ∃ C, ∀ᶠ n in atTop, ↑(f n) ≤ C * ↑(g n)`. -/
```

### Complexity.NTIME

[def in preserved source](../projects/IV-04/Challenge.lean#L356)

```lean
/-- `NTIME(T)` is the class of languages decidable by a nondeterministic TM in
    time `O(T(n))` (AB Definition 2.1). The machine may have any number of
    work tapes. -/
```

### Complexity.NP

[def in preserved source](../projects/IV-04/Challenge.lean#L367)

```lean
/-- **NP** is the class of languages decidable by a nondeterministic TM in
    polynomial time: `NP = ⋃_k NTIME(n^k)`. -/
```

### Complexity.FP

[def in preserved source](../projects/IV-04/Challenge.lean#L377)

```lean
/-- **FP** is the class of functions computable by a deterministic TM in
    polynomial time. -/
```

### IV04.Paper.Computational.readRationals

[def in preserved source](../projects/IV-04/Challenge.lean#L388)

```lean
/-- Semantic reference; the requested count is a natural value, not a runtime certificate. -/
```

### IV04.Paper.Computational.readMatrixRationals

[def in preserved source](../projects/IV-04/Challenge.lean#L402)

```lean
/-- Semantic reference to the manuscript's natural and rational decoders. -/
```

### IV04.Paper.Computational.rationalDenseEndpointAll

[def in preserved source](../projects/IV-04/Challenge.lean#L414)

```lean
/-- Check that both row-major endpoint tables vanish outside the three central diagonals. -/
```

### IV04.Paper.Computational.boxLowerReal

[def in preserved source](../projects/IV-04/Challenge.lean#L428)

```lean
/-- The real lower endpoint at row-major index i*n+j, using zero as the list default. -/
```

### IV04.Paper.Computational.boxUpperReal

[def in preserved source](../projects/IV-04/Challenge.lean#L431)

```lean
/-- The real upper endpoint at row-major index i*n+j, using zero as the list default. -/
```

### IV04.Paper.Computational.realDenseIntervalBox

[def in preserved source](../projects/IV-04/Challenge.lean#L434)

```lean
/-- All real matrices in the literal dense row-major rational interval box. -/
```

### IV04.Paper.Computational.rationalMatrixDeterminantDecisionLanguage

[def in preserved source](../projects/IV-04/Challenge.lean#L438)

```lean
/-- The actual determinant threshold task quantifies over every real interval realization. -/
```

### Complexity.MapReducesPoly

[def in preserved source](../projects/IV-04/Challenge.lean#L453)

```lean
/-- **Polynomial-time many-one reduction.** `MapReducesPoly L L'` (written
    `L ≤ₚ L'`) holds when there is a polynomial-time computable function `f`
    (`f ∈ FP`) with `x ∈ L ↔ f x ∈ L'` for every input `x`. -/
```

### Complexity.NPHard

[def in preserved source](../projects/IV-04/Challenge.lean#L458)

```lean
/-- **NP-hardness.** `L` is NP-hard when every language in `NP` reduces to `L`
    in polynomial time. -/
```

### Complexity.NPComplete

[def in preserved source](../projects/IV-04/Challenge.lean#L460)

```lean
/-- **NP-completeness.** `L` is NP-complete when it is in `NP` and NP-hard. -/
```

### IV04.Paper.positiveCornerRhs

[def in preserved source](../projects/IV-04/Challenge.lean#L471)

```lean
/-- The fixed right-hand side minus the last coordinate vector. -/
```

### IV04.Paper.positiveSolutions

[def in preserved source](../projects/IV-04/Challenge.lean#L474)

```lean
/-- The union of solution sets A*x = -e_last over matrices A in S. -/
```

### IV04.Paper.Computational.PolynomialOneQueryReduction

[def in preserved source](../projects/IV-04/Challenge.lean#L488)

```lean
/-- One literal call to an output task, with polynomial-time bit programs before and after it. -/
```

### IV04.Paper.Computational.NPHardOutputTask

[def in preserved source](../projects/IV-04/Challenge.lean#L496)

```lean
/-- Every NP language has a polynomial-time one-query reduction to this exact output relation. -/
```

### IV04.Paper.Computational.ExactDeterminantRangeOutput

[def in preserved source](../projects/IV-04/Challenge.lean#L500)

```lean
/-- Two complete rational fields are the actual minimum and maximum determinants. -/
```

### IV04.Paper.Computational.ExactFullHullOutput

[def in preserved source](../projects/IV-04/Challenge.lean#L519)

```lean
/-- Complete finite solution-hull output: literal lower/upper rational endpoints for every coordinate. -/
```

### IV04.Paper.Computational.RegularUnitMatrixPacket

[def in preserved source](../projects/IV-04/Challenge.lean#L548)

```lean
/-- A complete rational tridiagonal packet whose entire real interval family is regular
and has every superdiagonal entry fixed to one. -/
```

### IV04.Paper.Computational.regularUnitMatrixDeterminantDecisionLanguage

[def in preserved source](../projects/IV-04/Challenge.lean#L557)

```lean
/-- The determinant threshold language restricted to the regular unit-superdiagonal promise. -/
```

### IV04.Paper.Computational.RegularUnitDeterminantRangeOutput

[def in preserved source](../projects/IV-04/Challenge.lean#L560)

```lean
/-- Exact determinant-range output on a matrix satisfying the regular unit-superdiagonal promise. -/
```

### IV04.Paper.Computational.actual_paper_iv_det

[theorem in preserved source](../projects/IV-04/Challenge.lean#L571)

### Reference.IV04FullHullHardness.iv_hull_literal_np_hard

[theorem in preserved source](../projects/IV-04/Challenge.lean#L583)

## MI-19

### NLA.MI19.inversionCount

[def in preserved source](../projects/MI-19/Challenge.lean#L38)

```lean
/-- The number of inversions in the full original ordering of `Fin n`.
The paper's index `i + 1` is represented by Lean index `i`. -/
```

### NLA.MI19.qPermanentTerm

[def in preserved source](../projects/MI-19/Challenge.lean#L44)

```lean
/-- The term of the complex `q`-permanent belonging to a permutation.
The natural power retains the convention `0 ^ 0 = 1`. -/
```

### NLA.MI19.qPermanent

[def in preserved source](../projects/MI-19/Challenge.lean#L49)

```lean
/-- The `q`-permanent, with all inversions counted in the original ordering. -/
```

### NLA.MI19.PreservesSubset

[abbrev in preserved source](../projects/MI-19/Challenge.lean#L53)

```lean
/-- Setwise preservation, not pointwise fixation and not an initial-segment test. -/
```

### NLA.MI19.restrictedQPermanent

[def in preserved source](../projects/MI-19/Challenge.lean#L58)

```lean
/-- The subset-preserving sum. The exponent still uses `inversionCount` on
all `n` positions; it is not a product of smaller `q`-permanents. -/
```

### NLA.MI19.witness

[def in preserved source](../projects/MI-19/Challenge.lean#L72)

```lean
/-- Colbrook's exact real Gram witness, viewed as a complex matrix. -/
```

### NLA.MI19.witnessQ

[def in preserved source](../projects/MI-19/Challenge.lean#L80)

```lean
/-- The parameter lies strictly between the two allowed endpoints. -/
```

### NLA.MI19.witnessSubset

[def in preserved source](../projects/MI-19/Challenge.lean#L83)

```lean
/-- The interior singleton `{2}` in the paper's one-based indexing. -/
```

### NLA.MI19.Paper.realWitness

[def in preserved source](../projects/MI-19/Challenge.lean#L99)

### NLA.MI19.Paper.paper_counterexample

[theorem in preserved source](../projects/MI-19/Challenge.lean#L116)

## MI-21

### NLA.MI21.Mat

[abbrev in preserved source](../projects/MI-21/Challenge.lean#L37)

### NLA.MI21.spectralPower

[def in preserved source](../projects/MI-21/Challenge.lean#L41)

```lean
/-- Real powers from the actual continuous functional calculus. On the positive
definite inputs of the conjecture this is spectral matrix exponentiation. -/
```

### NLA.MI21.geometricMean

[def in preserved source](../projects/MI-21/Challenge.lean#L45)

```lean
/-- The weighted geometric mean in the exact order written in the canonical target.
The exponents `1/2`, `-1/2` and `t` are real spectral powers. -/
```

### NLA.MI21.operatorNorm

[def in preserved source](../projects/MI-21/Challenge.lean#L63)

```lean
/-- The genuine operator norm of the matrix acting on complex Euclidean space.
This explicit construction avoids the default entrywise matrix norm. -/
```

### NLA.MI21.leftMatrix

[def in preserved source](../projects/MI-21/Challenge.lean#L67)

```lean
/-- The sum of the powered weighted means on the left of MI-21. -/
```

### NLA.MI21.rightMatrix

[def in preserved source](../projects/MI-21/Challenge.lean#L73)

```lean
/-- The right side uses the actual aggregate sums and the original order of
the three noncommuting factors before its final real power. -/
```

### NLA.MI21.witnessC

[def in preserved source](../projects/MI-21/Challenge.lean#L90)

```lean
/-- The first positive diagonal matrix in Colbrook's witness. -/
```

### NLA.MI21.witnessE

[def in preserved source](../projects/MI-21/Challenge.lean#L93)

```lean
/-- The second positive diagonal matrix in Colbrook's witness. -/
```

### NLA.MI21.witnessS

[def in preserved source](../projects/MI-21/Challenge.lean#L97)

```lean
/-- The source's real symmetric involution, regarded as a complex matrix.
Its unitarity is a proof obligation, not an assumption. -/
```

### NLA.MI21.witnessA

[def in preserved source](../projects/MI-21/Challenge.lean#L99)

### NLA.MI21.witnessB

[def in preserved source](../projects/MI-21/Challenge.lean#L101)

### NLA.MI21.witnessL

[def in preserved source](../projects/MI-21/Challenge.lean#L107)

```lean
/-- A candidate rational expression for the actual left matrix.
The equality to `leftMatrix` is required by the counterexample theorem. -/
```

### NLA.MI21.witnessVector

[def in preserved source](../projects/MI-21/Challenge.lean#L110)

### NLA.MI21.witnessEigenvalue

[def in preserved source](../projects/MI-21/Challenge.lean#L112)

### NLA.MI21.Paper.paper_counterexample

[theorem in preserved source](../projects/MI-21/Challenge.lean#L129)

## MI-22

### NLA.MI22.Mat

[abbrev in preserved source](../projects/MI-22/Challenge.lean#L39)

### NLA.MI22.spectralPower

[def in preserved source](../projects/MI-22/Challenge.lean#L43)

```lean
/-- The genuine real power from continuous functional calculus. It is never
replaced by entrywise powers or an assumed rational matrix certificate. -/
```

### NLA.MI22.weightedMean

[def in preserved source](../projects/MI-22/Challenge.lean#L46)

```lean
/-- The exact weighted mean, with the original noncommuting order of factors. -/
```

### NLA.MI22.leftProduct

[def in preserved source](../projects/MI-22/Challenge.lean#L51)

### NLA.MI22.singularValue

[def in preserved source](../projects/MI-22/Challenge.lean#L57)

```lean
/-- Mathlib's actual singular values of the linear map on complex Euclidean
space: descending, repeated with multiplicity, and zero beyond dimension n.
The index zero is the first singular value. No user-supplied list is involved. -/
```

### NLA.MI22.singularPrefix

[def in preserved source](../projects/MI-22/Challenge.lean#L62)

```lean
/-- The first k actual singular values, with the original one-based range
1,...,k represented as the zero-based range 0,...,k-1. -/
```

### NLA.MI22.SingularLogMajorized

[def in preserved source](../projects/MI-22/Challenge.lean#L67)

```lean
/-- Full log-majorization, including equality at n rather than weak
log-majorization. Both matrices have the same actual dimension n. -/
```

### NLA.MI22.WeightedLogMajorizationConjecture

[def in preserved source](../projects/MI-22/Challenge.lean#L73)

```lean
/-- Every positive dimension, every complex positive definite pair, and every
real t in the closed interval [0,1], exactly as in the retained canonical target. -/
```

### NLA.MI22.operatorNorm

[def in preserved source](../projects/MI-22/Challenge.lean#L79)

```lean
/-- Actual induced Euclidean operator norm, made explicit to avoid a default
entrywise matrix norm. -/
```

### NLA.MI22.witnessD

[def in preserved source](../projects/MI-22/Challenge.lean#L86)

### NLA.MI22.witnessA

[def in preserved source](../projects/MI-22/Challenge.lean#L91)

```lean
/-- This A is the same diagonal matrix as in the source, diag(256,1/256,1). -/
```

### NLA.MI22.Paper.paperB

[def in preserved source](../projects/MI-22/Challenge.lean#L147)

### NLA.MI22.Paper.paper_counterexample

[theorem in preserved source](../projects/MI-22/Challenge.lean#L181)

### NLA.MI22.Paper.paper_conjecture_false

[theorem in preserved source](../projects/MI-22/Challenge.lean#L188)

## Explicit supporting theorem anchors

These technical propositions now have explicit public theorem declarations in Challenge. Their original generated names remain unchanged. The compiler cache reuses those declarations in the fixed definitions; it does not add assumptions. Exact normalized types and original proof ownership are recorded in the supporting-theorem manifest.

### NLA.MI22.singularValue._proof_1

[Explicit statement](../Challenge.lean#L987) · [Original proof owner](../projects/MI-22/NLA/MI22/Definitions.lean#L46)

Finite-dimensionality of every complex Euclidean coordinate space, required by the fixed singularValue definition.

### Complexity.NTM.trace._proof_6

[Explicit statement](../Challenge.lean#L860) · [Original proof owner](../projects/IV-04/NLA/IV04/Complexitylib/Models/TuringMachine.lean#L676)

For i in Fin T, the bound i.val + 1 < T + 1 needed to advance the finite computation trace.

### NLA.TR27.Paper.pivotIndex._proof_2

[Explicit statement](../Challenge.lean#L562) · [Original proof owner](../projects/TR-27/NLA/TR27/PaperCoordinateDefinitions.lean#L15)

The bound 1 < D + 1 under 2 <= D, required for the coordinate pivot index.

### NLA.TR27.Paper.recoveryIndex._proof_2

[Explicit statement](../Challenge.lean#L598) · [Original proof owner](../projects/TR-27/NLA/TR27/PaperRationalDefinitions.lean#L22)

The bound j.val + 1 < D for j in Fin 4 and 5 <= D, required by recoveryIndex.

### NLA.TR27.Paper.recoveryOpenPoints._proof_2

[Explicit statement](../Challenge.lean#L605) · [Original proof owner](../projects/TR-27/NLA/TR27/PaperRationalGeometryDefinitions.lean#L15)

The implication 5 <= D -> 2 <= D used by the coordinate pivot in recoveryOpenPoints.

### Reference.LexTensorCompletion.lexIndex._proof_5

[Explicit statement](../Challenge.lean#L333) · [Original proof owner](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L206)

The right inverse law of the lexicographic index equivalence for the empty mode list.

### Reference.LexTensorCompletion.lexIndex._proof_2

[Explicit statement](../Challenge.lean#L332) · [Original proof owner](../projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean#L206)

The bound 0 < lexCard [], making zero a valid finite index for the empty mode list.

### NLA.IE21.matrixMap._proof_6

[Explicit statement](../Challenge.lean#L184) · [Original proof owner](../projects/IE-21/NLA/IE21/Definitions.lean#L60)

Joint continuity of real scalar multiplication on the Euclidean domain required by the fixed matrixMap construction.

### NLA.IE21.matrixMap._proof_4

[Explicit statement](../Challenge.lean#L185) · [Original proof owner](../projects/IE-21/NLA/IE21/Definitions.lean#L60)

Continuity of multiplication by each fixed real scalar on the Euclidean codomain required by matrixMap.
