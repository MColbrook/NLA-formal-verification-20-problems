module

public import Mathlib

@[expose] public section

/-!
Standalone statement surface for IE-22.
Definitions and selected theorem types are retained from the original sources.
Historical notices below are preserved; current review status is in the audit records.
-/


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.IE21.Definitions -/








/-!
IE-21 statement draft. These definitions contain no resolution or assumed
probabilistic/spectral facts. Required semantic bridges are in Challenge.
The source proof is by Matthew J. Colbrook. Formalization draft: George
Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology

namespace NLA.IE21

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ
abbrev Sphere (n : ℕ) := Metric.sphere (0 : Space n) 1

instance matrixMeasurableSpace (m n : ℕ) : MeasurableSpace (Mat m n) :=
  inferInstanceAs (MeasurableSpace (Fin m → Fin n → ℝ))

instance matrixBorelSpace (m n : ℕ) : BorelSpace (Mat m n) :=
  inferInstanceAs (BorelSpace (Fin m → Fin n → ℝ))

/-- Actual Euclidean surface measure, obtained from Euclidean Lebesgue measure. -/
def surfaceMeasure (n : ℕ) : Measure (Sphere n) :=
  (volume : Measure (Space n)).toSphere

/-- Normalization is literal inverse total mass, with no probability axiom. -/
def surfaceLaw (n : ℕ) : Measure (Sphere n) :=
  (surfaceMeasure n Set.univ)⁻¹ • surfaceMeasure n

/-- Ambient-space law of a uniform unit vector. -/
def sphereLaw (n : ℕ) : Measure (Space n) :=
  (surfaceLaw n).map Subtype.val

def rowsMatrix {m n : ℕ} (u : Fin m → Space n) : Mat m n :=
  fun i j => u i j

def matrixRow {m n : ℕ} (A : Mat m n) (i : Fin m) : Space n :=
  WithLp.toLp 2 (A i)

/-- Independent normalized surface-measure rows; no Gaussian surrogate. -/
def matrixLaw (m n : ℕ) : Measure (Mat m n) :=
  (Measure.pi (fun _ : Fin m => sphereLaw n)).map rowsMatrix

def matrixMap {m n : ℕ} (A : Mat m n) : Space n →L[ℝ] Space m :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap

def operatorNorm {m n : ℕ} (A : Mat m n) : ℝ := ‖matrixMap A‖

def retainedRows (θ : ℝ) (m : ℕ) : ℕ := ⌊θ * (m : ℝ)⌋₊

def retainedMatrix {m n : ℕ} (A : Mat m n) (S : Finset (Fin m)) :
    Matrix S (Fin n) ℝ := fun i j => A i.val j

def retainedNorm {m n : ℕ} (A : Mat m n) (S : Finset (Fin m))
    (x : Space n) : ℝ := ‖Matrix.toEuclideanLin (retainedMatrix A S) x‖

/-- Infimum over the exact canonical pairs. Mandatory attainment and lower-bound
theorems rule out reliance on any empty-set/default behavior of real `sInf`. -/
def deletionSingular {m n : ℕ} (θ : ℝ) (A : Mat m n) : ℝ :=
  sInf {z | ∃ (S : Finset (Fin m)) (x : Space n),
    S.card = retainedRows θ m ∧ ‖x‖ = 1 ∧ z = retainedNorm A S x}

def finiteTrim {m : ℕ} (k : ℕ) (y : Fin m → ℝ) : ℝ :=
  sInf {z | ∃ S : Finset (Fin m), S.card = k ∧ z = ∑ i ∈ S, y i}

def trimDual {m : ℕ} (k : ℕ) (y : Fin m → ℝ) (t : ℝ) : ℝ :=
  (k : ℝ) / m * t - (1 / (m : ℝ)) * ∑ i, max (t - y i) 0

def directionalTrim {m n : ℕ} (θ : ℝ) (A : Mat m n) (x : Space n) : ℝ :=
  (n : ℝ) / m * finiteTrim (retainedRows θ m) (fun i => (matrixMap A x i) ^ 2)

def normalizedDeletion {m n : ℕ} (θ : ℝ) (A : Mat m n) : ℝ :=
  (n : ℝ) / m * deletionSingular θ A ^ 2

def normalizedOperator {m n : ℕ} (A : Mat m n) : ℝ :=
  (n : ℝ) / m * operatorNorm A ^ 2

def deletionRatio {m n : ℕ} (θ : ℝ) (A : Mat m n) : ℝ :=
  deletionSingular θ A ^ 2 / operatorNorm A ^ 2

def covarianceError {m n : ℕ} (A : Mat m n) : ℝ :=
  ‖((n : ℝ) / m) • ((matrixMap A).adjoint.comp (matrixMap A)) -
    ContinuousLinearMap.id ℝ (Space n)‖

def gaussianCutoff (θ : ℝ) : ℝ :=
  sInf {a : ℝ | 0 ≤ a ∧ θ ≤ (gaussianReal 0 1).real {g | |g| ≤ a}}

/-- Exact canonical Gaussian integral; its quantile semantics must be proved. -/
def gaussianTrim (θ : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) *
    ∫ g in Set.Icc (-gaussianCutoff θ) (gaussianCutoff θ),
      g ^ 2 * Real.exp (-(g ^ 2) / 2)

/-- The dual lower-tail functional; no unproved quantile or coupling axiom. -/
def populationTrim {Ω : Type*} [MeasurableSpace Ω]
    (θ : ℝ) (μ : Measure Ω) (Y : Ω → ℝ) : ℝ :=
  sSup {z | ∃ t : ℝ, 0 ≤ t ∧ z = θ * t - ∫ ω, max (t - Y ω) 0 ∂μ}

def directionalEnergy {n : ℕ} (x u : Space n) : ℝ :=
  (n : ℝ) * (inner ℝ u x) ^ 2

/-- At zero the value is zero; Gaussian nullity of this case is a required bridge. -/
def gaussianDirection {n : ℕ} (g : Space n) : Space n := ‖g‖⁻¹ • g

def truncationScale (θ : ℝ) : ℝ := 2 / (1 - θ)

def trimmingError (θ : ℝ) (m : ℕ) (t ε δ : ℝ) : ℝ :=
  2 * truncationScale θ * ε + truncationScale θ / m + 2 * (1 + t) * δ

def finiteFailure (m n : ℕ) (t ε δ : ℝ) : ℝ :=
  2 * (9 : ℝ) ^ n * Real.exp (-(m : ℝ) * t ^ 2 / 512) +
  5 * (1 + 2 / δ) ^ n * Real.exp (-2 * (m : ℝ) * ε ^ 2)

def finiteRatioError (θ : ℝ) (m n : ℕ) (t ε δ : ℝ) : ℝ :=
  (trimmingError θ m t ε δ + Real.sqrt (2 / (n : ℝ)) + t) / (1 - t)

def aspectParameter (m n : ℕ) : ℝ :=
  32 * Real.sqrt (Real.log ((m : ℝ) / n) / ((m : ℝ) / n))

def GoodEvent (θ : ℝ) (m n : ℕ) (t ε δ : ℝ) : Set (Mat m n) :=
  {A | covarianceError A ≤ t ∧ ∀ x : Space n, ‖x‖ = 1 →
    |directionalTrim θ A x - gaussianTrim θ| ≤
      trimmingError θ m t ε δ + Real.sqrt (2 / (n : ℝ))}

/-- Independent rows with the actual normalized surface law on any probability space. -/
def IndependentSphereRows {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (μ : Measure Ω) (A : Ω → Mat m n) : Prop :=
  Measurable A ∧
    iIndepFun (fun i ω => matrixRow (A ω) i) μ ∧
    ∀ i, μ.map (fun ω => matrixRow (A ω) i) = sphereLaw n

end NLA.IE21
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.IE22.Definitions -/


/-!
UNREVIEWED IE-22 statement draft. No proof implementation is present.
IE-21 is imported unchanged; portable dependency packaging is not selected yet.
Original mathematical proof: Matthew J. Colbrook.
Formalization draft: George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE22
open NLA.IE21

/-- Literal unit Euclidean row condition. -/
def UnitRows {m n : ℕ} (A : Mat m n) : Prop :=
  ∀ i, ‖matrixRow A i‖ = 1

/-- The canonical unsquared, normalized singular statistic. -/
def normalizedSingular {m n : ℕ} (θ : ℝ) (A : Mat m n) : ℝ :=
  Real.sqrt ((n : ℝ) / m) * deletionSingular θ A

def unitRowValues (θ : ℝ) (m n : ℕ) : Set ℝ :=
  {z | ∃ A : Mat m n, UnitRows A ∧ z = normalizedSingular θ A}

/-- Literal canonical supremum M; nonempty/finite/attained semantics are compulsory. -/
def extremalValue (θ : ℝ) (m n : ℕ) : ℝ := sSup (unitRowValues θ m n)

def sharpConstant (θ : ℝ) : ℝ := Real.sqrt (gaussianTrim θ)

/-- The original two-threshold eventual-uniform property, with epsilon outside
both existential thresholds. The natural thresholds are integers. -/
def EventualUniformUpper (θ C : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N R : ℕ,
    ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → N ≤ n → (R : ℝ) ≤ (m : ℝ) / n →
      extremalValue θ m n ≤ C + ε

/-- Actual restriction of A to an isometrically embedded Euclidean subspace. -/
def projectedMatrix {m n d : ℕ} (A : Mat m n)
    (J : Space d →ₗᵢ[ℝ] Space n) : Mat m d :=
  fun i j => inner ℝ (matrixRow A i) (J (EuclideanSpace.single j 1))

/-- The canonical threshold dual evaluated on correlated projected Gaussian rows. -/
def projectedObjective {m d : ℕ} (θ : ℝ) (B : Mat m d) (t : ℝ)
    (g : Space d) : ℝ :=
  trimDual (retainedRows θ m) (fun i => (matrixMap B g i) ^ 2) t

def projectedEnergy {m d : ℕ} (B : Mat m d) (g : Space d) : ℝ :=
  ‖matrixMap B g‖ ^ 2 / m

def gramMatrix {m d : ℕ} (B : Mat m d) : Matrix (Fin d) (Fin d) ℝ :=
  B.transpose * B

/-- The three source exceptional probabilities, with retained dimension d. -/
def projectionFailure (θ : ℝ) (d r : ℕ) (δ : ℝ) : ℝ :=
  2 / ((r : ℝ) + 1) +
    4 * truncationScale θ * (truncationScale θ / δ + 2) /
      (((r : ℝ) + 1) * δ ^ 2) +
    2 / ((d : ℝ) * δ ^ 2)

def ProjectionGood {m d : ℕ} (θ : ℝ) (B : Mat m d) (δ : ℝ) : Set (Space d) :=
  {g | projectedEnergy B g ≤ 2 ∧ (1 - δ) * (d : ℝ) ≤ ‖g‖ ^ 2 ∧
    ∀ t : ℝ, 0 ≤ t → t ≤ truncationScale θ →
      projectedObjective θ B t g ≤ gaussianTrim θ + 2 * δ}

def deterministicFailure (θ : ℝ) (n r : ℕ) (δ : ℝ) : ℝ :=
  projectionFailure θ (n - r) r δ

/-- Exact boxed deterministic bound; n-r is positive in all stated uses. -/
def deterministicBound (θ : ℝ) (n r : ℕ) (δ : ℝ) : ℝ :=
  (n : ℝ) / (((n - r : ℕ) : ℝ) * (1 - δ)) * (gaussianTrim θ + 2 * δ)

def deletionSchedule (n : ℕ) : ℕ := ⌊Real.rpow (n : ℝ) (2 / 3 : ℝ)⌋₊
def errorSchedule (n : ℕ) : ℝ := Real.rpow (n : ℝ) (-(1 / 6 : ℝ))

end NLA.IE22
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.IE22.PaperChallenge -/


set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE22.Paper
open NLA.IE21

theorem paper_high_aspect_supremum_limit (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop) :
    Tendsto (fun j => extremalValue θ (m j) (n j)) atTop (𝓝 (sharpConstant θ)) := by
  sorry

theorem paper_universal_squared_rate (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ m n : ℕ, 1 ≤ m → N ≤ n →
        (∀ A : Mat m n, UnitRows A →
          normalizedDeletion θ A ≤ gaussianTrim θ + C * errorSchedule n) ∧
        extremalValue θ m n ^ 2 ≤ gaussianTrim θ + C * errorSchedule n := by
  sorry


end NLA.IE22.Paper
end
end
