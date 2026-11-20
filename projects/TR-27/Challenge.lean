module
public import Mathlib
@[expose] public section
/-! Standalone exact statement and semantic-definition surface for TR-27.
Every helper theorem placeholder is explicitly compared and genuinely proved on the Solution side. -/


section
/- Original module: NLA.TR27.Definitions -/
/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original mathematical counterexample: Matthew J. Colbrook.
AI-assisted statement draft. No completed proof or verification is claimed.
-/










set_option autoImplicit false

noncomputable section
open scoped BigOperators TensorProduct LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra

namespace NLA.TR27

/-  A finite coordinate presentation of a projective algebraic subset of an
arbitrary complex vector space. No geometric admissibility or rank conclusion
is built into these data; those properties are stated separately below. -/
structure ProjectiveVariety (W : Type*) [AddCommGroup W] [Module ℂ W] where
  dimension : ℕ
  coordinates : W ≃ₗ[ℂ] (Fin dimension → ℂ)
  ideal : Ideal (MvPolynomial (Fin dimension) ℂ)

namespace ProjectiveVariety

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-  The entire affine zero locus, transported by the actual coordinate map. -/
def cone (X : ProjectiveVariety W) : Set W :=
  X.coordinates ⁻¹' MvPolynomial.zeroLocus ℂ X.ideal

/-  Projective points of the entire zero locus, using Mathlib representatives.
Homogeneity ensures representative independence; Challenge requires its proof. -/
def points (X : ProjectiveVariety W) : Set (ℙ ℂ W) :=
  {p | p.rep ∈ X.cone}

/-  Classical reduced irreducible nondegenerate projective-variety conditions
in homogeneous coordinates. There is no rank, decomposition or answer premise. -/
def Admissible (X : ProjectiveVariety W) : Prop :=
  X.ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin X.dimension) ℂ) ∧
  X.ideal.IsPrime ∧
  IsReduced ((MvPolynomial (Fin X.dimension) ℂ) ⧸ X.ideal) ∧
  (∃ v : W, v ∈ X.cone ∧ v ≠ 0) ∧
  Submodule.span ℂ X.cone = ⊤

/-  Common zero set of all homogeneous equations vanishing on the given
projective point set. The degree ranges over every natural number. -/
def zariskiClosure (X : ProjectiveVariety W) (Y : Set (ℙ ℂ W)) : Set (ℙ ℂ W) :=
  {p | ∀ (f : MvPolynomial (Fin X.dimension) ℂ) (d : ℕ),
    f.IsHomogeneous d →
    (∀ q ∈ Y, MvPolynomial.eval (X.coordinates q.rep) f = 0) →
    MvPolynomial.eval (X.coordinates p.rep) f = 0}

def IsClosed (X : ProjectiveVariety W) (Y : Set (ℙ ℂ W)) : Prop :=
  X.zariskiClosure Y = Y

/-  The classical closed-set union criterion, stated at complex points rather
than the generic prime-ideal points of a scheme spectrum. -/
def IsIrreducible (X : ProjectiveVariety W) (Y : Set (ℙ ℂ W)) : Prop :=
  Y.Nonempty ∧ ∀ A B : Set (ℙ ℂ W), X.IsClosed A → X.IsClosed B →
    Y ⊆ A ∪ B → Y ⊆ A ∨ Y ⊆ B

/-  Ordinary all-polynomial affine Zariski closure in the same coordinates. -/
end ProjectiveVariety

section RankDefinitions

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-  At most r projective points, with their actual projective linear span.
Lists may repeat points; the length k may be zero. -/
def ProjectiveRankAtMost (X : Set (ℙ ℂ W)) (r : ℕ) (p : ℙ ℂ W) : Prop :=
  ∃ k : ℕ, k ≤ r ∧ ∃ q : Fin k → ℙ ℂ W,
    (∀ i, q i ∈ X) ∧ p ∈ Projectivization.Subspace.span (Set.range q)

/-  Least spanning length. The Challenge separately requires nonempty length
sets for admissible varieties, so no default infimum is used as evidence. -/
def projectiveRank (X : Set (ℙ ℂ W)) (p : ℙ ℂ W) : ℕ :=
  sInf {r : ℕ | ProjectiveRankAtMost X r p}

def borderRank (X : ProjectiveVariety W) (p : ℙ ℂ W) : ℕ :=
  sInf {r : ℕ | p ∈ X.zariskiClosure {q | ProjectiveRankAtMost X.points r q}}

/-  Affine form of a span decomposition, with unrestricted complex scalars. -/
def Represents (v : W) (p : ℙ ℂ W) : Prop :=
  ∃ a : ℂ, a ≠ 0 ∧ p.rep = a • v

/-  The full Segre image, formed in the ordinary unmerged tensor product. -/
end RankDefinitions

/-  The complete original universal implication, over arbitrary complex vector
spaces equipped with a finite coordinate presentation of an admissible variety.
The coordinates do not constrain its dimension, variety, points or coefficients.
All finite-dimensional complex spaces admit such coordinates (required below). -/
end NLA.TR27
end
end


section
/- Original module: NLA.TR27.PaperCurveDefinitions -/


set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

abbrev CurveSpace (D : ℕ) := Fin (D + 1) → ℂ

/-  The actual degree-D rational normal curve, with its point at infinity. -/
def curveVector (D : ℕ) : Option ℂ → CurveSpace D
  | some t => fun j => t ^ (j : ℕ)
  | none => fun j => if (j : ℕ) = D then 1 else 0

def tangentVector (D : ℕ) : CurveSpace D := fun j => if (j : ℕ) = 1 then 1 else 0

end NLA.TR27.Paper
end
end


section
/- Original module: NLA.TR27.PaperProjectiveTopologyDefinitions -/





set_option autoImplicit false
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

/-  The usual quotient topology from the nonzero complex coordinate vectors.
This is defined independently of any particular curve or parametrization. -/
@[instance_reducible] def coordinateProjectiveTopology (n : ℕ) : TopologicalSpace (ℙ ℂ (Fin n → ℂ)) :=
  TopologicalSpace.coinduced (Projectivization.mk' ℂ)
    (inferInstance : TopologicalSpace {v : Fin n → ℂ // v ≠ 0})

end NLA.TR27.Paper
end
end


section
/- Original module: NLA.TR27.PaperProjectiveChartDefinitions -/



set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

def projectiveCoordinateRatio {n : ℕ} (i j : Fin n) (p : ℙ ℂ (Fin n → ℂ)) : ℂ :=
  p.rep j / p.rep i

end NLA.TR27.Paper
end
end


section
/- Original module: NLA.TR27.PaperProjectionDefinitions -/


set_option autoImplicit false
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

def projectionCenter (D r : ℕ) (a : Fin r → Option ℂ) : CurveSpace D :=
  tangentVector D - ∑ i, curveVector D (a i)

def centerLine (D r : ℕ) (a : Fin r → Option ℂ) : Submodule ℂ (CurveSpace D) :=
  Submodule.span ℂ {projectionCenter D r a}

abbrev QuotientSpace (D r : ℕ) (a : Fin r → Option ℂ) := CurveSpace D ⧸ centerLine D r a

def quotientProjection (D r : ℕ) (a : Fin r → Option ℂ) :
    CurveSpace D →ₗ[ℂ] QuotientSpace D r a := (centerLine D r a).mkQ

def quotientCurve (D r : ℕ) (a : Fin r → Option ℂ) (t : Option ℂ) : QuotientSpace D r a :=
  quotientProjection D r a (curveVector D t)

def quotientTangent (D r : ℕ) (a : Fin r → Option ℂ) : QuotientSpace D r a :=
  quotientProjection D r a (tangentVector D)

def quotientPoints (D r : ℕ) (a : Fin r → Option ℂ) : Set (ℙ ℂ (QuotientSpace D r a)) :=
  {p | ∃ t : Option ℂ, Represents (quotientCurve D r a t) p}

def chosenParameters (r : ℕ) : Fin r → Option ℂ := fun i => some (((i : ℕ) + 1 : ℕ) : ℂ)

def familyDegree (r m : ℕ) : ℕ := r ^ m + r

end NLA.TR27.Paper
end
end


section
/- Original module: NLA.TR27.PaperIntegralDefinitions -/



set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.TR27.Paper

def chosenPowerSum (r j : ℕ) : ℂ := ∑ i : Fin r, ((i.val+1 : ℕ) : ℂ)^j
def chosenPivot (r : ℕ) : ℂ := chosenPowerSum r 1 - 1

end NLA.TR27.Paper
end
end


section
/- Original module: NLA.TR27.PaperCoordinateDefinitions -/





set_option autoImplicit false
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

def pivotIndex (D : ℕ) (hD : 2 ≤ D) : Fin (D+1) := ⟨1, by omega⟩

/-  Source coordinates 0,2,...,D, in their original order. -/
def retainedIndex (D : ℕ) (hD : 2 ≤ D) : Fin D → Fin (D+1) :=
  (pivotIndex D hD).succAbove

def coordinateProjection (D r : ℕ) (hD : 2 ≤ D) : CurveSpace D →ₗ[ℂ] (Fin D → ℂ) where
  toFun w j := chosenPivot r * w (retainedIndex D hD j) -
    chosenPowerSum r (retainedIndex D hD j).val * w (pivotIndex D hD)
  map_add' u v := by ext j; simp only [Pi.add_apply]; ring
  map_smul' c w := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

end NLA.TR27.Paper
end
end


section
/- Original module: NLA.TR27.PaperHomogeneousDefinitions -/




set_option autoImplicit false
noncomputable section
namespace NLA.TR27.Paper

abbrev ImageCoordinatePolynomial (D : ℕ) := MvPolynomial (Fin D) ℂ
abbrev CurveParameterPolynomial := MvPolynomial (Fin 2) ℂ

def imageHomogeneousCoordinate (D r : ℕ) (hD : 2 ≤ D) (j : Fin D) :
    CurveParameterPolynomial :=
  MvPolynomial.C (chosenPivot r) * MvPolynomial.X 0 ^ (D-(retainedIndex D hD j).val) *
    MvPolynomial.X 1 ^ (retainedIndex D hD j).val -
  MvPolynomial.C (chosenPowerSum r (retainedIndex D hD j).val) *
    MvPolynomial.X 0 ^ (D-1) * MvPolynomial.X 1

def imageSubstitution (D r : ℕ) (hD : 2 ≤ D) :
    ImageCoordinatePolynomial D →ₐ[ℂ] CurveParameterPolynomial :=
  MvPolynomial.aeval (imageHomogeneousCoordinate D r hD)

def imageHomogeneousMap (D r : ℕ) (hD : 2 ≤ D) (u : Fin 2 → ℂ) : Fin D → ℂ :=
  fun j => MvPolynomial.eval u (imageHomogeneousCoordinate D r hD j)

def imageIdeal (D r : ℕ) (hD : 2 ≤ D) : Ideal (ImageCoordinatePolynomial D) :=
  RingHom.ker (imageSubstitution D r hD)

end NLA.TR27.Paper
end
end


section
/- Original module: NLA.TR27.PaperSmoothGraphDefinitions -/




set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace NLA.TR27.Paper
attribute [local instance] coordinateProjectiveTopology

/-  The whole projective zero set of the actual homogeneous image ideal,
in the certified quotient coordinates. -/
def coordinateImagePoints (D r : ℕ) (hD : 2 ≤ D) : Set (ℙ ℂ (Fin D → ℂ)) :=
  {p | p.rep ∈ MvPolynomial.zeroLocus ℂ (imageIdeal D r hD)}

/-  Explicit smooth-curve geometry: in an actual standard affine chart, the
WHOLE set near p is the graph of analytic functions of one free coordinate.
The neighborhood uses the usual ambient projective quotient topology. -/
def HasProjectiveAnalyticGraph {n : ℕ} (X : Set (ℙ ℂ (Fin n → ℂ))) (p : ℙ ℂ (Fin n → ℂ)) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ p.rep i ≠ 0 ∧
    ∃ V : Set ℂ, ∃ W : Set (ℙ ℂ (Fin n → ℂ)), ∃ H : ℂ → ℙ ℂ (Fin n → ℂ),
      IsOpen V ∧ projectiveCoordinateRatio i j p ∈ V ∧ IsOpen W ∧ p ∈ W ∧
      X ∩ W = H '' V ∧ H (projectiveCoordinateRatio i j p) = p ∧
      (∀ z ∈ V, (H z).rep i ≠ 0 ∧ projectiveCoordinateRatio i j (H z) = z) ∧
      (∀ k, AnalyticOnNhd ℂ (fun z => projectiveCoordinateRatio i k (H z)) V)

end NLA.TR27.Paper
end
end


section
/- Original module: NLA.TR27.PaperCoordinates -/





set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

theorem coordinateProjection_surjective (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r) :
    Function.Surjective (coordinateProjection D r hD) := by sorry
theorem coordinateProjection_kernel (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r) :
    LinearMap.ker (coordinateProjection D r hD) = centerLine D r (chosenParameters r) := by sorry
noncomputable def quotientCoordinateEquiv (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r) :
    QuotientSpace D r (chosenParameters r) ≃ₗ[ℂ] (Fin D → ℂ) :=
  (Submodule.quotEquivOfEq _ _ (coordinateProjection_kernel D r hD hr).symm).trans
    ((coordinateProjection D r hD).quotKerEquivOfSurjective
      (coordinateProjection_surjective D r hD hr))

end NLA.TR27.Paper
end
end


section
/- Original module: NLA.TR27.PaperImageGeometry -/





set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.TR27.Paper
attribute [local instance] MvPolynomial.gradedAlgebra

theorem imageHomogeneousMap_eq_zero_iff (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r)
    (u : Fin 2 → ℂ) : imageHomogeneousMap D r hD u = 0 ↔ u = 0 := by sorry
end NLA.TR27.Paper
end
end


section
/- Original module: NLA.TR27.PaperProjectiveCurveDefinitions -/



set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

/-  The actual degree-D homogeneous parametrization on the standard
projective line. Nonvanishing follows from the previously checked no-basepoint theorem. -/
def projectiveCurveMap (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r)
    (p : ℙ ℂ (Fin 2 → ℂ)) : ℙ ℂ (Fin D → ℂ) :=
  Projectivization.mk ℂ (imageHomogeneousMap D r hD p.rep)
    (fun h => p.rep_nonzero ((imageHomogeneousMap_eq_zero_iff D r hD hr p.rep).mp h))

end NLA.TR27.Paper
end
end


section
/- Original module: NLA.TR27.PaperRationalDefinitions -/



set_option autoImplicit false
noncomputable section
namespace NLA.TR27.Paper

def recoveryMomentA (r : ℕ) : ℂ :=
  chosenPowerSum r 3 * chosenPowerSum r 5 - chosenPowerSum r 4 ^ 2

def recoveryMomentB (r : ℕ) : ℂ :=
  chosenPowerSum r 3 * chosenPowerSum r 4 - chosenPowerSum r 2 * chosenPowerSum r 5

def recoveryMomentC (r : ℕ) : ℂ :=
  chosenPowerSum r 2 * chosenPowerSum r 4 - chosenPowerSum r 3 ^ 2

/-  Coordinates numbered 2,3,4,5 in the source, retained after deleting number 1. -/
def recoveryIndex (D : ℕ) (hD : 5 ≤ D) (j : Fin 4) : Fin D := ⟨j.val+1, by omega⟩

def recoveryDenominator (D r : ℕ) (hD : 5 ≤ D) : ImageCoordinatePolynomial D :=
  MvPolynomial.C (recoveryMomentA r) * MvPolynomial.X (recoveryIndex D hD 0) +
  MvPolynomial.C (recoveryMomentB r) * MvPolynomial.X (recoveryIndex D hD 1) +
  MvPolynomial.C (recoveryMomentC r) * MvPolynomial.X (recoveryIndex D hD 2)

def recoveryNumerator (D r : ℕ) (hD : 5 ≤ D) : ImageCoordinatePolynomial D :=
  MvPolynomial.C (recoveryMomentA r) * MvPolynomial.X (recoveryIndex D hD 1) +
  MvPolynomial.C (recoveryMomentB r) * MvPolynomial.X (recoveryIndex D hD 2) +
  MvPolynomial.C (recoveryMomentC r) * MvPolynomial.X (recoveryIndex D hD 3)

def recoveryPolynomial (r : ℕ) : Polynomial ℂ :=
  Polynomial.C (chosenPivot r) * Polynomial.X^2 *
    (Polynomial.C (recoveryMomentA r) + Polynomial.C (recoveryMomentB r)*Polynomial.X +
      Polynomial.C (recoveryMomentC r)*Polynomial.X^2)

def rationalRecovery (D r : ℕ) (hD : 5 ≤ D) (w : Fin D → ℂ) : ℂ :=
  MvPolynomial.eval w (recoveryNumerator D r hD) /
    MvPolynomial.eval w (recoveryDenominator D r hD)

end NLA.TR27.Paper
end
end


section
/- Original module: NLA.TR27.PaperRationalGeometryDefinitions -/



set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

/-  The actual quotient-curve points where the explicit linear denominator
does not vanish. Coordinates are the already certified quotient coordinates. -/
def recoveryOpenPoints (D r : ℕ) (hD : 5 ≤ D) (hr : 3 ≤ r) :
    Set (ℙ ℂ (QuotientSpace D r (chosenParameters r))) :=
  {p | p ∈ quotientPoints D r (chosenParameters r) ∧
    MvPolynomial.eval (quotientCoordinateEquiv D r (by omega) hr p.rep)
      (recoveryDenominator D r hD) ≠ 0}

end NLA.TR27.Paper
end
end


section
/- Original module: NLA.TR27.PaperProductDefinitions -/




set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct LinearAlgebra.Projectivization
namespace NLA.TR27.Paper
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem tensor_reps_nonzero (k : ℕ) (q : Fin k → ℙ ℂ W) :
    PiTensorProduct.tprod ℂ (fun i => (q i).rep) ≠ 0 := by sorry
def tensorPoint (k : ℕ) (q : Fin k → ℙ ℂ W) : ℙ ℂ (⨂[ℂ] _ : Fin k, W) :=
  Projectivization.mk ℂ (PiTensorProduct.tprod ℂ (fun i => (q i).rep)) (tensor_reps_nonzero k q)

def powerPoint (p : ℙ ℂ W) (k : ℕ) : ℙ ℂ (⨂[ℂ] _ : Fin k, W) :=
  tensorPoint k (fun _ => p)

/-  Full Segre product, with separately and freely selected projective factors. -/
def productPoints (X : Set (ℙ ℂ W)) (k : ℕ) : Set (ℙ ℂ (⨂[ℂ] _ : Fin k, W)) :=
  {z | ∃ q : Fin k → ℙ ℂ W, (∀ i, q i ∈ X) ∧
    Represents (PiTensorProduct.tprod ℂ (fun i => (q i).rep)) z}

end NLA.TR27.Paper
end
end


section
/- Original module: NLA.TR27.FullFamilyChallenge -/





set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace NLA.TR27.Paper
attribute [local instance] coordinateProjectiveTopology

theorem paper_full_family (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m) :
    ∃ hD : 2 ≤ familyDegree r m, ∃ h5 : 5 ≤ familyDegree r m,
      let D := familyDegree r m
      let E := quotientCoordinateEquiv D r hD hr
      let X := ProjectiveVariety.mk D E (imageIdeal D r hD)
      (∀ w, E (quotientProjection D r (chosenParameters r) w) = coordinateProjection D r hD w) ∧
      X.Admissible ∧ X.IsClosed X.points ∧ X.IsIrreducible X.points ∧
      X.points = quotientPoints D r (chosenParameters r) ∧
      Set.range (projectiveCurveMap D r hD hr) = coordinateImagePoints D r hD ∧
      (∀ p ∈ coordinateImagePoints D r hD, HasProjectiveAnalyticGraph (coordinateImagePoints D r hD) p) ∧
      Topology.IsClosedEmbedding (projectiveCurveMap D r hD hr) ∧
      recoveryPolynomial r ≠ 0 ∧
      Set.Finite {t : ℂ | Polynomial.eval t (recoveryPolynomial r) = 0} ∧
      (recoveryOpenPoints D r h5 hr).Nonempty ∧
      X.IsClosed {p | MvPolynomial.eval (E p.rep) (recoveryDenominator D r h5) = 0} ∧
      X.zariskiClosure (recoveryOpenPoints D r h5 hr) = X.points ∧
      (∃ e : {t : ℂ // Polynomial.eval t (recoveryPolynomial r) ≠ 0} ≃
          {p // p ∈ recoveryOpenPoints D r h5 hr},
        (∀ t, Represents (quotientCurve D r (chosenParameters r) (some t.val)) (e t).val) ∧
        (∀ p, (e.symm p).val = rationalRecovery D r h5 (E p.val.rep))) ∧
      (∃ hv : quotientTangent D r (chosenParameters r) ≠ 0,
        borderRank X (Projectivization.mk ℂ _ hv) = 2 ∧
        projectiveRank X.points (Projectivization.mk ℂ _ hv) = r ∧
        ∀ k : ℕ, 1 ≤ k → k ≤ m →
          projectiveRank (productPoints X.points k) (powerPoint (Projectivization.mk ℂ _ hv) k) = r^k) := by sorry
end NLA.TR27.Paper
end
end
