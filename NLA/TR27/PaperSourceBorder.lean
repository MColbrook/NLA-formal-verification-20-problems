module

public import NLA.TR27.PaperSourceBorderDefinitions
public import NLA.TR27.PaperHankelPolynomial

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical LinearAlgebra.Projectivization
open Polynomial
namespace NLA.TR27.Paper

theorem source_closure_agrees (D : ℕ) (I : Ideal (MvPolynomial (Fin (D+1)) ℂ))
    (Y : Set (ℙ ℂ (CurveSpace D))) :
    sourceProjectiveClosure D Y =
      (ProjectiveVariety.mk (D+1) (LinearEquiv.refl ℂ _) I).zariskiClosure Y := rfl

theorem curve_sum_projective_rank {D k : ℕ} (b : Fin k → ℂ) (t : Fin k → Option ℂ)
    (v : CurveSpace D) (hv : v ≠ 0) (heq : v = ∑ i, b i • curveVector D (t i)) :
    ProjectiveRankAtMost (curvePoints D) k (Projectivization.mk ℂ v hv) := by
  let q : Fin k → ℙ ℂ (CurveSpace D) := fun i =>
    Projectivization.mk ℂ (curveVector D (t i)) (curveVector_ne_zero D _)
  refine ⟨k, le_rfl, q, ?_, ?_⟩
  · intro i
    exact ⟨t i, represents_mk _ _⟩
  · rw [projective_span_mk, heq]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply (projective_span_mk (Set.range q) _ (curveVector_ne_zero D _)).mp
    exact Projectivization.Subspace.subset_span _ (Set.mem_range_self i)

theorem homogeneous_vanishes_curve_sum {D k n : ℕ} (hn : 1 ≤ n) (hk : k ≤ n)
    (f : MvPolynomial (Fin (D+1)) ℂ) (d : ℕ) (hf : f.IsHomogeneous d)
    (hvan : ∀ q, ProjectiveRankAtMost (curvePoints D) n q → MvPolynomial.eval q.rep f = 0)
    (b : Fin k → ℂ) (t : Fin k → Option ℂ) :
    MvPolynomial.eval (∑ i, b i • curveVector D (t i)) f = 0 := by
  have hnonzero (l : ℕ) (hl : l ≤ n) (b : Fin l → ℂ) (t : Fin l → Option ℂ)
      (hv : (∑ i, b i • curveVector D (t i)) ≠ 0) :
      MvPolynomial.eval (∑ i, b i • curveVector D (t i)) f = 0 := by
    let v := ∑ i, b i • curveVector D (t i)
    have hp := hvan (Projectivization.mk ℂ v hv)
      (projectiveRankAtMost_mono _ _ hl (curve_sum_projective_rank b t v hv rfl))
    obtain ⟨c, hc, heq⟩ := represents_mk v hv
    rw [heq, homogeneous_eval_smul f d hf] at hp
    exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero d hc)
  by_cases hv : (∑ i, b i • curveVector D (t i)) = 0
  · have hbase := hnonzero 1 hn (fun _ => 1) (fun _ => some 0)
      (by simpa using curveVector_ne_zero D (some 0))
    simp only [one_smul, Fin.sum_univ_one] at hbase
    have h := homogeneous_eval_smul f d hf 0 (curveVector D (some 0))
    simpa only [hv, zero_smul, hbase, mul_zero] using h
  · exact hnonzero k hk b t hv

theorem secantSlope_zero (D : ℕ) : secantSlope D 0 = tangentVector D := by
  ext j
  by_cases hj : j.val = 0
  · simp [secantSlope, tangentVector, hj]
  · by_cases hj1 : j.val = 1
    · simp [secantSlope, tangentVector, hj1]
    · have hpos : j.val-1 ≠ 0 := by omega
      simp [secantSlope, tangentVector, hj, hj1, hpos]

theorem secantSlope_divided_difference (D : ℕ) (t : ℂ) (ht : t ≠ 0) :
    secantSlope D t = t⁻¹ • (curveVector D (some t) - curveVector D (some 0)) := by
  ext j
  by_cases hj : j.val = 0
  · simp [secantSlope, curveVector, hj]
  · simp only [secantSlope, if_neg hj, curveVector, Pi.smul_apply, Pi.sub_apply,
      zero_pow hj, sub_zero, smul_eq_mul]
    have hp : t^j.val = t^(j.val-1)*t := by
      rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ j.val by omega)]
    rw [hp]
    field_simp

theorem centerDegeneration_zero (D r : ℕ) (a : Fin r → ℂ) :
    centerDegeneration D r a 0 = projectionCenter D r (fun i => some (a i)) := by
  rw [centerDegeneration, secantSlope_zero]
  rfl

theorem centerDegeneration_sum (D r : ℕ) (a : Fin r → ℂ) (t : ℂ) (ht : t ≠ 0) :
    centerDegeneration D r a t =
      ∑ i : Fin (r+2), ((Fin.cons t⁻¹ (Fin.cons (-t⁻¹) (fun _ : Fin r => (-1 : ℂ))) :
          Fin (r+2) → ℂ) i) •
        curveVector D ((Fin.cons (some t) (Fin.cons (some 0) (fun j => some (a j))) :
          Fin (r+2) → Option ℂ) i) := by
  rw [centerDegeneration, secantSlope_divided_difference D t ht,
    Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [sub_eq_add_neg, Finset.sum_neg_distrib, add_assoc]

def centerCoordinatePolynomial (D r : ℕ) (a : Fin r → ℂ) (j : Fin (D+1)) : ℂ[X] :=
  (if j.val = 0 then 0 else Polynomial.X^(j.val-1)) -
    Polynomial.C (∑ i, a i ^ j.val)

theorem eval_centerCoordinatePolynomial (D r : ℕ) (a : Fin r → ℂ) (j : Fin (D+1)) (t : ℂ) :
    Polynomial.eval t (centerCoordinatePolynomial D r a j) = centerDegeneration D r a t j := by
  by_cases hj : j.val = 0 <;>
    simp [centerCoordinatePolynomial, centerDegeneration, secantSlope, curveVector, hj,
      Finset.sum_apply, Polynomial.eval_finsetSum]

def centerSubstitution (D r : ℕ) (a : Fin r → ℂ) :
    MvPolynomial (Fin (D+1)) ℂ →ₐ[ℂ] ℂ[X] :=
  MvPolynomial.aeval (centerCoordinatePolynomial D r a)

theorem eval_centerSubstitution (D r : ℕ) (a : Fin r → ℂ)
    (f : MvPolynomial (Fin (D+1)) ℂ) (t : ℂ) :
    Polynomial.eval t (centerSubstitution D r a f) = MvPolynomial.eval (centerDegeneration D r a t) f := by
  simpa only [centerSubstitution, Polynomial.coe_aeval_eq_eval, eval_centerCoordinatePolynomial,
    MvPolynomial.aeval_eq_eval] using
    (MvPolynomial.comp_aeval_apply (centerCoordinatePolynomial D r a) (Polynomial.aeval t) f)

theorem center_in_rank_closure (D r : ℕ) (a : Fin r → ℂ)
    (p : ℙ ℂ (CurveSpace D)) (hp : Represents (projectionCenter D r (fun i => some (a i))) p) :
    p ∈ sourceProjectiveClosure D {q | ProjectiveRankAtMost (curvePoints D) (r+2) q} := by
  intro f d hf hvan
  have hpoly : centerSubstitution D r a f = 0 := by
    have hprod : Polynomial.X * centerSubstitution D r a f = 0 := by
      apply Polynomial.funext
      intro t
      by_cases ht : t = 0
      · simp [ht]
      · have hz : Polynomial.eval t (centerSubstitution D r a f) = 0 := by
          rw [eval_centerSubstitution, centerDegeneration_sum D r a t ht]
          exact homogeneous_vanishes_curve_sum (by omega) le_rfl f d hf hvan _ _
        simp [hz]
    exact (mul_eq_zero.mp hprod).resolve_left Polynomial.X_ne_zero
  have hz : MvPolynomial.eval (projectionCenter D r (fun i => some (a i))) f = 0 := by
    rw [← centerDegeneration_zero, ← eval_centerSubstitution, hpoly, Polynomial.eval_zero]
  obtain ⟨c, hc, heq⟩ := hp
  rw [heq, homogeneous_eval_smul f d hf, hz, mul_zero]

theorem source_closure_mono {D : ℕ} {Y Z : Set (ℙ ℂ (CurveSpace D))} (hYZ : Y ⊆ Z) :
    sourceProjectiveClosure D Y ⊆ sourceProjectiveClosure D Z := by
  intro p hp f d hf hvan
  exact hp f d hf (fun q hq => hvan q (hYZ hq))

theorem center_not_lower_rank_closure {D r : ℕ} (hD : 2*(r+1) ≤ D)
    (a : Fin r → ℂ) (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0)
    (p : ℙ ℂ (CurveSpace D)) (hp : Represents (projectionCenter D r (fun i => some (a i))) p) :
    p ∉ sourceProjectiveClosure D {q | ProjectiveRankAtMost (curvePoints D) (r+1) q} := by
  intro hclosure
  have hz := hclosure (hankelPolynomial (r+1) hD) (r+2)
    (hankelPolynomial_homogeneous hD) (fun q hq => hankelPolynomial_vanishes_projective_rank hD q hq)
  obtain ⟨c, hc, heq⟩ := hp
  rw [heq, homogeneous_eval_smul _ _ (hankelPolynomial_homogeneous hD)] at hz
  exact hankelPolynomial_center_nonzero hD a ha ha0
    ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hc))

theorem center_border_rank_minimum {D r : ℕ} (hD : 2*(r+1) ≤ D)
    (a : Fin r → ℂ) (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0)
    (p : ℙ ℂ (CurveSpace D)) (hp : Represents (projectionCenter D r (fun i => some (a i))) p) :
    IsLeast {k | p ∈ sourceProjectiveClosure D {q | ProjectiveRankAtMost (curvePoints D) k q}} (r+2) := by
  refine ⟨center_in_rank_closure D r a p hp, ?_⟩
  intro k hk
  by_contra hsmall
  have hk' : k ≤ r+1 := by omega
  exact center_not_lower_rank_closure hD a ha ha0 p hp
    (source_closure_mono (fun q hq => projectiveRankAtMost_mono _ _ hk' hq) hk)

theorem center_border_rank {D r : ℕ} (hD : 2*(r+1) ≤ D)
    (a : Fin r → ℂ) (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0) :
    ∃ hz : projectionCenter D r (fun i => some (a i)) ≠ 0,
      sourceBorderRank D (Projectivization.mk ℂ _ hz) = r+2 := by
  have hz : projectionCenter D r (fun i => some (a i)) ≠ 0 := by
    intro hzero
    have h := hankelPolynomial_center_nonzero hD a ha ha0
    apply h
    rw [hzero, hankelPolynomial_eval]
    have heq : sourceHankel (r+1) hD (0 : CurveSpace D) = 0 := rfl
    rw [heq, Matrix.det_zero]
  refine ⟨hz, ?_⟩
  exact (center_border_rank_minimum hD a ha ha0 _ (represents_mk _ _)).csInf_eq

#print axioms center_border_rank
#print axioms center_in_rank_closure
end NLA.TR27.Paper
