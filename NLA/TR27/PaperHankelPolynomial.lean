module

public import NLA.TR27.PaperHankelPolynomialDefinitions
public import NLA.TR27.PaperHankelRank

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

theorem hankelPolynomial_eval {D n : ℕ} (hD : 2*n ≤ D) (v : CurveSpace D) :
    MvPolynomial.eval v (hankelPolynomial n hD) = (sourceHankel n hD v).det := by
  rw [hankelPolynomial, (MvPolynomial.eval v).map_det]
  congr 1
  ext i j
  simp [sourceHankel, hankelPolynomialMatrix]

theorem hankelPolynomial_homogeneous {D n : ℕ} (hD : 2*n ≤ D) :
    (hankelPolynomial n hD).IsHomogeneous (n+1) := by
  classical
  unfold hankelPolynomial
  rw [Matrix.det_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro σ _
  simp only [hankelPolynomialMatrix, Matrix.of_apply]
  have hp := MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun i : Fin (n+1) => (MvPolynomial.X (⟨(σ i).val+i.val, by omega⟩ : Fin (D+1)) :
      MvPolynomial (Fin (D+1)) ℂ)) (fun _ => 1)
    (fun i _ => MvPolynomial.isHomogeneous_X ℂ _)
  have hp' : (∏ i : Fin (n+1), (MvPolynomial.X
      (⟨(σ i).val+i.val, by omega⟩ : Fin (D+1)) : MvPolynomial (Fin (D+1)) ℂ)).IsHomogeneous (n+1) := by
    simpa using hp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa only [hs, one_smul] using hp'
  · simpa [hs, Units.smul_def] using hp'.neg

theorem hankelPolynomial_vanishes_short_sum {D n k : ℕ} (hD : 2*n ≤ D) (hk : k ≤ n)
    (a : Fin k → ℂ) (t : Fin k → Option ℂ) :
    MvPolynomial.eval (∑ l, a l • curveVector D (t l)) (hankelPolynomial n hD) = 0 := by
  rw [hankelPolynomial_eval]
  exact sourceHankel_sum_det_zero hD hk a t

theorem hankelPolynomial_center_nonzero {D r : ℕ} (hD : 2*(r+1) ≤ D)
    (a : Fin r → ℂ) (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0) :
    MvPolynomial.eval (projectionCenter D r (fun i => some (a i)))
      (hankelPolynomial (r+1) hD) ≠ 0 := by
  rw [hankelPolynomial_eval, centerHankel_coordinates]
  exact centerHankel_det_ne_zero r a ha ha0

theorem hankelPolynomial_vanishes_projective_rank {D n : ℕ} (hD : 2*n ≤ D)
    (p : ℙ ℂ (CurveSpace D)) (hp : ProjectiveRankAtMost (curvePoints D) n p) :
    MvPolynomial.eval p.rep (hankelPolynomial n hD) = 0 := by
  obtain ⟨k, hk, q, hq, hspan⟩ := hp
  have hspan' : Projectivization.mk ℂ p.rep p.rep_nonzero ∈
      Projectivization.Subspace.span (Set.range q) := by simpa using hspan
  obtain ⟨b, hb⟩ := (projective_span_range k q _ _).mp hspan'
  choose t c hc hrep using hq
  have heq : p.rep = ∑ i, (b i*c i) • curveVector D (t i) := by
    rw [hb]
    apply Finset.sum_congr rfl
    intro i _
    rw [hrep i, smul_smul]
  rw [heq]
  exact hankelPolynomial_vanishes_short_sum hD hk _ _

#print axioms hankelPolynomial_center_nonzero
end NLA.TR27.Paper
