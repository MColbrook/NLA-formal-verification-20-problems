module

public import NLA.TR27.ArbitraryParametersDefinitions
public import NLA.TR27.PaperSecantRootAverage
public import NLA.TR27.PaperTensorMixture
public import NLA.TR27.PaperEventualPowerBound
public import NLA.TR27.PaperQuotientRank
public import NLA.TR27.PaperQuotientSpan
public import NLA.TR27.PaperTangentGeometry
public import NLA.TR27.PaperSourceBorder

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical TensorProduct LinearAlgebra.Projectivization
open Filter
namespace NLA.TR27.Paper

theorem parameterSecant_zero (D r : ℕ) (a : Fin r → Option ℂ) :
    parameterSecant D r a 0 = quotientTangent D r a := by
  rw [parameterSecant, secantSlope_zero]
  rfl

theorem parameterSecant_difference (D r : ℕ) (a : Fin r → Option ℂ)
    (t : ℂ) (ht : t ≠ 0) :
    parameterSecant D r a t =
      t⁻¹ • (quotientCurve D r a (some t) - quotientCurve D r a (some 0)) := by
  rw [parameterSecant, secantSlope_divided_difference D t ht, map_smul, map_sub]
  rfl

theorem parameterSecant_polynomial (D r : ℕ) (a : Fin r → Option ℂ) (t : ℂ) :
    parameterSecant D r a t = ∑ j : Fin D, t^j.val •
      quotientProjection D r a (Pi.single j.succ 1) := by
  rw [parameterSecant, secantSlope_polynomial, map_sum]
  simp only [map_smul]

theorem parameterSecant_tensor_root_average (D r k : ℕ) (a : Fin r → Option ℂ)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (k*(D-1)+1)) :
    ((k*(D-1)+1 : ℕ) : ℂ)⁻¹ •
      (∑ l : Fin (k*(D-1)+1), PiTensorProduct.tprod ℂ
        (fun _ : Fin k => parameterSecant D r a (ζ^l.val))) =
      PiTensorProduct.tprod ℂ (fun _ : Fin k => quotientTangent D r a) := by
  simpa only [← parameterSecant_polynomial, parameterSecant_zero] using
    polynomial_tensor_root_average D k
      (fun j => quotientProjection D r a (Pi.single j.succ 1)) hζ

/-- The manuscript's root-of-unity formula holds for every projection centre,
not just for the convenient integer choice used by the explicit example. -/
theorem paper_parameter_difference_tensor_root_average (D r k : ℕ)
    (a : Fin r → Option ℂ) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (k*(D-1)+1)) :
    ((k*(D-1)+1 : ℕ) : ℂ)⁻¹ •
      (∑ l : Fin (k*(D-1)+1), ((ζ^l.val)^k)⁻¹ • PiTensorProduct.tprod ℂ
        (fun _ : Fin k => quotientCurve D r a (some (ζ^l.val)) -
          quotientCurve D r a (some 0))) =
      PiTensorProduct.tprod ℂ (fun _ : Fin k => quotientTangent D r a) := by
  rw [← parameterSecant_tensor_root_average D r k a hζ]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [parameterSecant_difference D r a _ (pow_ne_zero _ (hζ.ne_zero (by omega)))]
  rw [MultilinearMap.map_smul_univ]
  simp

theorem paper_parameter_tangent_power_upper (D r : ℕ) (a : Fin r → Option ℂ)
    (hD : 1 ≤ D) (hgap : 1+r < D)
    (hv : quotientTangent D r a ≠ 0) (k : ℕ) :
    ProjectiveRankAtMost (productPoints (quotientPoints D r a) k)
      ((k*(D-1)+1)*2^k) (powerPoint (Projectivization.mk ℂ _ hv) k) := by
  let L := k*(D-1)+1
  let ζ : ℂ := Complex.exp (2*Real.pi*Complex.I / L)
  have hζ : IsPrimitiveRoot ζ L := Complex.isPrimitiveRoot_exp L (by dsimp [L]; omega)
  let t : Fin L → ℂ := fun l => ζ^l.val
  have ht (l : Fin L) : t l ≠ 0 := pow_ne_zero _ (hζ.ne_zero (by dsimp [L]; omega))
  let w : Fin L → Fin 2 → QuotientSpace D r a :=
    fun l => ![quotientCurve D r a (some (t l)), quotientCurve D r a (some 0)]
  have hw (l : Fin L) (j : Fin 2) : w l j ≠ 0 := by
    fin_cases j <;> exact quotient_curve_nonzero hD hgap _ _
  let q := fun l j => Projectivization.mk ℂ (w l j) (hw l j)
  apply projective_power_mixture_upper _ _ _ (represents_mk _ hv) L 2 k
    (fun l => parameterSecant D r a (t l)) w
    (fun l => ![(t l)⁻¹,-(t l)⁻¹]) (fun _ => (L : ℂ)⁻¹) q
  · intro l j
    exact represents_mk _ _
  · intro l j
    fin_cases j
    · exact ⟨some (t l), represents_mk _ _⟩
    · exact ⟨some 0, represents_mk _ _⟩
  · intro l
    rw [parameterSecant_difference D r a (t l) (ht l)]
    simp [w, Fin.sum_univ_two, sub_eq_add_neg]
  · rw [← Finset.smul_sum]
    exact (parameterSecant_tensor_root_average D r k a hζ).symm

theorem paper_parameter_tangent_power_rank_upper (D r : ℕ) (a : Fin r → Option ℂ)
    (hD : 1 ≤ D) (hgap : 1+r < D)
    (hv : quotientTangent D r a ≠ 0) (k : ℕ) :
    projectiveRank (productPoints (quotientPoints D r a) k)
      (powerPoint (Projectivization.mk ℂ _ hv) k) ≤ (k*(D-1)+1)*2^k := by
  exact csInf_le (OrderBot.bddBelow _)
    (paper_parameter_tangent_power_upper D r a hD hgap hv k)

theorem paper_parameter_tangent_eventual_saving (D r : ℕ) (a : Fin r → Option ℂ)
    (hD : 1 ≤ D) (hr : 2 < r) (hgap : 1+r < D)
    (hv : quotientTangent D r a ≠ 0) :
    ∀ᶠ k : ℕ in atTop,
      projectiveRank (productPoints (quotientPoints D r a) k)
        (powerPoint (Projectivization.mk ℂ _ hv) k) < r^k := by
  filter_upwards [eventual_power_bound D r hr] with k hk
  exact lt_of_le_of_lt (paper_parameter_tangent_power_rank_upper D r a hD hgap hv k) hk

theorem paper_parameter_family_tensor_rank (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m)
    (a : Fin r → Option ℂ) (ha : Function.Injective a) :
    ∃ hv : quotientTangent (familyDegree r m) r a ≠ 0,
      ∀ k : ℕ, k ≤ m → projectiveRank
        (productPoints (quotientPoints (familyDegree r m) r a) k)
        (powerPoint (Projectivization.mk ℂ _ hv) k) = r^k := by
  have hg := family_degree_gap hr hm
  have hD : 1 ≤ familyDegree r m := by omega
  have hv := quotient_tangent_nonzero hD (by omega) (by omega) a ha
  refine ⟨hv, ?_⟩
  intro k hk
  apply IsLeast.csInf_eq
  apply projective_power_rank _ _ r (r^m-1) k
    (quotient_tangent_rank hD (by omega) hg a ha)
  · intro s hs hpoints
    apply quotient_projective_independent hD (by omega) a s _ hpoints
    have hp : 0 < r^m := pow_pos (by omega) _
    change s.card+r < r^m+r
    omega
  · have hp : r^k ≤ r^m := pow_le_pow_right' (by omega) hk
    omega

theorem paper_parameter_family_eventual_saving (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m)
    (a : Fin r → Option ℂ) (ha : Function.Injective a) :
    ∃ hv : quotientTangent (familyDegree r m) r a ≠ 0,
      (∀ k : ℕ, projectiveRank
        (productPoints (quotientPoints (familyDegree r m) r a) k)
        (powerPoint (Projectivization.mk ℂ _ hv) k) ≤
          (k*(familyDegree r m-1)+1)*2^k) ∧
      (∀ᶠ k : ℕ in atTop,
        projectiveRank (productPoints (quotientPoints (familyDegree r m) r a) k)
          (powerPoint (Projectivization.mk ℂ _ hv) k) < r^k) := by
  have hgap := family_degree_gap hr hm
  have hv := quotient_tangent_nonzero (by omega : 1 ≤ familyDegree r m) (by omega : 1 ≤ r)
    (by omega : r+r < familyDegree r m) a ha
  exact ⟨hv, paper_parameter_tangent_power_rank_upper _ r a (by omega) (by omega) hv,
    paper_parameter_tangent_eventual_saving _ r a (by omega) (by omega) (by omega) hv⟩

/-- Distinct parameters still represent distinct points after the arbitrary
projection. No coordinate quotient or special choice of parameters is used. -/
theorem paper_parameter_curve_injective (D r : ℕ) (hD : 1 ≤ D) (hgap : r+2 < D)
    (a : Fin r → Option ℂ) (s t : Option ℂ) (p : ℙ ℂ (QuotientSpace D r a))
    (hs : Represents (quotientCurve D r a s) p)
    (ht : Represents (quotientCurve D r a t) p) : s = t := by
  by_contra hst
  have hinj : Function.Injective (![s,t] : Fin 2 → Option ℂ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hli := quotient_curve_independent hD (by omega : 2+r < D) a (![s,t]) hinj
  obtain ⟨c,hc,hec⟩ := hs
  obtain ⟨b,hb,heb⟩ := ht
  have hz : ∑ i : Fin 2, (![c,-b] : Fin 2 → ℂ) i •
      quotientCurve D r a ((![s,t] : Fin 2 → Option ℂ) i) = 0 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, neg_smul]
    rw [← hec, ← heb, add_neg_cancel]
  have hcoeff := (Fintype.linearIndependent_iff.mp hli) (![c,-b]) hz
  exact hc (hcoeff 0)

theorem paper_parameter_curve_immersion (D r : ℕ) (hr : 1 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ)
    (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0) (t : Option ℂ) (α β : ℂ)
    (h : α • quotientCurve D r (fun i => some (a i)) t +
      β • quotientProjection D r (fun i => some (a i)) (curveTangent D t) = 0) :
    α = 0 ∧ β = 0 := by
  exact projected_curve_tangent_coefficients_eq_zero hr hD a ha ha0 t α β h

#print axioms paper_parameter_difference_tensor_root_average
#print axioms paper_parameter_tangent_power_upper
#print axioms paper_parameter_tangent_power_rank_upper
#print axioms paper_parameter_tangent_eventual_saving
#print axioms paper_parameter_family_tensor_rank
#print axioms paper_parameter_family_eventual_saving
#print axioms paper_parameter_curve_injective
#print axioms paper_parameter_curve_immersion

end NLA.TR27.Paper
