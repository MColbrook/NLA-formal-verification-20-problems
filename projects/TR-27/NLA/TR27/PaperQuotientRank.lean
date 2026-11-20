module

public import NLA.TR27.PaperQuotient
public import NLA.TR27.PaperProduct

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization Classical
namespace NLA.TR27.Paper

theorem quotient_tangent_not_short_sum {D r n : ℕ} (hD : 1 ≤ D)
    (hgap : r+n+r < D) (hn : n < r) (a : Fin r → Option ℂ)
    (ha : Function.Injective a) (t : Fin n → Option ℂ) (b : Fin n → ℂ) :
    quotientTangent D r a ≠ ∑ i, b i • quotientCurve D r a (t i) := by
  classical
  intro heq
  let s := Finset.univ.image a ∪ Finset.univ.image t
  have hs : s.card+r < D := by
    have hcard := Finset.card_union_le (Finset.univ.image a) (Finset.univ.image t)
    have ha' := Finset.card_image_le (s := Finset.univ) (f := a)
    have ht' := Finset.card_image_le (s := Finset.univ) (f := t)
    simp only [Finset.card_univ, Fintype.card_fin] at ha' ht'
    dsimp [s]
    omega
  have haj (j : Fin r) : a j ∈ s := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have htj (j : Fin n) : t j ∈ s := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  obtain ⟨j, hj⟩ : ∃ j : Fin r, a j ∉ Finset.univ.image t := by
    by_contra h
    push Not at h
    have hsub : Finset.univ.image a ⊆ Finset.univ.image t := by
      rintro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact h i
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ ha] at hc
    have ht' := Finset.card_image_le (s := Finset.univ) (f := t)
    simp only [Finset.card_univ, Fintype.card_fin] at hc ht'
    omega
  obtain ⟨f, hf⟩ := independent_coordinate (fun u : s => quotientCurve D r a u)
    (quotient_curve_finset_independent hD a s hs) ⟨a j, haj j⟩
  have hfa (i : Fin r) : f (quotientCurve D r a (a i)) = if i = j then 1 else 0 := by
    simpa only [Subtype.mk.injEq, ha.eq_iff] using hf ⟨a i, haj i⟩
  have hft (i : Fin n) : f (quotientCurve D r a (t i)) = 0 := by
    have hne : t i ≠ a j := by
      intro h
      exact hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩)
    simpa only [Subtype.mk.injEq, if_neg hne] using hf ⟨t i, htj i⟩
  have hh := congrArg f heq
  rw [quotient_tangent_sum, map_sum, map_sum] at hh
  simp [hfa, hft] at hh

theorem quotient_tangent_rank {D r : ℕ} (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hgap : 3*r ≤ D) (a : Fin r → Option ℂ) (ha : Function.Injective a) :
    IsLeast {n | ProjectiveRankAtMost (quotientPoints D r a) n
      (Projectivization.mk ℂ (quotientTangent D r a)
        (quotient_tangent_nonzero hD hr (by omega) a ha))} r := by
  classical
  have hcurve (t : Option ℂ) := quotient_curve_nonzero hD (by omega : 1+r < D) a t
  constructor
  · let q : Fin r → ℙ ℂ (QuotientSpace D r a) := fun i =>
      Projectivization.mk ℂ (quotientCurve D r a (a i)) (hcurve _)
    refine ⟨r, le_rfl, q, ?_, ?_⟩
    · intro i
      exact ⟨a i, represents_mk _ _⟩
    · rw [projective_span_mk, quotient_tangent_sum]
      apply Submodule.sum_mem
      intro i _
      apply (projective_span_mk (Set.range q) _ (hcurve _)).mp
      exact Projectivization.Subspace.subset_span _ (Set.mem_range_self i)
  · intro n hn
    by_contra hsmall
    have hnlt : n < r := by omega
    obtain ⟨l, hl, q, hq, hspan⟩ := hn
    obtain ⟨b, hb⟩ := (projective_span_range l q _ _).mp hspan
    choose t c hc hrep using hq
    apply quotient_tangent_not_short_sum hD (by omega) (by omega) a ha t (fun i => b i*c i)
    rw [hb]
    apply Finset.sum_congr rfl
    intro i _
    rw [hrep i, smul_smul]

theorem quotient_projective_independent {D r : ℕ} (hD : 1 ≤ D)
    (hr : 1+r < D) (a : Fin r → Option ℂ)
    (s : Finset (ℙ ℂ (QuotientSpace D r a))) (hs : s.card+r < D)
    (hpoints : ∀ q ∈ s, q ∈ quotientPoints D r a) :
    LinearIndependent ℂ (fun q : s => (q : ℙ ℂ (QuotientSpace D r a)).rep) := by
  classical
  have hp (q : s) := hpoints q q.property
  choose t ht using hp
  have htinj : Function.Injective t := by
    intro q q' heq
    apply Subtype.ext
    have hq := (represents_iff_eq_mk _ (quotient_curve_nonzero hD hr a _) _).mp (ht q)
    have hq' := (represents_iff_eq_mk _ (quotient_curve_nonzero hD hr a _) _).mp (ht q')
    rw [hq, hq', heq]
  let e := Fintype.equivFin s
  have hli := quotient_curve_independent hD (by simpa only [Fintype.card_coe] using hs)
    a (t ∘ e.symm) (htinj.comp e.symm.injective)
  have hli' : LinearIndependent ℂ (fun q : s => quotientCurve D r a (t q)) := by
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hli.comp e e.injective
  choose c hc hrep using ht
  have hscaled := hli'.units_smul (fun q => Units.mk0 (c q) (hc q))
  change LinearIndependent ℂ (fun q => c q • quotientCurve D r a (t q)) at hscaled
  simpa only [← hrep] using hscaled

theorem family_degree_gap {r m : ℕ} (hr : 3 ≤ r) (hm : 2 ≤ m) :
    3*r ≤ familyDegree r m := by
  have hp : r^2 ≤ r^m := pow_le_pow_right' (by omega) hm
  dsimp [familyDegree]
  nlinarith

theorem family_tensor_rank {r m k : ℕ} (hr : 3 ≤ r) (hm : 2 ≤ m)
    (hk : k ≤ m) :
    ∃ hv : quotientTangent (familyDegree r m) r (chosenParameters r) ≠ 0,
      IsLeast {n | ProjectiveRankAtMost
        (productPoints (quotientPoints (familyDegree r m) r (chosenParameters r)) k) n
        (powerPoint (Projectivization.mk ℂ _ hv) k)} (r^k) := by
  have hg := family_degree_gap hr hm
  have hD : 1 ≤ familyDegree r m := by omega
  have hv := quotient_tangent_nonzero hD (by omega) (by omega)
    (chosenParameters r) (chosenParameters_injective r)
  refine ⟨hv, projective_power_rank _ _ r (r^m-1) k
    (quotient_tangent_rank hD (by omega) hg _ (chosenParameters_injective r)) ?_ ?_⟩
  · intro s hs hpoints
    apply quotient_projective_independent hD (by omega) _ s _ hpoints
    have hp : 0 < r^m := pow_pos (by omega) _
    change s.card+r < r^m+r
    omega
  · have hp : r^k ≤ r^m := pow_le_pow_right' (by omega) hk
    omega

#print axioms family_tensor_rank
#print axioms quotient_tangent_rank
end NLA.TR27.Paper
