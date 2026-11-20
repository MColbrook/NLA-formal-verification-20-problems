module

public import NLA.RA08.PaperNuclearPolarDefinitions
public import NLA.RA08.PaperNuclearTriangularSpectrum

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem nuclearTriangularGram_spectrum_pos (m : ℕ) (x : ℝ)
    (hx : x ∈ spectrum ℝ (nuclearTriangularGram m)) : 0 < x := by
  let hG := (nuclearGram_posSemidef (nuclearTriangular m)).isHermitian
  obtain ⟨e,he⟩ := nuclearTriangular_spectrum_permutation m
  have hr : x ∈ Set.range hG.eigenvalues := by
    rwa [← hG.spectrum_real_eq_range_eigenvalues]
  obtain ⟨i,rfl⟩ := hr
  obtain ⟨j,rfl⟩ := e.surjective i
  rw [he]
  exact inv_pos.mpr (nuclearDifferenceEigenvalue_pos j)

theorem nuclearTriangularPolar_unitary (m : ℕ) :
    nuclearTriangularPolar m ∈ Matrix.unitaryGroup (Fin m) ℝ := by
  let G := nuclearTriangularGram m
  let F := functionalCalculus (fun x : ℝ => (Real.sqrt x)⁻¹) G
  have hG : G.IsHermitian := (nuclearGram_posSemidef (nuclearTriangular m)).isHermitian
  have hidG : cfc (fun x : ℝ => x) G=G := cfc_id' ℝ G hG
  have hF : F.IsHermitian := cfc_predicate _ G
  have ht : F.transpose=F := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hF.eq
  have hf : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (spectrum ℝ G) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  have hfi : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹*x) (spectrum ℝ G) :=
    hf.mul continuous_id.continuousOn
  have hmul : F*G*F=cfc (fun x : ℝ => (Real.sqrt x)⁻¹*x*(Real.sqrt x)⁻¹) G := by
    rw [cfc_mul _ _ G hfi hf,cfc_mul (fun x : ℝ => (Real.sqrt x)⁻¹)
      (fun x : ℝ => x) G hf continuous_id.continuousOn,hidG]
    rfl
  have hid : F*G*F=1 := by
    rw [hmul,← cfc_const_one ℝ G]
    apply cfc_congr
    intro x hx
    have hp := nuclearTriangularGram_spectrum_pos m x hx
    have hs := Real.sq_sqrt hp.le
    have hn := ne_of_gt (Real.sqrt_pos.mpr hp)
    field_simp
    nlinarith
  have hR : (nuclearTriangularPolar m).transpose*nuclearTriangularPolar m=1 := by
    change (nuclearTriangular m*F).transpose*(nuclearTriangular m*F)=1
    rw [Matrix.transpose_mul,ht]
    change (F*(nuclearTriangular m).transpose)*(nuclearTriangular m*F)=1
    simpa only [G,nuclearTriangularGram,Matrix.mul_assoc] using hid
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hR

theorem nuclearTriangularPolar_attains (m : ℕ) :
    ((nuclearTriangularPolar m).transpose*nuclearTriangular m).trace=
      nuclearNorm (nuclearTriangular m) := by
  let G := nuclearTriangularGram m
  let F := functionalCalculus (fun x : ℝ => (Real.sqrt x)⁻¹) G
  have hG : G.IsHermitian := (nuclearGram_posSemidef (nuclearTriangular m)).isHermitian
  have hidG : cfc (fun x : ℝ => x) G=G := cfc_id' ℝ G hG
  have hF : F.IsHermitian := cfc_predicate _ G
  have ht : F.transpose=F := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hF.eq
  have hf : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (spectrum ℝ G) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  have he : F*G=functionalCalculus Real.sqrt G := by
    have hmul := cfc_mul (fun x : ℝ => (Real.sqrt x)⁻¹) (fun x : ℝ => x) G
      hf continuous_id.continuousOn
    rw [hidG] at hmul
    change cfc (fun x : ℝ => (Real.sqrt x)⁻¹) G*G=cfc Real.sqrt G
    rw [← hmul]
    apply cfc_congr
    intro x hx
    have hp := nuclearTriangularGram_spectrum_pos m x hx
    have hs := Real.sq_sqrt hp.le
    have hn := ne_of_gt (Real.sqrt_pos.mpr hp)
    change (Real.sqrt x)⁻¹*x=Real.sqrt x
    field_simp
    nlinarith
  change ((nuclearTriangular m*F).transpose*nuclearTriangular m).trace=_
  rw [Matrix.transpose_mul,ht,Matrix.mul_assoc]
  change (F*G).trace=_
  rw [he]
  rfl

#print axioms nuclearTriangularPolar_attains
end NLA.RA08.Paper
