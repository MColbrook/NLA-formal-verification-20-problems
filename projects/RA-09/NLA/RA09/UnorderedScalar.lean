module

public import NLA.RA09.Scalar
public import NLA.RA09.PaperDefinitions

@[expose] public section

/-!
The unordered scalar certificate in main.tex, Lemma raf-lem:unorderedscalar.
Mathematical argument: Matthew J. Colbrook. AI-assisted Lean extension.
This lemma does not by itself prove the unordered matrix transfer theorem.
-/

set_option autoImplicit false
noncomputable section
namespace NLA.RA09

private theorem unordered_unit_certificate (a b u v : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hau : a ≤ u) (hbv : b ≤ v) (hv1 : v ≤ 1)
    (hmono : b ≤ a → v ≤ u) (hcross : a ≤ b → a * v ≤ b * u) :
    v^2 - 2*v*u - 2*b^2 + 4*a*b ≤ 1 := by
  have hv : 0 ≤ v := hb.trans hbv
  by_cases hba : b ≤ a
  · have hvu := hmono hba
    by_cases hav : a ≤ v
    · nlinarith [mul_nonneg hv (sub_nonneg.mpr hvu), sq_nonneg (a-b)]
    · have hva : v ≤ a := le_of_not_ge hav
      have hprod : (v-b)*(v+b-2*a) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hbv) (by linarith)
      nlinarith [mul_nonneg hv (sub_nonneg.mpr hau), sq_nonneg (a-b)]
  · have hab : a ≤ b := le_of_lt (lt_of_not_ge hba)
    have hbpos : 0 < b := lt_of_le_of_lt ha (lt_of_not_ge hba)
    let z := a / b
    have hz : 0 ≤ z := div_nonneg ha hb
    have hz1 : z ≤ 1 := (div_le_one hbpos).mpr hab
    have haz : a = z*b := (div_mul_cancel₀ a hbpos.ne').symm
    have hzu : z*v ≤ u := by
      have h : (a*v)/b ≤ u :=
        (div_le_iff₀ hbpos).mpr (by simpa [mul_comm] using hcross hab)
      simpa only [z, div_mul_eq_mul_div] using h
    have hleft : v^2 - 2*v*u - 2*b^2 + 4*a*b ≤
        (1-2*z)*(v^2-2*b^2) := by
      rw [haz]
      nlinarith [mul_nonneg hv (sub_nonneg.mpr hzu)]
    apply hleft.trans
    by_cases hzhalf : z ≤ 1/2
    · have hc : 0 ≤ 1-2*z := by linarith
      have hvbound : v^2-2*b^2 ≤ 1 := by nlinarith [sq_nonneg b]
      have h := mul_le_mul_of_nonneg_left hvbound hc
      nlinarith
    · have hc : 1-2*z ≤ 0 := by linarith
      have hvbound : -b^2 ≤ v^2-2*b^2 := by nlinarith
      have h := mul_le_mul_of_nonpos_left hvbound hc
      have hbSq : b^2 ≤ 1 := by nlinarith
      have h' := mul_le_mul_of_nonneg_left hbSq (show 0 ≤ 2*z-1 by linarith)
      nlinarith

theorem concave_admissible_is_paper_admissible (g : ℝ → ℝ)
    (hg : AdmissibleFunction g) : PaperAdmissibleFunction g := by
  exact ⟨hg.1, hg.2.2.1, hg.2.2.2,
    (admissible_scalar_consequences_proved g hg 1 (by norm_num)).1⟩

theorem unordered_scalar_certificate_proved (g : ℝ → ℝ)
    (hg : PaperAdmissibleFunction g) (hg1 : g 1 = 1)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    g b^2 - 2*g b*g a - 2*b^2 + 4*a*b ≤ max (2*a^2-g a^2) 1 := by
  have hnonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ g x := hg.2.2.1 x hx
  have hmono {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y) : g x ≤ g y :=
    hg.2.1 hx hy hxy
  have hcross (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) (hxy : x ≤ y) :
      x*g y ≤ y*g x := by
    by_cases hx0 : x = 0
    · subst x
      simpa only [zero_mul] using mul_nonneg hy.le (hnonneg 0 le_rfl)
    · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      simpa only [mul_comm] using (div_le_div_iff₀ hy hxp).mp (hg.2.2.2 x y hxp hxy)
  have hdiff_bound (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy1 : 1 ≤ y) :
      0 ≤ g y-g x ∧ g y-g x ≤ y-x := by
    have hy : 0 < y := lt_of_lt_of_le (by norm_num) hy1
    have hgyle : g y ≤ y := by
      simpa only [hg1, one_mul, mul_one] using hcross 1 y (by norm_num) hy hy1
    refine ⟨sub_nonneg.mpr (hmono hx hy.le hxy), ?_⟩
    apply (mul_le_mul_iff_right₀ hy).mp
    nlinarith [hcross x y hx hy hxy,
      mul_nonneg (sub_nonneg.mpr hgyle) (sub_nonneg.mpr hxy)]
  by_cases hlarge : 1 ≤ max a b
  · have hdiff : (g a-g b)^2 ≤ (a-b)^2 := by
      rcases le_total a b with hab | hba
      · have h1b : 1 ≤ b := by simpa only [max_eq_right hab] using hlarge
        obtain ⟨hlo, hhi⟩ := hdiff_bound a b ha hab h1b
        nlinarith [mul_nonneg (sub_nonneg.mpr (show g b-g a ≤ b-a from hhi))
          (show 0 ≤ (b-a)+(g b-g a) by linarith)]
      · have h1a : 1 ≤ a := by simpa only [max_eq_left hba] using hlarge
        obtain ⟨hlo, hhi⟩ := hdiff_bound b a hb hba h1a
        nlinarith [mul_nonneg (sub_nonneg.mpr (show g a-g b ≤ a-b from hhi))
          (show 0 ≤ (a-b)+(g a-g b) by linarith)]
    exact (show g b^2 - 2*g b*g a - 2*b^2 + 4*a*b ≤ 2*a^2-g a^2 by
      nlinarith [sq_nonneg (a-b)]).trans (le_max_left _ _)
  · have ha1 : a ≤ 1 := (le_max_left a b).trans (le_of_lt (lt_of_not_ge hlarge))
    have hb1 : b ≤ 1 := (le_max_right a b).trans (le_of_lt (lt_of_not_ge hlarge))
    have hbelow (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) : x ≤ g x := by
      simpa only [hg1, one_mul, mul_one] using hcross x 1 hx (by norm_num) hx1
    have habcross : a ≤ b → a*g b ≤ b*g a := by
      intro hab
      by_cases ha0 : a = 0
      · simp only [ha0, zero_mul]
        exact mul_nonneg hb (hnonneg 0 le_rfl)
      · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hbp : 0 < b := hap.trans_le hab
        have h := hg.2.2.2 a b hap hab
        simpa only [mul_comm] using (div_le_div_iff₀ hbp hap).mp h
    have h := unordered_unit_certificate a b (g a) (g b) ha hb ha1 hb1
      (hbelow a ha ha1)
      (hbelow b hb hb1) (by simpa only [hg1] using hmono hb (by norm_num) hb1)
      (fun hba => hmono hb ha hba) habcross
    exact h.trans (le_max_right _ _)

#print axioms unordered_scalar_certificate_proved

end NLA.RA09
