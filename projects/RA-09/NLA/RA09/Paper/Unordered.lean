module

public import NLA.RA09.Paper.Transfer
public import NLA.RA09.UnorderedScalar

@[expose] public section

/-! Unordered Frobenius transfer for the exact function class in main.tex.
Mathematical proof: Matthew J. Colbrook. AI-assisted Lean formalization. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical MatrixOrder
namespace NLA.RA09.Paper

theorem normalized_function_admissible (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (τ : ℝ) (hτ : 0 < τ) (hfτ : 0 < f τ) :
    PaperAdmissibleFunction (fun x => f (τ*x) / f τ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hf.1.comp (continuousOn_const.mul continuousOn_id)
      (fun x hx => mul_nonneg hτ.le hx)).div_const _
  · intro x hx y hy hxy
    exact div_le_div_of_nonneg_right
      (hf.2.1 (mul_nonneg hτ.le hx) (mul_nonneg hτ.le hy)
        (mul_le_mul_of_nonneg_left hxy hτ.le)) hfτ.le
  · intro x hx
    exact div_nonneg (hf.2.2.1 _ (mul_nonneg hτ.le hx)) hfτ.le
  · intro x y hx hxy
    have hy : 0 < y := hx.trans_le hxy
    have h := mul_le_mul_of_nonneg_left
      (hf.2.2.2 (τ*x) (τ*y) (mul_pos hτ hx) (mul_le_mul_of_nonneg_left hxy hτ.le))
      (div_pos hτ hfτ).le
    have hyid : f (τ*y) / f τ / y = (τ/f τ) * (f (τ*y)/(τ*y)) := by
      field_simp
    have hxid : f (τ*x) / f τ / x = (τ/f τ) * (f (τ*x)/(τ*x)) := by
      field_simp
    rw [hyid, hxid]
    exact h

def unorderedAuxiliary (f : ℝ → ℝ) (τ a : ℝ) : ℝ :=
  max (2*(transferScale f τ)^2*a^2 - (f a)^2) ((f τ)^2)

theorem unordered_scalar_scaled (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (τ a b : ℝ) (hτ : 0 < τ) (hfτ : 0 < f τ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (f b)^2 - 2*f b*f a - 2*(transferScale f τ)^2*b^2 +
      4*(transferScale f τ)^2*a*b ≤ unorderedAuxiliary f τ a := by
  let g := fun x => f (τ*x) / f τ
  have hg := normalized_function_admissible f hf τ hτ hfτ
  have hg1 : g 1 = 1 := by simp [g, hfτ.ne']
  have h := unordered_scalar_certificate_proved g hg hg1 (a/τ) (b/τ)
    (div_nonneg ha hτ.le) (div_nonneg hb hτ.le)
  have hm := mul_le_mul_of_nonneg_left h (sq_nonneg (f τ))
  have hta : τ*(a/τ) = a := by field_simp
  have htb : τ*(b/τ) = b := by field_simp
  have hga : g (a/τ) = f a / f τ := by simp only [g, hta]
  have hgb : g (b/τ) = f b / f τ := by simp only [g, htb]
  rw [hga, hgb, mul_max_of_nonneg _ _ (sq_nonneg (f τ))] at hm
  have hleft : (f b)^2 - 2*f b*f a - 2*(transferScale f τ)^2*b^2 +
      4*(transferScale f τ)^2*a*b =
      (f τ)^2*((f b/f τ)^2-2*(f b/f τ)*(f a/f τ)-2*(b/τ)^2+4*(a/τ)*(b/τ)) := by
    dsimp [transferScale]
    field_simp
    <;> ring
  have hright : unorderedAuxiliary f τ a =
      max ((f τ)^2*(2*(a/τ)^2-(f a/f τ)^2)) ((f τ)^2*1) := by
    unfold unorderedAuxiliary
    rw [mul_one]
    congr 1
    dsimp [transferScale]
    field_simp
    <;> ring
  rw [hleft, hright]
  exact hm

theorem unordered_auxiliary_cutoff (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (τ : ℝ) (hτ : 0 < τ) :
    (∀ a : ℝ, 0 ≤ a → a ≤ τ → unorderedAuxiliary f τ a = (f τ)^2) ∧
    (∀ a : ℝ, τ ≤ a → unorderedAuxiliary f τ a =
      2*(transferScale f τ)^2*a^2 - (f a)^2) := by
  obtain ⟨_, hc, hlo, hhi, _, _⟩ := admissible_scalar_consequences_proved f hf τ hτ
  have hct : transferScale f τ * τ = f τ := div_mul_cancel₀ _ hτ.ne'
  constructor
  · intro a ha hat
    apply max_eq_right
    have hfa := hlo a ha hat
    have hca : 0 ≤ transferScale f τ * a := mul_nonneg hc ha
    have hcat := mul_le_mul_of_nonneg_left hat hc
    have h1 := mul_self_le_mul_self hca hfa
    have h2 := mul_self_le_mul_self hca hcat
    rw [hct] at h2
    nlinarith [sq_nonneg (f τ)]
  · intro a hta
    apply max_eq_left
    have ha : 0 ≤ a := hτ.le.trans hta
    have hfa := hhi a hta
    have hcat := mul_le_mul_of_nonneg_left hta hc
    have h1 := mul_self_le_mul_self (hf.2.2.1 a ha) hfa
    have h2 := mul_self_le_mul_self (mul_nonneg hc hτ.le) hcat
    rw [hct] at h2
    nlinarith

#print axioms normalized_function_admissible
#print axioms unordered_scalar_scaled
#print axioms unordered_auxiliary_cutoff

end NLA.RA09.Paper
