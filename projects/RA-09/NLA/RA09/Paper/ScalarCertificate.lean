module

public import NLA.RA09.Paper.Scalar

@[expose] public section

/-! The ordered scalar certificate also covers a zero transformed cutoff. -/
set_option autoImplicit false
noncomputable section
namespace NLA.RA09.Paper

theorem ordered_scalar_certificate (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (τ a b : ℝ) (hτ : 0 < τ) (ha : 0 < a) (hb : 0 < b) :
    f b * max (f b - transferScale f τ * b) 0 * (1-b/a) ≤
      scalarAuxiliary f τ a + 2*f b*f a - 2*(transferScale f τ)^2*b*a -
        (f b)^2 + (transferScale f τ)^2*b^2 := by
  by_cases hfτ : f τ = 0
  · have hz := (admissible_scalar_consequences_proved f hf τ hτ).2.2.2.2.2 hfτ
    simp [transferScale, scalarAuxiliary, hfτ, hz a ha.le, hz b hb.le]
  · exact ordered_scalar_certificate_proved f hf τ a b hτ
      (lt_of_le_of_ne (hf.2.2.1 τ hτ.le) (Ne.symm hfτ)) ha hb

#print axioms ordered_scalar_certificate

end NLA.RA09.Paper
