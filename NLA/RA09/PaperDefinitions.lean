module

public import NLA.RA09.Definitions

@[expose] public section

/- The larger function class in main.tex, equation raf-eq:subhom.
No concavity assumption is part of this paper-specific definition. -/
namespace NLA.RA09

def PaperAdmissibleFunction (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ici 0) ∧ MonotoneOn f (Set.Ici 0) ∧
    (∀ x : ℝ, 0 ≤ x → 0 ≤ f x) ∧
    ∀ x y : ℝ, 0 < x → x ≤ y → f y / y ≤ f x / x

end NLA.RA09
