module

public import NLA.RA02.PaperRationalFamilyDefinitions
public import NLA.RA02.PaperRationalCopyCounts
public import NLA.RA02.PaperSharpFamily
public import NLA.RA02.PaperPivotDefinitions

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem rationalLower_cast (n : ℕ) (t : ℚ) (i j : Fin n) :
    (rationalLower n t i j : ℝ)=lower n (t : ℝ) i j := by
  by_cases hij : i = j <;> by_cases hji : j < i <;> simp [rationalLower,lower,hij,hji]

theorem rationalSharpFamily_cast (n : ℕ) (t : ℚ) (i j : Fin n) :
    (rationalSharpFamily n t i j : ℝ)=sharpFamily n (t : ℝ) i j := by
  have hd : ∀ a b : Fin n, (rationalDiagonalScales n t a b : ℝ) =
      diagonalScales n (t : ℝ) a b := by
    intro a b
    by_cases hab : a = b <;>
      simp [rationalDiagonalScales,diagonalScales,epsilon,hab]
  simp only [rationalSharpFamily,sharpFamily,Matrix.mul_apply,Matrix.transpose_apply,
    Rat.cast_sum,Rat.cast_mul,rationalLower_cast,hd]

theorem rationalSharpFamily_entry_pos (r : ℕ) (t : ℚ) (ht : 0 < t) (i j : Fin (r+1)) :
    0 < rationalSharpFamily (r+1) t i j := by
  have hr : 0 < (t : ℝ) := by exact_mod_cast ht
  have he := sharpFamily_entry_pos r (t : ℝ) hr i j
  rw [← rationalSharpFamily_cast] at he
  exact_mod_cast he

theorem rational_family_copy_counts (r : ℕ) (t : ℚ) (ht : 0 < t) :
    ∃ (c : ℚ) (m : Fin (r+1) → ℕ), 0 < c ∧ (∀ i, 0 < m i) ∧
      ∀ i, complexify (sharpFamily (r+1) (t : ℝ)) i i=
        (((c : ℝ)*(m i : ℝ) : ℝ) : ℂ) := by
  obtain ⟨c,m,hc,hm,hd⟩ := exists_rational_copy_counts
    (fun i : Fin (r+1) => rationalSharpFamily (r+1) t i i)
    (fun i => rationalSharpFamily_entry_pos r t ht i i)
  refine ⟨c,m,hc,hm,?_⟩
  intro i
  have he : (rationalSharpFamily (r+1) t i i : ℝ)=(c : ℝ)*(m i : ℝ) := by exact_mod_cast hd i
  rw [rationalSharpFamily_cast] at he
  change (sharpFamily (r+1) (t : ℝ) i i : ℂ)=_
  rw [he]

#print axioms rational_family_copy_counts
end NLA.RA02.Paper
