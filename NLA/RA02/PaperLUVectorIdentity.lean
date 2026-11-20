module

public import NLA.RA02.PaperKyFan

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

/-- Complex Lagrange identity in the form needed for one conditional LU pivot. -/
theorem vector_cross_norm_identity {m : ℕ} (u y : Fin m → ℂ) :
    (∑ i, ∑ j, Complex.normSq (u i*y j-u j*y i)) =
      2*(∑ i, Complex.normSq (u i))*(∑ j, Complex.normSq (y j)) -
        2*Complex.normSq (∑ i, star (u i)*y i) := by
  have hc : (∑ i, ∑ j, (u i*y j*star (u j*y i))) =
      ((Complex.normSq (∑ i, star (u i)*y i) : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, map_mul, Complex.star_def, Complex.conj_conj]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcr : (∑ i, ∑ j, (u i*y j*star (u j*y i)).re) =
      Complex.normSq (∑ i, star (u i)*y i) := by
    have hh := congrArg Complex.re hc
    simpa only [Complex.re_sum, Complex.ofReal_re] using hh
  simp only [Complex.normSq_sub, Complex.normSq_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← Complex.star_def]
  rw [hcr]
  ring

#print axioms vector_cross_norm_identity
end NLA.RA02.Paper
