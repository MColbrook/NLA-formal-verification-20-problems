module

public import NLA.RA08.RangeBasis.Orthonormal

@[expose] public section

set_option autoImplicit false
noncomputable section
open Matrix
namespace NLA.RA08.Paper.RangeBasis

theorem nystrom_has_invertible_orthonormal_sketch {n l : ℕ} (A : RealMatrix n)
    (Ω : Matrix (Fin n) (Fin l) ℝ) (hΩ : FullColumns Ω)
    (hG : IsUnit (Ω.transpose * A * Ω).det) :
    ∃ Q : Matrix (Fin n) (Fin l) ℝ,
      Q.transpose * Q = 1 ∧ SameRange Ω Q ∧
      IsUnit (Q.transpose * A * Q).det ∧ nystrom A Q = nystrom A Ω := by
  obtain ⟨Q, hQ, hr⟩ := exists_orthonormal_range_basis Ω hΩ
  obtain ⟨T, hT, hQT⟩ := same_range_change_of_basis Ω Q hΩ
    (fullColumns_of_orthonormal Q hQ) hr
  have hGQ : IsUnit (Q.transpose * A * Q).det := by
    rw [← hQT]
    exact gram_basis_change_isUnit A Ω T hG hT
  exact ⟨Q, hQ, hr, hGQ, nystrom_orthonormal_range_basis A Ω Q hΩ hQ hr⟩

#print axioms nystrom_has_invertible_orthonormal_sketch
end NLA.RA08.Paper.RangeBasis
