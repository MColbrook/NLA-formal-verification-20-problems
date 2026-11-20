module

public import NLA.PF02.Normalization.Definitions
public import NLA.PF02.IntrinsicSupport.DimensionSupport

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02Normalization
open Matrix Module Reference.PF02Support Reference.PF02IntrinsicSupport
open scoped BigOperators MatrixOrder

theorem psd_full_rank_posDef {k : ℕ} (Q : Mat (Fin k))
    (hQ : Q.PosSemidef) (hrank : Q.rank = k) : Q.PosDef := by
  classical
  have hsum := image_kernel_finrank_sum Q
  rw [← rank_eq_image_finrank, hrank] at hsum
  have hdim : finrank ℝ (kernel Q) = 0 := by omega
  have hker : kernel Q = ⊥ := Submodule.finrank_eq_zero.mp hdim
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hQ.isHermitian
  intro x hx
  have hn := hQ.dotProduct_mulVec_nonneg x
  have hz : star x ⬝ᵥ Q *ᵥ x ≠ 0 := by
    intro h
    have hmul := (hQ.dotProduct_mulVec_zero_iff (x := x)).mp h
    have hlin : lin Q (WithLp.toLp 2 x) = 0 := (lin_zero_iff Q (WithLp.toLp 2 x)).mpr hmul
    have hmem : WithLp.toLp 2 x ∈ kernel Q := hlin
    rw [hker] at hmem
    exact hx ((WithLp.toLp_eq_zero 2).mp hmem)
  exact lt_of_le_of_ne hn hz.symm

theorem row_sum_rank_eq_of_full_trace_rank {p q k : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Mat (Fin k)) (B : Fin q → Mat (Fin k))
    (hA : ∀ i, (A i).PosSemidef)
    (htrace : ∀ i j, Matrix.trace (A i * B j) = M i j)
    (hrank : M.rank = k * (k + 1) / 2) : (rowSum A).rank = k := by
  have h := psd_family_image_trace_rank_le M A B hA htrace
  rw [hrank] at h
  have hl : k ≤ (rowSum A).rank := triangular_rank_dimension_le h
  have hu : (rowSum A).rank ≤ k := (rowSum A).rank_le_width
  exact le_antisymm hu hl

theorem row_sum_posDef_of_full_trace_rank {p q k : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Mat (Fin k)) (B : Fin q → Mat (Fin k))
    (hA : ∀ i, (A i).PosSemidef)
    (htrace : ∀ i j, Matrix.trace (A i * B j) = M i j)
    (hrank : M.rank = k * (k + 1) / 2) : (rowSum A).PosDef :=
  psd_full_rank_posDef (rowSum A) (psd_sum A hA)
    (row_sum_rank_eq_of_full_trace_rank M A B hA htrace hrank)

#print axioms psd_full_rank_posDef
#print axioms row_sum_rank_eq_of_full_trace_rank
#print axioms row_sum_posDef_of_full_trace_rank
end Reference.PF02Normalization
