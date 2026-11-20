module

public import NLA.MD06.QuantitativeCorrection.Definitions
public import NLA.MD06.GraphCriticalityHessian.Laplacian

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Correction
open scoped BigOperators
open Reference.MD06Actual

theorem actual_connected_mean_zero_laplacian_kernel {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : G.Connected) (z : Configuration n) (hz : (∑ i, z i) = 0) :
    LaplacianQuadratic G (fun i => z i) = 0 ↔ z = 0 := by
  classical
  constructor
  · intro hq
    have hb : Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) (fun i => z i) (fun i => z i) = 0 := by
      rw [Matrix.toLinearMap₂'_apply',actual_laplacian_quadratic_identity,hq]
    have he := (SimpleGraph.lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable ℝ G (fun i => z i)).mp hb
    let : Nonempty (Fin n) := hg.nonempty
    have hn : 0 < n := by simpa only [Fintype.card_fin] using Fintype.card_pos (α := Fin n)
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    ext i
    have hs : (∑ j, z j) = (n : ℝ)*z i := by
      calc
        (∑ j, z j) = ∑ j : Fin n, z i := Finset.sum_congr rfl (fun j _ => he j i (hg j i))
        _ = (n : ℝ)*z i := by simp
    have hm : (n : ℝ)*z i = 0 := hs.symm.trans hz
    exact (mul_eq_zero.mp hm).resolve_left hn'
  · intro hz'
    subst z
    simp [LaplacianQuadratic]

theorem actual_connected_mean_zero_laplacian_positive {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : G.Connected) (z : Configuration n) (hz : (∑ i, z i) = 0) (hne : z ≠ 0) :
    0 < LaplacianQuadratic G (fun i => z i) := by
  classical
  have hp : 0 ≤ LaplacianQuadratic G (fun i => z i) := by
    unfold LaplacianQuadratic
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact sq_nonneg _
    · exact le_refl _
  have hn : LaplacianQuadratic G (fun i => z i) ≠ 0 :=
    fun h => hne ((actual_connected_mean_zero_laplacian_kernel G hg z hz).mp h)
  exact lt_of_le_of_ne hp hn.symm

#print axioms actual_connected_mean_zero_laplacian_kernel
#print axioms actual_connected_mean_zero_laplacian_positive
end Reference.MD06Correction
