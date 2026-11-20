module

public import NLA.MD06.CleanCycleGraph.Definitions
public import NLA.MD06.CycleProfile.Nonsynchronization

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CleanCycle
open scoped BigOperators
open Reference.MD06CycleProfile

theorem actual_root_sign_square {ell : ℕ} (i : Fin ell) : (RootSign i)^2 = 1 := by
  unfold RootSign
  split <;> norm_num

theorem actual_root_sign_sine {ell : ℕ} (i : Fin ell) (x : ℝ) :
    Real.sin (RootSign i*x) = RootSign i*Real.sin x := by
  unfold RootSign
  split <;> simp

theorem actual_root_sign_cosine {ell : ℕ} (i : Fin ell) (x : ℝ) :
    Real.cos (RootSign i*x) = Real.cos x := by
  unfold RootSign
  split <;> simp

theorem actual_level_node_card (ell j : ℕ) : Fintype.card (LevelNodes ell j) = ell * 2^(j-1) := by
  simp [LevelNodes]

theorem actual_leaf_residual_square {ell R : ℕ} (x : LevelNodes ell R) :
    (LeafResidual x)^2 = (Root R)^2 / ((2 : ℝ)^(R-1))^2 := by
  unfold LeafResidual
  rw [div_pow,mul_pow,neg_sq,actual_root_sign_square,one_mul]

theorem actual_leaf_residual_norm_square (ell R : ℕ) :
    (∑ x : LevelNodes ell R, (LeafResidual x)^2) = (ell : ℝ)*(Root R)^2/(2 : ℝ)^(R-1) := by
  simp_rw [actual_leaf_residual_square]
  rw [Finset.sum_const,Finset.card_univ,actual_level_node_card]
  simp only [nsmul_eq_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  field_simp

theorem actual_node_profile_terminal {ell R : ℕ} (x : LevelNodes ell R) :
    NodeProfile (⟨⟨R,by omega⟩,x⟩ : TreeNodes ell R) = 0 := by
  simp [NodeProfile,actual_height_terminal]

theorem actual_node_profile_step {ell R j : ℕ} (hR : 4 ≤ R) (hj : j < R)
    (i : Fin ell) (a : Fin (2^(j-1))) (b : Fin (2^j)) :
    Real.sin (NodeProfile (⟨⟨j,by omega⟩,⟨i,a⟩⟩ : TreeNodes ell R) -
      NodeProfile (⟨⟨j+1,by omega⟩,⟨i,b⟩⟩ : TreeNodes ell R)) =
      RootSign i * Root R / (2 : ℝ)^j := by
  unfold NodeProfile
  rw [←mul_sub,actual_height_step hj,actual_root_sign_sine,
    actual_delta_sine (actual_root_spec hR).1]
  ring
end Reference.MD06CleanCycle
