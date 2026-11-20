module

public import NLA.MD06.CleanCycleGraph.RootLeafForces
public import NLA.MD06.CleanCycleGraph.ResidualDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CleanCycle
open scoped BigOperators
open Reference.MD06Actual Reference.MD06Correction Reference.MD06CycleProfile
attribute [local instance] Classical.propDecidable

theorem actual_node_root_form {ell R : ℕ} (x : TreeNodes ell R) (hx : x.1.val = 0) :
    x = RootNode (R := R) x.2.1 := by
  rcases x with ⟨⟨j,hj⟩,i,b⟩
  change j = 0 at hx
  subst j
  have hb : b = 0 := by
    apply Fin.ext
    have hb0 := b.isLt
    norm_num at hb0
    omega
  subst b
  rfl

theorem actual_embedded_gradient_node_residual {n ell R : ℕ} (G : SimpleGraph (Fin n))
    (hell : 4 ≤ ell) (hdiv : 4 ∣ ell) (hR : 4 ≤ R)
    (e : CleanCycleEmbedding (ell := ell) G hR) (x : TreeNodes ell R) :
    Gradient G (PhaseLift (fun v => EmbeddedProfile e.nodes v)) (e.nodes x) = NodeResidual x := by
  by_cases hx : x.1.val = R
  · rw [NodeResidual,if_pos hx]
    exact actual_embedded_leaf_gradient G hR e x hx
  · rw [NodeResidual,if_neg hx]
    by_cases h0 : x.1.val = 0
    · have he := actual_node_root_form x h0
      rw [he]
      exact actual_embedded_root_gradient_zero G hell hdiv hR e x.2.1
    · have hle := x.1.isLt
      exact actual_embedded_interior_gradient_zero G hR e x (by omega) (by omega)

theorem actual_node_residual_norm_square (ell R : ℕ) :
    (∑ x : TreeNodes ell R, (NodeResidual x)^2) = (ell : ℝ)*(Root R)^2/(2 : ℝ)^(R-1) := by
  rw [Fintype.sum_sigma]
  have hinner (j : Fin (R+1)) : (∑ u : LevelNodes ell j.val, (NodeResidual ⟨j,u⟩)^2) =
      if j.val = R then (ell : ℝ)*(Root R)^2/(2 : ℝ)^(R-1) else 0 := by
    by_cases hj : j.val = R
    · simp only [NodeResidual,if_pos hj]
      simp_rw [div_pow,mul_pow,neg_sq,actual_root_sign_square,one_mul]
      rw [Finset.sum_const,Finset.card_univ,actual_level_node_card]
      simp only [nsmul_eq_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      have he : (2 : ℝ)^(j.val-1) = (2 : ℝ)^(R-1) := by rw [hj]
      rw [he]
      field_simp
    · simp [NodeResidual,hj]
  simp_rw [hinner]
  rw [Finset.sum_eq_single (⟨R,by omega⟩ : Fin (R+1))]
  · simp
  · intro j hj hne
    have hn : j.val ≠ R := by intro hh; exact hne (Fin.ext hh)
    simp [hn]
  · intro hh
    exact False.elim (hh (Finset.mem_univ _))

theorem actual_embedded_gradient_norm_square {n ell R : ℕ} (G : SimpleGraph (Fin n))
    (hell : 4 ≤ ell) (hdiv : 4 ∣ ell) (hR : 4 ≤ R)
    (e : CleanCycleEmbedding (ell := ell) G hR) :
    ‖GradientVector G (EmbeddedProfile e.nodes)‖^2 =
      (ell : ℝ)*(Root R)^2/(2 : ℝ)^(R-1) := by
  rw [actual_euclidean_gradient_norm_squared]
  have he : (∑ v ∈ Finset.univ.image e.nodes,
      (Gradient G (PhaseLift (fun a => EmbeddedProfile e.nodes a)) v)^2) =
      ∑ v : Fin n, (Gradient G (PhaseLift (fun a => EmbeddedProfile e.nodes a)) v)^2 := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v hv hout
    have hvout : v ∉ Set.range e.nodes := by
      intro hh
      obtain ⟨x,hx⟩ := hh
      exact hout (Finset.mem_image.mpr ⟨x,Finset.mem_univ x,hx⟩)
    rw [actual_embedded_gradient_outside_zero G hR e v hvout]
    norm_num
  rw [←he,Finset.sum_image (by intro a ha b hb hab; exact e.nodes.injective hab)]
  simp_rw [actual_embedded_gradient_node_residual G hell hdiv hR e]
  exact actual_node_residual_norm_square ell R
end Reference.MD06CleanCycle
