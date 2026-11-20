module

public import NLA.MD06.FiniteProbability.Definitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06FiniteProbability
open SimpleGraph
open scoped ENNReal
attribute [local instance] Classical.propDecidable

theorem actual_prism_cubic (k : ℕ) : (Prism k).IsRegularOfDegree 3 := by
  classical
  intro v
  let H := (⊤ : SimpleGraph (Fin 2)) □ cycleGraph (k+3)
  let e := (finProdFinEquiv : Fin 2 × Fin (k+3) ≃ Fin (2*(k+3))).symm
  have hd := (SimpleGraph.Iso.comap e H).degree_eq v
  change H.degree (e v) = (Prism k).degree v at hd
  rw [← hd, degree_boxProd]
  have htop := (SimpleGraph.IsRegularOfDegree.top (V := Fin 2)).degree_eq (e v).1
  have hcycle := cycleGraph_degree_three_le (v := (e v).2)
  simpa using congrArg₂ (· + ·) htop hcycle

theorem actual_cubic_sample_nonempty (k : ℕ) : Nonempty (CubicSample k) := by
  classical
  cases k with
  | zero =>
      refine ⟨⟨⊤, ?_⟩⟩
      intro v
      unfold SimpleGraph.degree
      rw [SimpleGraph.neighborFinset_eq_filter]
      calc
        _ = (Finset.univ.erase v).card := by
          congr 1
          ext x
          simp [SimpleGraph.top_adj, ne_comm]
        _ = 3 := by simp
  | succ k =>
      exact ⟨⟨Prism k, actual_prism_cubic k⟩⟩

noncomputable instance sampleNonempty (k : ℕ) : Nonempty (CubicSample k) :=
  actual_cubic_sample_nonempty k

theorem actual_sample_card_positive (k : ℕ) : 0 < Fintype.card (CubicSample k) :=
  Fintype.card_pos

noncomputable def UniformCubic (k : ℕ) : PMF (CubicSample k) :=
  PMF.ofFintype (fun _ => (Fintype.card (CubicSample k) : ENNReal)⁻¹) (by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel
      (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card (CubicSample k) ≠ 0))
      (by simp))

theorem actual_uniform_cubic_point_mass (k : ℕ) (G : CubicSample k) :
    UniformCubic k G = (Fintype.card (CubicSample k) : ℝ≥0∞)⁻¹ := by
  simp [UniformCubic]

end Reference.MD06FiniteProbability
#print axioms Reference.MD06FiniteProbability.actual_prism_cubic
#print axioms Reference.MD06FiniteProbability.actual_cubic_sample_nonempty
#print axioms Reference.MD06FiniteProbability.actual_uniform_cubic_point_mass
