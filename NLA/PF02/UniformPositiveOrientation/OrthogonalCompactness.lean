module

public import NLA.PF02.UniformPositiveOrientation.Definitions
public import Mathlib.Topology.Order.Compact

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix
open scoped BigOperators

theorem orthogonal_set_isClosed (k : ℕ) : IsClosed (orthogonalSet k) := by
  apply isClosed_eq _ continuous_const
  fun_prop

theorem orthogonal_entry_bound {k : ℕ} (O : Matrix (Fin k) (Fin k) ℝ)
    (hO : O ∈ orthogonalSet k) (a b : Fin k) : |O a b| ≤ 1 := by
  change O * O.transpose = 1 at hO
  have hs : (∑ c : Fin k, (O a c)^2) = 1 := by
    simpa [Matrix.mul_apply,Matrix.transpose_apply,pow_two] using congrFun (congrFun hO a) a
  have hq : (O a b)^2 ≤ ∑ c : Fin k, (O a c)^2 :=
    Finset.single_le_sum (fun c _ => sq_nonneg (O a c)) (Finset.mem_univ b)
  rw [hs] at hq
  rw [abs_le]
  constructor <;> nlinarith

theorem orthogonal_set_isCompact (k : ℕ) : IsCompact (orthogonalSet k) := by
  let box : Set (Matrix (Fin k) (Fin k) ℝ) := {O | ∀ a b, O a b ∈ Set.Icc (-1) 1}
  have hc : IsCompact box :=
    isCompact_pi_infinite fun a => isCompact_pi_infinite fun b => isCompact_Icc
  apply hc.of_isClosed_subset (orthogonal_set_isClosed k)
  intro O hO a b
  exact abs_le.mp (orthogonal_entry_bound O hO a b)

#print axioms orthogonal_set_isClosed
#print axioms orthogonal_entry_bound
#print axioms orthogonal_set_isCompact
end Reference.PF02UniformPositiveOrientation
