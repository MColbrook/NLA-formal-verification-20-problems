module

public import NLA.TR27.PaperRootFilter
public import NLA.TR27.PaperProductDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical TensorProduct
namespace NLA.TR27.Paper
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem polynomial_tensor_expansion (D k : ℕ) (b : Fin D → V) (t : ℂ) :
    PiTensorProduct.tprod ℂ (fun _ : Fin k => ∑ j : Fin D, t^j.val • b j) =
      ∑ a : Fin k → Fin D, t^(∑ i, (a i).val) •
        PiTensorProduct.tprod ℂ (fun i => b (a i)) := by
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [MultilinearMap.map_smul_univ, Finset.prod_pow_eq_pow_sum]

/-- Averaging at exactly k(D-1)+1 roots extracts the constant term of the
actual k-fold tensor power of a degree-at-most-D-1 vector polynomial. -/
theorem polynomial_tensor_root_average (D k : ℕ) (b : Fin D → V) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (k*(D-1)+1)) :
    ((k*(D-1)+1 : ℕ) : ℂ)⁻¹ •
      (∑ a : Fin (k*(D-1)+1), PiTensorProduct.tprod ℂ
        (fun _ : Fin k => ∑ j : Fin D, (ζ^a.val)^j.val • b j)) =
      PiTensorProduct.tprod ℂ (fun _ : Fin k => ∑ j : Fin D, (0 : ℂ)^j.val • b j) := by
  simp_rw [polynomial_tensor_expansion]
  apply root_average_terms (by omega) hζ
  intro a
  have hsum : (∑ i : Fin k, (a i).val) ≤ k*(D-1) := by
    calc
      _ ≤ ∑ _ : Fin k, (D-1) := Finset.sum_le_sum (fun i _ => by
        have h := (a i).isLt
        omega)
      _ = _ := by simp
  omega

#print axioms polynomial_tensor_root_average
end NLA.TR27.Paper
