module

public import NLA.IV04.PaperEncoding

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper

theorem flatMap_length_bound {α β : Type*} (xs : List α) (f : α → List β) (B : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ B) : (xs.flatMap f).length ≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have hi := ih (fun x hx => h x (by simp [hx]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

namespace IntegerPartition

theorem matrix_rows_code_bound (P : IntegerPartition) :
    ((List.finRange P.layerCount).flatMap (fun i =>
      (List.finRange P.layerCount).flatMap (fun j =>
        rationalCode (P.rationalLower i j) ++ rationalCode (P.rationalUpper i j)))).length ≤
      P.layerCount^2*(2*(4*P.entryBitBound+3)) := by
  have hrow : ∀ i : Fin P.layerCount,
      ((List.finRange P.layerCount).flatMap (fun j =>
        rationalCode (P.rationalLower i j) ++ rationalCode (P.rationalUpper i j))).length ≤
      P.layerCount*(2*(4*P.entryBitBound+3)) := by
    intro i
    simpa using flatMap_length_bound (List.finRange P.layerCount)
      (fun j => rationalCode (P.rationalLower i j) ++ rationalCode (P.rationalUpper i j))
      (2*(4*P.entryBitBound+3)) (fun j _ => matrix_entry_code_length_bound P i j)
  have h := flatMap_length_bound (List.finRange P.layerCount)
    (fun i => (List.finRange P.layerCount).flatMap (fun j =>
      rationalCode (P.rationalLower i j) ++ rationalCode (P.rationalUpper i j)))
    (P.layerCount*(2*(4*P.entryBitBound+3))) (fun i _ => hrow i)
  simpa [pow_two,Nat.mul_assoc] using h

theorem matrix_box_code_size (P : IntegerPartition) :
    P.matrixBoxCode.length ≤
      (2*P.layerCount^2+1)*(4*P.entryBitBound+3)+2*P.layerCount.size+1 := by
  have hr := matrix_rows_code_bound P
  have ht := threshold_code_length_bound P
  dsimp [matrixBoxCode]
  rw [List.length_append,List.length_append,natural_code_length]
  nlinarith

/-- A concrete cubic bound on the length of the actual dense output code. -/
theorem matrix_box_code_polynomial_size (P : IntegerPartition) :
    P.matrixBoxCode.length ≤
      (2*(4*P.inputBits)^2+1)*(16*P.inputBits+35)+8*P.inputBits+1 := by
  have hN := matrix_dimension_bound P
  have hsize : P.layerCount.size ≤ 4*P.inputBits :=
    (Nat.size_le.mpr P.layerCount.lt_two_pow_self).trans hN
  have hpow : P.layerCount^2 ≤ (4*P.inputBits)^2 := Nat.pow_le_pow_left hN 2
  have hprod : (2*P.layerCount^2+1)*(4*P.entryBitBound+3) ≤
      (2*(4*P.inputBits)^2+1)*(4*P.entryBitBound+3) :=
    Nat.mul_le_mul_right _ (by omega)
  have h := matrix_box_code_size P
  dsimp [entryBitBound] at hprod h
  nlinarith

end IntegerPartition
end IV04.Paper
