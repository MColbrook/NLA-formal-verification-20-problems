module

public import NLA.IV04.PaperPositionalDigitDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace IV04.Paper.Computational.SATReduction

theorem positional_value_succ (b n : ℕ) (d : Fin (n+1) → ℕ) :
    positionalValue b d = d 0 + b * positionalValue b (fun i : Fin n => d i.succ) := by
  unfold positionalValue
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Carry-free positional digits are determined by their actual natural value. -/
theorem positional_value_injective (b : ℕ) (hb : 0 < b) (n : ℕ)
    (d e : Fin n → ℕ) (hd : ∀ i, d i < b) (he : ∀ i, e i < b)
    (hv : positionalValue b d = positionalValue b e) : d = e := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    rw [positional_value_succ, positional_value_succ] at hv
    have hfirst : d 0 = e 0 := by
      have hm := congrArg (fun x : ℕ => x % b) hv
      simpa [Nat.add_mod, Nat.mod_eq_of_lt (hd 0), Nat.mod_eq_of_lt (he 0)] using hm
    have hmul : b * positionalValue b (fun i : Fin n => d i.succ) =
        b * positionalValue b (fun i : Fin n => e i.succ) := by omega
    have htail : (fun i : Fin n => d i.succ) = (fun i : Fin n => e i.succ) :=
      ih _ _ (fun i => hd i.succ) (fun i => he i.succ) (Nat.eq_of_mul_eq_mul_left hb hmul)
    funext i
    refine Fin.cases hfirst (fun j => congrFun htail j) i

theorem positional_value_sum {ι : Type*} [Fintype ι]
    (b n : ℕ) (d : ι → Fin n → ℕ) :
    positionalValue b (fun j => ∑ i, d i j) = ∑ i, positionalValue b (d i) := by
  simp only [positionalValue, Finset.sum_mul]
  exact Finset.sum_comm

/-- Summing actual selected weights equals encoding their summed digits. -/
theorem positional_selected_value {ι : Type*} [Fintype ι]
    (b n : ℕ) (d : ι → Fin n → ℕ) (selected : ι → Bool) :
    (∑ i, if selected i then positionalValue b (d i) else 0) =
      positionalValue b (fun j => ∑ i, if selected i then d i j else 0) := by
  rw [positional_value_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases selected i <;> simp [positionalValue]

theorem positional_value_lt_power (b : ℕ) (hb : 0 < b) (n : ℕ)
    (d : Fin n → ℕ) (hd : ∀ i, d i < b) : positionalValue b d < b^n := by
  induction n with
  | zero => simp [positionalValue]
  | succ n ih =>
    rw [positional_value_succ, pow_succ]
    have ht := ih (fun i : Fin n => d i.succ) (fun i => hd i.succ)
    have hp : 0 < b^n := pow_pos hb _
    have hm : b * positionalValue b (fun i : Fin n => d i.succ) ≤ b * (b^n - 1) :=
      Nat.mul_le_mul_left b (by omega)
    have hstep : b*(b^n-1)+b = b^n*b := by
      have heq : b^n-1+1=b^n := by omega
      calc
        b*(b^n-1)+b = b*(b^n-1+1) := by ring
        _ = b^n*b := by rw [heq]; ring
    have h0 := hd 0
    omega

#print axioms positional_value_succ
#print axioms positional_value_injective
#print axioms positional_value_sum
#print axioms positional_selected_value
#print axioms positional_value_lt_power
end IV04.Paper.Computational.SATReduction