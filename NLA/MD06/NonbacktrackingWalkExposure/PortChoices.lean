module

public import NLA.MD06.NonbacktrackingWalkExposure.Definitions
public import NLA.MD06.NonbacktrackingFoundation.Algebra
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration Reference.MD06Nonbacktracking
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_port_choice_fst {n : ℕ} (a : Dart n) (i : Fin 2) : (PortChoice a i).1=a.1 := rfl

theorem actual_port_choice_ne {n : ℕ} (a : Dart n) (i : Fin 2) : PortChoice a i ≠ a := by
  rcases a with ⟨v,j⟩
  fin_cases j <;> fin_cases i <;> norm_num [PortChoice]

theorem actual_port_choices_injective {n : ℕ} (a : Dart n) : Function.Injective (PortChoice a) := by
  rcases a with ⟨v,j⟩
  intro i k h
  fin_cases j <;> fin_cases i <;> fin_cases k <;> simp_all [PortChoice]

theorem actual_port_choices_exhaustive {n : ℕ} (a b : Dart n)
    (hf : a.1=b.1) (hne : a≠b) : ∃ i : Fin 2, PortChoice a i=b := by
  rcases a with ⟨v,j⟩;rcases b with ⟨w,k⟩
  change v=w at hf;subst w
  have h : PortChoice (v,j) 0=(v,k) ∨ PortChoice (v,j) 1=(v,k) := by
    fin_cases j <;> fin_cases k <;> (first | exact (hne rfl).elim | norm_num [PortChoice])
  rcases h with h | h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩

theorem actual_binary_nonbacktracking_mul {n : ℕ} (p : Pairing n)
    (C : Matrix (Dart n) (Dart n) ℝ) (a b : Dart n) :
    (NonbacktrackingMatrix p * C) a b =
      C (PortChoice (p.val a) 0) b + C (PortChoice (p.val a) 1) b := by
  rw [Matrix.mul_apply]
  simp_rw [actual_nonbacktracking_entry]
  rcases h : p.val a with ⟨v,j⟩
  change (∑ c : Fin n × Fin 3, (if v=c.1 ∧ (v,j)≠c then (1 : ℝ) else 0)*C c b) = _
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ k : Fin 3, if j≠k then C (v,k) b else 0 := by
      rw [Finset.sum_eq_single v]
      · simp [Prod.mk.injEq]
      · intro w _ hw
        simp [Ne.symm hw]
      · simp
    _ = _ := by
      fin_cases j <;> simp [Fin.sum_univ_succ,PortChoice,add_comm]

#print axioms actual_port_choice_fst

#print axioms actual_port_choice_ne

#print axioms actual_port_choices_injective

#print axioms actual_port_choices_exhaustive

#print axioms actual_binary_nonbacktracking_mul
end Reference.MD06WalkExposure
