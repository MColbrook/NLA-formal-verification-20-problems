module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Exact interpreted atoms, genuine finite scans, and derived execution charges. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.Definitions
public import Mathlib.Data.List.Sort
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.LexTensorExecution
noncomputable section

@[simp] theorem value_pure {α : Type} (x : α) : (pureRun x).value=x := rfl
@[simp] theorem value_bind {α β : Type} (x : Run α) (f : α → Run β) :
    (bindRun x f).value=(f x.value).value := rfl
@[simp] theorem charge_pure {α : Type} (x : α) : charge (pureRun x)=0 := rfl
@[simp] theorem charge_bind {α β : Type} (x : Run α) (f : α → Run β) :
    charge (bindRun x f)=charge x+charge (f x.value) := by
  simp [charge,bindRun,List.map_append,List.sum_append]
@[simp] theorem value_lift {α : Type} (x : Reference.LexTensorArithmeticExecution.Run α) :
    (liftRun x).value=x.value := rfl
@[simp] theorem charge_lift {α : Type} (x : Reference.LexTensorArithmeticExecution.Run α) :
    charge (liftRun x)=Reference.LexTensorArithmeticExecution.charge x := by
  simp only [charge,liftRun,List.map_map]
  rfl

@[simp] theorem value_branch (b : Bool) : (branchRun b).value=b := rfl
@[simp] theorem charge_branch (b : Bool) : charge (branchRun b)=1 := rfl
@[simp] theorem value_equalReal (x y : ℝ) : (equalRealRun x y).value=decide (x=y) := rfl
@[simp] theorem charge_equalReal (x y : ℝ) : charge (equalRealRun x y)=1 := rfl
@[simp] theorem value_equalNat (x y : ℕ) : (equalNatRun x y).value=decide (x=y) := rfl
@[simp] theorem charge_equalNat (x y : ℕ) : charge (equalNatRun x y)=1 := rfl
@[simp] theorem value_lessNat (x y : ℕ) : (lessNatRun x y).value=decide (x<y) := rfl
@[simp] theorem charge_lessNat (x y : ℕ) : charge (lessNatRun x y)=1 := rfl
@[simp] theorem value_addNat (x y : ℕ) : (addNatRun x y).value=x+y := rfl
@[simp] theorem charge_addNat (x y : ℕ) : charge (addNatRun x y)=1 := rfl
@[simp] theorem value_subNat (x y : ℕ) : (subNatRun x y).value=x-y := rfl
@[simp] theorem charge_subNat (x y : ℕ) : charge (subNatRun x y)=1 := rfl
@[simp] theorem value_modNat (x y : ℕ) : (modNatRun x y).value=x%y := rfl
@[simp] theorem charge_modNat (x y : ℕ) : charge (modNatRun x y)=1 := rfl

@[simp] theorem filterRun_value {α : Type} (p : α → Run Bool) (xs : List α) :
    (filterRun p xs).value=xs.filter (fun i => (p i).value) := by
  induction xs with
  | nil => rfl
  | cons i is ih => simp [filterRun,ih,List.filter_cons]

theorem filterRun_charge {α : Type} (p : α → Run Bool) (xs : List α) (C : ℕ)
    (h : ∀ i ∈ xs, charge (p i) ≤ C) :
    charge (filterRun p xs) ≤ xs.length*(C+1) := by
  induction xs with
  | nil => simp [filterRun]
  | cons i is ih =>
      have hi := h i (by simp)
      have ht : ∀ j ∈ is, charge (p j) ≤ C := fun j hj => h j (by simp [hj])
      have hi' := ih ht
      simp only [filterRun,charge_bind,charge_branch,value_branch,charge_pure,
        List.length_cons]
      nlinarith

@[simp] theorem ordinalRun_value {m : ℕ} (i : Fin m) (xs : List (Fin m)) :
    (ordinalRun i xs).value=xs.idxOf i := by
  induction xs with
  | nil => rfl
  | cons j js ih =>
      by_cases h : i=j
      · subst j
        simp [ordinalRun]
      · have hv : i.val≠j.val := fun hh => h (Fin.ext hh)
        have hb : (j==i)=false := beq_eq_false_iff_ne.mpr (Ne.symm h)
        simp [ordinalRun,hv,ih,List.idxOf_cons,hb,Nat.add_comm]

theorem ordinalRun_charge {m : ℕ} (i : Fin m) (xs : List (Fin m)) :
    charge (ordinalRun i xs) ≤ 3*xs.length := by
  induction xs with
  | nil => simp [ordinalRun]
  | cons j js ih =>
      by_cases h : i.val=j.val
      · simp [ordinalRun,h]; omega
      · simp [ordinalRun,h]; omega

#print axioms filterRun_value
#print axioms filterRun_charge
#print axioms ordinalRun_value
#print axioms ordinalRun_charge
end
end Reference.LexTensorExecution
