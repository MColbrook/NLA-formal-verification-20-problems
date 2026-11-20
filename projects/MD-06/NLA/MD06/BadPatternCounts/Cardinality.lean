module

public import NLA.MD06.SimplicityBonferroni.Definitions
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06BadPatternCounts
open Reference.MD06Simplicity Reference.MD06CubicConfiguration
open scoped BigOperators

theorem actual_ordered_local_pair_card : Fintype.card OrderedLocalPair = 3 := by decide

attribute [local instance] Classical.propDecidable

theorem actual_strict_vertex_pair_card (n : ℕ) :
    Fintype.card {uv : Fin n × Fin n // uv.1 < uv.2} = n.choose 2 := by
  let e : {uv : Fin n × Fin n // uv.1 < uv.2} ≃
      (Σ v : Fin n, {u : Fin n // u < v}) :=
    { toFun := fun x => ⟨x.val.2,⟨x.val.1,x.property⟩⟩
      invFun := fun x => ⟨(x.2.val,x.1),x.2.property⟩
      left_inv := by rintro ⟨⟨u,v⟩,h⟩; rfl
      right_inv := by rintro ⟨v,u,h⟩; rfl }
  rw [Fintype.card_congr e,Fintype.card_sigma]
  have hc (v : Fin n) : Fintype.card {u : Fin n // u < v} = v.val := by
    change Fintype.card {u : Fin n // u.val < v.val} = v.val
    exact Fintype.card_fin_lt_of_le v.isLt.le
  simp_rw [hc]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n]
  have hs (m : ℕ) : (∑ i ∈ Finset.range m, i) = m.choose 2 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ,ih,Nat.choose_succ_succ]
      simp [Nat.add_comm]
  exact hs n

theorem actual_loop_datum_card (n : ℕ) : Fintype.card (LoopDatum n) = 3*n := by
  have hc : Fintype.card OrderedLocalPair = 3 := by
    simpa only [← Nat.card_eq_fintype_card] using actual_ordered_local_pair_card
  rw [Fintype.card_prod,Fintype.card_fin,hc]
  omega

theorem actual_double_datum_card (n : ℕ) :
    Fintype.card (DoubleDatum n) = 18*n.choose 2 := by
  have hc : Fintype.card OrderedLocalPair = 3 := by
    simpa only [← Nat.card_eq_fintype_card] using actual_ordered_local_pair_card
  simp only [DoubleDatum,Fintype.card_prod,actual_strict_vertex_pair_card,hc,
    Fintype.card_bool]
  ring

theorem actual_bad_datum_card (n : ℕ) :
    Fintype.card (BadDatum n) = 3*n + 18*n.choose 2 := by
  rw [Fintype.card_sum,actual_loop_datum_card,actual_double_datum_card]

#print axioms actual_ordered_local_pair_card
#print axioms actual_strict_vertex_pair_card
#print axioms actual_loop_datum_card
#print axioms actual_double_datum_card
#print axioms actual_bad_datum_card
end Reference.MD06BadPatternCounts