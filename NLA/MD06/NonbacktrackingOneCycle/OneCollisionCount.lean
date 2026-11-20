module

public import NLA.MD06.NonbacktrackingOneCycle.PrefixWords

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_one_collision_word_count_bound {n t : ℕ} (p : Pairing n) (a : Dart n) :
    Fintype.card {w : Fin t→Fin 2 // ClosedOneCollisionEvent p a t w}≤
      ∑ ell∈t.divisors,Fintype.card {v : Fin ell→Fin 2 // FirstCycleEvent p a ell v} := by
  let W:={w : Fin t→Fin 2 // ClosedOneCollisionEvent p a t w}
  let Target:=Σ ell : {ell : ℕ // ell∈t.divisors},{v : Fin ell.val→Fin 2 // FirstCycleEvent p a ell.val v}
  have hex (b : W) := actual_closed_one_collision_first_cycle_word p a b.val b.property
  let ell (b : W) : ℕ:=Classical.choose (hex b)
  have hell (b : W) : ell b∈t.divisors := (Classical.choose_spec (hex b)).1
  let hle (b : W) : ell b≤t := Classical.choose (Classical.choose_spec (hex b)).2
  have hinfo (b : W) : FirstCycleEvent p a (ell b) (PrefixWord (hle b) b.val) ∧
      (ExposureRun p (InitialState a) (List.ofFn (PrefixWord (hle b) b.val))).exposed=
        (ExposureRun p (InitialState a) (List.ofFn b.val)).exposed :=
    Classical.choose_spec (Classical.choose_spec (hex b)).2
  let f : W→Target:=fun b=>⟨⟨ell b,hell b⟩,⟨PrefixWord (hle b) b.val,(hinfo b).1⟩⟩
  have hf : Function.Injective f := by
    intro b c he
    have hlist:=congrArg (fun d : Target=>List.ofFn d.2.val) he
    change List.ofFn (PrefixWord (hle b) b.val)=List.ofFn (PrefixWord (hle c) c.val) at hlist
    have hC : (ExposureRun p (InitialState a) (List.ofFn b.val)).exposed=
        (ExposureRun p (InitialState a) (List.ofFn c.val)).exposed :=
      (hinfo b).2.symm.trans ((congrArg (fun w : List (Fin 2)=>(ExposureRun p (InitialState a) w).exposed) hlist).trans (hinfo c).2)
    have hw:=actual_one_collision_support_unique_length p a (List.ofFn b.val) (List.ofFn c.val)
      b.property.1 b.property.2 c.property.1 c.property.2 hC (by simp)
    exact Subtype.ext (List.ofFn_injective hw)
  have hc:=Fintype.card_le_of_injective f hf
  simp only [Target,Fintype.card_sigma] at hc
  have hs : (∑ ell∈t.divisors,Fintype.card {v : Fin ell→Fin 2 // FirstCycleEvent p a ell v})=
      ∑ ell : {ell : ℕ // ell∈t.divisors},Fintype.card {v : Fin ell.val→Fin 2 // FirstCycleEvent p a ell.val v} :=
    Finset.sum_subtype (p:=fun ell : ℕ=>ell∈t.divisors) t.divisors (fun _=>Iff.rfl)
    (fun ell : ℕ=>Fintype.card {v : Fin ell→Fin 2 // FirstCycleEvent p a ell v})
  rw [←hs] at hc
  exact hc

theorem actual_closed_one_collision_count_bound {n : ℕ} (p : Pairing n) (t : ℕ) :
    ClosedOneCollisionWords p t≤∑ ell∈t.divisors,FirstCycleWords p ell := by
  unfold ClosedOneCollisionWords FirstCycleWords
  calc
    _ ≤ ∑ a : Dart n,∑ ell∈t.divisors,Fintype.card {w : Fin ell→Fin 2 // FirstCycleEvent p a ell w} := by
      apply Finset.sum_le_sum
      intro a _
      exact actual_one_collision_word_count_bound p a
    _ = _ := Finset.sum_comm

#print axioms actual_one_collision_word_count_bound
#print axioms actual_closed_one_collision_count_bound
end Reference.MD06OneCycle
