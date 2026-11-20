module

public import NLA.MD06.NonbacktrackingOneCycle.ClosedPorts
public import NLA.MD06.PairingCounts.PatternRecurrence

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_used_ports_partition {n : ℕ} (C : Finset (Dart n × Dart n)) :
    ∑ v : Fin n,(UsedPorts C v).card=(UsedDarts C).card := by
  let e : {a : Dart n // a∈UsedDarts C} ≃ Σ v : Fin n,{a : Dart n // a∈UsedPorts C v} :=
    {toFun:=fun a=>⟨a.val.1,⟨a.val,by simp [UsedPorts,a.property]⟩⟩
     invFun:=fun a=>⟨a.2.val,(Finset.mem_filter.mp a.2.property).1⟩
     left_inv:=by intro a;rfl
     right_inv:=by
       rintro ⟨v,⟨⟨u,i⟩,ha⟩⟩
       have hv : u=v := (Finset.mem_filter.mp ha).2
       subst v
       rfl}
  have hc:=Fintype.card_congr e
  simpa only [Fintype.card_sigma,Fintype.card_coe] using hc.symm

theorem actual_used_ports_sum_on_support {n : ℕ} (C : Finset (Dart n × Dart n))
    (S : Finset (Fin n)) (hu : ∀ a∈UsedDarts C,a.1∈S) :
    ∑ v∈S,(UsedPorts C v).card=(UsedDarts C).card := by
  have hz (v : Fin n) (hv : v∉S) : (UsedPorts C v).card=0 := by
    have he : UsedPorts C v=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨ha,hav⟩ := Finset.mem_filter.mp ha
      exact hv (hav ▸ hu a ha)
    rw [he];rfl
  calc
    _ = ∑ v : Fin n,(UsedPorts C v).card := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro v _ hv
      exact hz v hv
    _ = _ := actual_used_ports_partition C

theorem actual_exposure_run_valid {n : ℕ} (p : Pairing n) (s : ExposureState n) (w : List (Fin 2))
    (hd : ∀ e∈s.exposed,e.1≠e.2)
    (hdis : ∀ e∈s.exposed,∀ f∈s.exposed,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2}) (hp : Matches s.exposed p) :
    (∀ e∈(ExposureRun p s w).exposed,e.1≠e.2) ∧
      (∀ e∈(ExposureRun p s w).exposed,∀ f∈(ExposureRun p s w).exposed,e≠f →
        Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2}) := by
  induction w generalizing s with
  | nil => exact ⟨hd,hdis⟩
  | cons i w ih =>
    have hv:=actual_step_valid p s i hd hdis hp
    exact ih (ExposureStep p s i) hv.1 hv.2 (actual_step_matches p s i hp)

theorem actual_initial_used_ports_sum {n : ℕ} (p : Pairing n) (a : Dart n) (w : List (Fin 2)) :
    (∑ v∈(ExposureRun p (InitialState a) w).visited,
      (UsedPorts (ExposureRun p (InitialState a) w).exposed v).card)=
      2*(ExposureRun p (InitialState a) w).exposed.card := by
  rw [actual_used_ports_sum_on_support _ _ (actual_initial_run_used_visited p a w)]
  have hv:=actual_exposure_run_valid p (InitialState a) w (by simp [InitialState])
    (by simp [InitialState]) (by simp [InitialState,Matches])
  exact actual_disjoint_pattern_used_card _ hv.1 hv.2

#print axioms actual_used_ports_partition
#print axioms actual_used_ports_sum_on_support
#print axioms actual_exposure_run_valid
#print axioms actual_initial_used_ports_sum
end Reference.MD06OneCycle
