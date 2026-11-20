module

public import NLA.MD06.NonbacktrackingOneCycle.PortPartition

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_closed_collision_positive {n : ℕ} (p : Pairing n) (a : Dart n) (w : List (Fin 2))
    (hw : w≠[]) (hclosed : (ExposureRun p (InitialState a) w).current=a) :
    1≤(ExposureRun p (InitialState a) w).collisions := by
  have he:=actual_initial_exposure_euler p a w
  have hs : 2*(ExposureRun p (InitialState a) w).visited.card≤
      2*(ExposureRun p (InitialState a) w).exposed.card := by
    calc
      _ = ∑ v∈(ExposureRun p (InitialState a) w).visited,(2 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ ∑ v∈(ExposureRun p (InitialState a) w).visited,
          (UsedPorts (ExposureRun p (InitialState a) w).exposed v).card := by
        apply Finset.sum_le_sum
        intro v hv
        exact actual_closed_visited_ports p a w hw hclosed v hv
      _ = _ := actual_initial_used_ports_sum p a w
  omega

theorem actual_one_collision_used_ports_card {n : ℕ} (p : Pairing n) (a : Dart n) (w : List (Fin 2))
    (hw : w≠[]) (hclosed : (ExposureRun p (InitialState a) w).current=a)
    (hc : (ExposureRun p (InitialState a) w).collisions=1)
    (v : Fin n) (hv : v∈(ExposureRun p (InitialState a) w).visited) :
    (UsedPorts (ExposureRun p (InitialState a) w).exposed v).card=2 := by
  have he:=actual_one_collision_edge_vertex_card p a w hc
  have hs : (∑ u∈(ExposureRun p (InitialState a) w).visited,
      (UsedPorts (ExposureRun p (InitialState a) w).exposed u).card)=
        ∑ _u∈(ExposureRun p (InitialState a) w).visited,(2 : ℕ) := by
    rw [actual_initial_used_ports_sum,he]
    simp [Nat.mul_comm]
  have hmin := actual_closed_visited_ports p a w hw hclosed v hv
  have hmax : (UsedPorts (ExposureRun p (InitialState a) w).exposed v).card≤2 := by
    by_contra h
    have hgt : 2<(UsedPorts (ExposureRun p (InitialState a) w).exposed v).card := by omega
    have hlt := Finset.sum_lt_sum
      (fun u hu=>actual_closed_visited_ports p a w hw hclosed u hu) ⟨v,hv,hgt⟩
    rw [hs] at hlt
    exact (lt_irrefl _) hlt
  omega

theorem actual_two_ports_unique_choice {n : ℕ} (C : Finset (Dart n × Dart n)) (b : Dart n)
    (hb : b∈UsedDarts C) (hc : (UsedPorts C b.1).card=2) :
    ∃! i : Fin 2,PortChoice b i∈UsedDarts C := by
  have hbp : b∈UsedPorts C b.1 := by simp [UsedPorts,hb]
  have hi : insert b ((UsedPorts C b.1).erase b)=UsedPorts C b.1 := Finset.insert_erase hbp
  have he : ((UsedPorts C b.1).erase b).card=1 := by
    have hh:=Finset.card_insert_of_notMem (show b∉(UsedPorts C b.1).erase b by simp)
    rw [hi,hc] at hh
    omega
  obtain ⟨d,hd⟩ := Finset.card_eq_one.mp he
  have hde : d∈(UsedPorts C b.1).erase b := by rw [hd];simp
  have hdm : d∈UsedPorts C b.1 := (Finset.mem_erase.mp hde).2
  have hdn : d≠b := (Finset.mem_erase.mp hde).1
  have hdv : d.1=b.1 := (Finset.mem_filter.mp hdm).2
  obtain ⟨i,hi⟩ := actual_port_choices_exhaustive b d hdv.symm hdn.symm
  refine ⟨i,?_,?_⟩
  · change PortChoice b i∈UsedDarts C
    rw [hi];exact (Finset.mem_filter.mp hdm).1
  · intro j hj
    have hm : PortChoice b j∈(UsedPorts C b.1).erase b := by
      apply Finset.mem_erase.mpr
      refine ⟨actual_port_choice_ne b j,?_⟩
      simp [UsedPorts,hj,actual_port_choice_fst]
    rw [hd] at hm
    have hjd : PortChoice b j=d := Finset.mem_singleton.mp hm
    apply actual_port_choices_injective b
    rw [hjd,hi]

#print axioms actual_closed_collision_positive
#print axioms actual_one_collision_used_ports_card
#print axioms actual_two_ports_unique_choice
end Reference.MD06OneCycle
