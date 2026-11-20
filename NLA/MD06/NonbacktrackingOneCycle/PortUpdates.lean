module

public import NLA.MD06.NonbacktrackingOneCycle.NoCollision

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
attribute [local instance] Classical.propDecidable

theorem actual_used_ports_insert_at_first {n : ℕ} (C : Finset (Dart n × Dart n)) (a b : Dart n)
    (ha : a∉UsedDarts C) (hab : b.1≠a.1) :
    (UsedPorts (insert (a,b) C) a.1).card=(UsedPorts C a.1).card+1 := by
  have he : UsedPorts (insert (a,b) C) a.1=insert a (UsedPorts C a.1) := by
    ext d
    simp [UsedPorts,actual_used_insert_pair]
    aesop
  rw [he]
  apply Finset.card_insert_of_notMem
  intro h
  exact ha (Finset.mem_filter.mp h).1

theorem actual_used_ports_insert_at_second {n : ℕ} (C : Finset (Dart n × Dart n)) (a b : Dart n)
    (hb : b∉UsedDarts C) (hab : a.1≠b.1) :
    (UsedPorts (insert (a,b) C) b.1).card=(UsedPorts C b.1).card+1 := by
  have he : UsedPorts (insert (a,b) C) b.1=insert b (UsedPorts C b.1) := by
    ext d
    simp [UsedPorts,actual_used_insert_pair]
    aesop
  rw [he]
  apply Finset.card_insert_of_notMem
  intro h
  exact hb (Finset.mem_filter.mp h).1

theorem actual_used_ports_insert_else {n : ℕ} (C : Finset (Dart n × Dart n)) (a b : Dart n)
    (v : Fin n) (ha : a.1≠v) (hb : b.1≠v) :
    UsedPorts (insert (a,b) C) v=UsedPorts C v := by
  ext d
  simp [UsedPorts,actual_used_insert_pair]
  aesop

theorem actual_fresh_new_step_ports {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2)
    (hc : s.current.1∈s.visited) (hu : ∀ a∈UsedDarts s.exposed,a.1∈s.visited)
    (hf : s.current∉UsedDarts s.exposed) (hn : (p.val s.current).1∉s.visited) (v : Fin n) :
    (UsedPorts (ExposureStep p s i).exposed v).card=
      (UsedPorts s.exposed v).card+(if s.current.1=v then 1 else 0)+
        (if (p.val s.current).1=v then 1 else 0) := by
  have hneq : (p.val s.current).1≠s.current.1 := by intro h;exact hn (h ▸ hc)
  have hb : p.val s.current∉UsedDarts s.exposed := by intro h;exact hn (hu _ h)
  change (UsedPorts (if s.current∉UsedDarts s.exposed then insert (s.current,p.val s.current) s.exposed else s.exposed) v).card=_
  rw [if_pos hf]
  by_cases hv : s.current.1=v
  · subst v
    simpa [hneq] using actual_used_ports_insert_at_first s.exposed s.current (p.val s.current) hf hneq
  · by_cases hv' : (p.val s.current).1=v
    · subst v
      simpa [hneq,hneq.symm] using actual_used_ports_insert_at_second s.exposed s.current (p.val s.current) hb hneq.symm
    · simp [actual_used_ports_insert_else s.exposed s.current (p.val s.current) v hv hv',hv,hv']

#print axioms actual_used_ports_insert_at_first
#print axioms actual_used_ports_insert_at_second
#print axioms actual_used_ports_insert_else
#print axioms actual_fresh_new_step_ports
end Reference.MD06OneCycle
