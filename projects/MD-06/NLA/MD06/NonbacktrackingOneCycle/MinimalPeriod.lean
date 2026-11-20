module

public import NLA.MD06.NonbacktrackingOneCycle.SupportIteration
public import NLA.MD06.NonbacktrackingOneCycle.FirstCollisionSplit

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
attribute [local instance] Classical.propDecidable

theorem actual_zero_collision_prefix {n : ℕ} (p : Pairing n) (a : Dart n) (u : List (Fin 2))
    (hz : (ExposureRun p (InitialState a) u).collisions=0) (q : ℕ) :
    (ExposureRun p (InitialState a) (u.take q)).collisions=0 := by
  have hm:=actual_run_collision_mono p (ExposureRun p (InitialState a) (u.take q)) (u.drop q)
  rw [←actual_exposure_run_append,List.take_append_drop] at hm
  omega

theorem actual_first_cycle_minimal_period {n : ℕ} (p : Pairing n) (a : Dart n)
    (u z : List (Fin 2)) (i : Fin 2)
    (hz : (ExposureRun p (InitialState a) u).collisions=0)
    (hv : (p.val (ExposureRun p (InitialState a) u).current).1∈
      (ExposureRun p (InitialState a) u).visited)
    (hclosed : (ExposureRun p (InitialState a) (u++i::z)).current=a)
    (hc : (ExposureRun p (InitialState a) (u++i::z)).collisions=1) :
    Function.minimalPeriod (SupportNext p (ExposureRun p (InitialState a) (u++i::z)).exposed) a=u.length+1 := by
  let f:=SupportNext p (ExposureRun p (InitialState a) (u++i::z)).exposed
  have hw : u++i::z≠[] := by simp
  have heq : (u++[i])++z=u++i::z := by simp
  have hfclosed : (ExposureRun p (InitialState a) (u++[i])).current=a := by
    simpa only [actual_exposure_run_append,ExposureRun] using actual_first_collision_returns_start p a u z i hz hv hclosed hc
  have hpr:=actual_closed_prefix_iteration p a (u++[i]) z
    (by rw [heq];exact hw) (by rw [heq];exact hclosed) (by rw [heq];exact hc)
  have hpr' : (ExposureRun p (InitialState a) (u++[i])).current=f^[u.length+1] a := by
    simpa only [heq,List.length_append,List.length_singleton,f] using hpr
  have hfirst : Function.IsPeriodicPt f (u.length+1) a := hpr'.symm.trans hfclosed
  have hfullpr:=actual_closed_prefix_iteration p a (u++i::z) [] (by simp)
    (by simpa using hclosed) (by simpa using hc)
  have hfull : Function.IsPeriodicPt f (u++i::z).length a := by
    have hh : (ExposureRun p (InitialState a) (u++i::z)).current=f^[(u++i::z).length] a := by
      simpa only [List.append_nil,f] using hfullpr
    exact hh.symm.trans hclosed
  have hjpos : 0<Function.minimalPeriod f a := hfull.minimalPeriod_pos (by simp)
  apply le_antisymm (hfirst.minimalPeriod_le (by omega))
  by_contra h
  have hjle : Function.minimalPeriod f a≤u.length := by omega
  let j:=Function.minimalPeriod f a
  have hword : u.take j++(u.drop j++i::z)=u++i::z := by
    rw [←List.append_assoc,List.take_append_drop]
  have hsmallpr:=actual_closed_prefix_iteration p a (u.take j) (u.drop j++i::z)
    (by rw [hword];exact hw) (by rw [hword];exact hclosed) (by rw [hword];exact hc)
  have hsmall : (ExposureRun p (InitialState a) (u.take j)).current=f^[j] a := by
    simpa only [hword,List.length_take,Nat.min_eq_left hjle,f,j] using hsmallpr
  have hsclosed : (ExposureRun p (InitialState a) (u.take j)).current=a :=
    hsmall.trans (Function.iterate_minimalPeriod (f:=f) (x:=a))
  have hnonempty : u.take j≠[] := by
    intro hh
    have hlen : (u.take j).length=j := List.length_take_of_le hjle
    rw [hh] at hlen
    change 0=j at hlen
    omega
  have hpositive:=actual_closed_collision_positive p a (u.take j) hnonempty hsclosed
  rw [actual_zero_collision_prefix p a u hz j] at hpositive
  omega

theorem actual_one_collision_first_cycle_divides {n : ℕ} (p : Pairing n) (a : Dart n)
    (u z : List (Fin 2)) (i : Fin 2)
    (hz : (ExposureRun p (InitialState a) u).collisions=0)
    (hv : (p.val (ExposureRun p (InitialState a) u).current).1∈
      (ExposureRun p (InitialState a) u).visited)
    (hclosed : (ExposureRun p (InitialState a) (u++i::z)).current=a)
    (hc : (ExposureRun p (InitialState a) (u++i::z)).collisions=1) :
    u.length+1∣(u++i::z).length := by
  have hpr:=actual_closed_prefix_iteration p a (u++i::z) [] (by simp)
    (by simpa using hclosed) (by simpa using hc)
  have hperiod : Function.IsPeriodicPt (SupportNext p (ExposureRun p (InitialState a) (u++i::z)).exposed)
      (u++i::z).length a := by
    have hh : (ExposureRun p (InitialState a) (u++i::z)).current=
        (SupportNext p (ExposureRun p (InitialState a) (u++i::z)).exposed)^[(u++i::z).length] a := by
      simpa only [List.append_nil] using hpr
    exact hh.symm.trans hclosed
  have hd:=hperiod.minimalPeriod_dvd
  rw [actual_first_cycle_minimal_period p a u z i hz hv hclosed hc] at hd
  exact hd

theorem actual_closed_one_collision_cycle_prefix {n : ℕ} (p : Pairing n) (a : Dart n)
    (w : List (Fin 2)) (hclosed : (ExposureRun p (InitialState a) w).current=a)
    (hc : (ExposureRun p (InitialState a) w).collisions=1) :
    ∃ u z : List (Fin 2),∃ i : Fin 2,w=u++i::z ∧
      (ExposureRun p (InitialState a) u).collisions=0 ∧
      (ExposureRun p (InitialState a) (u++[i])).current=a ∧
      u.length+1∣w.length ∧
      (ExposureRun p (InitialState a) (u++[i])).exposed=(ExposureRun p (InitialState a) w).exposed := by
  obtain ⟨u,z,i,hw,hz,hf,hv⟩:=actual_first_collision_split p (InitialState a) w rfl (by omega)
  have hclosed' : (ExposureRun p (InitialState a) (u++i::z)).current=a := hw ▸ hclosed
  have hc' : (ExposureRun p (InitialState a) (u++i::z)).collisions=1 := hw ▸ hc
  refine ⟨u,z,i,hw,hz,?_,?_,?_⟩
  · simpa only [actual_exposure_run_append,ExposureRun] using actual_first_collision_returns_start p a u z i hz hv hclosed' hc'
  · rw [hw]
    exact actual_one_collision_first_cycle_divides p a u z i hz hv hclosed' hc'
  · rw [hw]
    exact actual_one_collision_after_first_return_no_new_edges p a u z i hz hv hclosed' hc'

#print axioms actual_zero_collision_prefix
#print axioms actual_first_cycle_minimal_period
#print axioms actual_one_collision_first_cycle_divides
#print axioms actual_closed_one_collision_cycle_prefix
end Reference.MD06OneCycle
