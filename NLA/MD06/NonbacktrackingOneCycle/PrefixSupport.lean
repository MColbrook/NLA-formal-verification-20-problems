module

public import NLA.MD06.NonbacktrackingOneCycle.Euler
public import NLA.MD06.NonbacktrackingOneCycle.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
attribute [local instance] Classical.propDecidable

theorem actual_exposure_run_append {n : ℕ} (p : Pairing n) (s : ExposureState n)
    (u w : List (Fin 2)) :
    ExposureRun p s (u++w)=ExposureRun p (ExposureRun p s u) w := by
  induction u generalizing s with
  | nil => rfl
  | cons i u ih => exact ih (ExposureStep p s i)

theorem actual_step_exposed_mono {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2) :
    s.exposed⊆(ExposureStep p s i).exposed := by
  by_cases ha : s.current∉UsedDarts s.exposed
  · simpa only [ExposureStep,if_pos ha] using Finset.subset_insert (s.current,p.val s.current) s.exposed
  · simpa only [ExposureStep,if_neg ha] using (Finset.Subset.refl s.exposed)

theorem actual_run_exposed_mono {n : ℕ} (p : Pairing n) (s : ExposureState n) (w : List (Fin 2)) :
    s.exposed⊆(ExposureRun p s w).exposed := by
  induction w generalizing s with
  | nil => exact Finset.Subset.refl _
  | cons i w ih => exact Finset.Subset.trans (actual_step_exposed_mono p s i) (ih (ExposureStep p s i))

theorem actual_used_darts_mono {n : ℕ} (C D : Finset (Dart n × Dart n)) (h : C⊆D) :
    UsedDarts C⊆UsedDarts D := by
  intro a ha
  obtain ⟨e,he,ha⟩ := Finset.mem_biUnion.mp ha
  exact Finset.mem_biUnion.mpr ⟨e,h he,ha⟩

theorem actual_step_current_used {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2) :
    s.current∈UsedDarts (ExposureStep p s i).exposed := by
  by_cases ha : s.current∉UsedDarts s.exposed
  · have hc : s.current∈UsedDarts (insert (s.current,p.val s.current) s.exposed) :=
      Finset.mem_biUnion.mpr ⟨(s.current,p.val s.current),Finset.mem_insert_self _ _,by simp⟩
    simpa only [ExposureStep,if_pos ha] using hc
  · simpa only [ExposureStep,if_neg ha] using Classical.not_not.mp ha

theorem actual_step_partner_used {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2)
    (hp : Matches s.exposed p) : p.val s.current∈UsedDarts (ExposureStep p s i).exposed := by
  exact actual_matching_partner_used (ExposureStep p s i).exposed p (actual_step_matches p s i hp)
    s.current (actual_step_current_used p s i)

theorem actual_first_current_used {n : ℕ} (p : Pairing n) (s : ExposureState n)
    (w : List (Fin 2)) (hw : w≠[]) : s.current∈UsedDarts (ExposureRun p s w).exposed := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons i w =>
    exact actual_used_darts_mono _ _ (actual_run_exposed_mono p (ExposureStep p s i) w)
      (actual_step_current_used p s i)

theorem actual_step_darts_in_final {n : ℕ} (p : Pairing n) (s : ExposureState n)
    (hp : Matches s.exposed p) (u z : List (Fin 2)) (i : Fin 2) :
    (ExposureRun p s u).current∈UsedDarts (ExposureRun p s (u++i::z)).exposed ∧
      p.val (ExposureRun p s u).current∈UsedDarts (ExposureRun p s (u++i::z)).exposed := by
  rw [actual_exposure_run_append,ExposureRun]
  have hm:=actual_used_darts_mono _ _ (actual_run_exposed_mono p (ExposureStep p (ExposureRun p s u) i) z)
  exact ⟨hm (actual_step_current_used p (ExposureRun p s u) i),
    hm (actual_step_partner_used p (ExposureRun p s u) i (actual_run_matches p s u hp))⟩

theorem actual_run_visited_witness {n : ℕ} (p : Pairing n) (s : ExposureState n)
    (w : List (Fin 2)) (v : Fin n) (hv : v∈(ExposureRun p s w).visited) :
    v∈s.visited ∨ ∃ u z : List (Fin 2),∃ i : Fin 2,w=u++i::z ∧
      (p.val (ExposureRun p s u).current).1=v := by
  induction w generalizing s with
  | nil => exact Or.inl hv
  | cons i w ih =>
    rcases ih (ExposureStep p s i) hv with hv | ⟨u,z,j,hw,hj⟩
    · change v∈insert (p.val s.current).1 s.visited at hv
      rcases Finset.mem_insert.mp hv with hv | hv
      · exact Or.inr ⟨[],w,i,rfl,hv.symm⟩
      · exact Or.inl hv
    · exact Or.inr ⟨i::u,z,j,by simp [hw],hj⟩

#print axioms actual_exposure_run_append
#print axioms actual_step_exposed_mono
#print axioms actual_run_exposed_mono
#print axioms actual_used_darts_mono
#print axioms actual_step_current_used
#print axioms actual_step_partner_used
#print axioms actual_first_current_used
#print axioms actual_step_darts_in_final
#print axioms actual_run_visited_witness
end Reference.MD06OneCycle
