module

public import NLA.MD06.NonbacktrackingWalkExposure.KnownMate
public import NLA.MD06.NonbacktrackingWalkExposure.RunBounds

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts
attribute [local instance] Classical.propDecidable

theorem actual_step_used_visited {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2)
    (hc : s.current.1∈s.visited) (hu : ∀ a∈UsedDarts s.exposed,a.1∈s.visited) :
    ∀ a∈UsedDarts (ExposureStep p s i).exposed,a.1∈(ExposureStep p s i).visited := by
  intro a ha
  change a.1∈insert (p.val s.current).1 s.visited
  by_cases hf : s.current ∉ UsedDarts s.exposed
  · have h : a∈UsedDarts (insert (s.current,p.val s.current) s.exposed) := by
      simpa [ExposureStep,hf] using ha
    obtain ⟨e,he,hae⟩ := Finset.mem_biUnion.mp h
    rcases Finset.mem_insert.mp he with he | he
    · subst e
      simp only [Finset.mem_insert,Finset.mem_singleton] at hae
      rcases hae with hae | hae
      · subst a;exact Finset.mem_insert_of_mem hc
      · subst a;exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hu a (Finset.mem_biUnion.mpr ⟨e,he,hae⟩))
  · have h : a∈UsedDarts s.exposed := by simpa [ExposureStep,hf] using ha
    exact Finset.mem_insert_of_mem (hu a h)

theorem actual_step_old_visited {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2)
    (hp : Matches s.exposed p) (hu : ∀ a∈UsedDarts s.exposed,a.1∈s.visited)
    (ha : s.current∈UsedDarts s.exposed) : (ExposureStep p s i).visited=s.visited := by
  exact Finset.insert_eq_of_mem (hu (p.val s.current)
    (actual_matching_partner_used s.exposed p hp s.current ha))

theorem actual_run_current_visited {n : ℕ} (p : Pairing n) (s : ExposureState n) (w : List (Fin 2))
    (hc : s.current.1∈s.visited) : (ExposureRun p s w).current.1∈(ExposureRun p s w).visited := by
  induction w generalizing s with
  | nil => exact hc
  | cons i w ih => exact ih (ExposureStep p s i) (actual_step_current_visited p s i)

theorem actual_run_used_visited {n : ℕ} (p : Pairing n) (s : ExposureState n) (w : List (Fin 2))
    (hc : s.current.1∈s.visited) (hu : ∀ a∈UsedDarts s.exposed,a.1∈s.visited) :
    ∀ a∈UsedDarts (ExposureRun p s w).exposed,a.1∈(ExposureRun p s w).visited := by
  induction w generalizing s with
  | nil => exact hu
  | cons i w ih =>
    exact ih (ExposureStep p s i) (actual_step_current_visited p s i)
      (actual_step_used_visited p s i hc hu)

theorem actual_initial_run_used_visited {n : ℕ} (p : Pairing n) (a : Dart n) (w : List (Fin 2)) :
    ∀ b∈UsedDarts (ExposureRun p (InitialState a) w).exposed,
      b.1∈(ExposureRun p (InitialState a) w).visited := by
  apply actual_run_used_visited
  · exact Finset.mem_singleton_self _
  · simp [InitialState,UsedDarts]

#print axioms actual_step_used_visited

#print axioms actual_step_old_visited

#print axioms actual_run_current_visited

#print axioms actual_run_used_visited

#print axioms actual_initial_run_used_visited
end Reference.MD06WalkExposure
