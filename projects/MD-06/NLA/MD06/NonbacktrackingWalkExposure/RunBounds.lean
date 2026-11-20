module

public import NLA.MD06.NonbacktrackingWalkExposure.StateBasic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts

theorem actual_run_matches {n : ℕ} (p : Pairing n) (s : ExposureState n) (w : List (Fin 2))
    (hp : Matches s.exposed p) : Matches (ExposureRun p s w).exposed p := by
  induction w generalizing s with
  | nil => exact hp
  | cons i w ih => exact ih (ExposureStep p s i) (actual_step_matches p s i hp)

theorem actual_run_end {n : ℕ} (p : Pairing n) (s : ExposureState n) (w : List (Fin 2)) :
    (ExposureRun p s w).current=WalkEnd p s.current w := by
  induction w generalizing s with
  | nil => rfl
  | cons i w ih => exact ih (ExposureStep p s i)

theorem actual_run_exposure_card {n : ℕ} (p : Pairing n) (s : ExposureState n) (w : List (Fin 2)) :
    (ExposureRun p s w).exposed.card ≤ s.exposed.card+w.length := by
  induction w generalizing s with
  | nil => exact le_refl _
  | cons i w ih =>
    have h := ih (ExposureStep p s i)
    have h1 := actual_step_exposure_card p s i
    simp only [ExposureRun,List.length_cons]
    omega

theorem actual_run_visited_card {n : ℕ} (p : Pairing n) (s : ExposureState n) (w : List (Fin 2)) :
    (ExposureRun p s w).visited.card ≤ s.visited.card+w.length := by
  induction w generalizing s with
  | nil => exact le_refl _
  | cons i w ih =>
    have h := ih (ExposureStep p s i)
    have h1 := actual_step_visited_card p s i
    simp only [ExposureRun,List.length_cons]
    omega

theorem actual_run_collision_card {n : ℕ} (p : Pairing n) (s : ExposureState n) (w : List (Fin 2)) :
    (ExposureRun p s w).collisions ≤ s.collisions+w.length := by
  induction w generalizing s with
  | nil => exact le_refl _
  | cons i w ih =>
    have h := ih (ExposureStep p s i)
    have h1 := actual_step_collision_card p s i
    simp only [ExposureRun,List.length_cons]
    omega

theorem actual_initial_run_visited_card {n : ℕ} (p : Pairing n) (a : Dart n) (w : List (Fin 2)) :
    (ExposureRun p (InitialState a) w).visited.card ≤ w.length+1 := by
  simpa [InitialState,Nat.add_comm] using actual_run_visited_card p (InitialState a) w

#print axioms actual_run_matches

#print axioms actual_run_end

#print axioms actual_run_exposure_card

#print axioms actual_run_visited_card

#print axioms actual_run_collision_card

#print axioms actual_initial_run_visited_card
end Reference.MD06WalkExposure
