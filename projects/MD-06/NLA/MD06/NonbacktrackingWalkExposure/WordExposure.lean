module

public import NLA.MD06.NonbacktrackingWalkExposure.WordCounts
public import NLA.MD06.NonbacktrackingWalkExposure.CollisionConsequences
public import Mathlib.Data.List.OfFn

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability
attribute [local instance] Classical.propDecidable

theorem actual_word_run_list {n : ℕ} (p : Pairing n) (t : ℕ) (a : Dart n) (w : Fin t→Fin 2) :
    WordRun p a t w=WalkEnd p a (List.ofFn w) := by
  induction t generalizing a with
  | zero => simp [WordRun,WalkEnd]
  | succ t ih =>
    rw [List.ofFn_succ,WalkEnd,WordRun]
    exact ih (PortChoice (p.val a) (w 0)) (fun j=>w j.succ)

theorem actual_word_exposure_end {n : ℕ} (p : Pairing n) (t : ℕ) (a : Dart n) (w : Fin t→Fin 2) :
    (ExposureRun p (InitialState a) (List.ofFn w)).current=WordRun p a t w := by
  calc
    _ = WalkEnd p (InitialState a).current (List.ofFn w) := actual_run_end p (InitialState a) (List.ofFn w)
    _ = _ := (actual_word_run_list p t a w).symm

theorem actual_binary_word_two_collision_bound (k t : ℕ) (a : Dart (Size k)) (w : Fin t→Fin 2)
    (hn : 2*t+1≤Size k) :
    PairingProbability (Size k)
      (fun p=>2≤(ExposureRun p (InitialState a) (List.ofFn w)).collisions) ≤
      9*(t : ℝ)^2*(t+1 : ℕ)^2/(Size k : ℝ)^2 := by
  simpa only [List.length_ofFn] using actual_initial_two_collision_bound k a (List.ofFn w)
    (by simpa only [List.length_ofFn] using hn)

#print axioms actual_word_run_list
#print axioms actual_word_exposure_end
#print axioms actual_binary_word_two_collision_bound
end Reference.MD06WalkExposure
