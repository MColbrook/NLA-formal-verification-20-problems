module

public import NLA.MD06.NonbacktrackingOneCycle.ClosedPrefixProbability
public import NLA.MD06.NonbacktrackingOneCycle.ClosedPorts
public import NLA.MD06.NonbacktrackingOneCycle.CycleDefinitions
public import NLA.MD06.NonbacktrackingWalkExposure.MultipleCollisionMean

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
open Reference.MD06ConditionalPartner Reference.MD06AdaptiveExposure Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_first_cycle_word_probability_bound (k t : ℕ) (ht : 0<t) (hn : 2*t+1≤Size k)
    (a : Dart (Size k)) (w : Fin t→Fin 2) :
    PairingProbability (Size k) (fun p=>FirstCycleEvent p a t w)≤
      1/(3*(Size k : ℝ)-2*t+1) := by
  have hne : List.ofFn w≠[] := by
    intro h
    have hl : (List.ofFn w).length=t := by simp
    rw [h] at hl
    simp only [List.length_nil] at hl
    omega
  obtain ⟨u,i,hu⟩:=actual_nonempty_list_last (List.ofFn w) hne
  have hlen : u.length+1=t := by
    have hh : (List.ofFn w).length=t := by simp
    simpa only [hu,List.length_append,List.length_singleton] using hh
  have htake : (List.ofFn w).take (t-1)=u := by
    rw [hu]
    have hsub : t-1=u.length := by omega
    rw [hsub,List.take_append]
    simp
  have hp0 : 0<3*Size k-2*u.length-1 := by omega
  have hb:=actual_first_cycle_prefix_probability_bound k a u i hp0
  have hmono : PairingProbability (Size k) (fun p=>FirstCycleEvent p a t w)≤
      PairingProbability (Size k) (fun p=> (ExposureRun p (InitialState a) u).collisions=0 ∧
        (ExposureRun p (InitialState a) (u++[i])).current=a) := by
    rw [←actual_empty_conditional_probability,←actual_empty_conditional_probability]
    apply actual_conditional_probability_mono
    intro p _ h
    exact ⟨htake ▸ h.2.2,hu ▸ h.2.1⟩
  have hnat : (3*Size k-2*u.length-1)+2*t=3*Size k+1 := by omega
  have hreal:=congrArg (fun j : ℕ=>(j : ℝ)) hnat
  push_cast at hreal
  have hden : ((3*Size k-2*u.length-1 : ℕ) : ℝ)=3*(Size k : ℝ)-2*t+1 := by
    simp only [Size,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    linarith
  exact le_trans hmono (by simpa only [hden] using hb)

theorem actual_first_cycle_mean_identity (n t : ℕ) :
    MeanFirstCycleWords n t=∑ a : Dart n,∑ w : Fin t→Fin 2,
      PairingProbability n (fun p=>FirstCycleEvent p a t w) := by
  simpa only [MeanFirstCycleWords,FirstCycleWords,Fintype.card_eq_nat_card] using
    actual_pairing_mean_fiber_card n (fun p a w=>FirstCycleEvent p a t w)

theorem actual_first_cycle_mean_bound (k t : ℕ) (ht : 0<t) (hn : 2*t+1≤Size k) :
    MeanFirstCycleWords (Size k) t≤3*(Size k : ℝ)*2^t/(3*(Size k : ℝ)-2*t+1) := by
  rw [actual_first_cycle_mean_identity]
  calc
    _ ≤ ∑ _a : Dart (Size k),∑ _w : Fin t→Fin 2,(1/(3*(Size k : ℝ)-2*t+1)) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro w _
      exact actual_first_cycle_word_probability_bound k t ht hn a w
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Fintype.card_prod]
      push_cast
      ring

#print axioms actual_first_cycle_word_probability_bound
#print axioms actual_first_cycle_mean_identity
#print axioms actual_first_cycle_mean_bound
end Reference.MD06OneCycle
