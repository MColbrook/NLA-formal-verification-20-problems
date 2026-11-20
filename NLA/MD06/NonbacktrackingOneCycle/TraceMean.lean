module

public import NLA.MD06.NonbacktrackingOneCycle.OneCollisionMean
public import NLA.MD06.NonbacktrackingWalkExposure.MultipleCollisionMean

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
open Reference.MD06Nonbacktracking Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_closed_word_collision_count_bound {n t : ℕ} (p : Pairing n) (a : Dart n) (ht : 0<t) :
    WordCount p t a a≤Fintype.card {w : Fin t→Fin 2 // ClosedOneCollisionEvent p a t w}+
      Fintype.card {w : Fin t→Fin 2 // 2≤(ExposureRun p (InitialState a) (List.ofFn w)).collisions} := by
  let W:={w : Fin t→Fin 2 // WordRun p a t w=a}
  let C:={w : Fin t→Fin 2 // ClosedOneCollisionEvent p a t w}
  let M:={w : Fin t→Fin 2 // 2≤(ExposureRun p (InitialState a) (List.ofFn w)).collisions}
  have hc (b : W) : (ExposureRun p (InitialState a) (List.ofFn b.val)).current=a :=
    (actual_word_exposure_end p t a b.val).trans b.property
  have hp (b : W) : 1≤(ExposureRun p (InitialState a) (List.ofFn b.val)).collisions := by
    apply actual_closed_collision_positive p a (List.ofFn b.val) _ (hc b)
    intro h
    have hl : (List.ofFn b.val).length=t := by simp
    rw [h] at hl
    simp only [List.length_nil] at hl
    omega
  let f : W→Sum C M:=fun b=>
    if h : (ExposureRun p (InitialState a) (List.ofFn b.val)).collisions=1 then
      Sum.inl ⟨b.val,hc b,h⟩
    else Sum.inr ⟨b.val,by have hh:=hp b;omega⟩
  let g : Sum C M→(Fin t→Fin 2):=Sum.elim Subtype.val Subtype.val
  have hgf (b : W) : g (f b)=b.val := by
    by_cases h : (ExposureRun p (InitialState a) (List.ofFn b.val)).collisions=1 <;> simp [f,g,h]
  have hf : Function.Injective f := by
    intro b c h
    have hh:=congrArg g h
    rw [hgf,hgf] at hh
    exact Subtype.ext hh
  have hcard:=Fintype.card_le_of_injective f hf
  simpa only [W,C,M,WordCount,Fintype.card_sum] using hcard

theorem actual_closed_word_total_collision_count_bound {n : ℕ} (p : Pairing n) (t : ℕ) (ht : 0<t) :
    ClosedWordCount p t≤ClosedOneCollisionWords p t+MultipleCollisionWords p t := by
  unfold ClosedWordCount ClosedOneCollisionWords MultipleCollisionWords
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  exact actual_closed_word_collision_count_bound p a ht

theorem actual_pairing_mean_add (n : ℕ) (f g : Pairing n→ℝ) :
    PairingMean n (fun p=>f p+g p)=PairingMean n f+PairingMean n g := by
  unfold PairingMean
  rw [Finset.sum_add_distrib,add_div]

theorem actual_trace_mean_collision_decomposition (n t : ℕ) (ht : 0<t) :
    MeanNonbacktrackingTrace n t≤MeanClosedOneCollisionWords n t+MeanMultipleCollisionWords n t := by
  unfold MeanNonbacktrackingTrace MeanClosedOneCollisionWords MeanMultipleCollisionWords
  rw [←actual_pairing_mean_add]
  apply actual_pairing_mean_mono
  intro p
  rw [actual_closed_word_trace]
  exact_mod_cast actual_closed_word_total_collision_count_bound p t ht

theorem actual_nonbacktracking_trace_mean_bound (k t : ℕ) (ht : 0<t) (hn : 2*t+1≤Size k) :
    MeanNonbacktrackingTrace (Size k) t≤
      (∑ ell∈t.divisors,3*(Size k : ℝ)*2^ell/(3*(Size k : ℝ)-2*ell+1))+
        27*(t : ℝ)^2*(t+1 : ℕ)^2*2^t/(Size k : ℝ) := by
  exact le_trans (actual_trace_mean_collision_decomposition (Size k) t ht)
    (add_le_add (actual_closed_one_collision_mean_bound k t ht hn) (actual_multiple_collision_mean_bound k t hn))

#print axioms actual_closed_word_collision_count_bound
#print axioms actual_closed_word_total_collision_count_bound
#print axioms actual_pairing_mean_add
#print axioms actual_trace_mean_collision_decomposition
#print axioms actual_nonbacktracking_trace_mean_bound
end Reference.MD06OneCycle
