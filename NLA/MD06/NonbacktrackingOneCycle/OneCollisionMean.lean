module

public import NLA.MD06.NonbacktrackingOneCycle.OneCollisionCount
public import NLA.MD06.NonbacktrackingOneCycle.FirstCycleMean

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
open Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_pairing_mean_mono (n : ℕ) (f g : Pairing n→ℝ) (h : ∀ p,f p≤g p) :
    PairingMean n f≤PairingMean n g := by
  unfold PairingMean
  apply div_le_div_of_nonneg_right (Finset.sum_le_sum (fun p _=>h p)) (Nat.cast_nonneg _)

theorem actual_pairing_mean_finset_sum (n : ℕ) {α : Type*} [DecidableEq α]
    (S : Finset α) (f : Pairing n→α→ℝ) :
    PairingMean n (fun p=>∑ a∈S,f p a)=∑ a∈S,PairingMean n (fun p=>f p a) := by
  unfold PairingMean
  rw [Finset.sum_comm,Finset.sum_div]

theorem actual_closed_one_collision_mean_bound (k t : ℕ) (ht : 0<t) (hn : 2*t+1≤Size k) :
    MeanClosedOneCollisionWords (Size k) t≤
      ∑ ell∈t.divisors,3*(Size k : ℝ)*2^ell/(3*(Size k : ℝ)-2*ell+1) := by
  have hm : MeanClosedOneCollisionWords (Size k) t≤
      PairingMean (Size k) (fun p=>∑ ell∈t.divisors,(FirstCycleWords p ell : ℝ)) := by
    apply actual_pairing_mean_mono
    intro p
    exact_mod_cast actual_closed_one_collision_count_bound p t
  rw [actual_pairing_mean_finset_sum] at hm
  apply le_trans hm
  apply Finset.sum_le_sum
  intro ell hell
  have hd:=Nat.mem_divisors.mp hell
  have hlpos : 0<ell := by
    by_contra h
    have he : ell=0 := by omega
    have ht0 : t=0 := by
      obtain ⟨q,hq⟩:=hd.1
      simpa only [he,zero_mul] using hq
    omega
  have hle : ell≤t := Nat.le_of_dvd ht hd.1
  exact actual_first_cycle_mean_bound k ell hlpos (by omega)

#print axioms actual_pairing_mean_mono
#print axioms actual_pairing_mean_finset_sum
#print axioms actual_closed_one_collision_mean_bound
end Reference.MD06OneCycle
