module

public import NLA.MD06.NonbacktrackingOneCycle.CycleDefinitions
public import NLA.MD06.NonbacktrackingOneCycle.WordUnique

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
attribute [local instance] Classical.propDecidable

theorem actual_prefix_word_list {t ell : ℕ} (h : ell≤t) (w : Fin t→Fin 2) :
    List.ofFn (PrefixWord h w)=(List.ofFn w).take ell := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left h]
  · intro i hi hj
    simp [PrefixWord]

theorem actual_closed_one_collision_first_cycle_word {n t : ℕ} (p : Pairing n) (a : Dart n)
    (w : Fin t→Fin 2) (hw : ClosedOneCollisionEvent p a t w) :
    ∃ ell : ℕ,ell∈t.divisors ∧ ∃ h : ell≤t,
      FirstCycleEvent p a ell (PrefixWord h w) ∧
        (ExposureRun p (InitialState a) (List.ofFn (PrefixWord h w))).exposed=
          (ExposureRun p (InitialState a) (List.ofFn w)).exposed := by
  obtain ⟨u,z,i,heq,hz,hclosed,hdvd,hC⟩:=actual_closed_one_collision_cycle_prefix p a (List.ofFn w) hw.1 hw.2
  have hlen : (u++i::z).length=t := by rw [←heq];simp
  have ht : t≠0 := by simp only [List.length_append,List.length_cons] at hlen;omega
  have hle : u.length+1≤t := by simp only [List.length_append,List.length_cons] at hlen;omega
  have hprefix : List.ofFn (PrefixWord hle w)=u++[i] := by
    rw [actual_prefix_word_list,heq,List.take_append]
    have hu : u.take (u.length+1)=u := List.take_of_length_le (by omega)
    rw [hu]
    simp
  have htake : (List.ofFn (PrefixWord hle w)).take (u.length+1-1)=u := by
    rw [hprefix]
    simp
  have hmem : u.length+1∈t.divisors := Nat.mem_divisors.mpr ⟨by simpa only [List.length_ofFn] using hdvd,ht⟩
  refine ⟨u.length+1,hmem,hle,?_,?_⟩
  · exact ⟨by omega,hprefix.symm ▸ hclosed,htake.symm ▸ hz⟩
  · rw [hprefix]
    exact hC

theorem actual_cycle_prefix_data_unique {n t ell : ℕ} (p : Pairing n) (a : Dart n)
    (w v : Fin t→Fin 2) (hw : ClosedOneCollisionEvent p a t w) (hv : ClosedOneCollisionEvent p a t v)
    (h : ell≤t) (hprefix : PrefixWord h w=PrefixWord h v)
    (hCw : (ExposureRun p (InitialState a) (List.ofFn (PrefixWord h w))).exposed=
      (ExposureRun p (InitialState a) (List.ofFn w)).exposed)
    (hCv : (ExposureRun p (InitialState a) (List.ofFn (PrefixWord h v))).exposed=
      (ExposureRun p (InitialState a) (List.ofFn v)).exposed) : w=v := by
  have hC : (ExposureRun p (InitialState a) (List.ofFn w)).exposed=
      (ExposureRun p (InitialState a) (List.ofFn v)).exposed := by
    rw [←hCw,←hCv,hprefix]
  have hl:=actual_one_collision_support_unique_length p a (List.ofFn w) (List.ofFn v)
    hw.1 hw.2 hv.1 hv.2 hC (by simp)
  exact List.ofFn_injective hl

#print axioms actual_prefix_word_list
#print axioms actual_closed_one_collision_first_cycle_word
#print axioms actual_cycle_prefix_data_unique
end Reference.MD06OneCycle
