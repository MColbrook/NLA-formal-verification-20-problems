module

public import NLA.MD06.GraphCycleEvent.Definitions
public import NLA.MD06.CyclePairPatterns.PatternProperties
public import NLA.MD06.CanonicalCyclePatterns.Normalization
public import NLA.MD06.CanonicalCyclePatterns.MeanDefinitions
public import NLA.MD06.CubicConfiguration.UniformLaw

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06GraphCycleEvent
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06CanonicalCyclePatterns Reference.MD06PairingCounts
open Reference.MD06FiniteProbability
attribute [local instance] Classical.propDecidable

theorem actual_previous_ne_next {ell : ℕ} (h3 : 3 ≤ ell) (i : Fin ell) :
    (finRotate ell).symm i ≠ finRotate ell i := by
  letI : NeZero ell := ⟨by omega⟩
  intro h
  have hstep : i = (i + 1) + 1 := by
    have hc := congrArg (fun j : Fin ell => j + 1) h
    simpa only [finRotate_symm_apply, finRotate_apply, sub_add_cancel] using hc
  have hz : (0 : Fin ell) = (1 : Fin ell) + 1 :=
    add_left_cancel (a := i) (by simpa only [add_zero, add_assoc] using hstep)
  have hv := congrArg Fin.val hz
  change 0 = (1 % ell + 1 % ell) % ell at hv
  have hone : 1 % ell = 1 := Nat.mod_eq_of_lt (by omega)
  simp only [hone] at hv
  change 0 = 2 % ell at hv
  rw [Nat.mod_eq_of_lt (by omega : 2 < ell)] at hv
  omega

theorem actual_raw_matching_graph_cycle {n ell : ℕ} (h3 : 3 ≤ ell)
    (p : SimpleConfiguration n) (h : RawPairingCycleExists p.val ell) :
    GraphCycleExists (configurationGraph p) ell := by
  obtain ⟨D, hD⟩ := h
  exact ⟨h3, D.1, fun i => actual_cycle_matching_graph_adjacency D p hD i⟩

theorem actual_graph_cycle_raw_matching {n ell : ℕ} (h3 : 3 ≤ ell)
    (p : SimpleConfiguration n) (h : GraphCycleExists (configurationGraph p) ell) :
    RawPairingCycleExists p.val ell := by
  classical
  obtain ⟨_, vertices, hadj⟩ := h
  let out : Fin ell → Fin 3 := fun i => Classical.choose (hadj i)
  have hout (i : Fin ell) :
      (p.val.val (vertices i, out i)).fst = vertices (finRotate ell i) :=
    Classical.choose_spec (hadj i)
  let partner : Fin ell → Dart n := fun i => p.val.val (vertices i, out i)
  let inn : Fin ell → Fin 3 := fun i => (partner ((finRotate ell).symm i)).snd
  have hpartner (i : Fin ell) :
      partner i = (vertices (finRotate ell i), inn (finRotate ell i)) := by
    apply Prod.ext
    · exact hout i
    · simp only [inn, Equiv.symm_apply_apply]
  have hdistinct (i : Fin ell) : inn i ≠ out i := by
    intro heq
    have hprev : partner ((finRotate ell).symm i) = (vertices i, out i) := by
      apply Prod.ext
      · simpa only [Equiv.apply_symm_apply] using hout ((finRotate ell).symm i)
      · exact heq
    have hback := congrArg p.val.val hprev
    change p.val.val (p.val.val
        (vertices ((finRotate ell).symm i), out ((finRotate ell).symm i))) =
      p.val.val (vertices i, out i) at hback
    rw [p.val.property.1] at hback
    have hs : vertices ((finRotate ell).symm i) = vertices (finRotate ell i) :=
      (congrArg Prod.fst hback).trans (hout i)
    exact actual_previous_ne_next h3 i (vertices.injective hs)
  let D : CycleData n ell :=
    (vertices, fun i => ⟨(inn i, out i), hdistinct i⟩)
  refine ⟨D, ?_⟩
  intro e he
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
  change partner i = (vertices (finRotate ell i), inn (finRotate ell i))
  exact hpartner i

theorem actual_graph_cycle_raw_iff {n ell : ℕ} (h3 : 3 ≤ ell)
    (p : SimpleConfiguration n) :
    GraphCycleExists (configurationGraph p) ell ↔ RawPairingCycleExists p.val ell :=
  ⟨actual_graph_cycle_raw_matching h3 p, actual_raw_matching_graph_cycle h3 p⟩

theorem actual_canonical_raw_cycle_iff {n ell : ℕ} (p : Pairing n) :
    CanonicalPairingCycleExists p ell ↔ RawPairingCycleExists p ell := by
  constructor
  · rintro ⟨⟨C, D, hD⟩, hC⟩
    refine ⟨D, (actual_canonical_cycle_matching D p).mp ?_⟩
    simpa only [hD] using hC
  · rintro ⟨D, hD⟩
    exact ⟨⟨CanonicalCyclePattern D, ⟨D, rfl⟩⟩,
      (actual_canonical_cycle_matching D p).mpr hD⟩

theorem actual_graph_cycle_canonical_iff {n ell : ℕ} (h3 : 3 ≤ ell)
    (p : SimpleConfiguration n) :
    GraphCycleExists (configurationGraph p) ell ↔ CanonicalPairingCycleExists p.val ell :=
  (actual_graph_cycle_raw_iff h3 p).trans (actual_canonical_raw_cycle_iff p.val).symm

theorem actual_canonical_count_zero_iff {n ell : ℕ} (p : Pairing n) :
    CanonicalCycleCount n ell p = 0 ↔ ¬CanonicalPairingCycleExists p ell := by
  classical
  letI : Fintype {C : CanonicalCycleDatum n ell // Matches C.val p} :=
    Fintype.ofFinite _
  rw [CanonicalCycleCount, Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
  constructor
  · intro hz h
    obtain ⟨C, hC⟩ := h
    exact hz.false ⟨C, hC⟩
  · intro h
    refine ⟨?_⟩
    rintro ⟨C, hC⟩
    exact h ⟨C, hC⟩

theorem actual_canonical_count_zero_graph_iff {n ell : ℕ} (h3 : 3 ≤ ell)
    (p : SimpleConfiguration n) :
    CanonicalCycleCount n ell p.val = 0 ↔ ¬GraphCycleExists (configurationGraph p) ell := by
  rw [actual_canonical_count_zero_iff]
  exact not_congr (actual_graph_cycle_canonical_iff h3 p).symm

theorem actual_uniform_graph_no_cycle_model (k ell : ℕ) :
    GraphProbability k (fun G => ¬GraphCycleExists G ell) =
      ConditionedGraphProbability (Size k) (fun G => ¬GraphCycleExists G ell) :=
  (actual_configuration_conditioned_uniform_graph_law k _).symm

theorem actual_simple_no_cycle_event_iff {n ell : ℕ} (h3 : 3 ≤ ell)
    (p : Pairing n) :
    (∃ h : IsSimplePairing p, ¬GraphCycleExists (configurationGraph ⟨p, h⟩) ell) ↔
      IsSimplePairing p ∧ CanonicalCycleCount n ell p = 0 := by
  constructor
  · rintro ⟨h, hcycle⟩
    exact ⟨h, (actual_canonical_count_zero_graph_iff h3 ⟨p, h⟩).mpr hcycle⟩
  · rintro ⟨h, hzero⟩
    exact ⟨h, (actual_canonical_count_zero_graph_iff h3 ⟨p, h⟩).mp hzero⟩

theorem actual_uniform_graph_no_cycle_probability {ell : ℕ} (h3 : 3 ≤ ell)
    (k : ℕ) :
    GraphProbability k (fun G => ¬GraphCycleExists G ell) =
      PairingProbability (Size k)
        (fun p => IsSimplePairing p ∧ CanonicalCycleCount (Size k) ell p = 0) /
      PairingProbability (Size k) IsSimplePairing := by
  rw [actual_uniform_graph_no_cycle_model]
  unfold ConditionedGraphProbability
  congr 1
  congr 1
  funext p
  exact propext (actual_simple_no_cycle_event_iff h3 p)

#print axioms actual_previous_ne_next
#print axioms actual_raw_matching_graph_cycle
#print axioms actual_graph_cycle_raw_matching
#print axioms actual_graph_cycle_raw_iff
#print axioms actual_canonical_raw_cycle_iff
#print axioms actual_graph_cycle_canonical_iff
#print axioms actual_canonical_count_zero_iff
#print axioms actual_canonical_count_zero_graph_iff
#print axioms actual_uniform_graph_no_cycle_model
#print axioms actual_simple_no_cycle_event_iff
#print axioms actual_uniform_graph_no_cycle_probability
end Reference.MD06GraphCycleEvent
