module

public import NLA.MD06.CanonicalCyclePatterns.SymmetryDefinitions
public import NLA.MD06.CanonicalCyclePatterns.CycleSupport

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalCyclePatterns
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06BadOverlap Reference.MD06BadJointMoments
attribute [local instance] Classical.propDecidable

theorem actual_normalized_pair_comm {n : ℕ} (x y : Dart n) :
    OrientedEdge x y = OrientedEdge y x := by
  unfold OrientedEdge DartLT
  split_ifs with hxy hyx
  · exfalso
    omega
  · rfl
  · rfl
  · have he : x=y := by
      apply Prod.ext <;> apply Fin.ext <;> omega
    subst y
    rfl

theorem actual_cycle_rotate_commute {ell : ℕ} (s i : Fin ell) :
    finCycle s (finRotate ell i) = finRotate ell (finCycle s i) := by
  let := i.neZero
  simp only [finCycle_apply,finRotate_apply]
  ac_rfl

theorem actual_cycle_reflected_rotate {ell : ℕ} [NeZero ell] (i : Fin ell) :
    finRotate ell (-(finRotate ell i)) = -i := by
  simp only [finRotate_apply]
  abel

theorem actual_canonical_cycle_pattern_image {n ell : ℕ} (D : CycleData n ell) :
    CanonicalCyclePattern D =
      Finset.univ.image (fun i => OrientedEdge (outgoing D i)
        (incoming D (finRotate ell i))) := by
  rw [CanonicalCyclePattern,CanonicalConstraints,CyclePattern,Finset.image_image]
  rfl

theorem actual_rotated_cycle_pattern {n ell : ℕ}
    (D : CycleData n ell) (s : Fin ell) :
    CanonicalCyclePattern (RotatedCycle D s)=CanonicalCyclePattern D := by
  have he : ∀ i, OrientedEdge (outgoing (RotatedCycle D s) i)
      (incoming (RotatedCycle D s) (finRotate ell i)) =
      OrientedEdge (outgoing D (finCycle s i))
        (incoming D (finRotate ell (finCycle s i))) := by
    intro i
    change OrientedEdge (outgoing D (finCycle s i))
      (incoming D (finCycle s (finRotate ell i))) = _
    rw [actual_cycle_rotate_commute]
  rw [actual_canonical_cycle_pattern_image,actual_canonical_cycle_pattern_image]
  ext e
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨i,hi,hie⟩
    exact Finset.mem_image.mpr ⟨finCycle s i,Finset.mem_univ _,(he i).symm.trans hie⟩
  · intro h
    rcases Finset.mem_image.mp h with ⟨i,hi,hie⟩
    refine Finset.mem_image.mpr ⟨(finCycle s).symm i,Finset.mem_univ _,?_⟩
    rw [he,Equiv.apply_symm_apply]
    exact hie

theorem actual_reflected_cycle_pattern {n ell : ℕ} [NeZero ell]
    (D : CycleData n ell) :
    CanonicalCyclePattern (ReflectedCycle D)=CanonicalCyclePattern D := by
  have he : ∀ i, OrientedEdge (outgoing (ReflectedCycle D) i)
      (incoming (ReflectedCycle D) (finRotate ell i)) =
      OrientedEdge (outgoing D (-(finRotate ell i)))
        (incoming D (finRotate ell (-(finRotate ell i)))) := by
    intro i
    change OrientedEdge (incoming D (-i)) (outgoing D (-(finRotate ell i))) = _
    rw [actual_cycle_reflected_rotate,actual_normalized_pair_comm]
  rw [actual_canonical_cycle_pattern_image,actual_canonical_cycle_pattern_image]
  ext e
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨i,hi,hie⟩
    exact Finset.mem_image.mpr ⟨-(finRotate ell i),Finset.mem_univ _,(he i).symm.trans hie⟩
  · intro h
    rcases Finset.mem_image.mp h with ⟨i,hi,hie⟩
    refine Finset.mem_image.mpr ⟨-(finRotate ell i),Finset.mem_univ _,?_⟩
    rw [he,actual_cycle_reflected_rotate,neg_neg]
    exact hie

theorem actual_symmetry_cycle_pattern {n ell : ℕ} [NeZero ell]
    (D : CycleData n ell) (z : Fin ell × Bool) :
    CanonicalCyclePattern (SymmetryCycle D z)=CanonicalCyclePattern D := by
  unfold SymmetryCycle
  split
  · exact actual_rotated_cycle_pattern D z.1
  · exact (actual_reflected_cycle_pattern (RotatedCycle D z.1)).trans
      (actual_rotated_cycle_pattern D z.1)

theorem actual_symmetry_cycle_start {n ell : ℕ} [NeZero ell]
    (D : CycleData n ell) (z : Fin ell × Bool) :
    (SymmetryCycle D z).1 0 = D.1 z.1 := by
  rcases z with ⟨s,b⟩
  cases b <;> simp [SymmetryCycle,RotatedCycle,ReflectedCycle,finCycle_apply]

theorem actual_symmetry_cycle_injective {n ell : ℕ} [NeZero ell]
    (D : CycleData n ell) :
    Function.Injective (SymmetryCycle D) := by
  intro z w h
  have hs : z.1=w.1 := D.1.injective (by
    simpa only [actual_symmetry_cycle_start] using
      congrArg (fun C : CycleData n ell => C.1 0) h)
  rcases z with ⟨s,b⟩
  rcases w with ⟨t,c⟩
  change s=t at hs
  subst t
  have hp := congrArg (fun C : CycleData n ell => (C.2 (0 : Fin ell)).val.1) h
  apply Prod.ext
  · rfl
  · cases b <;> cases c
    · rfl
    · exact False.elim (((D.2 s).property).symm (by
        simpa [SymmetryCycle,RotatedCycle,ReflectedCycle,finCycle_apply] using hp))
    · exact False.elim ((D.2 s).property (by
        simpa [SymmetryCycle,RotatedCycle,ReflectedCycle,finCycle_apply] using hp))
    · rfl

#print axioms actual_normalized_pair_comm
#print axioms actual_cycle_rotate_commute
#print axioms actual_cycle_reflected_rotate
#print axioms actual_canonical_cycle_pattern_image
#print axioms actual_rotated_cycle_pattern
#print axioms actual_reflected_cycle_pattern
#print axioms actual_symmetry_cycle_pattern
#print axioms actual_symmetry_cycle_start
#print axioms actual_symmetry_cycle_injective
end Reference.MD06CanonicalCyclePatterns
