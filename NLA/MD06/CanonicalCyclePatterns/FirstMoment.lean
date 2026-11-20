module

public import NLA.MD06.CanonicalCyclePatterns.MeanDefinitions
public import NLA.MD06.CanonicalCyclePatterns.Fibers
public import NLA.MD06.CyclePairPatterns.FirstMoment

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalCyclePatterns
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability
open Reference.MD06CyclePairPatterns Reference.MD06PairingCounts
attribute [local instance] Classical.propDecidable

theorem actual_canonical_cycle_card_product (n ell : ℕ) [NeZero ell] :
    (2*ell)*Fintype.card (CanonicalCycleDatum n ell)=n.descFactorial ell * 6^ell := by
  rw [←actual_canonical_cycle_card_relation,actual_cycle_data_card]

theorem actual_raw_canonical_cycle_count {n ell : ℕ} [NeZero ell] (p : Pairing n) :
    RawCycleCount n ell p=(2*ell)*CanonicalCycleCount n ell p := by
  let e : {D : CycleData n ell // Matches (CyclePattern D) p} ≃
      (Σ C : {C : CanonicalCycleDatum n ell // Matches C.val p},
        CycleFiber n ell C.val.val) :=
    { toFun := fun D => ⟨
        ⟨⟨CanonicalCyclePattern D.val,⟨D.val,rfl⟩⟩,
          (actual_canonical_cycle_matching D.val p).mpr D.property⟩,⟨D.val,rfl⟩⟩
      invFun := fun X => ⟨X.2.val,(actual_canonical_cycle_matching X.2.val p).mp
        ((congrArg (fun C => Matches C p) X.2.property).mpr X.1.property)⟩
      left_inv := by intro D;apply Subtype.ext;rfl
      right_inv := by
        rintro ⟨C,D⟩
        apply Sigma.subtype_ext
        · exact Subtype.ext (Subtype.ext D.property)
        · rfl }
  have h := Fintype.card_congr e
  rw [Fintype.card_sigma] at h
  simp_rw [actual_canonical_cycle_fiber_card] at h
  simpa only [RawCycleCount,CanonicalCycleCount,←Nat.card_eq_fintype_card,
    Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul,Nat.mul_comm] using h

theorem actual_mean_raw_canonical_cycle_relation (k ell : ℕ) [NeZero ell] :
    MeanOrientedCycles k ell=(2*(ell : ℝ))*MeanCanonicalCycles k ell := by
  unfold MeanOrientedCycles MeanCanonicalCycles
  simp only [actual_raw_canonical_cycle_count,Nat.cast_mul,Nat.cast_ofNat]
  rw [←Finset.mul_sum]
  ring

theorem actual_mean_canonical_cycles (k ell : ℕ) [NeZero ell] :
    MeanCanonicalCycles k ell=MeanOrientedCycles k ell/(2*(ell : ℝ)) := by
  have hn : (2*(ell : ℝ))≠0 := mul_ne_zero (by norm_num) (by exact_mod_cast NeZero.ne ell)
  apply (eq_div_iff hn).mpr
  simpa only [mul_comm] using (actual_mean_raw_canonical_cycle_relation k ell).symm

#print axioms actual_canonical_cycle_card_product
#print axioms actual_raw_canonical_cycle_count
#print axioms actual_mean_raw_canonical_cycle_relation
#print axioms actual_mean_canonical_cycles
end Reference.MD06CanonicalCyclePatterns
