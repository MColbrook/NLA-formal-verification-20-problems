module

public import NLA.RA02.PaperLUContinuity
public import NLA.RA02.FiniteExpectation

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Topology Matrix
open Filter
namespace NLA.RA02.Paper

theorem continuous_cholesky_realTrace {n : ℕ} :
    Continuous (NLA.RA02.realTrace (n:=n)) := by
  unfold NLA.RA02.realTrace
  fun_prop

theorem cholesky_pivotMass_continuousAt_trace {n : ℕ} (A : NLA.RA02.Square n)
    (ht : NLA.RA02.realTrace A ≠ 0) (j : Fin n) :
    ContinuousAt (fun B => NLA.RA02.pivotMass B j) A := by
  have he : ContinuousAt (fun B : NLA.RA02.Square n => (B j j).re) A :=
    (Complex.continuous_re.comp (continuous_id.matrix_elem j j)).continuousAt
  have hc : ContinuousAt (fun B : NLA.RA02.Square n => (B j j).re/NLA.RA02.realTrace B) A :=
    he.div continuous_cholesky_realTrace.continuousAt ht
  apply hc.congr_of_eventuallyEq
  filter_upwards [continuous_cholesky_realTrace.continuousAt.eventually (eventually_ne_nhds ht)] with B hB
  simp [NLA.RA02.pivotMass,hB]

theorem cholesky_expectedTrace_lowerSemicontinuous {n : ℕ} (r : ℕ) :
    LowerSemicontinuous (fun A : {A : NLA.RA02.Square n // A.PosSemidef} =>
      NLA.RA02.expectedTrace A.val r) := by
  intro A
  induction r generalizing A with
  | zero =>
    have hc : Continuous (fun A : {A : NLA.RA02.Square n // A.PosSemidef} =>
        NLA.RA02.realTrace A.val) := continuous_cholesky_realTrace.comp continuous_subtype_val
    simpa only [NLA.RA02.expectedTrace_zero_steps] using hc.continuousAt.lowerSemicontinuousAt
  | succ r ih =>
    by_cases hA : A.val = 0
    · apply lowerSemicontinuousAt_nonneg_zero _ A
        (fun B => NLA.RA02.expectedTrace_nonneg B.val B.property (r+1))
      rw [hA]
      exact (NLA.RA02.zero_residual n (r+1) []).2
    have ht : NLA.RA02.realTrace A.val ≠ 0 := ne_of_gt (NLA.RA02.realTrace_pos A.property hA)
    have hs : LowerSemicontinuousAt (fun B : {B : NLA.RA02.Square n // B.PosSemidef} =>
        ∑ j : Fin n, NLA.RA02.pivotMass B.val j *
          NLA.RA02.expectedTrace (NLA.RA02.choleskyStep B.val j) r) A := by
      apply lowerSemicontinuousAt_sum
      intro j _
      by_cases hj : A.val j j = 0
      · apply lowerSemicontinuousAt_nonneg_zero _ A
          (fun B => mul_nonneg (NLA.RA02.pivotMass_nonneg B.property j)
            (NLA.RA02.expectedTrace_nonneg _ (NLA.RA02.choleskyStep_posSemidef B.val B.property j) r))
        simp [NLA.RA02.pivotMass,ht,hj]
      · let update : {B : NLA.RA02.Square n // B.PosSemidef} →
            {B : NLA.RA02.Square n // B.PosSemidef} :=
          fun B => ⟨NLA.RA02.choleskyStep B.val j,NLA.RA02.choleskyStep_posSemidef B.val B.property j⟩
        have hc : ContinuousAt (fun B => NLA.RA02.choleskyStep B j) A.val :=
          lu_pivotResidual_continuousAt_entry A.val (j,j) hj
        have hu : ContinuousAt update A := (hc.comp continuousAt_subtype_val).codRestrict _
        have hrec := LowerSemicontinuousAt.comp (g:=update) (ih (update A)) hu
        have hm : ContinuousAt (fun B : {B : NLA.RA02.Square n // B.PosSemidef} =>
            NLA.RA02.pivotMass B.val j) A :=
          (cholesky_pivotMass_continuousAt_trace A.val ht j).comp continuousAt_subtype_val
        exact lowerSemicontinuousAt_mul_nonneg _ _ A hm hrec
          (fun B => NLA.RA02.pivotMass_nonneg B.property j)
          (fun B => NLA.RA02.expectedTrace_nonneg _ (NLA.RA02.choleskyStep_posSemidef B.val B.property j) r)
    simpa only [NLA.RA02.expectedTrace_succ] using hs

#print axioms cholesky_expectedTrace_lowerSemicontinuous
end NLA.RA02.Paper
