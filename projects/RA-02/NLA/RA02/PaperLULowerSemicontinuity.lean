module

public import NLA.RA02.PaperLUContinuity

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology Matrix
open Filter
namespace NLA.RA02.Paper

theorem lu_expectedError_lowerSemicontinuous {m n : ℕ} (r : ℕ) :
    LowerSemicontinuous (fun A : Matrix (Fin m) (Fin n) ℂ => NLA.RA03.expectedError A r) := by
  intro A
  induction r generalizing A with
  | zero =>
    simpa only [lu_expectedError_zero] using continuous_lu_frobeniusSq.continuousAt.lowerSemicontinuousAt
  | succ r ih =>
    have hs : LowerSemicontinuousAt (fun B : Matrix (Fin m) (Fin n) ℂ =>
        ∑ p : NLA.RA03.Pivot m n, NLA.RA03.pivotMass B p *
          NLA.RA03.expectedError (NLA.RA03.nextResidual B p) r) A := by
      apply lowerSemicontinuousAt_sum
      intro p _
      cases p with
      | none =>
        simpa only [NLA.RA03.nextResidual,lu_expectedError_zero_matrix,mul_zero] using
          (lowerSemicontinuousAt_const (α:=Matrix (Fin m) (Fin n) ℂ) (z:=(0 : ℝ)) (x:=A))
      | some p =>
        by_cases hp : A p.1 p.2 = 0
        · apply lowerSemicontinuousAt_nonneg_zero _ A
            (fun B => mul_nonneg (lu_pivotMass_nonneg B (some p)) (lu_expectedError_nonneg _ r))
          have hz : NLA.RA03.pivotMass A (some p) = 0 := by
            by_cases hA : A = 0 <;> simp [NLA.RA03.pivotMass,hA,hp]
          rw [hz,zero_mul]
        · have hrec := LowerSemicontinuousAt.comp
            (g:=fun B : Matrix (Fin m) (Fin n) ℂ => NLA.RA03.pivotResidual B p)
            (ih (NLA.RA03.pivotResidual A p)) (lu_pivotResidual_continuousAt_entry A p hp)
          exact lowerSemicontinuousAt_mul_nonneg
            (fun B => NLA.RA03.pivotMass B (some p))
            (fun B => NLA.RA03.expectedError (NLA.RA03.pivotResidual B p) r) A
            (lu_pivotMass_continuousAt_entry A p hp) hrec
            (fun B => lu_pivotMass_nonneg B (some p)) (fun B => lu_expectedError_nonneg _ r)
    simpa only [lu_expectedError_succ] using hs

#print axioms lu_expectedError_lowerSemicontinuous
end NLA.RA02.Paper
