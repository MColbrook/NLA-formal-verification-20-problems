module

public import NLA.RA02.PaperLULowerSemicontinuity
public import NLA.RA02.PaperCholeskyLowerSemicontinuity
public import NLA.RA02.PaperCorrelationRegularization

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Topology Matrix
open Filter
namespace NLA.RA02.Paper

theorem regularizedCorrelation_lu_lower_limit {n : ℕ} (C : NLA.RA02.Square n)
    (r : ℕ) (y : ℝ) (hy : y < NLA.RA03.expectedError C r) :
    ∀ᶠ δ in 𝓝[>] 0, y < NLA.RA03.expectedError (regularizedCorrelation C δ) r := by
  have hs : LowerSemicontinuousAt (fun δ => NLA.RA03.expectedError (regularizedCorrelation C δ) r) 0 :=
    LowerSemicontinuousAt.comp (g:=regularizedCorrelation C)
      (by simpa [regularizedCorrelation] using lu_expectedError_lowerSemicontinuous (m:=n) (n:=n) r C)
      (regularizedCorrelation_continuousAt_zero C)
  exact (hs y (by simpa [regularizedCorrelation] using hy)).filter_mono nhdsWithin_le_nhds

theorem regularizedCorrelation_cholesky_lower_limit {n : ℕ} (C : NLA.RA02.Square n)
    (hC : C.PosSemidef) (r : ℕ) (y : ℝ) (hy : y < NLA.RA02.expectedTrace C r) :
    ∀ᶠ δ in 𝓝[>] 0, y < NLA.RA02.expectedTrace (regularizedCorrelation C δ) r := by
  have ho : LowerSemicontinuousOn (fun A : NLA.RA02.Square n => NLA.RA02.expectedTrace A r)
      {A | A.PosSemidef} := lowerSemicontinuous_restrict_iff.mp (cholesky_expectedTrace_lowerSemicontinuous r)
  have hs : LowerSemicontinuousWithinAt
      (fun δ => NLA.RA02.expectedTrace (regularizedCorrelation C δ) r) (Set.Ioi 0) 0 := by
    apply LowerSemicontinuousWithinAt.comp (g:=regularizedCorrelation C)
      (f:=fun A : NLA.RA02.Square n => NLA.RA02.expectedTrace A r)
      (x:=(0 : ℝ)) (t:=Set.Ioi (0 : ℝ))
      (s:={A : NLA.RA02.Square n | A.PosSemidef})
    · simpa [regularizedCorrelation] using ho C hC
    · exact (regularizedCorrelation_continuousAt_zero C).continuousWithinAt
    · intro δ hδ
      exact (regularizedCorrelation_posDef C hC hδ).posSemidef
  exact hs y (by simpa [regularizedCorrelation] using hy)

#print axioms regularizedCorrelation_cholesky_lower_limit
end NLA.RA02.Paper
