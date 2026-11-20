module

public import NLA.PF02.BlockSupportRecovery.Definitions
public import NLA.PF02.IntrinsicSupport.IntrinsicRank

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02BlockSupportRecovery
open Matrix NLA.PF02.Paper Reference.PF02BlockConstruction Reference.PF02Support
open scoped BigOperators MatrixOrder

theorem finite_psd_supported_trace_rank_le {ι κ : Type*} [Fintype ι] [Fintype κ] {k : ℕ}
    (M : Matrix ι κ ℝ) (A : ι → Mat (Fin k)) (B : κ → Mat (Fin k))
    (U : Submodule ℝ (Reference.PF02Support.Vector (Fin k)))
    (hA : ∀ i, (A i).PosSemidef) (hsupport : ∀ i, SupportedOn (A i) U)
    (htrace : ∀ i j, trace (A i * B j) = M i j) :
    M.rank ≤ Module.finrank ℝ U * (Module.finrank ℝ U+1)/2 := by
  classical
  let ei := Fintype.equivFin ι
  let ej := Fintype.equivFin κ
  have h := Reference.PF02IntrinsicSupport.psd_supported_trace_rank_le
    (M.reindex ei ej) (fun i => A (ei.symm i)) (fun j => B (ej.symm j)) U
    (fun i => hA _) (fun i => hsupport _) (fun i j => htrace _ _)
  simpa only [Matrix.rank_reindex] using h

#print axioms finite_psd_supported_trace_rank_le
end Reference.PF02BlockSupportRecovery
