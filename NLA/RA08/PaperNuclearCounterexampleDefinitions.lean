module

public import NLA.RA08.PaperNuclearLiftTraceDefinitions
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace NLA.RA08.Paper

/-- The printed nuclear theorem, with actual Nyström and actual ordered truncations. -/
def NuclearTransferFailure (C ε₀ : ℝ) : Prop :=
  ∃ (n l k : ℕ) (A : RealMatrix n) (Ω : Matrix (Fin n) (Fin l) ℝ)
      (d : OrderedSpectralData A) (ε : ℝ),
    A.PosDef ∧ Function.Injective (fun x => Ω *ᵥ x) ∧
    k=(nystrom A Ω).rank ∧ 0 < ε ∧ ε < ε₀ ∧
    nuclearNorm (A-nystrom A Ω)=(1+ε)*nuclearNorm (A-truncation d k) ∧
    nuclearNorm (functionalCalculus witnessFunction A-
      functionalCalculus witnessFunction (nystrom A Ω)) >
        (1+C*ε)*nuclearNorm (functionalCalculus witnessFunction A-
          functionTruncation d witnessFunction k)

end NLA.RA08.Paper
