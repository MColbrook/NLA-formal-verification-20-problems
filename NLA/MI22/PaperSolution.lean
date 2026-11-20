module

public import NLA.MI22.PaperCounterexample

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped MatrixOrder ComplexOrder
namespace NLA.MI22.Paper

theorem paper_printed_inputs :
    witnessA = Matrix.diagonal (![256,1/256,1] : Fin 3 → ℂ) ∧
    paperB = !![17,-4,0; -4,16385,-8192; 0,-8192,4096] := by
  exact ⟨witnessA_diagonal,rfl⟩

theorem paper_counterexample :
    witnessA.PosDef ∧ paperB.PosDef ∧
    10900 < operatorNorm (leftProduct witnessA paperB (1/8)) ∧
    operatorNorm (witnessA*paperB) < 10200 ∧
    ¬ SingularLogMajorized (leftProduct witnessA paperB (1/8)) (witnessA*paperB) := by
  exact printed_counterexample

theorem paper_conjecture_false :
    ¬ WeightedLogMajorizationConjecture := by
  intro h
  exact printed_counterexample.2.2.2.2
    (h 3 (by norm_num) witnessA paperB witnessA_posDef paperB_posDef
      (1/8) (by norm_num) (by norm_num))

#print axioms paper_printed_inputs
#print axioms paper_counterexample
#print axioms paper_conjecture_false

end NLA.MI22.Paper
