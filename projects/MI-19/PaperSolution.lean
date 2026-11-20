module

public import NLA.MI19.PaperRank

@[expose] public section

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
namespace NLA.MI19.Paper

theorem paper_counterexample :
    realWitness.PosSemidef ∧ realWitness.rank = 2 ∧
    witness = realWitness.map (fun x : ℝ => (x : ℂ)) ∧
    0 ≤ witnessQ ∧ witnessQ ≤ 1 ∧
    witnessSubset.Nonempty ∧ witnessSubset ≠ Finset.univ ∧
    qPermanent witnessQ witness - restrictedQPermanent witnessQ witness witnessSubset =
      (-3235575 / 16384 : ℂ) ∧
    qPermanent witnessQ witness < restrictedQPermanent witnessQ witness witnessSubset := by
  obtain ⟨_, _, _, hq0, hq1, hs, hsn, _, _, hgap, hlt⟩ := counterexample_proved
  exact ⟨real_witness_psd, real_witness_rank, complex_witness_bridge,
    hq0, hq1, hs, hsn, hgap, hlt⟩

#print axioms paper_counterexample

end NLA.MI19.Paper
