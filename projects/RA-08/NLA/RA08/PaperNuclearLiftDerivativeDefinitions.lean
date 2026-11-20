module

public import NLA.RA08.PaperNuclearTailDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA08.Paper

def nuclearLiftDerivative (m : ℕ) (η : ℝ) : RealMatrix (m+m+1) :=
  clippingDerivative (nuclearLiftBaseEntries m) (nuclearLiftPerturbation m η)

def nuclearLiftOutput (m : ℕ) (η t : ℝ) : RealMatrix (m+m+1) :=
  functionalCalculus witnessFunction (nuclearLiftA m η t)-
    functionalCalculus witnessFunction (nuclearLiftBase m)

end NLA.RA08.Paper
