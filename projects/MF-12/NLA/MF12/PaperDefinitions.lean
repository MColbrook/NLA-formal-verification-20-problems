module

public import NLA.MF12.Definitions

@[expose] public section

/- Proof-independent general parameters used in the manuscript. -/
set_option autoImplicit false
noncomputable section
namespace NLA.MF12.Paper

def parameterMatrix (lam μ : ℝ) : Square 6 :=
  !![1,0,0,0,0,0; 0,lam,lam,0,0,0; 0,0,lam,0,0,0;
     0,0,0,μ,μ,0; 0,0,0,0,μ,0; 0,0,0,0,0,1]

def parameterLoss (lam : ℝ) (q : ℕ) : ℝ := (q : ℝ) * lam ^ q
def parameterGain (μ : ℝ) (q : ℕ) : ℝ := (q : ℝ) * μ ^ q
def parameterCompressed (lam μ : ℝ) (q : ℕ) : Square 2 :=
  sourceU * parameterMatrix lam μ ^ q * sourceV

end NLA.MF12.Paper
