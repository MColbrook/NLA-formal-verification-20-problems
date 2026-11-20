module

public import NLA.RA08.PaperNuclearDefinitions
public import NLA.RA08.PaperDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA08.Paper

def nuclearLiftBaseEntries (m : ℕ) : Fin (m+m+1) → ℝ :=
  Fin.snoc (nuclearBaseEntries m) 0

def nuclearLiftBase (m : ℕ) : RealMatrix (m+m+1) :=
  Matrix.diagonal (nuclearLiftBaseEntries m)

def nuclearLiftVector (m : ℕ) (η : ℝ) : Fin (m+m+1) → ℝ :=
  Fin.snoc (fun i => Real.sqrt η*nuclearUnitVector m i) (Real.sqrt (1-η))

def nuclearLiftPerturbation (m : ℕ) (η : ℝ) : RealMatrix (m+m+1) :=
  Matrix.vecMulVec (nuclearLiftVector m η) (nuclearLiftVector m η)

def nuclearLiftA (m : ℕ) (η t : ℝ) : RealMatrix (m+m+1) :=
  nuclearLiftBase m+t • nuclearLiftPerturbation m η

/-- The printed sketch, with sqrt(eta)/sqrt(1-eta) in the last row. -/
def nuclearLiftSketch (m : ℕ) (η : ℝ) : Matrix (Fin (m+m+1)) (Fin (m+m)) ℝ :=
  Fin.snoc (1 : RealMatrix (m+m))
    (fun j => -(Real.sqrt η/Real.sqrt (1-η))*nuclearUnitVector m j)

def nuclearLiftAOmega (m : ℕ) : Matrix (Fin (m+m+1)) (Fin (m+m)) ℝ :=
  Fin.snoc (nuclearBase m) 0

def nuclearBaseInverse (m : ℕ) : RealMatrix (m+m) :=
  Matrix.diagonal (fun i => (nuclearBaseEntries m i)⁻¹)

end NLA.RA08.Paper
