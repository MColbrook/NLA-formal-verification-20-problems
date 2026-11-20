module
import all Lean.Meta.Match.Match
public import Mathlib
@[expose] public section
set_option autoImplicit false noncomputable section
local macro "reset_proof_cache":command => `(run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {})
local macro "cache_proof" n:ident:command => `(run_cmd do let info ← Lean.getConstInfo $(Lean.quote n.getId); Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun s => {s with lemmas := s.lemmas.insert {type := info.type,isPrivate := false,defeq := false} (info.name,info.levelParams)})
set_option quotPrecheck false local notation "qA" => (@OfNat.ofNat ENNReal (nat_lit 2) (@instOfNatAtLeastTwo ENNReal (nat_lit 2) ((ENNReal.instAddCommMonoidWithOne).toAddMonoidWithOne).toNatCast PiLp.innerProductSpace._proof_1)) local notation "qB" d => (@WithLp.instAddCommGroup (qA) ((Fin d) -> Real) (@Pi.addCommGroup (Fin d) (fun (z0:Fin d) => Real) (fun (i:Fin d) => Real.instAddCommGroup)))
local notation "qC" d => (EuclideanSpace Real (Fin d)) local notation "qD" => ((((Real.instRCLike).toDenselyNormedField).toNormedField).toField)
local notation "qE" d => (@SubNegMonoid.toAddMonoid (qC d) (@AddGroup.toSubNegMonoid (qC d) (@AddCommGroup.toAddGroup (qC d) (qB d)))) local notation "qF" => ((((Real.normedField).toField).toSemifield).toCommSemiring)
local notation "qG" d => (@Pi.addCommGroup (Fin d) (fun (z0:Fin d) => Complex) (fun (i:Fin d) => @SeminormedAddCommGroup.toAddCommGroup Complex (Complex.instNormedAddCommGroup).toSeminormedAddCommGroup)) local notation "qH" d => (@AddCommGroup.toAddCommMonoid (qC d) (qB d))
local notation "qI" d => (@PiLp.topologicalSpace (qA) (Fin d) (fun (z0:Fin d) => Real) (fun (i:Fin d) => @UniformSpace.toTopologicalSpace Real (Real.pseudoMetricSpace).toUniformSpace)) local notation "qJ" => ((((Complex.instRCLike).toDenselyNormedField).toNormedField).toField)
local notation "qK" => ((((((Real.denselyNormedField).toNontriviallyNormedField).toNormedField).toField).toSemifield).toCommSemiring) local notation "qL" d => (@AddCommMonoid.toAddMonoid (qC d) (qH d))
local notation "qM" => (((qD).toSemifield).toCommSemiring) local notation "qN" => (Complex.instNormedAddCommGroup) set_option quotPrecheck true
/-! Numerical Linear Algebra, Explained: twenty problem resolutions. Unchanged semantic definitions and theorem types from preserved components.
Accounts and attribution: README.md, docs/COMBINED-DEFINITIONS.md, formalization.yaml and NOTICE.md.
At 92 original source-module boundaries, only Lean's auxiliary-proof and matcher caches are cleared, preserving generated names;
no declarations or assumptions change. Type notation shares exact Mathlib instance expressions. -/
/- MF-05: Uniform matrix-product growth and Hölder continuity of the joint spectral radius. -/ reset_proof_cache section namespace NLA.MF05.Paper
abbrev RealSquare (d:ℕ) := Matrix (Fin d) (Fin d) ℝ
def realSpectralNorm {d:ℕ} (A:RealSquare d):ℝ := ‖Matrix.toEuclideanCLM (𝕜:=ℝ) A‖
def realMatrixProduct {d:ℕ} (w:List (RealSquare d)):RealSquare d := w.reverse.prod
def realWordNorms {d:ℕ} (M:Set (RealSquare d)) (n:ℕ):Set ℝ := {r | ∃ w:List (RealSquare d), w.length = n ∧ (∀ A ∈ w, A ∈ M) ∧ r = realSpectralNorm (realMatrixProduct w)}
def realFamilyGrowth {d:ℕ} (M:Set (RealSquare d)) (n:ℕ) := sSup (realWordNorms M n)
def realRootGrowth {d:ℕ} (M:Set (RealSquare d)) (n:ℕ) := Real.rpow (realFamilyGrowth M n) (1/(n:ℝ))
def realRadius {d:ℕ} (M:Set (RealSquare d)):ℝ := sInf {r:ℝ | ∃ n:ℕ, 1 ≤ n ∧ r = realRootGrowth M n}
def realPointDistance {d:ℕ} (A:RealSquare d) (N:Set (RealSquare d)):ℝ := sInf ((fun B => realSpectralNorm (A-B)) '' N)
def realDirectedDistance {d:ℕ} (M N:Set (RealSquare d)):ℝ := sSup ((fun A => realPointDistance A N) '' M)
def realHausdorff {d:ℕ} (M N:Set (RealSquare d)):ℝ := max (realDirectedDistance M N) (realDirectedDistance N M)
end NLA.MF05.Paper end reset_proof_cache section namespace NLA.MF05.Paper
def theta (d:ℕ):ℝ := if d ≤ 1 then 1 else (d:ℝ) * (2 * Real.exp 1 * (d:ℝ)^2 / ((d-1:ℕ):ℝ))^(d-1)
end NLA.MF05.Paper end reset_proof_cache section open scoped Topology Matrix.Norms.L2Operator open Filter namespace NLA.MF05.Paper
theorem paper_real_bounded_positive_radius_growth {d:ℕ} (hd:1 ≤ d) (M:Set (RealSquare d)) (hM:Bornology.IsBounded M) (hne:M.Nonempty) (L:ℝ) (hL:0 < L) (hML:∀ A ∈ M, realSpectralNorm A ≤ L) (hr:0 < realRadius M) (n:ℕ) (hn:1 ≤ n):realFamilyGrowth M n ≤ theta d * (L*(n:ℝ))^(d-1) * (realRadius
  M)^((n:ℤ)-(d:ℤ)+1) := by sorry
theorem paper_real_bounded_zero_radius_nilpotent {d:ℕ} (hd:1 ≤ d) (M:Set (RealSquare d)) (hM:Bornology.IsBounded M) (hne:M.Nonempty) (L:ℝ) (hL:0 < L) (hML:∀ A ∈ M, realSpectralNorm A ≤ L) (hr:realRadius M = 0) (w:List (RealSquare d)) (hw:∀ A ∈ w, A ∈ M) (hlen:d ≤ w.length):realMatrixProduct w
  = 0 := by sorry
end NLA.MF05.Paper end reset_proof_cache section open scoped Topology open Filter namespace NLA.MF05.Paper
theorem paper_real_uniform_holder {d:ℕ} (hd:1 ≤ d) (M N:Set (RealSquare d)) (hM:IsCompact M) (hneM:M.Nonempty) (hN:IsCompact N) (hneN:N.Nonempty) (L:ℝ) (hL:0 < L) (hML:∀ A ∈ M, realSpectralNorm A ≤ L) (hNL:∀ A ∈ N, realSpectralNorm A ≤ L) :
    |realRadius M - realRadius N| ≤
      (d:ℝ)*(2*(d:ℝ)+1) * Real.rpow L (1-1/(d:ℝ)) *
        Real.rpow (realHausdorff M N) (1/(d:ℝ)) := by sorry
end NLA.MF05.Paper end
/- MF-12: Prescribed polynomial growth from two real matrices. -/ reset_proof_cache section open scoped BigOperators Classical namespace NLA.MF12
abbrev Square (d:ℕ) := Matrix (Fin d) (Fin d) ℝ
def spectralNorm {d:ℕ} (A:Square d):ℝ := ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A‖
def matrixProduct {d:ℕ} (w:List (Square d)):Square d := w.reverse.prod
def wordNorms {d:ℕ} (M:Finset (Square d)) (n:ℕ):Set ℝ := {r | ∃ w:List (Square d), w.length = n ∧ (∀ A ∈ w, A ∈ M) ∧ r = spectralNorm (matrixProduct w)}
def familyGrowth {d:ℕ} (M:Finset (Square d)) (n:ℕ):ℝ := sSup (wordNorms M n)
def pairFamily {d:ℕ} (A P:Square d):Finset (Square d) := {A, P}
end NLA.MF12 end reset_proof_cache section namespace NLA.MF12.Paper
def IsDyadic (x:ℝ):Prop := ∃ (z:ℤ) (k:ℕ), x = (z:ℝ)/(2:ℝ)^k
end NLA.MF12.Paper end reset_proof_cache section open Filter open scoped Topology namespace NLA.MF12.Paper
def paperDimension (γ:ℝ):ℕ := if γ = (⌊γ⌋₊:ℝ) then ⌊γ⌋₊ + 1 else 6 * (⌊γ⌋₊ + 1)
def Realizes {d:ℕ} (A P:Square d) (γ:ℝ):Prop := A ≠ P ∧ ∃ c C:ℝ, 0 < c ∧ c ≤ C ∧ (∀ n:ℕ, 1 ≤ n → c * Real.rpow (n:ℝ) γ ≤ familyGrowth (pairFamily A P) n ∧ familyGrowth (pairFamily A P) n ≤ C * Real.rpow (n:ℝ) γ) ∧ Tendsto (fun n:ℕ => Real.rpow (familyGrowth (pairFamily A P) n) (1 / (n:ℝ))) atTop (𝓝
  1)
end NLA.MF12.Paper end reset_proof_cache section namespace NLA.MF12.Paper
theorem paper_main_realization (γ:ℝ) (hγ:0 ≤ γ):∃ d:ℕ, d = paperDimension γ ∧ 1 ≤ d ∧ ∃ A P:Square d, Realizes A P γ ∧ ((∃ q:ℚ, (q:ℝ) = γ) → ∀ i j, IsDyadic (A i j) ∧ IsDyadic (P i j)) := by sorry
theorem paper_rational_realization (q:ℚ) (hq:0 ≤ q):∃ d:ℕ, d = paperDimension (q:ℝ) ∧ 1 ≤ d ∧ ∃ A P:Square d, Realizes A P (q:ℝ) ∧ ∀ i j, IsDyadic (A i j) ∧ IsDyadic (P i j) := by sorry
end NLA.MF12.Paper end
/- RA-02: Sharp random-pivoting losses for Cholesky and LU. -/ reset_proof_cache section namespace NLA.RA02 open scoped BigOperators ComplexOrder Matrix
abbrev Square (n:ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev History (n k:ℕ) := Fin k → Fin n
def realTrace {n:ℕ} (A:Square n):ℝ := A.trace.re
def choleskyStep {n:ℕ} (A:Square n) (j:Fin n):Square n := if A j j = 0 then A else fun a b => A a b - A a j * A j b / A j j
def pivotMass {n:ℕ} (A:Square n) (j:Fin n):ℝ := if realTrace A = 0 then 1 / (n:ℝ) else (A j j).re / realTrace A
def pathResidual {n:ℕ} (A:Square n):List (Fin n) → Square n
  | [] => A
  | j :: w => pathResidual (choleskyStep A j) w
def pathWeight {n:ℕ} (A:Square n):List (Fin n) → ℝ
  | [] => 1
  | j :: w => pivotMass A j * pathWeight (choleskyStep A j) w
def pathContribution {n:ℕ} (A:Square n) (w:List (Fin n)):ℝ := pathWeight A w * realTrace (pathResidual A w)
def expectedTrace {n:ℕ} (A:Square n) (k:ℕ):ℝ := ∑ f:History n k, pathContribution A (List.ofFn f)
def orderedEigenvalues {n:ℕ} (A:Square n) (hA:A.IsHermitian):Fin n → ℝ := fun i => hA.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i)
def rankTail {n:ℕ} (A:Square n) (hA:A.IsHermitian) (r:ℕ):ℝ := ∑ i ∈ (Finset.univ.filter fun i:Fin n => r ≤ i.val), orderedEigenvalues A hA i
end NLA.RA02 end reset_proof_cache section open scoped BigOperators Classical namespace NLA.RA03
def frobeniusSq {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℂ):ℝ := ∑ i, ∑ j, Complex.normSq (A i j)
abbrev Pivot (m n:ℕ) := Option (Fin m × Fin n)
def pivotMass {m n:ℕ} (S:Matrix (Fin m) (Fin n) ℂ):Pivot m n → ℝ
  | none => if S = 0 then 1 else 0
  | some ij => if S = 0 then 0 else Complex.normSq (S ij.1 ij.2) / frobeniusSq S
def pivotResidual {m n:ℕ} (S:Matrix (Fin m) (Fin n) ℂ) (ij:Fin m × Fin n):Matrix (Fin m) (Fin n) ℂ := if S ij.1 ij.2 = 0 then S else fun a b => S a b - S a ij.2 * S ij.1 b / S ij.1 ij.2
def nextResidual {m n:ℕ} (S:Matrix (Fin m) (Fin n) ℂ):Pivot m n → Matrix (Fin m) (Fin n) ℂ
  | none => 0
  | some ij => pivotResidual S ij
def historyResidual {m n:ℕ} (S:Matrix (Fin m) (Fin n) ℂ):{k:ℕ} → (Fin k → Pivot m n) → Matrix (Fin m) (Fin n) ℂ
  | 0, _ => S
  | k + 1, h => historyResidual (nextResidual S (h 0)) (fun i:Fin k => h i.succ)
def historyMass {m n:ℕ} (S:Matrix (Fin m) (Fin n) ℂ):{k:ℕ} → (Fin k → Pivot m n) → ℝ
  | 0, _ => 1
  | k + 1, h => pivotMass S (h 0) *
      historyMass (nextResidual S (h 0)) (fun i:Fin k => h i.succ)
def expectedError {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℂ) (k:ℕ):ℝ := ∑ h:Fin k → Pivot m n, historyMass A h * frobeniusSq (historyResidual A h)
end NLA.RA03 end reset_proof_cache section namespace NLA.RA02.Paper
def rectangularBestRankErrorSquared {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℂ) (r:ℕ):ℝ := sInf {e:ℝ | ∃ B:Matrix (Fin m) (Fin n) ℂ, B.rank ≤ r ∧ NLA.RA03.frobeniusSq (A-B) = e}
end NLA.RA02.Paper end reset_proof_cache section open scoped ComplexOrder namespace NLA.RA02.Paper
def luRatios (r:ℕ):Set ℝ := {x | ∃ (m n:ℕ) (A:Matrix (Fin m) (Fin n) ℂ), 0 < rectangularBestRankErrorSquared A r ∧ x = NLA.RA03.expectedError A r / rectangularBestRankErrorSquared A r}
def realPositiveLURatios (r:ℕ):Set ℝ := {x | ∃ (n:ℕ) (A:NLA.RA02.Square n) (hA:A.PosDef), (∀ i j, (A i j).im = 0 ∧ 0 < (A i j).re) ∧ 0 < rectangularBestRankErrorSquared A r ∧ x = NLA.RA03.expectedError A r / rectangularBestRankErrorSquared A r}
end NLA.RA02.Paper end reset_proof_cache section open scoped ComplexOrder namespace NLA.RA02.Paper
def choleskyRatios (r:ℕ):Set ℝ := {x | ∃ (n:ℕ) (A:NLA.RA02.Square n) (hA:A.PosSemidef), r ≤ n ∧ 0 < NLA.RA02.rankTail A hA.isHermitian r ∧ x = NLA.RA02.expectedTrace A r / NLA.RA02.rankTail A hA.isHermitian r}
def realPositiveCholeskyRatios (r:ℕ):Set ℝ := {x | ∃ (n:ℕ) (A:NLA.RA02.Square n) (hA:A.PosDef), (∀ i j, (A i j).im = 0 ∧ 0 < (A i j).re) ∧ r ≤ n ∧ 0 < NLA.RA02.rankTail A hA.isHermitian r ∧ x = NLA.RA02.expectedTrace A r / NLA.RA02.rankTail A hA.isHermitian r}
end NLA.RA02.Paper end reset_proof_cache section open scoped BigOperators Classical ComplexOrder Matrix namespace NLA.RA02.Paper
theorem paper_sup_worst_case_constants (r:ℕ):IsLUB (choleskyRatios r) ((2:ℝ)^r) ∧ IsLUB (realPositiveCholeskyRatios r) ((2:ℝ)^r) ∧ IsLUB (luRatios r) ((4:ℝ)^r) ∧ IsLUB (realPositiveLURatios r) ((4:ℝ)^r) := by sorry
end NLA.RA02.Paper end
/- RA-08: Counterexamples to concave matrix-function transfer. -/ reset_proof_cache section open scoped BigOperators Classical MatrixOrder namespace NLA.RA08
abbrev RealMatrix (n:ℕ) := Matrix (Fin n) (Fin n) ℝ
def spectralNorm {n:ℕ} (A:RealMatrix n):ℝ := ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖
structure OrderedSpectralData {n:ℕ} (A:RealMatrix n) where
  eigenvalues:Fin n → ℝ
  orthogonal:Matrix.unitaryGroup (Fin n) ℝ
  decreasing:Antitone eigenvalues
  nonnegative:∀ i, 0 ≤ eigenvalues i
  reconstruct:A =
    (orthogonal:RealMatrix n) * Matrix.diagonal eigenvalues *
      (orthogonal:RealMatrix n).transpose
def spectralCombination {n:ℕ} {A:RealMatrix n} (d:OrderedSpectralData A) (values:Fin n → ℝ):RealMatrix n := (d.orthogonal:RealMatrix n) * Matrix.diagonal values * (d.orthogonal:RealMatrix n).transpose
def truncation {n:ℕ} {A:RealMatrix n} (d:OrderedSpectralData A) (k:ℕ):RealMatrix n := spectralCombination d (fun i => if i.val < k then d.eigenvalues i else 0)
def functionalCalculus {n:ℕ} (f:ℝ → ℝ) (A:RealMatrix n):RealMatrix n := cfc (R := ℝ) f A
def functionTruncation {n:ℕ} {A:RealMatrix n} (d:OrderedSpectralData A) (f:ℝ → ℝ) (k:ℕ):RealMatrix n := spectralCombination d (fun i => if i.val < k then f (d.eigenvalues i) else 0)
def witnessFunction (x:ℝ):ℝ := min x 1
def witnessT:ℝ := 1 / 65536
def witnessA:ℝ := 17 / 16
def witnessB:ℝ := 127 / 128
def witnessF:RealMatrix 6 := (1 / 5265:ℝ) • !![4160, 1024, 1792, 72, 576, 0; 1024, 4160, -1792, 576, 72, 0; 1792, -1792, 2048, -288, 288, 0; 72, 576, -288, 81, 0, 0; 576, 72, 288, 0, 81, 0; 0, 0, 0, 0, 0, 5265]
def witnessApproximation:RealMatrix 6 := Matrix.diagonal ![1 / 2, witnessB, witnessA, 0, 0, 0]
def witnessMatrix:RealMatrix 6 := witnessApproximation + witnessT • witnessF
end NLA.RA08 end reset_proof_cache section open Matrix namespace NLA.RA08.Paper
def nystrom {n l:ℕ} (A:RealMatrix n) (Ω:Matrix (Fin n) (Fin l) ℝ):RealMatrix n := A * Ω * (Ω.transpose * A * Ω)⁻¹ * Ω.transpose * A
end NLA.RA08.Paper end reset_proof_cache section open scoped MatrixOrder open Matrix namespace NLA.RA08.Paper
theorem paper_spectral_failure (C:ℝ) (dA:OrderedSpectralData witnessMatrix):spectralNorm (witnessMatrix - witnessApproximation) ≤ (1 + (0:ℝ)) * spectralNorm (witnessMatrix - truncation dA 3) ∧ ¬ (spectralNorm (functionalCalculus witnessFunction witnessMatrix - functionalCalculus witnessFunction
  witnessApproximation) ≤ (1 + C * 0) * spectralNorm (functionalCalculus witnessFunction witnessMatrix - functionTruncation dA witnessFunction 3)) := by sorry
end NLA.RA08.Paper end reset_proof_cache section open scoped Classical Matrix namespace NLA.RA08.Paper
def nuclearNorm {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℝ):ℝ := (functionalCalculus Real.sqrt (A.transpose*A)).trace
end NLA.RA08.Paper end reset_proof_cache section open scoped Matrix namespace NLA.RA08.Paper
def NuclearTransferFailure (C ε₀:ℝ):Prop := ∃ (n l k:ℕ) (A:RealMatrix n) (Ω:Matrix (Fin n) (Fin l) ℝ) (d:OrderedSpectralData A) (ε:ℝ), A.PosDef ∧ Function.Injective (fun x => Ω *ᵥ x) ∧ k=(nystrom A Ω).rank ∧ 0 < ε ∧ ε < ε₀ ∧ nuclearNorm (A-nystrom A Ω)=(1+ε)*nuclearNorm (A-truncation d k) ∧ nuclearNorm
  (functionalCalculus witnessFunction A- functionalCalculus witnessFunction (nystrom A Ω)) > (1+C*ε)*nuclearNorm (functionalCalculus witnessFunction A- functionTruncation d witnessFunction k)
end NLA.RA08.Paper end reset_proof_cache section open scoped Classical Matrix BigOperators namespace NLA.RA08.Paper
theorem verified_paper_nuclear_counterexample (C ε₀:ℝ) (hC:0 ≤ C) (hε:0 < ε₀):NuclearTransferFailure C ε₀ := by sorry
end NLA.RA08.Paper end
/- RA-09: Sharp Frobenius transfer bounds. -/ reset_proof_cache section open scoped BigOperators Classical MatrixOrder namespace NLA.RA09
abbrev RealMatrix (n:ℕ) := Matrix (Fin n) (Fin n) ℝ
def frobeniusSquared {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℝ):ℝ := ∑ i, ∑ j, A i j ^ 2
section FrobeniusInstance open scoped Matrix.Norms.Frobenius
def frobeniusNorm {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℝ):ℝ := ‖A‖
end FrobeniusInstance
structure OrderedSpectralData {n:ℕ} (A:RealMatrix n) where
  eigenvalues:Fin n → ℝ
  orthogonal:Matrix.unitaryGroup (Fin n) ℝ
  decreasing:Antitone eigenvalues
  nonnegative:∀ i, 0 ≤ eigenvalues i
  reconstruct:A =
    (orthogonal:RealMatrix n) * Matrix.diagonal eigenvalues *
      (orthogonal:RealMatrix n).transpose
def spectralCombination {n:ℕ} {A:RealMatrix n} (d:OrderedSpectralData A) (values:Fin n → ℝ):RealMatrix n := (d.orthogonal:RealMatrix n) * Matrix.diagonal values * (d.orthogonal:RealMatrix n).transpose
def functionalCalculus {n:ℕ} (f:ℝ → ℝ) (A:RealMatrix n):RealMatrix n := cfc (R := ℝ) f A
def functionTruncation {n:ℕ} {A:RealMatrix n} (d:OrderedSpectralData A) (f:ℝ → ℝ) (k:ℕ):RealMatrix n := spectralCombination d (fun i => if i.val < k then f (d.eigenvalues i) else 0)
def spectralTail {n:ℕ} {A:RealMatrix n} (d:OrderedSpectralData A) (k:ℕ):ℝ := ∑ i ∈ Finset.univ.filter (fun i:Fin n => k ≤ i.val), d.eigenvalues i ^ 2
def functionTail {n:ℕ} {A:RealMatrix n} (d:OrderedSpectralData A) (f:ℝ → ℝ) (k:ℕ):ℝ := ∑ i ∈ Finset.univ.filter (fun i:Fin n => k ≤ i.val), f (d.eigenvalues i) ^ 2
end NLA.RA09 end reset_proof_cache section set_option autoImplicit true namespace NLA.RA09
def PaperAdmissibleFunction (f:ℝ → ℝ):Prop := ContinuousOn f (Set.Ici 0) ∧ MonotoneOn f (Set.Ici 0) ∧ (∀ x:ℝ, 0 ≤ x → 0 ≤ f x) ∧ ∀ x y:ℝ, 0 < x → x ≤ y → f y / y ≤ f x / x
end NLA.RA09 end reset_proof_cache section set_option autoImplicit true namespace NLA.RA09
def UnorderedSharpnessWitness (γ:ℝ):Prop := ∃ (n:ℕ) (hn:1 < n) (p:ℝ) (A B:RealMatrix n) (dA:OrderedSpectralData A) (dB:OrderedSpectralData B), 0 < p ∧ p < 1 ∧ B.rank ≤ 1 ∧ dA.eigenvalues ⟨1,hn⟩ = 1 ∧ 0 < spectralTail dA 1 ∧ 0 < frobeniusSquared (A-B) - spectralTail dA 1 ∧ 0 < frobeniusNorm (A-B) /
  Real.sqrt (spectralTail dA 1) - 1 ∧ γ * (frobeniusSquared (A-B) - spectralTail dA 1) < frobeniusSquared (functionalCalculus (fun x:ℝ => x^p) A - functionTruncation dB (fun x:ℝ => x^p) 1) - functionTail dA (fun x:ℝ => x^p) 1 ∧ γ * (frobeniusNorm (A-B) / Real.sqrt (spectralTail dA 1) - 1) < frobeniusNorm
  (functionalCalculus (fun x:ℝ => x^p) A - functionTruncation dB (fun x:ℝ => x^p) 1) / Real.sqrt (functionTail dA (fun x:ℝ => x^p) 1) - 1
end NLA.RA09 end reset_proof_cache section open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder open Matrix namespace NLA.RA09
theorem paper_ordered_matrix_norm_relative {n:ℕ} {A B:RealMatrix n} (dA:OrderedSpectralData A) (dB:OrderedSpectralData B) (hBA:B ≤ A) (f:ℝ → ℝ) (hf:PaperAdmissibleFunction f) (k:ℕ) (hk:k < n) (hB:B.rank ≤ k) (hτ:0 < dA.eigenvalues ⟨k,hk⟩) (ε:ℝ) (hε:0 ≤ ε) (hA:frobeniusNorm (A-B) ≤
  (1+ε)*Real.sqrt (spectralTail dA k)):frobeniusNorm (functionalCalculus f A - functionTruncation dB f k) ≤ (1+ε)*Real.sqrt (functionTail dA f k) := by sorry
theorem paper_unordered_matrix_norm_relative {n:ℕ} {A B:RealMatrix n} (dA:OrderedSpectralData A) (dB:OrderedSpectralData B) (f:ℝ → ℝ) (hf:PaperAdmissibleFunction f) (k:ℕ) (hk:k < n) (hB:B.rank ≤ k) (hτ:0 < dA.eigenvalues ⟨k,hk⟩) (ε:ℝ) (hε:0 ≤ ε) (hA:frobeniusNorm (A-B) ≤ (1+ε)*Real.sqrt
  (spectralTail dA k)):frobeniusNorm (functionalCalculus f A - functionTruncation dB f k) ≤ (1+2*ε)*Real.sqrt (functionTail dA f k) := by sorry
theorem paper_ordered_sharpness (γ:ℝ) (hγ:γ < 1):∃ (A B:RealMatrix 3) (dA:OrderedSpectralData A) (dB:OrderedSpectralData B), B ≤ A ∧ B.rank ≤ 1 ∧ dA.eigenvalues ⟨1, by decide⟩ = 1 ∧ frobeniusSquared (A-B) - spectralTail dA 1 = 1 ∧ γ * (frobeniusSquared (A-B) - spectralTail dA 1) < frobeniusSquared
  (functionalCalculus (fun x:ℝ => x) A - functionTruncation dB (fun x:ℝ => x) 1) - functionTail dA (fun x:ℝ => x) 1 := by sorry
theorem paper_unordered_sharpness (γ:ℝ) (hγ:γ < 2):UnorderedSharpnessWitness γ := by sorry
end NLA.RA09 end
/- IE-21: Limit for random-row deletion. -/ reset_proof_cache section open MeasureTheory ProbabilityTheory Filter Set open scoped BigOperators ENNReal RealInnerProductSpace Topology namespace NLA.IE21
abbrev Space (n:ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Mat (m n:ℕ) := Matrix (Fin m) (Fin n) ℝ
abbrev Sphere (n:ℕ) := Metric.sphere (0:Space n) 1
instance matrixMeasurableSpace (m n:ℕ):MeasurableSpace (Mat m n) := inferInstanceAs (MeasurableSpace (Fin m → Fin n → ℝ))
instance matrixBorelSpace (m n:ℕ):BorelSpace (Mat m n) := inferInstanceAs (BorelSpace (Fin m → Fin n → ℝ))
def surfaceMeasure (n:ℕ):Measure (Sphere n) := (volume:Measure (Space n)).toSphere
def surfaceLaw (n:ℕ):Measure (Sphere n) := (surfaceMeasure n Set.univ)⁻¹ • surfaceMeasure n
def sphereLaw (n:ℕ):Measure (Space n) := (surfaceLaw n).map Subtype.val
def matrixRow {m n:ℕ} (A:Mat m n) (i:Fin m):Space n := WithLp.toLp 2 (A i)
/-- Scalar multiplication on the Euclidean domain is continuous. -/ theorem matrixMap._proof_6 {d:ℕ}:@ContinuousSMul Real (qC d) (@SMulZeroClass.toSMul Real (qC d) (@AddZero.toZero (qC d) (@AddZeroClass.toAddZero (qC d) (@AddMonoid.toAddZeroClass (qC d) (qE d)))) (@DistribSMul.toSMulZeroClass Real (qC d) (@AddMonoid.toAddZeroClass (qC d) (qE d)) (@DistribMulAction.toDistribSMul Real (qC d) ((qF).toSemiring).toMonoid (qE d) (@Module.toDistribMulAction Real (qC d) (qF).toSemiring (qH d) (@WithLp.instModule (qA) Real ((Fin d) -> Real) (qF).toSemiring (@Pi.addCommGroup (Fin d) (fun (z0:Fin d) => Real) (fun (i:Fin d) => Real.instAddCommGroup)) (@Pi.Function.module (Fin d) Real Real (qF).toSemiring ((Real.instRing).toSemiring).toAddCommMonoid ((qF).toSemiring).toModule)))))) ((((((Real.normedField).toNormedCommRing).toSeminormedCommRing).toSeminormedRing).toPseudoMetricSpace).toUniformSpace).toTopologicalSpace (qI d) := (by sorry) cache_proof NLA.IE21.matrixMap._proof_6
/-- Each fixed scalar acts continuously on the Euclidean codomain. -/ theorem matrixMap._proof_4 {d:ℕ}:@ContinuousConstSMul Real (qC d) (qI d) (@SMulZeroClass.toSMul Real (qC d) (@AddZero.toZero (qC d) (@AddZeroClass.toAddZero (qC d) (@AddMonoid.toAddZeroClass (qC d) (qL d)))) (@DistribSMul.toSMulZeroClass Real (qC d) (@AddMonoid.toAddZeroClass (qC d) (qL d)) (@DistribMulAction.toDistribSMul Real (qC d) ((qK).toSemiring).toMonoid (qL d) (@Module.toDistribMulAction Real (qC d) (qK).toSemiring (qH d) (@WithLp.instModule (qA) Real ((Fin d) -> Real) (qM).toSemiring (@Pi.addCommGroup (Fin d) (fun (z0:Fin d) => Real) (fun (i:Fin d) => @Ring.toAddCommGroup Real ((qD).toDivisionRing).toRing)) (@Pi.Function.module (Fin d) Real Real (qM).toSemiring ((((qD).toDivisionRing).toRing).toSemiring).toAddCommMonoid ((qM).toSemiring).toModule)))))) := (by sorry) cache_proof NLA.IE21.matrixMap._proof_4
def matrixMap {m n:ℕ} (A:Mat m n):Space n →L[ℝ] Space m := (Matrix.toEuclideanLin A).toContinuousLinearMap
def operatorNorm {m n:ℕ} (A:Mat m n):ℝ := ‖matrixMap A‖
def retainedRows (θ:ℝ) (m:ℕ):ℕ := ⌊θ * (m:ℝ)⌋₊
def retainedMatrix {m n:ℕ} (A:Mat m n) (S:Finset (Fin m)):Matrix S (Fin n) ℝ := fun i j => A i.val j
def retainedNorm {m n:ℕ} (A:Mat m n) (S:Finset (Fin m)) (x:Space n):ℝ := ‖Matrix.toEuclideanLin (retainedMatrix A S) x‖
def deletionSingular {m n:ℕ} (θ:ℝ) (A:Mat m n):ℝ := sInf {z | ∃ (S:Finset (Fin m)) (x:Space n), S.card = retainedRows θ m ∧ ‖x‖ = 1 ∧ z = retainedNorm A S x}
def normalizedDeletion {m n:ℕ} (θ:ℝ) (A:Mat m n):ℝ := (n:ℝ) / m * deletionSingular θ A ^ 2
def normalizedOperator {m n:ℕ} (A:Mat m n):ℝ := (n:ℝ) / m * operatorNorm A ^ 2
def deletionRatio {m n:ℕ} (θ:ℝ) (A:Mat m n):ℝ := deletionSingular θ A ^ 2 / operatorNorm A ^ 2
def gaussianCutoff (θ:ℝ):ℝ := sInf {a:ℝ | 0 ≤ a ∧ θ ≤ (gaussianReal 0 1).real {g | |g| ≤ a}}
def gaussianTrim (θ:ℝ):ℝ := (1 / Real.sqrt (2 * Real.pi)) * ∫ g in Set.Icc (-gaussianCutoff θ) (gaussianCutoff θ), g ^ 2 * Real.exp (-(g ^ 2) / 2)
def IndependentSphereRows {Ω:Type*} [MeasurableSpace Ω] {m n:ℕ} (μ:Measure Ω) (A:Ω → Mat m n):Prop := Measurable A ∧ iIndepFun (fun i ω => matrixRow (A ω) i) μ ∧ ∀ i, μ.map (fun ω => matrixRow (A ω) i) = sphereLaw n
end NLA.IE21 end reset_proof_cache section open MeasureTheory ProbabilityTheory Filter Set open scoped BigOperators ENNReal RealInnerProductSpace Topology namespace NLA.IE21.Paper open NLA.IE21
theorem paper_random_rows (θ:ℝ) (hθ:0 < θ ∧ θ < 1) (m n:ℕ → ℕ) (hm:∀ j, 1 ≤ m j) (hn:∀ j, 1 ≤ n j) (hnlim:Tendsto n atTop atTop) (hQlim:Tendsto (fun j => (m j:ℝ)/n j) atTop atTop) (Ω:ℕ → Type*) [∀ j, MeasurableSpace (Ω j)] (μ:(j:ℕ) → Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)] (A:(j:ℕ) → Ω j → Mat (m j) (n j)) (hA:∀ j, IndependentSphereRows (μ j) (A j)) (η:ℝ) (hη:0 < η):Tendsto (fun j => (μ j).real {ω | ¬(|normalizedDeletion θ (A j ω)-gaussianTrim θ| ≤ η ∧
        |normalizedOperator (A j ω)-1| ≤ η ∧ |deletionRatio θ (A j ω)-gaussianTrim θ| ≤ η)})
      atTop (𝓝 0) := by sorry
end NLA.IE21.Paper end
/- IE-22: The sharp universal row-deletion constant. -/ reset_proof_cache reset_proof_cache section open MeasureTheory ProbabilityTheory Filter Set open scoped BigOperators ENNReal RealInnerProductSpace Topology namespace NLA.IE22 open NLA.IE21
def UnitRows {m n:ℕ} (A:Mat m n):Prop := ∀ i, ‖matrixRow A i‖ = 1
def normalizedSingular {m n:ℕ} (θ:ℝ) (A:Mat m n):ℝ := Real.sqrt ((n:ℝ) / m) * deletionSingular θ A
def unitRowValues (θ:ℝ) (m n:ℕ):Set ℝ := {z | ∃ A:Mat m n, UnitRows A ∧ z = normalizedSingular θ A}
def extremalValue (θ:ℝ) (m n:ℕ):ℝ := sSup (unitRowValues θ m n)
def sharpConstant (θ:ℝ):ℝ := Real.sqrt (gaussianTrim θ)
def errorSchedule (n:ℕ):ℝ := Real.rpow (n:ℝ) (-(1 / 6:ℝ))
end NLA.IE22 end reset_proof_cache section open MeasureTheory ProbabilityTheory Filter Set open scoped BigOperators ENNReal RealInnerProductSpace Topology namespace NLA.IE22.Paper open NLA.IE21
theorem paper_high_aspect_supremum_limit (θ:ℝ) (hθ:0 < θ ∧ θ < 1) (m n:ℕ → ℕ) (hm:∀ j, 1 ≤ m j) (hn:∀ j, 1 ≤ n j) (hnlim:Tendsto n atTop atTop) (hQlim:Tendsto (fun j => (m j:ℝ) / n j) atTop atTop):Tendsto (fun j => extremalValue θ (m j) (n j)) atTop (𝓝 (sharpConstant θ)) := by sorry
theorem paper_universal_squared_rate (θ:ℝ) (hθ:0 < θ ∧ θ < 1):∃ C:ℝ, 0 < C ∧ ∃ N:ℕ, 1 ≤ N ∧ ∀ m n:ℕ, 1 ≤ m → N ≤ n → (∀ A:Mat m n, UnitRows A → normalizedDeletion θ A ≤ gaussianTrim θ + C * errorSchedule n) ∧ extremalValue θ m n ^ 2 ≤ gaussianTrim θ + C * errorSchedule n := by sorry
end NLA.IE22.Paper end
/- TR-04: A strict tensor-train approximation bound. -/ reset_proof_cache section namespace Reference.RealSVDPackage open scoped BigOperators Matrix
abbrev Rect (m n:ℕ) := Matrix (Fin m) (Fin n) ℝ
abbrev Square (r:ℕ) := Rect r r
abbrev EuclideanVector (n:ℕ) := EuclideanSpace ℝ (Fin n)
def euclideanLin {m n:ℕ} (A:Rect m n):EuclideanVector n →ₗ[ℝ] EuclideanVector m := Matrix.toEuclideanLin A
def singularValue {m n:ℕ} (A:Rect m n) (k:ℕ):ℝ := (euclideanLin A).singularValues k
def basisMatrix {r:ℕ} (v:OrthonormalBasis (Fin r) ℝ (EuclideanVector r)):Square r := fun i j => v j i
end Reference.RealSVDPackage end reset_proof_cache section namespace Reference.RealOptimalityEquality open Reference.RealSVDPackage
def leftBasis {m n:ℕ} (A:Rect m n):OrthonormalBasis (Fin m) ℝ (EuclideanVector m) := (euclideanLin A.transpose).isSymmetric_adjoint_comp_self.eigenvectorBasis (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := m))
def leftVectorMatrix {m n:ℕ} (A:Rect m n):Square m := basisMatrix (leftBasis A)
end Reference.RealOptimalityEquality end reset_proof_cache section namespace Reference.RecursiveTensorCompletion open Reference.RealSVDPackage open scoped BigOperators Matrix Kronecker
def ModeIndex:List ℕ → Type
  | [] => PUnit
  | n::ns => Fin n × ModeIndex ns
instance modeIndexFintype (ns:List ℕ):Fintype (ModeIndex ns) := by
  induction ns with
  | nil => exact inferInstanceAs (Fintype PUnit)
  | cons n ns ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Fin n × ModeIndex ns))
instance modeIndexDecidableEq (ns:List ℕ):DecidableEq (ModeIndex ns) := by
  induction ns with
  | nil => exact inferInstanceAs (DecidableEq PUnit)
  | cons n ns ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (Fin n × ModeIndex ns))
abbrev Tensor (m:ℕ) (ns:List ℕ) := Matrix (Fin m) (ModeIndex ns) ℝ
def tensorFrobeniusSq {m:ℕ} {ns:List ℕ} (A:Tensor m ns):ℝ := ∑ i, ∑ j, A i j ^ 2
def rowCount (m n:ℕ):ℕ := Fintype.card (Fin m × Fin n)
def rowEquiv (m n:ℕ):(Fin m × Fin n) ≃ Fin (rowCount m n) := Fintype.equivFin (Fin m × Fin n)
def merge {m n:ℕ} {ns:List ℕ} (A:Tensor m (n::ns)):Tensor (rowCount m n) ns := fun i j => A ((rowEquiv m n).symm i).1 (((rowEquiv m n).symm i).2, j)
def feasible (m:ℕ) (ns:List ℕ) (A:Tensor m ns) (rs:List ℕ):Prop :=
  match ns, A, rs with
  | [], _, rs => rs=[]
  | _::_, _, [] => False
  | n::ns, A, r::rs => A.rank ≤ r ∧ feasible (rowCount m n) ns (merge A) rs
termination_by ns.length
end Reference.RecursiveTensorCompletion end reset_proof_cache section namespace Reference.LexicographicFeasibilityBridge open Reference.RecursiveTensorCompletion
theorem product_eq_rowCount (m n:ℕ):m*n = rowCount m n := by sorry
def rowEquivLex (m n:ℕ):Fin m × Fin n ≃ Fin (rowCount m n) := (finProdFinEquiv:Fin m × Fin n ≃ Fin (m*n)).trans (finCongr (product_eq_rowCount m n))
end Reference.LexicographicFeasibilityBridge end reset_proof_cache section namespace Reference.TensorCandidateSelection attribute [local instance] Classical.propDecidable open Reference.RealSVDPackage Reference.RecursiveTensorCompletion
def error {m:ℕ} {ns:List ℕ} (A X:Tensor m ns):ℝ := tensorFrobeniusSq (A-X)
end Reference.TensorCandidateSelection end reset_proof_cache section namespace Reference.TensorOptimumAttainment open Reference.RecursiveTensorCompletion Reference.TensorCandidateSelection
def feasibleSet (m:ℕ) (ns:List ℕ) (rs:List ℕ):Set (Tensor m ns) := {Y | feasible m ns Y rs}
def optimalError {m:ℕ} {ns:List ℕ} (A:Tensor m ns) (rs:List ℕ):ℝ := sInf (error A '' feasibleSet m ns rs)
end Reference.TensorOptimumAttainment end reset_proof_cache section open Reference.RealSVDPackage namespace Reference.LexTensorArithmeticExecution open Reference.RealSVDPackage Reference.RealOptimalityEquality open scoped Matrix
inductive Event where
  | read (x:ℝ)
  | zero
  | add (x y:ℝ)
  | sub (x y:ℝ)
  | mul (x y:ℝ)
  | less (x y:ℝ)
  | leftSubspace (m n:ℕ) (A:Rect m n)
def eventCharge:Event → ℕ
  | .leftSubspace m n _ => (m+n+1)^3
  | _ => 1
structure Run (α:Type) where
  value:α
  trace:List Event
def pureRun {α:Type} (x:α):Run α := ⟨x,[]⟩
def bindRun {α β:Type} (x:Run α) (f:α → Run β):Run β :=
  let y:=f x.value
  ⟨y.value,x.trace++y.trace⟩
instance:Monad Run where
  pure := pureRun
  bind := bindRun
def readReal (x:ℝ):Run ℝ := ⟨x,[.read x]⟩
def zeroReal:Run ℝ := ⟨0,[.zero]⟩
def addReal (x y:ℝ):Run ℝ := ⟨x+y,[.add x y]⟩
def subReal (x y:ℝ):Run ℝ := ⟨x-y,[.sub x y]⟩
def mulReal (x y:ℝ):Run ℝ := ⟨x*y,[.mul x y]⟩
def lessReal (x y:ℝ):Run Bool := ⟨decide (x<y),[.less x y]⟩
def leftSubspace {m n:ℕ} (A:Rect m n):Run (Square m) := ⟨leftVectorMatrix A,[.leftSubspace m n A]⟩
end Reference.LexTensorArithmeticExecution namespace Reference.LexTensorCompletion open Reference.RealSVDPackage open scoped BigOperators Matrix Kronecker
abbrev ModeIndex (ns:List ℕ) := Reference.RecursiveTensorCompletion.ModeIndex ns
abbrev Tensor (m:ℕ) (ns:List ℕ) := Reference.RecursiveTensorCompletion.Tensor m ns
def tensorFrobeniusSq {m:ℕ} {ns:List ℕ} (A:Tensor m ns):ℝ := ∑ i, ∑ j, A i j ^ 2
abbrev rowCount (m n:ℕ) := Reference.RecursiveTensorCompletion.rowCount m n
def rowEquiv (m n:ℕ):(Fin m × Fin n) ≃ Fin (rowCount m n) := Reference.LexicographicFeasibilityBridge.rowEquivLex m n
def merge {m n:ℕ} {ns:List ℕ} (A:Tensor m (n::ns)):Tensor (rowCount m n) ns := fun i j => A ((rowEquiv m n).symm i).1 (((rowEquiv m n).symm i).2, j)
def unmerge {m n:ℕ} {ns:List ℕ} (A:Tensor (rowCount m n) ns):Tensor m (n::ns) := fun i j => A (rowEquiv m n (i,j.1)) j.2
def feasible (m:ℕ) (ns:List ℕ) (A:Tensor m ns) (rs:List ℕ):Prop :=
  match ns, A, rs with
  | [], _, rs => rs=[]
  | _::_, _, [] => False
  | n::ns, A, r::rs => A.rank ≤ r ∧ feasible (rowCount m n) ns (merge A) rs
termination_by ns.length
end Reference.LexTensorCompletion namespace Reference.LexOrderedIndex
def indexList {m:ℕ} (p:Fin m → Prop) [DecidablePred p]:List (Fin m) := (List.finRange m).filter (fun i => decide (p i))
theorem mem_indexList {m:ℕ} (p:Fin m → Prop) [DecidablePred p] (i:Fin m):i∈indexList p ↔ p i := by simp [indexList]
theorem nodup_indexList {m:ℕ} (p:Fin m → Prop) [DecidablePred p]:(indexList p).Nodup := (List.nodup_finRange m).filter _
def predicateListEquiv {m:ℕ} (p:Fin m → Prop) [DecidablePred p]:{i:Fin m // p i} ≃ {i:Fin m // i∈indexList p} where
  toFun i := ⟨i.val,(mem_indexList p i.val).mpr i.property⟩
  invFun i := ⟨i.val,(mem_indexList p i.val).mp i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
def listEnum {m:ℕ} (p:Fin m → Prop) [DecidablePred p]:{i:Fin m // p i} ≃ Fin (indexList p).length := (predicateListEquiv p).trans (List.Nodup.getEquiv (indexList p) (nodup_indexList p)).symm
theorem indexList_length {m:ℕ} (p:Fin m → Prop) [DecidablePred p]:(indexList p).length=Fintype.card {i:Fin m // p i} := by
  have h:=Fintype.card_congr (listEnum p)
  simpa only [Fintype.card_fin] using h.symm
def indexEnum {m:ℕ} (p:Fin m → Prop) [DecidablePred p]:{i:Fin m // p i} ≃ Fin (Fintype.card {i:Fin m // p i}) := (listEnum p).trans (finCongr (indexList_length p))
end Reference.LexOrderedIndex set_option maxHeartbeats 2000000 set_option backward.isDefEq.respectTransparency false namespace Reference.LexTensorArithmeticExecution open Reference.RealSVDPackage open scoped BigOperators Matrix
def vectorRun {α:Type}:(n:ℕ) → (Fin n → Run α) → Run (Fin n → α)
  | 0,_ => pureRun Fin.elim0
  | n+1,f => bindRun (f 0) fun x =>
      bindRun (vectorRun n (fun i => f i.succ)) fun xs => pureRun (Fin.cases x xs)
def dotRun:(k:ℕ) → (Fin k → ℝ) → (Fin k → ℝ) → Run ℝ
  | 0,_,_ => zeroReal
  | k+1,a,b => bindRun (readReal (a 0)) fun x =>
      bindRun (readReal (b 0)) fun y =>
      bindRun (mulReal x y) fun p =>
      bindRun (dotRun k (fun i => a i.succ) (fun i => b i.succ)) fun q => addReal p q
def matrixMulRun {m k n:ℕ} (A:Rect m k) (B:Rect k n):Run (Rect m n) := vectorRun m fun i => vectorRun n fun j => dotRun k (fun a => A i a) (fun a => B a j)
end Reference.LexTensorArithmeticExecution namespace Reference.LexTensorCompletion
def lexCard:List ℕ → ℕ
  | [] => 1
  | n::ns => n*lexCard ns
/-- The empty tensor mode list has a valid zero index. -/ theorem lexIndex._proof_2:0 < lexCard [] := (by sorry) cache_proof Reference.LexTensorCompletion.lexIndex._proof_2
/-- The empty-mode lexicographic index has a right inverse. -/ theorem lexIndex._proof_5 (j:Fin (lexCard [])):(fun (_:ModeIndex []) => (⟨0,lexIndex._proof_2⟩:Fin (lexCard []))) ((fun (_:Fin (lexCard [])) => PUnit.unit) j) = j := (by sorry) cache_proof Reference.LexTensorCompletion.lexIndex._proof_5
def lexIndex:(ns:List ℕ) → ModeIndex ns ≃ Fin (lexCard ns)
  | [] => {
      toFun := fun _ => ⟨0,by change 0<1; omega⟩
      invFun := fun _ => PUnit.unit
      left_inv := fun i => by cases i; rfl
      right_inv := fun j => by apply Fin.ext; change 0=j.val; have hj:=j.isLt; change j.val<1 at hj; omega }
  | n::ns => (Equiv.prodCongr (Equiv.refl (Fin n)) (lexIndex ns)).trans finProdFinEquiv
theorem lexCard_eq_card (ns:List ℕ):lexCard ns=Fintype.card (ModeIndex ns) := by sorry
def concreteLayout (ns:List ℕ):ModeIndex ns ≃ Fin (Fintype.card (ModeIndex ns)) := (lexIndex ns).trans (finCongr (lexCard_eq_card ns))
end Reference.LexTensorCompletion namespace Reference.LexOrderedCyclicBoundary attribute [local instance] Classical.propDecidable open Reference.RealSVDPackage Reference.RealOptimalityEquality open scoped Matrix BigOperators
def EIndex {m n:ℕ} (A:Rect m n) (tau:ℝ) := {i:Fin m // singularValue A.transpose i.val=tau}
def HIndex {m n:ℕ} (A:Rect m n) (tau:ℝ) := {i:Fin m // tau<singularValue A.transpose i.val}
noncomputable instance eFinite {m n:ℕ} (A:Rect m n) (tau:ℝ):Fintype (EIndex A tau) := by
  classical
  exact inferInstanceAs (Fintype {i:Fin m // singularValue A.transpose i.val=tau})
noncomputable instance hFinite {m n:ℕ} (A:Rect m n) (tau:ℝ):Fintype (HIndex A tau) := by
  classical
  exact inferInstanceAs (Fintype {i:Fin m // tau<singularValue A.transpose i.val})
def eCount {m n:ℕ} (A:Rect m n) (tau:ℝ) := Fintype.card (EIndex A tau)
def hCount {m n:ℕ} (A:Rect m n) (tau:ℝ) := Fintype.card (HIndex A tau)
def boundaryOrdinal {m n:ℕ} (A:Rect m n) (tau:ℝ) := Reference.LexOrderedIndex.indexEnum (fun i:Fin m => singularValue A.transpose i.val=tau)
def inWindow {t:ℕ} (s:ℕ) (j i:Fin t):Prop := (i-j).val<s
def windowSelected {m n:ℕ} (A:Rect m n) (tau:ℝ) (s:ℕ) (j:Fin (eCount A tau)) (i:Fin m):Prop := if he:singularValue A.transpose i.val=tau then inWindow s j (boundaryOrdinal A tau ⟨i,he⟩) else False
def selected {m n:ℕ} (A:Rect m n) (tau:ℝ) (s:ℕ) (j:Fin (eCount A tau)) (i:Fin m):Prop := tau<singularValue A.transpose i.val ∨ windowSelected A tau s j i
def indicatorFrame {m:ℕ} (V:Square m) (p:Fin m → Prop):Rect m (Fintype.card {i:Fin m // p i}) := V.submatrix id (fun j => ((Reference.LexOrderedIndex.indexEnum p).symm j).val)
def candidateFrame {m n:ℕ} (A:Rect m n) (tau:ℝ) (s:ℕ) (j:Fin (eCount A tau)) := indicatorFrame (leftVectorMatrix A) (selected A tau s j)
end Reference.LexOrderedCyclicBoundary namespace Reference.LexTensorCompletion open Reference.RealSVDPackage
def denseTensor {m:ℕ} {ns:List ℕ} (A:Tensor m ns):Rect m (Fintype.card (ModeIndex ns)) := A.submatrix id (concreteLayout ns).symm
def svdFrame {m:ℕ} {ns:List ℕ} (A:Tensor m ns) (r:ℕ):Rect m (min r m) := fun i j => Reference.RealOptimalityEquality.leftVectorMatrix (denseTensor A) i ⟨j.val,j.isLt.trans_le (Nat.min_le_right r m)⟩
def ttSVD (m:ℕ) (ns:List ℕ) (A:Tensor m ns) (rs:List ℕ):Tensor m ns :=
  match ns,A,rs with
  | [],A,_ => A
  | _::_,A,[] => A
  | n::ns,A,r::rs =>
    let U := svdFrame A r
    let C := merge (U.transpose*A)
    let Z := ttSVD (rowCount (min r m) n) ns C rs
    U * unmerge (m:=min r m) (n:=n) Z
termination_by ns.length
def completeFrame {m k n:ℕ} {ns:List ℕ} (A:Tensor m (n::ns)) (U:Rect m k) (rs:List ℕ):Tensor m (n::ns) := U * unmerge (m:=k) (n:=n) (ttSVD (rowCount k n) ns (merge (U.transpose*A)) rs)
end Reference.LexTensorCompletion namespace Reference.LexOrderedCyclicBoundary attribute [local instance] Classical.propDecidable open Reference.RealSVDPackage Reference.RealOptimalityEquality open scoped BigOperators end Reference.LexOrderedCyclicBoundary namespace Reference.LexOrderedCyclicBoundary open Reference.RealSVDPackage Reference.LexTensorCompletion
def tensorBoundary {m:ℕ} {ns:List ℕ} (A:Tensor m ns) (r:ℕ):ℝ := singularValue (denseTensor A) (r-1)
def tensorBoundaryCount {m:ℕ} {ns:List ℕ} (A:Tensor m ns) (r:ℕ):ℕ := eCount (denseTensor A) (tensorBoundary A r)
def tensorRetainedBoundary {m:ℕ} {ns:List ℕ} (A:Tensor m ns) (r:ℕ):ℕ := r-hCount (denseTensor A) (tensorBoundary A r)
def tensorCandidateFrame {m:ℕ} {ns:List ℕ} (A:Tensor m ns) (r:ℕ) (j:Fin (tensorBoundaryCount A r)) := candidateFrame (denseTensor A) (tensorBoundary A r) (tensorRetainedBoundary A r) j
def cyclicCompletion {m n:ℕ} {ns:List ℕ} (A:Tensor m (n::ns)) (r:ℕ) (rs:List ℕ) (j:Fin (tensorBoundaryCount A r)):Tensor m (n::ns) := completeFrame A (tensorCandidateFrame A r j) rs
end Reference.LexOrderedCyclicBoundary namespace Reference.LexOrderedTensorSolver attribute [local instance] Classical.propDecidable open Reference.RealSVDPackage Reference.LexTensorCompletion Reference.LexOrderedCyclicBoundary
def error {m:ℕ} {ns:List ℕ} (A X:Tensor m ns):ℝ := tensorFrobeniusSq (A-X)
def firstMinimum {m:ℕ} {ns:List ℕ} (A:Tensor m ns) (x:Tensor m ns):List (Tensor m ns) → Tensor m ns
  | [] => x
  | y::ys => if error A y<error A x then firstMinimum A y ys else firstMinimum A x ys
def leadingCompletion {m n:ℕ} {ns:List ℕ} (A:Tensor m (n::ns)) (r:ℕ) (rs:List ℕ) := completeFrame A (svdFrame A r) rs
def columnSpaceCompletion {m n:ℕ} {ns:List ℕ} (A:Tensor m (n::ns)) (rs:List ℕ) := completeFrame A (svdFrame A (denseTensor A).rank) rs
def candidates {m n:ℕ} {ns:List ℕ} (A:Tensor m (n::ns)) (r:ℕ) (rs:List ℕ):List (Tensor m (n::ns)) := if (denseTensor A).rank ≤ r then [columnSpaceCompletion A rs] else if ht:0<tensorBoundaryCount A r then if tensorRetainedBoundary A r=tensorBoundaryCount A r then [cyclicCompletion A r rs ⟨0,ht⟩] else
  List.ofFn (cyclicCompletion A r rs) else [leadingCompletion A r rs]
def solver {m n:ℕ} {ns:List ℕ} (A:Tensor m (n::ns)) (r:ℕ) (rs:List ℕ) :=
  match candidates A r rs with
  | [] => leadingCompletion A r rs
  | x::xs => firstMinimum A x xs
end Reference.LexOrderedTensorSolver namespace Reference.LexTensorExecution open Reference.RealSVDPackage Reference.RealOptimalityEquality open scoped Matrix
inductive Event where
  | ordinary (e:Reference.LexTensorArithmeticExecution.Event)
  | spectral (m n:ℕ) (A:Rect m n)
  | equalReal (x y:ℝ)
  | equalNat (x y:ℕ)
  | lessNat (x y:ℕ)
  | addNat (x y:ℕ)
  | subNat (x y:ℕ)
  | modNat (x y:ℕ)
  | branch (b:Bool)
def eventCharge:Event → ℕ
  | .ordinary e => Reference.LexTensorArithmeticExecution.eventCharge e
  | .spectral m n _ => (m+n+1)^3
  | _ => 1
structure Run (α:Type) where
  value:α
  trace:List Event
def pureRun {α:Type} (x:α):Run α := ⟨x,[]⟩
def bindRun {α β:Type} (x:Run α) (f:α → Run β):Run β :=
  let y:=f x.value
  ⟨y.value,x.trace++y.trace⟩
def liftRun {α:Type} (x:Reference.LexTensorArithmeticExecution.Run α):Run α := ⟨x.value,x.trace.map Event.ordinary⟩
def spectralRun {m n:ℕ} (A:Rect m n):Run (Square m × (Fin m → ℝ)) := ⟨(leftVectorMatrix A,fun i => singularValue A.transpose i.val),[.spectral m n A]⟩
def equalRealRun (x y:ℝ):Run Bool := ⟨decide (x=y),[.equalReal x y]⟩
def equalNatRun (x y:ℕ):Run Bool := ⟨decide (x=y),[.equalNat x y]⟩
def lessNatRun (x y:ℕ):Run Bool := ⟨decide (x<y),[.lessNat x y]⟩
def addNatRun (x y:ℕ):Run ℕ := ⟨x+y,[.addNat x y]⟩
def subNatRun (x y:ℕ):Run ℕ := ⟨x-y,[.subNat x y]⟩
def modNatRun (x y:ℕ):Run ℕ := ⟨x%y,[.modNat x y]⟩
def branchRun (b:Bool):Run Bool := ⟨b,[.branch b]⟩
def charge {α:Type} (x:Run α):ℕ := (x.trace.map eventCharge).sum
def filterRun {α:Type} (p:α → Run Bool):List α → Run (List α)
  | [] => pureRun []
  | i::is => bindRun (p i) fun b =>
      bindRun (branchRun b) fun keep =>
      bindRun (filterRun p is) fun rest => pureRun (if keep then i::rest else rest)
def ordinalRun {m:ℕ} (i:Fin m):List (Fin m) → Run ℕ
  | [] => pureRun 0
  | j::js => bindRun (equalNatRun i.val j.val) fun equal =>
      bindRun (branchRun equal) fun equal =>
      if equal then pureRun 0 else bindRun (ordinalRun i js) fun n => addNatRun 1 n
end Reference.LexTensorExecution namespace Reference.LexTensorExecution open Reference.RealSVDPackage
def readRun (x:ℝ):Run ℝ := liftRun (Reference.LexTensorArithmeticExecution.readReal x)
def lessRealRun (x y:ℝ):Run Bool := liftRun (Reference.LexTensorArithmeticExecution.lessReal x y)
def equalScanRun {m:ℕ} (sigma:Fin m → ℝ) (tau:ℝ):Run (List (Fin m)) := filterRun (fun i => bindRun (readRun (sigma i)) fun x => equalRealRun x tau) (List.finRange m)
def aboveScanRun {m:ℕ} (sigma:Fin m → ℝ) (tau:ℝ):Run (List (Fin m)) := filterRun (fun i => bindRun (readRun (sigma i)) fun x => lessRealRun tau x) (List.finRange m)
def windowMaskRun {m:ℕ} (sigma:Fin m → ℝ) (tau:ℝ) (boundary:List (Fin m)) (s j:ℕ) (i:Fin m):Run Bool := bindRun (readRun (sigma i)) fun x => bindRun (lessRealRun tau x) fun above => bindRun (branchRun above) fun above => if above then pureRun true else bindRun (equalRealRun x tau) fun equal => bindRun
  (branchRun equal) fun equal => if equal then bindRun (ordinalRun i boundary) fun a => bindRun (subNatRun boundary.length j) fun b => bindRun (addNatRun a b) fun c => bindRun (modNatRun c boundary.length) fun d => lessNatRun d s else pureRun false
def windowScanRun {m:ℕ} (sigma:Fin m → ℝ) (tau:ℝ) (boundary:List (Fin m)) (s j:ℕ):Run (List (Fin m)) := filterRun (windowMaskRun sigma tau boundary s j) (List.finRange m)
def frameFromListRun {m:ℕ} (V:Square m) (is:List (Fin m)):Run (Rect m is.length) := liftRun (Reference.LexTensorArithmeticExecution.vectorRun m fun i => Reference.LexTensorArithmeticExecution.vectorRun is.length fun j => Reference.LexTensorArithmeticExecution.readReal (V i (is.get j)))
end Reference.LexTensorExecution set_option maxHeartbeats 2000000 namespace Reference.LexTensorExecution attribute [local instance] Classical.propDecidable open Reference.RealSVDPackage Reference.RealOptimalityEquality open scoped Matrix end Reference.LexTensorExecution set_option maxHeartbeats 2000000 set_option backward.isDefEq.respectTransparency false namespace Reference.LexTensorExecution attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.LexOrderedCyclicBoundary end Reference.LexTensorExecution set_option maxHeartbeats 2000000 set_option backward.isDefEq.respectTransparency false namespace Reference.LexTensorArithmeticExecution open Reference.RealSVDPackage Reference.LexTensorCompletion Reference.LexOrderedCyclicBoundary Reference.TensorCandidateSelection open scoped BigOperators Matrix
def rowErrorRun:(n:ℕ) → (Fin n → ℝ) → (Fin n → ℝ) → Run ℝ
  | 0,_,_ => zeroReal
  | n+1,a,b => bindRun (readReal (a 0)) fun x =>
      bindRun (readReal (b 0)) fun y =>
      bindRun (subReal x y) fun z =>
      bindRun (mulReal z z) fun p =>
      bindRun (rowErrorRun n (fun i => a i.succ) (fun i => b i.succ)) fun q => addReal p q
def matrixErrorRun:(m n:ℕ) → Rect m n → Rect m n → Run ℝ
  | 0,_,_,_ => zeroReal
  | m+1,n,A,B => bindRun (rowErrorRun n (fun j => A 0 j) (fun j => B 0 j)) fun x =>
      bindRun (matrixErrorRun m n (fun i j => A i.succ j) (fun i j => B i.succ j)) fun y => addReal x y
def tensorErrorRun {m:ℕ} {ns:List ℕ} (A B:Tensor m ns):Run ℝ := matrixErrorRun m (Fintype.card (ModeIndex ns)) (denseTensor A) (denseTensor B)
end Reference.LexTensorArithmeticExecution set_option maxHeartbeats 2000000 namespace Reference.LexTensorArithmeticExecution open Reference.LexTensorCompletion Reference.TensorCandidateSelection
def minimumRun {m:ℕ} {ns:List ℕ} (A:Tensor m ns) (x:Tensor m ns):List (Tensor m ns) → Run (Tensor m ns)
  | [] => pureRun x
  | y::ys => bindRun (tensorErrorRun A y) fun ey =>
      bindRun (tensorErrorRun A x) fun ex =>
      bindRun (lessReal ey ex) fun better =>
      if better then minimumRun A y ys else minimumRun A x ys
end Reference.LexTensorArithmeticExecution set_option maxHeartbeats 2000000 set_option backward.isDefEq.respectTransparency false namespace Reference.LexTensorArithmeticExecution open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.LexTensorCompletion Reference.LexOrderedCyclicBoundary open scoped BigOperators Matrix
def copyMatrixRun {m n:ℕ} (A:Rect m n):Run (Rect m n) := vectorRun m fun i => vectorRun n fun j => readReal (A i j)
def tensorCopyRun {m:ℕ} {ns:List ℕ} (A:Tensor m ns):Run (Tensor m ns) := bindRun (copyMatrixRun (denseTensor A)) fun Z => pureRun (Z.submatrix id (concreteLayout ns))
def tensorMulRun {m k:ℕ} {ns:List ℕ} (V:Rect m k) (A:Tensor k ns):Run (Tensor m ns) := bindRun (matrixMulRun V (denseTensor A)) fun Z => pureRun (Z.submatrix id (concreteLayout ns))
def frameRun {m:ℕ} {ns:List ℕ} (A:Tensor m ns) (r:ℕ):Run (Rect m (min r m)) := bindRun (leftSubspace (denseTensor A)) fun V => copyMatrixRun (fun i j => V i ⟨j.val,j.isLt.trans_le (Nat.min_le_right r m)⟩)
end Reference.LexTensorArithmeticExecution set_option maxHeartbeats 2000000 set_option backward.isDefEq.respectTransparency false namespace Reference.LexTensorArithmeticExecution open Reference.RealSVDPackage Reference.LexTensorCompletion open scoped Matrix
def ttRun (m:ℕ) (ns:List ℕ) (A:Tensor m ns) (rs:List ℕ):Run (Tensor m ns) :=
  match ns,A,rs with
  | [],A,_ => pureRun A
  | _::_,A,[] => pureRun A
  | n::ns,A,r::rs =>
    bindRun (frameRun A r) fun U =>
    bindRun (tensorMulRun U.transpose A) fun C0 =>
    bindRun (tensorCopyRun (merge C0)) fun C =>
    bindRun (ttRun (rowCount (min r m) n) ns C rs) fun Z =>
    bindRun (tensorCopyRun (unmerge (m:=min r m) (n:=n) Z)) fun Z0 =>
    tensorMulRun U Z0
termination_by ns.length
def completionRun {m k n:ℕ} {ns:List ℕ} (A:Tensor m (n::ns)) (U:Rect m k) (rs:List ℕ):Run (Tensor m (n::ns)) := bindRun (tensorMulRun U.transpose A) fun C0 => bindRun (tensorCopyRun (merge C0)) fun C => bindRun (ttRun (rowCount k n) ns C rs) fun Z => bindRun (tensorCopyRun (unmerge (m:=k) (n:=n) Z)) fun Z0
  => tensorMulRun U Z0
end Reference.LexTensorArithmeticExecution set_option maxHeartbeats 4000000 set_option backward.isDefEq.respectTransparency false open Reference.RealSVDPackage Reference.LexTensorCompletion namespace Reference.LexTensorExecution open Reference.RealSVDPackage Reference.LexTensorCompletion
def cyclicExecutionRun {m n:ℕ} {ns:List ℕ} (A:Tensor m (n::ns)) (V:Square m) (sigma:Fin m → ℝ) (tau:ℝ) (s j:ℕ) (rs:List ℕ):Run (Tensor m (n::ns)) := bindRun (equalScanRun sigma tau) fun boundary => bindRun (windowScanRun sigma tau boundary s j) fun indices => bindRun (frameFromListRun V indices) fun U
  => liftRun (Reference.LexTensorArithmeticExecution.completionRun A U rs)
end Reference.LexTensorExecution set_option maxHeartbeats 4000000 set_option backward.isDefEq.respectTransparency false open Reference.RealSVDPackage Reference.LexTensorCompletion namespace Reference.LexTensorExecution open Reference.RealSVDPackage Reference.LexTensorCompletion
def listMapRun {α β:Type} (f:α → Run β):List α → Run (List β)
  | [] => pureRun []
  | x::xs => bindRun (f x) fun y => bindRun (listMapRun f xs) fun ys => pureRun (y::ys)
def prefixFrameRun {m:ℕ} (V:Square m) (k:ℕ):Run (Rect m (min k m)) := liftRun (Reference.LexTensorArithmeticExecution.vectorRun m fun i => Reference.LexTensorArithmeticExecution.vectorRun (min k m) fun j => Reference.LexTensorArithmeticExecution.readReal (V i ⟨j.val,lt_of_lt_of_le j.isLt (Nat.min_le_right k
  m)⟩))
def prefixCompletionRun {m n:ℕ} {ns:List ℕ} (A:Tensor m (n::ns)) (V:Square m) (k:ℕ) (rs:List ℕ):Run (Tensor m (n::ns)) := bindRun (prefixFrameRun V k) fun U => liftRun (Reference.LexTensorArithmeticExecution.completionRun A U rs)
def sigmaAtRun {m:ℕ} (sigma:Fin m → ℝ) (a:ℕ):Run ℝ :=
  let test := lessNatRun a m
  let control := branchRun test.value
  if h:control.value=true then
    let x := readRun (sigma ⟨a,of_decide_eq_true h⟩)
    ⟨x.value,test.trace++control.trace++x.trace⟩
  else
    let x := liftRun Reference.LexTensorArithmeticExecution.zeroReal
    ⟨x.value,test.trace++control.trace++x.trace⟩
def candidateDataRun {m n:ℕ} {ns:List ℕ} (A:Tensor m (n::ns)) (V:Square m) (sigma:Fin m → ℝ) (r:ℕ) (rs:List ℕ):Run (List (Tensor m (n::ns))) := bindRun (aboveScanRun sigma 0) fun positive => bindRun (lessNatRun r positive.length) fun greater => bindRun (branchRun greater) fun greater => if greater then
  bindRun (subNatRun r 1) fun a => bindRun (sigmaAtRun sigma a) fun tau => bindRun (aboveScanRun sigma tau) fun above => bindRun (equalScanRun sigma tau) fun boundary => bindRun (subNatRun r above.length) fun s => bindRun (lessNatRun 0 boundary.length) fun nonempty => bindRun (branchRun nonempty) fun nonempty => if
  nonempty then bindRun (equalNatRun s boundary.length) fun full => bindRun (branchRun full) fun full => if full then bindRun (cyclicExecutionRun A V sigma tau s 0 rs) fun X => pureRun [X] else listMapRun (fun j:Fin boundary.length => cyclicExecutionRun A V sigma tau s j.val rs) (List.finRange boundary.length) else
  bindRun (prefixCompletionRun A V r rs) fun X => pureRun [X] else bindRun (prefixCompletionRun A V positive.length rs) fun X => pureRun [X]
def candidatesExecutionRun {m n:ℕ} {ns:List ℕ} (A:Tensor m (n::ns)) (r:ℕ) (rs:List ℕ):Run (List (Tensor m (n::ns))) := bindRun (spectralRun (denseTensor A)) fun data => candidateDataRun A data.1 data.2 r rs
def solverExecutionRun {m n:ℕ} {ns:List ℕ} (A:Tensor m (n::ns)) (r:ℕ) (rs:List ℕ):Run (Tensor m (n::ns)) :=
  bindRun (candidatesExecutionRun A r rs) fun xs =>
  match xs with
  | [] => bindRun (spectralRun (denseTensor A)) fun data => prefixCompletionRun A data.1 r rs
  | x::ys => liftRun (Reference.LexTensorArithmeticExecution.minimumRun A x ys)
end Reference.LexTensorExecution end reset_proof_cache section namespace Reference.LexTensorExecution open Reference.LexTensorCompletion Reference.TensorOptimumAttainment
theorem actual_lexicographic_paper_algorithm {m n:ℕ} {ns:List ℕ} (A:Tensor m (n::ns)) (r:ℕ) (rs:List ℕ) (hlen:rs.length=ns.length) (hr:0<r) (hns:0<ns.length) (hm:1 ≤ m) (hmode:∀ a∈n::ns,2 ≤ a):Reference.RecursiveTensorCompletion.feasible m (n::ns) (solverExecutionRun A r rs).value (r::rs) ∧
  0<(candidatesExecutionRun A r rs).value.length ∧ (candidatesExecutionRun A r rs).value.length ≤ m ∧ (0<optimalError A (r::rs) → Reference.RecursiveTensorCompletion.tensorFrobeniusSq (A-(solverExecutionRun A r rs).value)<((n::ns).length:ℝ)*optimalError A (r::rs)) ∧ (optimalError A (r::rs)=0 → (solverExecutionRun A r
  rs).value=A) ∧ charge (solverExecutionRun A r rs) ≤ 1500*(m*(n::ns).prod)^5 := by sorry
end Reference.LexTensorExecution set_option maxHeartbeats 4000000 open Reference.LexTensorCompletion set_option maxHeartbeats 4000000 open Reference.RealSVDPackage Reference.LexTensorCompletion set_option maxHeartbeats 4000000 open Reference.RealSVDPackage Reference.LexTensorCompletion set_option maxHeartbeats 2000000 namespace Reference.LexTensorExecution attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality open scoped Matrix end Reference.LexTensorExecution set_option maxHeartbeats 2000000 namespace Reference.LexTensorExecution attribute [local instance] Classical.propDecidable open Reference.RealSVDPackage Reference.RealOptimalityEquality open scoped Matrix end Reference.LexTensorExecution open Reference.RealSVDPackage open Reference.RealSVDPackage set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false open Reference.RealSVDPackage Reference.LexTensorCompletion open scoped Matrix set_option maxHeartbeats 2000000 set_option backward.isDefEq.respectTransparency false open Reference.RealSVDPackage Reference.LexTensorCompletion open scoped Matrix set_option maxHeartbeats 2000000 open Reference.LexTensorCompletion Reference.TensorOptimumAttainment end
/- TR-27: Delayed tensor-power rank savings. -/ section attribute [-instance] CommCStarAlgebra.toNormedCommRing NonUnitalCStarAlgebra.toNormedSpace reset_proof_cache section open scoped BigOperators TensorProduct LinearAlgebra.Projectivization attribute [local instance] MvPolynomial.gradedAlgebra namespace NLA.TR27
structure ProjectiveVariety (W:Type*) [AddCommGroup W] [Module ℂ W] where
  dimension:ℕ
  coordinates:W ≃ₗ[ℂ] (Fin dimension → ℂ)
  ideal:Ideal (MvPolynomial (Fin dimension) ℂ)
namespace ProjectiveVariety variable {W:Type*} [AddCommGroup W] [Module ℂ W]
def cone (X:ProjectiveVariety W):Set W := X.coordinates ⁻¹' MvPolynomial.zeroLocus ℂ X.ideal
def points (X:ProjectiveVariety W):Set (ℙ ℂ W) := {p | p.rep ∈ X.cone}
def Admissible (X:ProjectiveVariety W):Prop := X.ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin X.dimension) ℂ) ∧ X.ideal.IsPrime ∧ IsReduced ((MvPolynomial (Fin X.dimension) ℂ) ⧸ X.ideal) ∧ (∃ v:W, v ∈ X.cone ∧ v ≠ 0) ∧ Submodule.span ℂ X.cone = ⊤
def zariskiClosure (X:ProjectiveVariety W) (Y:Set (ℙ ℂ W)):Set (ℙ ℂ W) := {p | ∀ (f:MvPolynomial (Fin X.dimension) ℂ) (d:ℕ), f.IsHomogeneous d → (∀ q ∈ Y, MvPolynomial.eval (X.coordinates q.rep) f = 0) → MvPolynomial.eval (X.coordinates p.rep) f = 0}
def IsClosed (X:ProjectiveVariety W) (Y:Set (ℙ ℂ W)):Prop := X.zariskiClosure Y = Y
def IsIrreducible (X:ProjectiveVariety W) (Y:Set (ℙ ℂ W)):Prop := Y.Nonempty ∧ ∀ A B:Set (ℙ ℂ W), X.IsClosed A → X.IsClosed B → Y ⊆ A ∪ B → Y ⊆ A ∨ Y ⊆ B
end ProjectiveVariety section RankDefinitions variable {W:Type*} [AddCommGroup W] [Module ℂ W]
def ProjectiveRankAtMost (X:Set (ℙ ℂ W)) (r:ℕ) (p:ℙ ℂ W):Prop := ∃ k:ℕ, k ≤ r ∧ ∃ q:Fin k → ℙ ℂ W, (∀ i, q i ∈ X) ∧ p ∈ Projectivization.Subspace.span (Set.range q)
def projectiveRank (X:Set (ℙ ℂ W)) (p:ℙ ℂ W):ℕ := sInf {r:ℕ | ProjectiveRankAtMost X r p}
def borderRank (X:ProjectiveVariety W) (p:ℙ ℂ W):ℕ := sInf {r:ℕ | p ∈ X.zariskiClosure {q | ProjectiveRankAtMost X.points r q}}
def Represents (v:W) (p:ℙ ℂ W):Prop := ∃ a:ℂ, a ≠ 0 ∧ p.rep = a • v
end RankDefinitions end NLA.TR27 end reset_proof_cache section open scoped LinearAlgebra.Projectivization namespace NLA.TR27.Paper
abbrev CurveSpace (D:ℕ) := Fin (D + 1) → ℂ
def curveVector (D:ℕ):Option ℂ → CurveSpace D
  | some t => fun j => t ^ (j:ℕ)
  | none => fun j => if (j:ℕ) = D then 1 else 0
def tangentVector (D:ℕ):CurveSpace D := fun j => if (j:ℕ) = 1 then 1 else 0
end NLA.TR27.Paper end reset_proof_cache section open scoped BigOperators LinearAlgebra.Projectivization namespace NLA.TR27.Paper
@[instance_reducible] def coordinateProjectiveTopology (n:ℕ):TopologicalSpace (ℙ ℂ (Fin n → ℂ)) := TopologicalSpace.coinduced (Projectivization.mk' ℂ) (inferInstance:TopologicalSpace {v:Fin n → ℂ // v ≠ 0})
end NLA.TR27.Paper end reset_proof_cache section open scoped LinearAlgebra.Projectivization namespace NLA.TR27.Paper
def projectiveCoordinateRatio {n:ℕ} (i j:Fin n) (p:ℙ ℂ (Fin n → ℂ)):ℂ := p.rep j / p.rep i
end NLA.TR27.Paper end reset_proof_cache section open scoped BigOperators LinearAlgebra.Projectivization namespace NLA.TR27.Paper
def projectionCenter (D r:ℕ) (a:Fin r → Option ℂ):CurveSpace D := tangentVector D - ∑ i, curveVector D (a i)
def centerLine (D r:ℕ) (a:Fin r → Option ℂ):Submodule ℂ (CurveSpace D) := Submodule.span ℂ {projectionCenter D r a}
abbrev QuotientSpace (D r:ℕ) (a:Fin r → Option ℂ) := CurveSpace D ⧸ centerLine D r a
def quotientProjection (D r:ℕ) (a:Fin r → Option ℂ):CurveSpace D →ₗ[ℂ] QuotientSpace D r a := (centerLine D r a).mkQ
def quotientCurve (D r:ℕ) (a:Fin r → Option ℂ) (t:Option ℂ):QuotientSpace D r a := quotientProjection D r a (curveVector D t)
def quotientTangent (D r:ℕ) (a:Fin r → Option ℂ):QuotientSpace D r a := quotientProjection D r a (tangentVector D)
def quotientPoints (D r:ℕ) (a:Fin r → Option ℂ):Set (ℙ ℂ (QuotientSpace D r a)) := {p | ∃ t:Option ℂ, Represents (quotientCurve D r a t) p}
def chosenParameters (r:ℕ):Fin r → Option ℂ := fun i => some (((i:ℕ) + 1:ℕ):ℂ)
def familyDegree (r m:ℕ):ℕ := r ^ m + r
end NLA.TR27.Paper end reset_proof_cache section open scoped BigOperators namespace NLA.TR27.Paper
def chosenPowerSum (r j:ℕ):ℂ := ∑ i:Fin r, ((i.val+1:ℕ):ℂ)^j
def chosenPivot (r:ℕ):ℂ := chosenPowerSum r 1 - 1
end NLA.TR27.Paper end reset_proof_cache section open scoped BigOperators LinearAlgebra.Projectivization namespace NLA.TR27.Paper
/-- The coordinate pivot index is in range. -/ theorem pivotIndex._proof_2 (D:ℕ):2 ≤ D → 1 < D+1 := (by sorry) cache_proof NLA.TR27.Paper.pivotIndex._proof_2
def pivotIndex (D:ℕ) (hD:2 ≤ D):Fin (D+1) := ⟨1, by omega⟩
def retainedIndex (D:ℕ) (hD:2 ≤ D):Fin D → Fin (D+1) := (pivotIndex D hD).succAbove
def coordinateProjection (D r:ℕ) (hD:2 ≤ D):CurveSpace D →ₗ[ℂ] (Fin D → ℂ) where
  toFun w j := chosenPivot r * w (retainedIndex D hD j) -
    chosenPowerSum r (retainedIndex D hD j).val * w (pivotIndex D hD)
  map_add' u v := by ext j; simp only [Pi.add_apply]; ring
  map_smul' c w := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
end NLA.TR27.Paper end reset_proof_cache section namespace NLA.TR27.Paper
abbrev ImageCoordinatePolynomial (D:ℕ) := MvPolynomial (Fin D) ℂ
abbrev CurveParameterPolynomial := MvPolynomial (Fin 2) ℂ
def imageHomogeneousCoordinate (D r:ℕ) (hD:2 ≤ D) (j:Fin D):CurveParameterPolynomial := MvPolynomial.C (chosenPivot r) * MvPolynomial.X 0 ^ (D-(retainedIndex D hD j).val) * MvPolynomial.X 1 ^ (retainedIndex D hD j).val - MvPolynomial.C (chosenPowerSum r (retainedIndex D hD j).val) * MvPolynomial.X 0 ^ (D-1) *
  MvPolynomial.X 1
def imageSubstitution (D r:ℕ) (hD:2 ≤ D):ImageCoordinatePolynomial D →ₐ[ℂ] CurveParameterPolynomial := MvPolynomial.aeval (imageHomogeneousCoordinate D r hD)
def imageHomogeneousMap (D r:ℕ) (hD:2 ≤ D) (u:Fin 2 → ℂ):Fin D → ℂ := fun j => MvPolynomial.eval u (imageHomogeneousCoordinate D r hD j)
def imageIdeal (D r:ℕ) (hD:2 ≤ D):Ideal (ImageCoordinatePolynomial D) := RingHom.ker (imageSubstitution D r hD)
end NLA.TR27.Paper end reset_proof_cache section open scoped LinearAlgebra.Projectivization namespace NLA.TR27.Paper attribute [local instance] coordinateProjectiveTopology
def coordinateImagePoints (D r:ℕ) (hD:2 ≤ D):Set (ℙ ℂ (Fin D → ℂ)) := {p | p.rep ∈ MvPolynomial.zeroLocus ℂ (imageIdeal D r hD)}
def HasProjectiveAnalyticGraph {n:ℕ} (X:Set (ℙ ℂ (Fin n → ℂ))) (p:ℙ ℂ (Fin n → ℂ)):Prop := ∃ i j:Fin n, i ≠ j ∧ p.rep i ≠ 0 ∧ ∃ V:Set ℂ, ∃ W:Set (ℙ ℂ (Fin n → ℂ)), ∃ H:ℂ → ℙ ℂ (Fin n → ℂ), IsOpen V ∧ projectiveCoordinateRatio i j p ∈ V ∧ IsOpen W ∧ p ∈ W ∧ X ∩ W = H '' V ∧ H (projectiveCoordinateRatio i
  j p) = p ∧ (∀ z ∈ V, (H z).rep i ≠ 0 ∧ projectiveCoordinateRatio i j (H z) = z) ∧ (∀ k, AnalyticOnNhd ℂ (fun z => projectiveCoordinateRatio i k (H z)) V)
end NLA.TR27.Paper end reset_proof_cache section open scoped BigOperators Classical LinearAlgebra.Projectivization namespace NLA.TR27.Paper
theorem coordinateProjection_surjective (D r:ℕ) (hD:2 ≤ D) (hr:3 ≤ r):Function.Surjective (coordinateProjection D r hD) := by sorry
theorem coordinateProjection_kernel (D r:ℕ) (hD:2 ≤ D) (hr:3 ≤ r):LinearMap.ker (coordinateProjection D r hD) = centerLine D r (chosenParameters r) := by sorry
noncomputable def quotientCoordinateEquiv (D r:ℕ) (hD:2 ≤ D) (hr:3 ≤ r):QuotientSpace D r (chosenParameters r) ≃ₗ[ℂ] (Fin D → ℂ) := (Submodule.quotEquivOfEq _ _ (coordinateProjection_kernel D r hD hr).symm).trans ((coordinateProjection D r hD).quotKerEquivOfSurjective (coordinateProjection_surjective D r hD
  hr))
end NLA.TR27.Paper end reset_proof_cache section open scoped BigOperators Classical namespace NLA.TR27.Paper attribute [local instance] MvPolynomial.gradedAlgebra
theorem imageHomogeneousMap_eq_zero_iff (D r:ℕ) (hD:2 ≤ D) (hr:3 ≤ r) (u:Fin 2 → ℂ):imageHomogeneousMap D r hD u = 0 ↔ u = 0 := by sorry
end NLA.TR27.Paper end reset_proof_cache section open scoped LinearAlgebra.Projectivization namespace NLA.TR27.Paper
def projectiveCurveMap (D r:ℕ) (hD:2 ≤ D) (hr:3 ≤ r) (p:ℙ ℂ (Fin 2 → ℂ)):ℙ ℂ (Fin D → ℂ) := Projectivization.mk ℂ (imageHomogeneousMap D r hD p.rep) (fun h => p.rep_nonzero ((imageHomogeneousMap_eq_zero_iff D r hD hr p.rep).mp h))
end NLA.TR27.Paper end reset_proof_cache section namespace NLA.TR27.Paper
def recoveryMomentA (r:ℕ):ℂ := chosenPowerSum r 3 * chosenPowerSum r 5 - chosenPowerSum r 4 ^ 2
def recoveryMomentB (r:ℕ):ℂ := chosenPowerSum r 3 * chosenPowerSum r 4 - chosenPowerSum r 2 * chosenPowerSum r 5
def recoveryMomentC (r:ℕ):ℂ := chosenPowerSum r 2 * chosenPowerSum r 4 - chosenPowerSum r 3 ^ 2
/-- Recovery coordinates are in range. -/ theorem recoveryIndex._proof_2 (D:ℕ):5 ≤ D → ∀ j:Fin 4, j.val+1 < D := (by sorry) cache_proof NLA.TR27.Paper.recoveryIndex._proof_2
def recoveryIndex (D:ℕ) (hD:5 ≤ D) (j:Fin 4):Fin D := ⟨j.val+1, by omega⟩
def recoveryDenominator (D r:ℕ) (hD:5 ≤ D):ImageCoordinatePolynomial D := MvPolynomial.C (recoveryMomentA r) * MvPolynomial.X (recoveryIndex D hD 0) + MvPolynomial.C (recoveryMomentB r) * MvPolynomial.X (recoveryIndex D hD 1) + MvPolynomial.C (recoveryMomentC r) * MvPolynomial.X (recoveryIndex D hD 2)
def recoveryNumerator (D r:ℕ) (hD:5 ≤ D):ImageCoordinatePolynomial D := MvPolynomial.C (recoveryMomentA r) * MvPolynomial.X (recoveryIndex D hD 1) + MvPolynomial.C (recoveryMomentB r) * MvPolynomial.X (recoveryIndex D hD 2) + MvPolynomial.C (recoveryMomentC r) * MvPolynomial.X (recoveryIndex D hD 3)
def recoveryPolynomial (r:ℕ):Polynomial ℂ := Polynomial.C (chosenPivot r) * Polynomial.X^2 * (Polynomial.C (recoveryMomentA r) + Polynomial.C (recoveryMomentB r)*Polynomial.X + Polynomial.C (recoveryMomentC r)*Polynomial.X^2)
def rationalRecovery (D r:ℕ) (hD:5 ≤ D) (w:Fin D → ℂ):ℂ := MvPolynomial.eval w (recoveryNumerator D r hD) / MvPolynomial.eval w (recoveryDenominator D r hD)
end NLA.TR27.Paper end reset_proof_cache section open scoped LinearAlgebra.Projectivization namespace NLA.TR27.Paper
/-- The recovery dimension permits coordinate pivots. -/ theorem recoveryOpenPoints._proof_2 (D r:ℕ):5 ≤ D → 2 ≤ D := (by sorry) cache_proof NLA.TR27.Paper.recoveryOpenPoints._proof_2
def recoveryOpenPoints (D r:ℕ) (hD:5 ≤ D) (hr:3 ≤ r):Set (ℙ ℂ (QuotientSpace D r (chosenParameters r))) :=
  {p | p ∈ quotientPoints D r (chosenParameters r) ∧
    MvPolynomial.eval (quotientCoordinateEquiv D r (by omega) hr p.rep)
      (recoveryDenominator D r hD) ≠ 0}
end NLA.TR27.Paper end reset_proof_cache section open scoped BigOperators TensorProduct LinearAlgebra.Projectivization namespace NLA.TR27.Paper variable {W:Type*} [AddCommGroup W] [Module ℂ W]
theorem tensor_reps_nonzero (k:ℕ) (q:Fin k → ℙ ℂ W):PiTensorProduct.tprod ℂ (fun i => (q i).rep) ≠ 0 := by sorry
def tensorPoint (k:ℕ) (q:Fin k → ℙ ℂ W):ℙ ℂ (⨂[ℂ] _:Fin k, W) := Projectivization.mk ℂ (PiTensorProduct.tprod ℂ (fun i => (q i).rep)) (tensor_reps_nonzero k q)
def powerPoint (p:ℙ ℂ W) (k:ℕ):ℙ ℂ (⨂[ℂ] _:Fin k, W) := tensorPoint k (fun _ => p)
def productPoints (X:Set (ℙ ℂ W)) (k:ℕ):Set (ℙ ℂ (⨂[ℂ] _:Fin k, W)) := {z | ∃ q:Fin k → ℙ ℂ W, (∀ i, q i ∈ X) ∧ Represents (PiTensorProduct.tprod ℂ (fun i => (q i).rep)) z}
end NLA.TR27.Paper end reset_proof_cache section open scoped LinearAlgebra.Projectivization namespace NLA.TR27.Paper attribute [local instance] coordinateProjectiveTopology
theorem paper_full_family (r m:ℕ) (hr:3 ≤ r) (hm:2 ≤ m) :
    ∃ hD:2 ≤ familyDegree r m, ∃ h5:5 ≤ familyDegree r m,
      let D := familyDegree r m
      let E := quotientCoordinateEquiv D r hD hr
      let X := ProjectiveVariety.mk D E (imageIdeal D r hD)
      (∀ w, E (quotientProjection D r (chosenParameters r) w) = coordinateProjection D r hD w) ∧
      X.Admissible ∧ X.IsClosed X.points ∧ X.IsIrreducible X.points ∧
      X.points = quotientPoints D r (chosenParameters r) ∧
      Set.range (projectiveCurveMap D r hD hr) = coordinateImagePoints D r hD ∧
      (∀ p ∈ coordinateImagePoints D r hD, HasProjectiveAnalyticGraph (coordinateImagePoints D r hD) p) ∧
      Topology.IsClosedEmbedding (projectiveCurveMap D r hD hr) ∧
      recoveryPolynomial r ≠ 0 ∧
      Set.Finite {t:ℂ | Polynomial.eval t (recoveryPolynomial r) = 0} ∧
      (recoveryOpenPoints D r h5 hr).Nonempty ∧
      X.IsClosed {p | MvPolynomial.eval (E p.rep) (recoveryDenominator D r h5) = 0} ∧
      X.zariskiClosure (recoveryOpenPoints D r h5 hr) = X.points ∧
      (∃ e:{t:ℂ // Polynomial.eval t (recoveryPolynomial r) ≠ 0} ≃
          {p // p ∈ recoveryOpenPoints D r h5 hr},
        (∀ t, Represents (quotientCurve D r (chosenParameters r) (some t.val)) (e t).val) ∧
        (∀ p, (e.symm p).val = rationalRecovery D r h5 (E p.val.rep))) ∧
      (∃ hv:quotientTangent D r (chosenParameters r) ≠ 0,
        borderRank X (Projectivization.mk ℂ _ hv) = 2 ∧
        projectiveRank X.points (Projectivization.mk ℂ _ hv) = r ∧
        ∀ k:ℕ, 1 ≤ k → k ≤ m →
          projectiveRank (productPoints X.points k) (powerPoint (Projectivization.mk ℂ _ hv) k) = r^k) := by sorry
end NLA.TR27.Paper end end
/- IS-03: Differentiation and nonnegative spectral realizability. -/ reset_proof_cache section set_option autoImplicit true open Matrix Polynomial open scoped Matrix namespace NLA.IS03
abbrev RealMatrix (n:ℕ) := Matrix (Fin n) (Fin n) ℝ
def EntrywiseNonnegative {n:ℕ} (A:RealMatrix n):Prop := ∀ i j, 0 ≤ A i j
def normalizedDerivative (n:ℕ) (p:ℝ[X]):ℝ[X] := ((n:ℝ)⁻¹) • p.derivative
def witnessMatrix:RealMatrix 7 := !![1/2, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 0]
end NLA.IS03 end reset_proof_cache section set_option autoImplicit true namespace NLA.IS03
theorem paper_counterexample:EntrywiseNonnegative witnessMatrix ∧ ∀ (r:ℕ) (B:RealMatrix (6 + r)), EntrywiseNonnegative B → B.charpoly ≠ Polynomial.X ^ r * normalizedDerivative 7 witnessMatrix.charpoly := by sorry
end NLA.IS03 end
/- NM-04: The rectangular Rowland–Wu identity. -/ reset_proof_cache section namespace NLA.NM04 open scoped BigOperators Matrix attribute [local instance] Classical.propDecidable universe u v w variable {α:Type u} {β:Type v} {𝕜:Type w}
abbrev MinorIndex (α:Type u) (β:Type v) := {RC:Finset α × Finset β // RC.1.card = RC.2.card}
def position [LinearOrder α] (s:α) (U:Finset α):ℕ := (U.filter (fun t => t < s)).card + 1
def minorMatrix [LinearOrder α] [LinearOrder β] (T:Matrix α β 𝕜) (I:MinorIndex α β):Matrix (Fin I.1.1.card) (Fin I.1.1.card) 𝕜 := fun i j => T (I.1.1.orderEmbOfFin rfl i) (I.1.2.orderEmbOfFin I.property.symm j)
def minor [LinearOrder α] [LinearOrder β] [CommRing 𝕜] (T:Matrix α β 𝕜) (I:MinorIndex α β):𝕜 := (minorMatrix T I).det
def RaisingSupport [DecidableEq α] [DecidableEq β] (I J:MinorIndex α β) (s:α) (t:β):Prop := I.1.1 \ J.1.1 = ∅ ∧ J.1.1 \ I.1.1 = {s} ∧ I.1.2 \ J.1.2 = ∅ ∧ J.1.2 \ I.1.2 = {t}
def LoweringSupport [DecidableEq α] [DecidableEq β] (I J:MinorIndex α β) (s:α) (t:β):Prop := I.1.1 \ J.1.1 = {s} ∧ J.1.1 \ I.1.1 = ∅ ∧ I.1.2 \ J.1.2 = {t} ∧ J.1.2 \ I.1.2 = ∅
def ColumnExchangeSupport [DecidableEq α] [DecidableEq β] (I J:MinorIndex α β) (s t:β):Prop := I.1.1 \ J.1.1 = ∅ ∧ J.1.1 \ I.1.1 = ∅ ∧ I.1.2 \ J.1.2 = {s} ∧ J.1.2 \ I.1.2 = {t}
def RowExchangeSupport [DecidableEq α] [DecidableEq β] (I J:MinorIndex α β) (s t:α):Prop := I.1.1 \ J.1.1 = {s} ∧ J.1.1 \ I.1.1 = {t} ∧ I.1.2 \ J.1.2 = ∅ ∧ J.1.2 \ I.1.2 = ∅
def raisingCoefficient [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β] (I J:MinorIndex α β):ℤ := ∑ s:α, ∑ t:β, if RaisingSupport I J s t then (-1) ^ (position s J.1.1 + position t J.1.2) else 0
def loweringCoefficient [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β] (I J:MinorIndex α β):ℤ := ∑ s:α, ∑ t:β, if LoweringSupport I J s t then (-1) ^ (position s I.1.1 + position t I.1.2) else 0
def columnExchangeCoefficient [Fintype β] [DecidableEq α] [LinearOrder β] (I J:MinorIndex α β):ℤ := ∑ s:β, ∑ t:β, if ColumnExchangeSupport I J s t then (-1) ^ (position s I.1.2 + position t J.1.2) else 0
def rowExchangeCoefficient [Fintype α] [LinearOrder α] [DecidableEq β] (I J:MinorIndex α β):ℤ := ∑ s:α, ∑ t:α, if RowExchangeSupport I J s t then (-1) ^ (position s I.1.1 + position t J.1.1) else 0
abbrev Rect (m n:ℕ) := Matrix (Fin m) (Fin n) ℝ
abbrev Tail (m:ℕ) := {i:Fin m // 0 < i.val}
abbrev Index (m n:ℕ) := MinorIndex (Tail m) (Tail n)
def firstIndex {m:ℕ} (hm:1 ≤ m):Fin m := ⟨0, hm⟩
def tailMatrix {m n:ℕ} (A:Rect m n):Matrix (Tail m) (Tail n) ℝ := fun i j => A i.val j.val
def delta {m n:ℕ} (A:Rect m n) (hm:1 ≤ m) (hn:1 ≤ n) (I:Index m n):ℝ := Matrix.det (A.submatrix (Fin.cons (firstIndex hm) (fun i => (I.1.1.orderEmbOfFin rfl i).val)) (Fin.cons (firstIndex hn) (fun j => (I.1.2.orderEmbOfFin I.property.symm j).val)))
def gamma {m n:ℕ} (A:Rect m n) (hm:1 ≤ m) (hn:1 ≤ n) (I:Index m n):ℝ := A (firstIndex hm) (firstIndex hn) * minor (tailMatrix A) I
def H (m n:ℕ):Matrix (Index m n) (Index m n) ℤ := fun I J => if I = J then (I.1.1.card:ℤ) * ((m:ℤ) + (n:ℤ)) - (m:ℤ) * (n:ℤ) else (m:ℤ) * raisingCoefficient I J - (n:ℤ) * loweringCoefficient I J + (m:ℤ) * columnExchangeCoefficient I J + (n:ℤ) * rowExchangeCoefficient I J
def HReal (m n:ℕ):Matrix (Index m n) (Index m n) ℝ := fun I J => (H m n I J:ℝ)
def Positive {m n:ℕ} (A:Rect m n):Prop := ∀ i j, 0 < A i j
def Balanced {m n:ℕ} (S:Rect m n):Prop := (∀ i, ∑ j, S i j = 1) ∧ (∀ j, ∑ i, S i j = (m:ℝ) / (n:ℝ))
def diagonalScale {m n:ℕ} (A:Rect m n) (a:Fin m → ℝ) (b:Fin n → ℝ):Rect m n := fun i j => a i * A i j * b j
def ScaledBalanced {m n:ℕ} (A S:Rect m n):Prop := ∃ (a:Fin m → ℝ) (b:Fin n → ℝ), (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧ S = diagonalScale A a b ∧ Balanced S
def sinkhorn {m n:ℕ} (A:Rect m n):Rect m n := if h:∃ S, ScaledBalanced A S then Classical.choose h else 0
end NLA.NM04 end reset_proof_cache section open scoped BigOperators namespace NLA.NM04.Paper universe u v attribute [local instance] Classical.propDecidable attribute [local instance] ContinuousMul.to_continuousSMul attribute [-instance] IsModuleTopology.toContinuousSMul
theorem paper_rowland_wu_identity {m n:ℕ} (hm:1 ≤ m) (hn:1 ≤ n) (A:Rect m n) (hA:Positive A):(∑ E:Finset (Index m n), ((m:ℝ)⁻¹ • (HReal m n).submatrix (Subtype.val:E → Index m n) (Subtype.val:E → Index m n)).det * (∏ I ∈ E, delta A hm hn I) * (∏ I ∈ (Finset.univ \ E), gamma A hm hn I) * ((sinkhorn
  A) (firstIndex hm) (firstIndex hn)) ^ E.card) = 0 := by sorry
end NLA.NM04.Paper end
/- PF-02: Disconnected minimal PSD factorization spaces. -/ reset_proof_cache section set_option autoImplicit true open Matrix namespace NLA.PF02
abbrev Mat (m n:ℕ) := Matrix (Fin m) (Fin n) ℝ
abbrev FactorTuple (p q k:ℕ) := (Fin p → Mat k k) × (Fin q → Mat k k)
def IsFactorization {p q k:ℕ} (M:Mat p q) (F:FactorTuple p q k):Prop := (∀ i, (F.1 i).PosSemidef) ∧ (∀ j, (F.2 j).PosSemidef) ∧ ∀ i j, Matrix.trace (F.1 i * F.2 j) = M i j
abbrev Factorization {p q:ℕ} (M:Mat p q) (k:ℕ) := {F:FactorTuple p q k // IsFactorization M F}
def IsPSDRank {p q:ℕ} (M:Mat p q) (k:ℕ):Prop := IsLeast {ℓ:ℕ | 1 ≤ ℓ ∧ Nonempty (Factorization M ℓ)} k
def Congruent {p q k:ℕ} {M:Mat p q} (F G:Factorization M k):Prop := ∃ S:(Mat k k)ˣ, (∀ i, G.val.1 i = (↑S:Mat k k).transpose * F.val.1 i * ↑S) ∧ (∀ j, G.val.2 j = (↑(S⁻¹):Mat k k) * F.val.2 j * (↑(S⁻¹):Mat k k).transpose)
abbrev OrbitSpace {p q:ℕ} (M:Mat p q) (k:ℕ) := Quot (@Congruent p q k M)
end NLA.PF02 end reset_proof_cache section namespace Reference.PF02UniformPositiveOrientation open Matrix
theorem paper_all_size_disconnected_witness {k:ℕ} (hk:3 ≤ k):(∃ (N:ℕ) (M:Matrix (Fin N) (Fin N) ℤ), N = k*(k+1)/2 ∧ (∀ i j, 0 ≤ M i j) ∧ (M.map (Int.castRingHom ℝ)).rank = N ∧ NLA.PF02.IsPSDRank (M.map (Int.castRingHom ℝ)) k ∧ ¬ IsConnected (Set.univ:Set (NLA.PF02.OrbitSpace (M.map (Int.castRingHom ℝ)) k)))
  ∧ (∃ (N:ℕ) (M:Matrix (Fin N) (Fin N) ℚ), N = k*(k+1)/2 ∧ (∀ i j, 0 < M i j) ∧ (M.map (Rat.castHom ℝ)).rank = N ∧ NLA.PF02.IsPSDRank (M.map (Rat.castHom ℝ)) k ∧ ¬ IsConnected (Set.univ:Set (NLA.PF02.OrbitSpace (M.map (Rat.castHom ℝ)) k))) := by sorry
end Reference.PF02UniformPositiveOrientation end
/- MD-06: Stable nonsynchronous equilibria on random cubic graphs. -/ reset_proof_cache section namespace Reference.MD06Actual open scoped BigOperators
abbrev Phase (n:ℕ) := Fin n → Real.Angle
def Energy {n:ℕ} (G:SimpleGraph (Fin n)) (theta:Phase n):ℝ := by
  classical
  exact ∑ i, ∑ j, if i < j ∧ G.Adj i j then 1 - Real.Angle.cos (theta i - theta j) else 0
def Synchronized {n:ℕ} (theta:Phase n):Prop := ∀ i j, theta i = theta j
def Gradient {n:ℕ} (G:SimpleGraph (Fin n)) (theta:Phase n) (i:Fin n):ℝ := by
  classical
  exact ∑ j, if G.Adj i j then Real.Angle.sin (theta i - theta j) else 0
def HessianQuadratic {n:ℕ} (G:SimpleGraph (Fin n)) (theta:Phase n) (z:Fin n → ℝ):ℝ := by
  classical
  exact ∑ i, ∑ j, if i < j ∧ G.Adj i j then Real.Angle.cos (theta i - theta j) * (z i - z j)^2 else 0
end Reference.MD06Actual end reset_proof_cache section namespace Reference.MD06FiniteProbability open scoped BigOperators open SimpleGraph attribute [local instance] Classical.propDecidable
abbrev Size (k:ℕ):ℕ := 2*(k+2)
abbrev CubicSample (k:ℕ) := {G:SimpleGraph (Fin (Size k)) // G.IsRegularOfDegree 3}
noncomputable instance sampleFintype (k:ℕ):Fintype (CubicSample k) := Fintype.ofFinite _
end Reference.MD06FiniteProbability end reset_proof_cache section namespace Reference.MD06FiniteProbability open SimpleGraph open scoped ENNReal attribute [local instance] Classical.propDecidable
theorem actual_cubic_sample_nonempty (k:ℕ):Nonempty (CubicSample k) := by sorry
noncomputable instance sampleNonempty (k:ℕ):Nonempty (CubicSample k) := actual_cubic_sample_nonempty k
noncomputable def UniformCubic (k:ℕ):PMF (CubicSample k) :=
  PMF.ofFintype (fun _ => (Fintype.card (CubicSample k):ENNReal)⁻¹) (by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel
      (by exact_mod_cast (Fintype.card_ne_zero:Fintype.card (CubicSample k) ≠ 0))
      (by simp))
end Reference.MD06FiniteProbability end reset_proof_cache section namespace Reference.MD06MainAssembly.Interface open Reference.MD06MainAssembly Reference.MD06Actual open Reference.MD06FiniteProbability open Filter Topology open scoped BigOperators attribute [local instance] Classical.propDecidable
theorem actual_paper_md_main:(Tendsto (fun k=>((UniformCubic k).toOuterMeasure {G:CubicSample k| ∀ theta:Phase (Size k),IsLocalMin (Energy G.val) theta → Synchronized theta}).toReal) atTop (𝓝 0)) ∧ Tendsto (fun k=>((UniformCubic k).toOuterMeasure {G:CubicSample k| ∃ theta:Phase (Size k), (∀ i,Gradient G.val
  theta i=0) ∧ IsLocalMin (Energy G.val) theta ∧ ¬Synchronized theta ∧ (∀ i j,G.val.Adj i j → (1/32:ℝ)<Real.Angle.cos (theta i-theta j)) ∧ ∀ z:Fin (Size k)→ℝ,(∑ i,z i)=0 → (1/320:ℝ)*(∑ i,(z i)^2) ≤ HessianQuadratic G.val theta z}).toReal) atTop (𝓝 1) := by sorry
end Reference.MD06MainAssembly.Interface end
/- IV-04: Hardness of interval determinant ranges and solution hulls. -/ reset_proof_cache section set_option autoImplicit true namespace Complexity
def delimit (x:List Bool):List Bool := (x.flatMap fun b => [b, b]) ++ [false, true]
end Complexity end reset_proof_cache section set_option autoImplicit true namespace Complexity
def pair (x y:List Bool):List Bool := delimit x ++ y
end Complexity end reset_proof_cache section namespace IV04.Paper.Computational
def firstBit (bits:List Bool):Bool := bits.headD false
end IV04.Paper.Computational end reset_proof_cache section namespace IV04.Paper
abbrev Mat (n:ℕ) := Matrix (Fin n) (Fin n) ℝ
end IV04.Paper end reset_proof_cache section namespace IV04.Paper
def naturalCode (n:ℕ):List Bool := List.replicate n.bits.length true ++ [false] ++ n.bits
def readUnary:List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0,rest)
  | true :: rest => do
      let (n,tail) ← readUnary rest
      return (n+1,tail)
def readNatural (bits:List Bool):Option (ℕ × List Bool) := do
  let (n,tail) ← readUnary bits
  if n ≤ tail.length then
    return ((tail.take n).foldr Nat.bit 0,tail.drop n)
  else none
def rationalCode (q:ℚ):List Bool := decide (q.num < 0) :: (naturalCode q.num.natAbs ++ naturalCode q.den)
def readRational:List Bool → Option (ℚ × List Bool)
  | [] => none
  | sign :: rest => do
      let (num,tail) ← readNatural rest
      let (den,last) ← readNatural tail
      let signed:ℤ := if sign then -(num:ℤ) else (num:ℤ)
      return ((signed:ℚ)/(den:ℚ),last)
end IV04.Paper end reset_proof_cache section set_option autoImplicit true namespace Complexity
inductive Γ where
  | zero | one | blank | start
  deriving Repr, DecidableEq
instance:Fintype Γ where
  elems := {.zero, .one, .blank, .start}
  complete := fun x => by cases x <;> simp
instance:Inhabited Γ := ⟨Γ.blank⟩
inductive Γw where
  | zero | one | blank
  deriving Repr, DecidableEq
instance:Fintype Γw where
  elems := {.zero, .one, .blank}
  complete := fun x => by cases x <;> simp
@[simp] def Γw.toΓ:Γw → Γ
  | .zero => .zero
  | .one => .one
  | .blank => .blank
instance:Coe Γw Γ where coe := Γw.toΓ
def Γ.ofBool:Bool → Γ
  | false => .zero
  | true => .one
inductive Dir3 where
  | left | right | stay
  deriving Repr, DecidableEq
instance:Fintype Dir3 where
  elems := {.left, .right, .stay}
  complete := fun x => by cases x <;> simp
@[ext] structure Tape where
  head:ℕ
  cells:ℕ → Γ
namespace Tape
def read (t:Tape):Γ := t.cells t.head
def write (t:Tape) (s:Γ):Tape :=
  if t.head = 0 then t
  else { t with cells := Function.update t.cells t.head s }
def move (t:Tape) (d:Dir3):Tape :=
  match d with
  | .left => { t with head := t.head - 1 }
  | .right => { t with head := t.head + 1 }
  | .stay => t
def HasOutput (t:Tape) (y:List Bool):Prop := (∀ (i:ℕ) (h:i < y.length), t.cells (i + 1) = Γ.ofBool (y[i]'h)) ∧ t.cells (y.length + 1) = Γ.blank
instance decidableHasOutput (t:Tape) (y:List Bool):Decidable (t.HasOutput y) := if h:(∀ i:Fin y.length, t.cells (i.val + 1) = Γ.ofBool (y[i.val]'i.isLt)) ∧ t.cells (y.length + 1) = Γ.blank then isTrue ⟨fun i hi => h.1 ⟨i, hi⟩, h.2⟩ else isFalse (fun ⟨h1, h2⟩ => h ⟨fun i => h1 i.val i.isLt, h2⟩)
abbrev writeAndMove (t:Tape) (s:Γ) (d:Dir3):Tape := (t.write s).move d
end Tape
def Tape.init (contents:List Γ):Tape where
  head := 0
  cells := fun i =>
    if i = 0 then Γ.start
    else (contents[i - 1]?).getD Γ.blank
abbrev Language := Set (List Bool)
structure Cfg (n:ℕ) (Q:Type) where
  state:Q
  input:Tape
  work:Fin n → Tape
  output:Tape
namespace Cfg
abbrev init (qstart:Q) (x:List Bool):Cfg n Q :=
  { state := qstart
    input := Tape.init (x.map Γ.ofBool)
    work := fun _ => Tape.init []
    output := Tape.init [] }
abbrev isHalted (qhalt:Q) (c:Cfg n Q):Prop := c.state = qhalt
end Cfg
structure TM (n:ℕ) where
  Q:Type
  [decEq:DecidableEq Q]
  [finQ:Fintype Q]
  qstart:Q
  qhalt:Q
  δ:Q → Γ → (Fin n → Γ) → Γ →
      Q × (Fin n → Γw) × Γw × Dir3 × (Fin n → Dir3) × Dir3
  δ_right_of_start:∀ (q:Q) (iHead:Γ) (wHeads:Fin n → Γ) (oHead:Γ),
    let (_, _, _, inDir, workDirs, outDir) := δ q iHead wHeads oHead
    (iHead = Γ.start → inDir = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → workDirs i = Dir3.right) ∧
    (oHead = Γ.start → outDir = Dir3.right)
attribute [instance] TM.decEq TM.finQ
structure NTM (n:ℕ) where
  Q:Type
  [decEq:DecidableEq Q]
  [finQ:Fintype Q]
  qstart:Q
  qhalt:Q
  δ:Bool → Q → Γ → (Fin n → Γ) → Γ →
      Q × (Fin n → Γw) × Γw × Dir3 × (Fin n → Dir3) × Dir3
  δ_right_of_start:∀ (b:Bool) (q:Q) (iHead:Γ) (wHeads:Fin n → Γ) (oHead:Γ),
    let (_, _, _, inDir, workDirs, outDir) := δ b q iHead wHeads oHead
    (iHead = Γ.start → inDir = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → workDirs i = Dir3.right) ∧
    (oHead = Γ.start → outDir = Dir3.right)
attribute [instance] NTM.decEq NTM.finQ namespace TM variable {n:ℕ}
def step (tm:TM n) (c:Cfg n tm.Q):Option (Cfg n tm.Q) :=
  if c.state = tm.qhalt then none
  else
    let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
      tm.δ c.state c.input.read (fun i => (c.work i).read) c.output.read
    some
      { state := q'
        input := c.input.move inDir
        work := fun i => (c.work i).writeAndMove (workWrites i) (workDirs i)
        output := c.output.writeAndMove outWrite outDir }
abbrev initCfg (tm:TM n) (x:List Bool):Cfg n tm.Q := Cfg.init tm.qstart x
abbrev halted (tm:TM n) (c:Cfg n tm.Q):Prop := Cfg.isHalted tm.qhalt c
inductive reachesIn (tm:TM n):ℕ → Cfg n tm.Q → Cfg n tm.Q → Prop where
  | zero:reachesIn tm 0 c c
  | step:tm.step c = some c'' → reachesIn tm t c'' c' → reachesIn tm (t + 1) c c'
def ComputesInTime (tm:TM n) (f:List Bool → List Bool) (T:ℕ → ℕ):Prop := ∀ x, ∃ c' t, t ≤ T x.length ∧ tm.reachesIn t (tm.initCfg x) c' ∧ tm.halted c' ∧ c'.output.HasOutput (f x)
end TM namespace NTM variable {n:ℕ}
/-- The next trace index stays in the enlarged time interval. -/ theorem trace._proof_6 (T:ℕ) (i:Fin T):i.val+1 < T+1 := (by sorry) cache_proof Complexity.NTM.trace._proof_6
def trace (tm:NTM n):(T:ℕ) → (Fin T → Bool) → Cfg n tm.Q → Cfg n tm.Q
  | 0, _, c => c
  | T + 1, choices, c =>
    if c.state = tm.qhalt then c
    else
      let b := choices ⟨0, Nat.zero_lt_succ T⟩
      let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
        tm.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read
      let c':Cfg n tm.Q :=
        { state := q'
          input := c.input.move inDir
          work := fun i => (c.work i).writeAndMove (workWrites i) (workDirs i)
          output := c.output.writeAndMove outWrite outDir }
      tm.trace T (fun i => choices ⟨i.val + 1, by omega⟩) c'
abbrev initCfg (tm:NTM n) (x:List Bool):Cfg n tm.Q := Cfg.init tm.qstart x
abbrev halted (tm:NTM n) (c:Cfg n tm.Q):Prop := Cfg.isHalted tm.qhalt c
def AcceptsInTime (tm:NTM n) (x:List Bool) (T:ℕ):Prop :=
  ∃ choices:Fin T → Bool,
    let c' := tm.trace T choices (tm.initCfg x)
    tm.halted c' ∧ c'.output.cells 1 = Γ.one
def AllPathsHaltIn (tm:NTM n) (T:ℕ → ℕ):Prop := ∀ x (choices:Fin (T x.length) → Bool), tm.halted (tm.trace (T x.length) choices (tm.initCfg x))
def DecidesInTime (tm:NTM n) (L:Language) (T:ℕ → ℕ):Prop := tm.AllPathsHaltIn T ∧ (∀ x, x ∈ L ↔ tm.AcceptsInTime x (T x.length))
end NTM end Complexity end reset_proof_cache section set_option autoImplicit true open Asymptotics Filter namespace Complexity
def BigO (f g:ℕ → ℕ):Prop := (fun n => (f n:ℝ)) =O[atTop] (fun n => (g n:ℝ))
@[inherit_doc BigO]
scoped infixl:50 " =O " => BigO
end Complexity end reset_proof_cache section set_option autoImplicit true namespace Complexity
def NTIME (T:ℕ → ℕ):Set Language := {L | ∃ (k:ℕ) (tm:NTM k) (f:ℕ → ℕ), tm.DecidesInTime L f ∧ f =O T}
end Complexity end reset_proof_cache section set_option autoImplicit true namespace Complexity
def NP:Set Language := ⋃ k:ℕ, NTIME (· ^ k)
end Complexity end reset_proof_cache section set_option autoImplicit true namespace Complexity
def FP:Set (List Bool → List Bool) := {f | ∃ (d k:ℕ) (tm:TM k) (T:ℕ → ℕ), tm.ComputesInTime f T ∧ T =O (· ^ d)}
end Complexity end reset_proof_cache section namespace IV04.Paper.Computational
def readRationals:ℕ → List Bool → Option (List ℚ × List Bool)
  | 0, input => some ([],input)
  | count+1, input => do
      let (value,tail) ← IV04.Paper.readRational input
      let (values,last) ← readRationals count tail
      return (value :: values,last)
end IV04.Paper.Computational end reset_proof_cache section namespace IV04.Paper.Computational
def readMatrixRationals (input:List Bool):Option (ℕ × List ℚ × List Bool) := do
  let (n,rest) ← IV04.Paper.readNatural input
  let (values,tail) ← readRationals (2*n*n+1) rest
  return (n,values,tail)
end IV04.Paper.Computational end reset_proof_cache section namespace IV04.Paper.Computational
def rationalDenseEndpointAll (n:ℕ):ℕ → ℕ → List (ℚ × ℚ) → Prop
  | _, _, [] => True
  | i, j, (lower,upper)::rows =>
      ((i ≤ j+1 ∧ j ≤ i+1) ∨ (lower=0 ∧ upper=0)) ∧
      rationalDenseEndpointAll n (if n ≤ j+1 then i+1 else i) (if n ≤ j+1 then 0 else j+1) rows
end IV04.Paper.Computational end reset_proof_cache section namespace IV04.Paper.Computational
def boxLowerReal (n:ℕ) (pairs:List (ℚ × ℚ)) (i j:Fin n):ℝ := (pairs.getD (i.val*n+j.val) (0,0)).1
def boxUpperReal (n:ℕ) (pairs:List (ℚ × ℚ)) (i j:Fin n):ℝ := (pairs.getD (i.val*n+j.val) (0,0)).2
def realDenseIntervalBox (n:ℕ) (pairs:List (ℚ × ℚ)):Set (Matrix (Fin n) (Fin n) ℝ) := {A | ∀ i j, boxLowerReal n pairs i j ≤ A i j ∧ A i j ≤ boxUpperReal n pairs i j}
def rationalMatrixDeterminantDecisionLanguage:Set (List Bool) := {matrix | ∃ (n:ℕ) (pairs:List (ℚ × ℚ)) (threshold:ℚ), readMatrixRationals matrix=some (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],[]) ∧ pairs.length=n*n ∧ (∀ row ∈ pairs, row.1 ≤ row.2) ∧ rationalDenseEndpointAll n 0 0 pairs ∧ ∃ A ∈
  realDenseIntervalBox n pairs, (threshold:ℝ) ≤ A.det}
end IV04.Paper.Computational end reset_proof_cache section set_option autoImplicit true namespace Complexity
def MapReducesPoly (L L':Language):Prop := ∃ f:List Bool → List Bool, f ∈ FP ∧ ∀ x, x ∈ L ↔ f x ∈ L'
@[inherit_doc] infix:50 " ≤ₚ " => MapReducesPoly
def NPHard (L:Language):Prop := ∀ L' ∈ NP, L' ≤ₚ L
def NPComplete (L:Language):Prop := L ∈ NP ∧ NPHard L
end Complexity end reset_proof_cache section open scoped Matrix BigOperators namespace IV04.Paper
def positiveCornerRhs (n:ℕ) (hn:0 < n):Fin n → ℝ :=
  Pi.single ⟨n-1,Nat.sub_lt hn (by decide)⟩ (-1)
def positiveSolutions (n:ℕ) (hn:0 < n) (S:Set (Mat n)):Set (Fin n → ℝ) := {x | ∃ A ∈ S, A.mulVec x=positiveCornerRhs n hn}
end IV04.Paper end reset_proof_cache section namespace IV04.Paper.Computational open Complexity
def PolynomialOneQueryReduction (L:Set (List Bool)) (task:List Bool → List Bool → Prop):Prop := ∃ query:List Bool → List Bool, query ∈ FP ∧ ∃ finish:List Bool → List Bool, finish ∈ FP ∧ (∀ input, ∃ answer, task (query input) answer) ∧ ∀ input answer, task (query input) answer → (firstBit (finish (pair input
  answer)) = true ↔ input ∈ L)
def NPHardOutputTask (task:List Bool → List Bool → Prop):Prop := ∀ L ∈ NP, PolynomialOneQueryReduction L task
def ExactDeterminantRangeOutput (matrix answer:List Bool):Prop := ∃ (n:ℕ) (pairs:List (ℚ × ℚ)), readMatrixRationals matrix = some (n,pairs.flatMap (fun row => [row.1,row.2]) ++ [0],[]) ∧ pairs.length = n*n ∧ (∀ row ∈ pairs, row.1 ≤ row.2) ∧ rationalDenseEndpointAll n 0 0 pairs ∧ ∃ (lo hi:ℚ) (tail:List
  Bool), IV04.Paper.readRational answer = some (lo,tail) ∧ IV04.Paper.readRational tail = some (hi,[]) ∧ IsLeast (Matrix.det '' realDenseIntervalBox n pairs) (lo:ℝ) ∧ IsGreatest (Matrix.det '' realDenseIntervalBox n pairs) (hi:ℝ)
end IV04.Paper.Computational end reset_proof_cache section namespace IV04.Paper.Computational
def ExactFullHullOutput (matrix answer:List Bool):Prop := ∃ (n:ℕ) (hn:0 < n) (pairs bounds:List (ℚ × ℚ)), readMatrixRationals matrix = some (n,pairs.flatMap (fun row => [row.1,row.2]) ++ [0],[]) ∧ pairs.length = n*n ∧ (∀ row ∈ pairs, row.1 ≤ row.2) ∧ rationalDenseEndpointAll n 0 0 pairs ∧ (∀ A ∈
  realDenseIntervalBox n pairs, A.det ≠ 0 ∧ ∀ i j:Fin n, j.val = i.val+1 → A i j = 1) ∧ (IV04.Paper.positiveSolutions n hn (realDenseIntervalBox n pairs)).Nonempty ∧ Bornology.IsBounded (IV04.Paper.positiveSolutions n hn (realDenseIntervalBox n pairs)) ∧ bounds.length = n ∧ answer = bounds.flatMap (fun row =>
  IV04.Paper.rationalCode row.1 ++ IV04.Paper.rationalCode row.2) ∧ ∀ i:Fin n, IsLeast ((fun x:Fin n → ℝ => x i) '' IV04.Paper.positiveSolutions n hn (realDenseIntervalBox n pairs)) ((bounds.getD i.val (0,0)).1:ℝ) ∧ IsGreatest ((fun x:Fin n → ℝ => x i) '' IV04.Paper.positiveSolutions n hn (realDenseIntervalBox
  n pairs)) ((bounds.getD i.val (0,0)).2:ℝ)
end IV04.Paper.Computational end reset_proof_cache section namespace IV04.Paper.Computational open Complexity
def RegularUnitMatrixPacket (matrix:List Bool):Prop := ∃ (n:ℕ) (pairs:List (ℚ × ℚ)) (threshold:ℚ), readMatrixRationals matrix = some (n,pairs.flatMap (fun row => [row.1,row.2]) ++ [threshold],[]) ∧ pairs.length = n*n ∧ (∀ row ∈ pairs, row.1 ≤ row.2) ∧ rationalDenseEndpointAll n 0 0 pairs ∧ ∀ A ∈
  realDenseIntervalBox n pairs, A.det ≠ 0 ∧ ∀ i j:Fin n, j.val = i.val+1 → A i j = 1
def regularUnitMatrixDeterminantDecisionLanguage:Set (List Bool) := {matrix | matrix ∈ rationalMatrixDeterminantDecisionLanguage ∧ RegularUnitMatrixPacket matrix}
def RegularUnitDeterminantRangeOutput (matrix answer:List Bool):Prop := ExactDeterminantRangeOutput matrix answer ∧ RegularUnitMatrixPacket matrix
end IV04.Paper.Computational end reset_proof_cache section namespace IV04.Paper.Computational open Complexity
theorem actual_paper_iv_det:NPComplete rationalMatrixDeterminantDecisionLanguage ∧ NPHard regularUnitMatrixDeterminantDecisionLanguage ∧ NPHardOutputTask RegularUnitDeterminantRangeOutput := by sorry
end IV04.Paper.Computational end reset_proof_cache section namespace Reference.IV04FullHullHardness open Complexity IV04.Paper.Computational
theorem iv_hull_literal_np_hard:NPHardOutputTask ExactFullHullOutput := by sorry
end Reference.IV04FullHullHardness end
/- MI-19: A q-permanent subset-inequality counterexample. -/ reset_proof_cache section open scoped BigOperators ComplexOrder namespace NLA.MI19
def inversionCount {n:ℕ} (σ:Equiv.Perm (Fin n)):ℕ := ((Finset.univ:Finset (Fin n × Fin n)).filter fun ij => ij.1 < ij.2 ∧ σ ij.2 < σ ij.1).card
def qPermanentTerm {n:ℕ} (q:ℝ) (A:Matrix (Fin n) (Fin n) ℂ) (σ:Equiv.Perm (Fin n)):ℂ := (q:ℂ) ^ inversionCount σ * ∏ i:Fin n, A i (σ i)
def qPermanent {n:ℕ} (q:ℝ) (A:Matrix (Fin n) (Fin n) ℂ):ℂ := ∑ σ:Equiv.Perm (Fin n), qPermanentTerm q A σ
abbrev PreservesSubset {n:ℕ} (σ:Equiv.Perm (Fin n)) (S:Finset (Fin n)):Prop := S.image σ = S
def restrictedQPermanent {n:ℕ} (q:ℝ) (A:Matrix (Fin n) (Fin n) ℂ) (S:Finset (Fin n)):ℂ := ∑ σ ∈ (Finset.univ:Finset (Equiv.Perm (Fin n))).filter (fun σ => PreservesSubset σ S), qPermanentTerm q A σ
def witness:Matrix (Fin 4) (Fin 4) ℂ := !![170, 1, 167, 170; 1, 1, -2, 1; 167, -2, 173, 167; 170, 1, 167, 170]
def witnessQ:ℝ := 7 / 8
def witnessSubset:Finset (Fin 4) := {1}
end NLA.MI19 end reset_proof_cache section namespace NLA.MI19.Paper
def realWitness:Matrix (Fin 4) (Fin 4) ℝ := !![170,1,167,170; 1,1,-2,1; 167,-2,173,167; 170,1,167,170]
end NLA.MI19.Paper end reset_proof_cache section open scoped ComplexOrder namespace NLA.MI19.Paper
theorem paper_counterexample:realWitness.PosSemidef ∧ realWitness.rank = 2 ∧ witness = realWitness.map (fun x:ℝ => (x:ℂ)) ∧ 0 ≤ witnessQ ∧ witnessQ ≤ 1 ∧ witnessSubset.Nonempty ∧ witnessSubset ≠ Finset.univ ∧ qPermanent witnessQ witness - restrictedQPermanent witnessQ witness witnessSubset = (-3235575 / 16384 :
  ℂ) ∧ qPermanent witnessQ witness < restrictedQPermanent witnessQ witness witnessSubset := by sorry
end NLA.MI19.Paper end
/- MI-21: A geometric-mean norm counterexample. -/ reset_proof_cache section open scoped BigOperators Classical ComplexOrder MatrixOrder open Matrix namespace NLA.MI21
abbrev Mat (n:ℕ) := Matrix (Fin n) (Fin n) ℂ
def spectralPower {n:ℕ} (A:Mat n) (r:ℝ):Mat n := CFC.rpow A r
def geometricMean {n:ℕ} (A B:Mat n) (t:ℝ):Mat n := spectralPower A (1 / 2) * spectralPower (spectralPower A (-1 / 2) * B * spectralPower A (-1 / 2)) t * spectralPower A (1 / 2)
def operatorNorm {n:ℕ} (A:Mat n):ℝ := ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖
def leftMatrix {m n:ℕ} (A B:Fin m → Mat n) (s t r:ℝ):Mat n := ∑ i, spectralPower (geometricMean (spectralPower (A i) s) (spectralPower (B i) s) t) r
def rightMatrix {m n:ℕ} (A B:Fin m → Mat n) (s t r p:ℝ):Mat n := spectralPower (spectralPower (∑ i, A i) ((1 - t) * s * r * p / 2) * spectralPower (∑ i, B i) (t * s * r * p) * spectralPower (∑ i, A i) ((1 - t) * s * r * p / 2)) (1 / p)
def witnessC:Mat 2 := Matrix.diagonal (![12 / 37, 21 / 29]:Fin 2 → ℂ)
def witnessE:Mat 2 := Matrix.diagonal (![35 / 37, 20 / 29]:Fin 2 → ℂ)
def witnessS:Mat 2 := (1 / 17:ℂ) • !![15, 8; 8, -15]
def witnessA:Fin 2 → Mat 2 := ![witnessC ^ (2:ℕ), witnessE ^ (2:ℕ)]
def witnessB:Fin 2 → Mat 2 := ![witnessS * witnessE ^ (2:ℕ) * witnessS, witnessS * witnessC ^ (2:ℕ) * witnessS]
def witnessL:Mat 2 := (1 / 12158163:ℂ) • !![8216600, -985600; -985600, 11912600]
def witnessVector:Fin 2 → ℂ := ![1, -4]
def witnessEigenvalue:ℝ := 1351000 / 1350907
end NLA.MI21 end reset_proof_cache section open scoped BigOperators Classical ComplexOrder MatrixOrder open Matrix namespace NLA.MI21.Paper
theorem paper_counterexample (p:ℝ) (hp:0 < p):(∀ i:Fin 2, (witnessA i).PosDef ∧ (witnessB i).PosDef) ∧ (∑ i, witnessA i) = 1 ∧ (∑ i, witnessB i) = 1 ∧ leftMatrix witnessA witnessB (1 / 2) (1 / 2) 2 = witnessL ∧ rightMatrix witnessA witnessB (1 / 2) (1 / 2) 2 p = 1 ∧ witnessVector ≠ 0 ∧ witnessL *ᵥ witnessVector
  = (witnessEigenvalue:ℂ) • witnessVector ∧ 1 < witnessEigenvalue ∧ witnessEigenvalue ≤ operatorNorm (leftMatrix witnessA witnessB (1 / 2) (1 / 2) 2) ∧ operatorNorm (rightMatrix witnessA witnessB (1 / 2) (1 / 2) 2 p) = 1 ∧ operatorNorm (rightMatrix witnessA witnessB (1 / 2) (1 / 2) 2 p) < operatorNorm (leftMatrix
  witnessA witnessB (1 / 2) (1 / 2) 2) := by sorry
end NLA.MI21.Paper end
/- MI-22: A weighted log-majorization counterexample. -/ reset_proof_cache section open scoped BigOperators Classical ComplexOrder MatrixOrder namespace NLA.MI22
abbrev Mat (n:ℕ) := Matrix (Fin n) (Fin n) ℂ
def spectralPower {n:ℕ} (A:Mat n) (t:ℝ):Mat n := CFC.rpow A t
def weightedMean {n:ℕ} (A B:Mat n) (t:ℝ):Mat n := spectralPower A (1 / 2) * spectralPower (spectralPower A (-1 / 2) * B * spectralPower A (-1 / 2)) t * spectralPower A (1 / 2)
def leftProduct {n:ℕ} (A B:Mat n) (t:ℝ):Mat n := spectralPower A t * weightedMean A B t * spectralPower B (1 - t)
/-- Complex Euclidean spaces are finite-dimensional. -/ theorem singularValue._proof_1 {d:ℕ}:@Module.Finite Complex (WithLp (qA) ((Fin d) -> Complex)) (((qJ).toDivisionRing).toRing).toSemiring (@AddCommGroup.toAddCommMonoid (WithLp (qA) ((Fin d) -> Complex)) (@WithLp.instAddCommGroup (qA) ((Fin d) -> Complex) (qG d))) (@WithLp.instModule (qA) Complex ((Fin d) -> Complex) (((qJ).toDivisionRing).toRing).toSemiring (qG d) (@Pi.module (Fin d) (fun (z0:Fin d) => Complex) Complex (((qJ).toSemifield).toCommSemiring).toSemiring (fun (i:Fin d) => @AddCommGroup.toAddCommMonoid Complex ((qN).toSeminormedAddCommGroup).toAddCommGroup) (fun (i:Fin d) => @NormedSpace.toModule Complex Complex ((Complex.instRCLike).toDenselyNormedField).toNormedField (qN).toSeminormedAddCommGroup (@InnerProductSpace.toNormedSpace Complex Complex Complex.instRCLike (qN).toSeminormedAddCommGroup (@RCLike.innerProductSpace Complex Complex.instRCLike))))) := (by sorry) cache_proof NLA.MI22.singularValue._proof_1
def singularValue {n:ℕ} (A:Mat n) (j:ℕ):ℝ := (Matrix.toEuclideanLin A).singularValues j
def singularPrefix {n:ℕ} (A:Mat n) (k:ℕ):ℝ := ∏ j ∈ Finset.range k, singularValue A j
def SingularLogMajorized {n:ℕ} (X Y:Mat n):Prop := (∀ k:ℕ, 1 ≤ k → k < n → singularPrefix X k ≤ singularPrefix Y k) ∧ singularPrefix X n = singularPrefix Y n
def WeightedLogMajorizationConjecture:Prop := ∀ n:ℕ, 1 ≤ n → ∀ A B:Mat n, A.PosDef → B.PosDef → ∀ t:ℝ, 0 ≤ t → t ≤ 1 → SingularLogMajorized (leftProduct A B t) (A * B)
def operatorNorm {n:ℕ} (A:Mat n):ℝ := ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖
def witnessD:Mat 3 := Matrix.diagonal (![16, 1 / 16, 1]:Fin 3 → ℂ)
def witnessA:Mat 3 := witnessD ^ (2:ℕ)
end NLA.MI22 end reset_proof_cache section namespace NLA.MI22.Paper
def paperB:Mat 3 := !![17, -4, 0; -4, 16385, -8192; 0, -8192, 4096]
end NLA.MI22.Paper end reset_proof_cache section open scoped MatrixOrder ComplexOrder namespace NLA.MI22.Paper
theorem paper_counterexample:witnessA.PosDef ∧ paperB.PosDef ∧ 10900 < operatorNorm (leftProduct witnessA paperB (1/8)) ∧ operatorNorm (witnessA*paperB) < 10200 ∧ ¬ SingularLogMajorized (leftProduct witnessA paperB (1/8)) (witnessA*paperB) := by sorry
theorem paper_conjecture_false:¬ WeightedLogMajorizationConjecture := by sorry
end NLA.MI22.Paper end
