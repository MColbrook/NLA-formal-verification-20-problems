module

/- The signed orthant is encoded as actual added matrix inequalities. -/
public import NLA.IV04.AffinePolyhedronSteps.Extreme
public import NLA.IV04.ExactOutputSupport.Orthant

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix

 def withOrthant {ι : Type*} {n : ℕ} (A : Matrix ι (Fin n) ℝ)
    (s : Fin n → ℝ) : Matrix (ι ⊕ Fin n) (Fin n) ℝ
  | Sum.inl i, j => A i j
  | Sum.inr i, j => if i=j then -s i else 0

 def withOrthantBounds {ι : Type*} {n : ℕ} (b : ι → ℝ) : ι ⊕ Fin n → ℝ
  | Sum.inl i => b i
  | Sum.inr _ => 0

 def signedFeasibleSet {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (s : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | feasible A b x ∧ ∀ j, 0 ≤ s j*x j}

 theorem withOrthant_mulVec_inl {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (s x : Fin n → ℝ) (i : ι) :
    (withOrthant A s *ᵥ x) (Sum.inl i) = (A *ᵥ x) i := rfl

 theorem withOrthant_mulVec_inr {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (s x : Fin n → ℝ) (j : Fin n) :
    (withOrthant A s *ᵥ x) (Sum.inr j) = -s j*x j := by
  classical
  simp [withOrthant,Matrix.mulVec,dotProduct]

 theorem feasible_withOrthant_iff {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (s x : Fin n → ℝ) :
    feasible (withOrthant A s) (withOrthantBounds b) x ↔
      feasible A b x ∧ ∀ j, 0 ≤ s j*x j := by
  constructor
  · intro h
    constructor
    · intro i
      exact h (Sum.inl i)
    · intro j
      have hj := h (Sum.inr j)
      rw [withOrthant_mulVec_inr] at hj
      change -s j*x j ≤ 0 at hj
      nlinarith
  · rintro ⟨hA,hs⟩ i
    cases i with
    | inl i => exact hA i
    | inr j =>
      rw [withOrthant_mulVec_inr]
      change -s j*x j ≤ 0
      have hj := hs j
      nlinarith

 theorem signed_orthant_lineFree {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (s : Fin n → ℝ)
    (hs : ∀ j, s j ≠ 0) : lineFree (withOrthant A s) (withOrthantBounds b) := by
  intro x d hline
  apply Reference.IV04ExactOutputSupport.signed_orthant_affine_line_direction_zero s x d hs
  intro t j
  have hj := (feasible_withOrthant_iff A b s (x+t • d)).mp (hline t)
  simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] using hj.2 j

 theorem exists_signed_orthant_extreme_point {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (s : Fin n → ℝ)
    (hs : ∀ j, s j ≠ 0) (hne : (signedFeasibleSet A b s).Nonempty) :
    ∃ x, x ∈ (signedFeasibleSet A b s).extremePoints ℝ ∧
      ∀ d : Fin n → ℝ,
        (∀ i ∈ tightRows (withOrthant A s) (withOrthantBounds b) x,
          (withOrthant A s *ᵥ d) i=0) → d=0 := by
  have heq : feasibleSet (withOrthant A s) (withOrthantBounds b)=signedFeasibleSet A b s := by
    ext x
    exact feasible_withOrthant_iff A b s x
  have hnonempty : ∃ x, feasible (withOrthant A s) (withOrthantBounds b) x := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨x,(feasible_withOrthant_iff A b s x).mpr hx⟩
  obtain ⟨x,hx,hkernel⟩ := exists_extreme_point_of_lineFree
    (withOrthant A s) (withOrthantBounds b) hnonempty (signed_orthant_lineFree A b s hs)
  exact ⟨x,heq ▸ hx,hkernel⟩

#print axioms withOrthant_mulVec_inl
#print axioms withOrthant_mulVec_inr
#print axioms feasible_withOrthant_iff
#print axioms signed_orthant_lineFree
#print axioms exists_signed_orthant_extreme_point
end
end Reference.IV04AffinePolyhedronSteps
