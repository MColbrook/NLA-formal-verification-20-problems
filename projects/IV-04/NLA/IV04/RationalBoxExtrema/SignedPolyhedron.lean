module

public import NLA.IV04.RationalBoxExtrema.EndpointBounds
public import NLA.IV04.AffinePolyhedronSteps.RationalSignedOrthant

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace Reference.IV04RationalBoxExtrema
open Reference.IV04AffinePolyhedronSteps

def endpointMatrix {m n : ℕ} (L U : Matrix (Fin m) (Fin n) ℚ)
    (s : Fin n → Bool) : Matrix (Fin m ⊕ Fin m) (Fin n) ℚ
  | Sum.inl i,j => lowerRow L U s i j
  | Sum.inr i,j => -upperRow L U s i j

def endpointBounds {m : ℕ} (b : Fin m → ℚ) : Fin m ⊕ Fin m → ℚ
  | Sum.inl i => b i
  | Sum.inr i => -b i

def orthantSigns {n : ℕ} (s : Fin n → Bool) : Fin n → ℚ :=
  fun j => if s j then 1 else -1

def signedMatrix {m n : ℕ} (L U : Matrix (Fin m) (Fin n) ℚ)
    (s : Fin n → Bool) := rationalWithOrthant (endpointMatrix L U s) (orthantSigns s)

def signedBounds {m n : ℕ} (b : Fin m → ℚ) :=
  rationalWithOrthantBounds (n:=n) (endpointBounds b)

theorem endpoint_feasible_iff {m n : ℕ} (L U : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) (s : Fin n → Bool) (x : Fin n → ℝ) :
    feasible (realMatrix (endpointMatrix L U s)) (realVector (endpointBounds b)) x ↔
      rowBounds L U b s x := by
  constructor
  · intro h i
    have hl := h (Sum.inl i)
    have hu := h (Sum.inr i)
    change (∑ j, (lowerRow L U s i j : ℝ)*x j) ≤ (b i : ℝ) at hl
    change (∑ j, ((-upperRow L U s i j : ℚ) : ℝ)*x j) ≤ ((-b i : ℚ) : ℝ) at hu
    simp only [Rat.cast_neg,neg_mul,Finset.sum_neg_distrib] at hu
    exact ⟨hl,by linarith⟩
  · intro h i
    cases i with
    | inl i => exact (h i).1
    | inr i =>
      have hu := (h i).2
      change (∑ j, ((-upperRow L U s i j : ℚ) : ℝ)*x j) ≤ ((-b i : ℚ) : ℝ)
      simp only [Rat.cast_neg,neg_mul,Finset.sum_neg_distrib]
      linarith

theorem signed_feasible_iff {m n : ℕ} (L U : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) (s : Fin n → Bool) (x : Fin n → ℝ) :
    feasible (realMatrix (signedMatrix L U s)) (realVector (signedBounds (n:=n) b)) x ↔
      inOrthant s x ∧ rowBounds L U b s x := by
  rw [signedMatrix,signedBounds,realMatrix_rationalWithOrthant,
    realVector_rationalWithOrthantBounds,feasible_withOrthant_iff,endpoint_feasible_iff]
  have heq : (∀ j, 0 ≤ realVector (orthantSigns s) j*x j) ↔ inOrthant s x := by
    constructor <;> intro h j <;> have hj := h j <;>
      cases hs : s j <;> simpa [realVector,orthantSigns,hs,inOrthant] using hj
  rw [heq,and_comm]

theorem signed_polyhedron_lineFree {m n : ℕ} (L U : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) (s : Fin n → Bool) :
    lineFree (realMatrix (signedMatrix L U s)) (realVector (signedBounds (n:=n) b)) := by
  rw [signedMatrix,signedBounds,realMatrix_rationalWithOrthant,
    realVector_rationalWithOrthantBounds]
  apply signed_orthant_lineFree
  intro j
  cases hs : s j <;> simp [realVector,orthantSigns,hs]

theorem solutions_iff_actual_signed_polyhedron {m n : ℕ}
    (L U : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (hLU : ∀ i j, L i j ≤ U i j) (x : Fin n → ℝ) :
    x ∈ solutions L U b ↔ ∃ s : Fin n → Bool,
      feasible (realMatrix (signedMatrix L U s)) (realVector (signedBounds (n:=n) b)) x := by
  rw [solutions_iff_signed_rowBounds L U b hLU]
  exact exists_congr (fun s => (signed_feasible_iff L U b s x).symm)

#print axioms endpoint_feasible_iff
#print axioms signed_feasible_iff
#print axioms signed_polyhedron_lineFree
#print axioms solutions_iff_actual_signed_polyhedron
end Reference.IV04RationalBoxExtrema
