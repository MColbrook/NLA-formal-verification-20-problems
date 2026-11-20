module

public import NLA.IV04.PaperMatrixVertexDecisionDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational
noncomputable section

def boxLowerReal (n : ℕ) (pairs : List (ℚ × ℚ)) (i j : Fin n) : ℝ :=
  (pairs.getD (i.val*n+j.val) (0,0)).1

def boxUpperReal (n : ℕ) (pairs : List (ℚ × ℚ)) (i j : Fin n) : ℝ :=
  (pairs.getD (i.val*n+j.val) (0,0)).2

/-- All real matrices in the literal dense row-major rational interval box. -/
def realDenseIntervalBox (n : ℕ) (pairs : List (ℚ × ℚ)) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | ∀ i j, boxLowerReal n pairs i j ≤ A i j ∧ A i j ≤ boxUpperReal n pairs i j}

def normalizedBoxMatrix (n : ℕ) (pairs : List (ℚ × ℚ))
    (q : Fin n × Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ((1-q (i,j))/2)*boxLowerReal n pairs i j+
    ((1+q (i,j))/2)*boxUpperReal n pairs i j

def rationalBoxVertex (n : ℕ) (pairs : List (ℚ × ℚ))
    (choices : Fin n × Fin n → Bool) : RatMat n :=
  fun i j => if choices (i,j) then (pairs.getD (i.val*n+j.val) (0,0)).2
    else (pairs.getD (i.val*n+j.val) (0,0)).1

/-- Fixed row-major coordinate arithmetic; dimension zero has an empty domain. -/
def rowMajorCoordinate (n : ℕ) (k : Fin (n*n)) : Fin n × Fin n :=
  have hp : 0<n := by
    have hk := k.isLt
    by_contra h
    have hn : n=0 := by omega
    have hz : n*n=0 := by simp [hn]
    omega
  (⟨k.val/n,Nat.div_lt_of_lt_mul k.isLt⟩,⟨k.val%n,Nat.mod_lt k.val hp⟩)

def boxVertexCertificate (n : ℕ) (choices : Fin n × Fin n → Bool) : List Bool :=
  List.ofFn (fun k : Fin (n*n) => choices (rowMajorCoordinate n k))

/-- The actual determinant threshold task quantifies over every real interval realization. -/
def rationalMatrixDeterminantDecisionLanguage : Set (List Bool) :=
  {matrix | ∃ (n : ℕ) (pairs : List (ℚ × ℚ)) (threshold : ℚ),
    readMatrixRationals matrix=some (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],[]) ∧
    pairs.length=n*n ∧ (∀ row ∈ pairs, row.1 ≤ row.2) ∧ rationalDenseEndpointAll n 0 0 pairs ∧
    ∃ A ∈ realDenseIntervalBox n pairs, (threshold : ℝ) ≤ A.det}

end
end IV04.Paper.Computational
