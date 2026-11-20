module

public import NLA.TR04.LexicographicTensorCompletion.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace NLA.TR04.AllOrderSharp
open Reference.LexTensorCompletion

def zeroWord (N : ℕ) (hN : 0 < N) : (q : ℕ) → ModeIndex (List.replicate q N)
  | 0 => PUnit.unit
  | q+1 => (⟨0, hN⟩, zeroWord N hN q)

def branchWord (N : ℕ) (hN : 0 < N) :
    (q : ℕ) → Fin N → ModeIndex (List.replicate (q+1) N)
  | 0, b => (b, PUnit.unit)
  | q+1, b => (b, if b.val < q+2 then branchWord N hN q b else zeroWord N hN (q+1))

def activeWord {N q : ℕ} (hN : q+2 ≤ N) (b : Fin (q+2)) :
    ModeIndex (List.replicate (q+1) N) :=
  branchWord N (by omega) q ⟨b.val, b.isLt.trans_le hN⟩

def selector {N q : ℕ} (hN : q+2 ≤ N) :
    Matrix (Fin (q+2)) (ModeIndex (List.replicate (q+1) N)) ℝ :=
  fun b j => if j = activeWord hN b then 1 else 0

def family {N q m : ℕ} (hN : q+2 ≤ N) (V : Matrix (Fin m) (Fin (q+2)) ℝ) :
    Tensor m (List.replicate (q+1) N) := V * selector hN

def ranks : ℕ → List ℕ
  | 0 => [1]
  | q+1 => (q+2) :: ranks q

@[simp] theorem branchWord_head {N : ℕ} (hN : 0 < N) (q : ℕ) (b : Fin N) :
    (branchWord N hN q b).1 = b := by
  cases q <;> rfl

theorem activeWord_injective {N q : ℕ} (hN : q+2 ≤ N) :
    Function.Injective (activeWord hN) := by
  intro a b hab
  have hh := congrArg (fun j => j.1.val) hab
  apply Fin.ext
  simpa [activeWord] using hh

@[simp] theorem family_apply {N q m : ℕ} (hN : q+2 ≤ N)
    (V : Matrix (Fin m) (Fin (q+2)) ℝ) (i : Fin m)
    (j : ModeIndex (List.replicate (q+1) N)) :
    family hN V i j = ∑ b, if j = activeWord hN b then V i b else 0 := by
  simp only [family, Matrix.mul_apply, selector, mul_ite, mul_one, mul_zero]

theorem selector_gram {N q : ℕ} (hN : q+2 ≤ N) :
    selector hN * (selector hN).transpose = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (activeWord hN a)]
  · simp [selector, (activeWord_injective hN).eq_iff, Matrix.one_apply]
  · intro j _ hj
    simp [selector, hj]
  · simp

theorem family_gram {N q m : ℕ} (hN : q+2 ≤ N)
    (V : Matrix (Fin m) (Fin (q+2)) ℝ) :
    family hN V * (family hN V).transpose = V * V.transpose := by
  unfold family
  rw [Matrix.transpose_mul]
  calc
    (V * selector hN) * ((selector hN).transpose * V.transpose) =
        (V * (selector hN * (selector hN).transpose)) * V.transpose := by
      simp only [Matrix.mul_assoc]
    _ = V * V.transpose := by rw [selector_gram, Matrix.mul_one]

theorem family_norm {N q m : ℕ} (hN : q+2 ≤ N)
    (V : Matrix (Fin m) (Fin (q+2)) ℝ) :
    tensorFrobeniusSq (family hN V) = ∑ i, ∑ b, V i b ^ 2 := by
  unfold tensorFrobeniusSq
  apply Finset.sum_congr rfl
  intro i _
  have hh := congrArg (fun M => M i i) (family_gram hN V)
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hh

theorem family_rank_column_zero {N q m : ℕ} (hN : q+2 ≤ N)
    (V : Matrix (Fin m) (Fin (q+2)) ℝ) (i0 : Fin (q+2))
    (hV : ∀ i, V i i0 = 0) : (family hN V).rank ≤ q+1 := by
  let A : Matrix (Fin m) (Fin (q+1)) ℝ := fun i b => V i (i0.succAbove b)
  let B : Matrix (Fin (q+1)) (ModeIndex (List.replicate (q+1) N)) ℝ :=
    fun b j => selector hN (i0.succAbove b) j
  have he : family hN V = A * B := by
    ext i j
    change (∑ b, V i b * selector hN b j) =
      ∑ b : Fin (q+1), V i (i0.succAbove b) * selector hN (i0.succAbove b) j
    rw [Fin.sum_univ_succAbove _ i0]
    simp only [hV i, zero_mul, zero_add]
  rw [he]
  simpa using (Matrix.rank_mul_le_left A B).trans (Matrix.rank_le_card_width A)

end NLA.TR04.AllOrderSharp
