module

public import NLA.IV04.RationalBoxExtrema.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace Reference.IV04RationalBoxExtrema

theorem rowwise_interpolation {m n : ℕ}
    (L U : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (hLU : ∀ i j, L i j ≤ U i j) (s : Fin n → Bool) (x : Fin n → ℝ)
    (h : rowBounds L U b s x) : x ∈ solutions L U b := by
  classical
  let lo : Fin m → ℝ := fun i => ∑ j, (lowerRow L U s i j : ℝ) * x j
  let hi : Fin m → ℝ := fun i => ∑ j, (upperRow L U s i j : ℝ) * x j
  let t : Fin m → ℝ := fun i => if hi i = lo i then 0 else ((b i : ℝ)-lo i)/(hi i-lo i)
  have ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1 := by
    intro i
    have hb := h i
    change lo i ≤ (b i : ℝ) ∧ (b i : ℝ) ≤ hi i at hb
    by_cases he : hi i = lo i
    · simp [t,he]
    · have hg : 0 < hi i-lo i := sub_pos.mpr
        (lt_of_le_of_ne (hb.1.trans hb.2) (Ne.symm he))
      simp only [t,if_neg he]
      exact ⟨div_nonneg (by linarith) hg.le, (div_le_one hg).mpr (by linarith)⟩
  let A : Matrix (Fin m) (Fin n) ℝ := fun i j =>
    (1-t i)*(lowerRow L U s i j : ℝ)+t i*(upperRow L U s i j : ℝ)
  refine ⟨A,?_,?_⟩
  · intro i j
    have hij : (L i j : ℝ) ≤ (U i j : ℝ) := by exact_mod_cast hLU i j
    have hti := ht i
    change (L i j : ℝ) ≤ A i j ∧ A i j ≤ (U i j : ℝ)
    cases hs : s j <;> simp only [A,lowerRow,upperRow,hs,Bool.false_eq_true,
      ↓reduceIte] <;> constructor <;> nlinarith
  · funext i
    have hb := h i
    change lo i ≤ (b i : ℝ) ∧ (b i : ℝ) ≤ hi i at hb
    have heval : (A *ᵥ x) i = (1-t i)*lo i+t i*hi i := by
      simp only [Matrix.mulVec,dotProduct,A,add_mul, mul_assoc,
        Finset.sum_add_distrib,← Finset.mul_sum,lo,hi]
    rw [heval]
    by_cases he : hi i = lo i
    · simp [t,he]
      linarith
    · have hg : hi i-lo i ≠ 0 := sub_ne_zero.mpr he
      simp only [t,if_neg he]
      field_simp
      nlinarith

#print axioms rowwise_interpolation
end Reference.IV04RationalBoxExtrema
