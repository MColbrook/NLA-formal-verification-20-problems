module

public import NLA.TR04.FixedSharp.GreedyBasic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace NLA.TR04.FixedSharp

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem kernel_action_le_error {n : ℕ} (A B : Matrix ι (Fin n) ℝ)
    (v : Fin n → ℝ) (hv : (∑ j, v j^2) = 1)
    (hBv : ∀ i, (∑ j, B i j * v j) = 0) :
    (∑ i, (∑ j, A i j * v j)^2) ≤ ∑ i, ∑ j, (A i j - B i j)^2 := by
  apply Finset.sum_le_sum
  intro i _
  have he : (∑ j, (A i j - B i j) * v j) = ∑ j, A i j * v j := by
    simp only [sub_mul, Finset.sum_sub_distrib, hBv i, sub_zero]
  have hi := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j - B i j) v
  rwa [hv, mul_one, he] at hi

theorem nonneg_sum_exhausted (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (i₀ : ι) (hs : (∑ i, f i) ≤ f i₀) : ∀ i, i ≠ i₀ → f i = 0 := by
  intro i hi
  have he := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i₀)
  have hb : f i ≤ Finset.sum (Finset.univ.erase i₀) f :=
    Finset.single_le_sum (fun j _ => hf j) (by simp [hi])
  have hn := hf i
  linarith

theorem row_exhausts_error (A B : Matrix ι κ ℝ) (i₀ : ι)
    (hs : (∑ i, ∑ j, (A i j - B i j)^2) ≤ ∑ j, (A i₀ j - B i₀ j)^2) :
    ∀ i, i ≠ i₀ → ∀ j, B i j = A i j := by
  intro i hi j
  have hz := nonneg_sum_exhausted (fun i => ∑ j, (A i j - B i j)^2)
    (fun i => Finset.sum_nonneg (fun j _ => sq_nonneg _)) i₀ hs i hi
  have hj : (A i j - B i j)^2 ≤ ∑ k, (A i k - B i k)^2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (A i k - B i k)) (Finset.mem_univ j)
  nlinarith [sq_nonneg (A i j - B i j)]

#print axioms kernel_action_le_error
#print axioms row_exhausts_error

end NLA.TR04.FixedSharp
