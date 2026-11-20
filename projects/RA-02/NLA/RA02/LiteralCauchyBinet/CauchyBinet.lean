module

public import NLA.RA02.LiteralCauchyBinet.Enumeration

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace RootRA02CauchyBinet
open Finset Function Matrix Equiv
open scoped BigOperators

theorem rectangular_determinant_map_sum {s n : ℕ}
    (A : Matrix (Fin s) (Fin n) ℝ) (B : Matrix (Fin n) (Fin s) ℝ) :
    (A * B).det = ∑ f : Fin s → Fin n,
      (A.submatrix id f).det * ∏ i, B (f i) i := by
  classical
  calc
    (A * B).det = ∑ f : Fin s → Fin n, ∑ σ : Equiv.Perm (Fin s),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A (σ i) (f i) * B (f i) i := by
      simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
        Finset.mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [Matrix.det_apply', Finset.prod_mul_distrib,
        Finset.sum_mul, Matrix.submatrix_apply, id_eq, mul_assoc]

theorem rectangular_determinant_embedding_sum {s n : ℕ}
    (A : Matrix (Fin s) (Fin n) ℝ) (B : Matrix (Fin n) (Fin s) ℝ) :
    (A * B).det = ∑ f : Fin s ↪ Fin n,
      (A.submatrix id f).det * ∏ i, B (f i) i := by
  classical
  rw [rectangular_determinant_map_sum]
  calc
    (∑ f : Fin s → Fin n, (A.submatrix id f).det * ∏ i, B (f i) i) =
        ∑ f : Fin s → Fin n with Function.Injective f,
          (A.submatrix id f).det * ∏ i, B (f i) i := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro f hf hn
      have hni : ¬Function.Injective f := by simpa only [Finset.mem_filter_univ] using hn
      obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
        unfold Function.Injective at hni
        push Not at hni
        exact hni
      have hd : (A.submatrix id f).det = 0 :=
        Matrix.det_zero_of_column_eq hne (fun k => congrArg (A k) hij)
      simp [hd]
    _ = _ := by
      apply Finset.sum_bij (fun f hf => (⟨f, (Finset.mem_filter.mp hf).2⟩ : Fin s ↪ Fin n))
      · intro f hf
        exact Finset.mem_univ _
      · intro f hf g hg h
        exact congrArg DFunLike.coe h
      · intro f hf
        exact ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, f.injective⟩, rfl⟩
      · intro f hf
        rfl

theorem rectangular_cauchy_binet {s n : ℕ}
    (A : Matrix (Fin s) (Fin n) ℝ) (B : Matrix (Fin n) (Fin s) ℝ) :
    (A * B).det = ∑ T : SizedSubset n s,
      (A.submatrix id (enumerate T)).det * (B.submatrix (enumerate T) id).det := by
  classical
  rw [rectangular_determinant_embedding_sum]
  have hreindex :
      (∑ f : Fin s ↪ Fin n, (A.submatrix id f).det * ∏ i, B (f i) i) =
      ∑ p : SizedSubset n s × Equiv.Perm (Fin s),
        (A.submatrix id (enumeratedPermutation p)).det *
          ∏ i, B (enumeratedPermutation p i) i := by
    exact (Fintype.sum_bijective (@enumeratedPermutation n s)
      (enumeratedPermutation_bijective n s) _ _ (fun _ => rfl)).symm
  rw [hreindex]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro T hT
  calc
    (∑ σ : Equiv.Perm (Fin s),
      (A.submatrix id (enumeratedPermutation (T, σ))).det *
        ∏ i, B (enumeratedPermutation (T, σ) i) i) =
      ∑ σ : Equiv.Perm (Fin s),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * (A.submatrix id (enumerate T)).det *
          ∏ i, B (enumerate T (σ i)) i := by
      apply Finset.sum_congr rfl
      intro σ hσ
      change ((A.submatrix id (enumerate T)).submatrix id σ).det * _ = _
      rw [Matrix.det_permute']
      rfl
    _ = _ := by
      rw [Matrix.det_apply' (B.submatrix (enumerate T) id), Finset.mul_sum]
      simp only [Matrix.submatrix_apply, id_eq]
      apply Finset.sum_congr rfl
      intro σ hσ
      ring

end RootRA02CauchyBinet
