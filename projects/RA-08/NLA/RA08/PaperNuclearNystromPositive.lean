module

public import NLA.RA08.PaperNuclearNystromNorm
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem nuclear_real_outer_mulVec {n : ℕ} (v x : Fin n → ℝ) :
    Matrix.vecMulVec v v *ᵥ x=(v ⬝ᵥ x) • v := by
  ext i
  simp only [Matrix.mulVec,dotProduct,Matrix.vecMulVec,Matrix.of_apply,
    Pi.smul_apply,smul_eq_mul,mul_assoc,← Finset.mul_sum]
  exact mul_comm _ _

theorem nuclear_real_outer_energy {n : ℕ} (v x : Fin n → ℝ) :
    x ⬝ᵥ (Matrix.vecMulVec v v *ᵥ x)=(v ⬝ᵥ x)^2 := by
  rw [nuclear_real_outer_mulVec,dotProduct_smul,dotProduct_comm x v]
  simp only [smul_eq_mul,pow_two]

theorem nuclearLiftBase_energy (m : ℕ) (x : Fin (m+m+1) → ℝ) :
    x ⬝ᵥ (nuclearLiftBase m *ᵥ x)=
      ∑ i : Fin (m+m), nuclearBaseEntries m i*(x i.castSucc)^2 := by
  simp only [dotProduct,nuclearLiftBase,Matrix.mulVec_diagonal,Fin.sum_univ_castSucc,
    nuclearLiftBaseEntries,Fin.snoc_castSucc,Fin.snoc_last,zero_mul,mul_zero,add_zero]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem nuclearLiftA_energy (m : ℕ) (η t : ℝ) (x : Fin (m+m+1) → ℝ) :
    x ⬝ᵥ (nuclearLiftA m η t *ᵥ x)=
      (∑ i : Fin (m+m), nuclearBaseEntries m i*(x i.castSucc)^2)+
      t*(nuclearLiftVector m η ⬝ᵥ x)^2 := by
  rw [nuclearLiftA,Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_add,dotProduct_smul,
    nuclearLiftBase_energy]
  simp only [nuclearLiftPerturbation,nuclear_real_outer_energy,smul_eq_mul]

theorem nuclearLiftBase_posSemidef (m : ℕ) : (nuclearLiftBase m).PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [nuclearLiftBaseEntries]
  · simpa [nuclearLiftBaseEntries] using (nuclearBaseEntries_pos m j).le

theorem nuclearLiftA_posDef (m : ℕ) (η t : ℝ) (hη : η < 1) (ht : 0 < t) :
    (nuclearLiftA m η t).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (nuclearLiftA_isHermitian m η t)
  intro x hx
  have hsum : 0 ≤ ∑ i : Fin (m+m), nuclearBaseEntries m i*(x i.castSucc)^2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (nuclearBaseEntries_pos m i).le (sq_nonneg _)
  have henergy : 0 < x ⬝ᵥ (nuclearLiftA m η t *ᵥ x) := by
    rw [nuclearLiftA_energy]
    by_cases hp : ∃ i : Fin (m+m), x i.castSucc ≠ 0
    · obtain ⟨i,hi⟩ := hp
      have hs : 0 < ∑ i : Fin (m+m), nuclearBaseEntries m i*(x i.castSucc)^2 :=
        Finset.sum_pos' (fun j _ => mul_nonneg (nuclearBaseEntries_pos m j).le (sq_nonneg _))
          ⟨i,Finset.mem_univ _,mul_pos (nuclearBaseEntries_pos m i) (sq_pos_of_ne_zero hi)⟩
      exact add_pos_of_pos_of_nonneg hs (mul_nonneg ht.le (sq_nonneg _))
    · push Not at hp
      have hl : x (Fin.last (m+m)) ≠ 0 := by
        intro hl
        apply hx
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · exact hl
        · exact hp j
      have hv : nuclearLiftVector m η ⬝ᵥ x=Real.sqrt (1-η)*x (Fin.last (m+m)) := by
        simp [dotProduct,Fin.sum_univ_castSucc,nuclearLiftVector,hp]
      have hs : Real.sqrt (1-η) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
      have hpos := mul_pos ht (sq_pos_of_ne_zero (mul_ne_zero hs hl))
      rw [hv]
      exact add_pos_of_nonneg_of_pos hsum hpos
  simpa only [star_trivial] using henergy

theorem nuclearLiftSketch_rank (m : ℕ) (η : ℝ) : (nuclearLiftSketch m η).rank=m+m := by
  rw [Matrix.rank,LinearMap.finrank_range_of_inj (nuclearLiftSketch_injective m η)]
  simp

theorem nuclearBaseEntries_lower (m : ℕ) (i : Fin (m+m)) :
    (3/4 : ℝ) ≤ nuclearBaseEntries m i := by
  unfold nuclearBaseEntries
  cases h : (finSumFinEquiv (m := m) (n := m)).symm i with
  | inl j => simp only [Sum.elim_inl]; linarith [nuclearHeight_le_quarter j]
  | inr j => simp only [Sum.elim_inr]; linarith [nuclearHeight_pos j]

theorem nuclearLiftBaseEntries_ne_one (m : ℕ) (i : Fin (m+m+1)) :
    nuclearLiftBaseEntries m i ≠ 1 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [nuclearLiftBaseEntries]
  · simpa [nuclearLiftBaseEntries] using nuclearBaseEntries_ne_one m j

theorem nuclearLiftBaseEntries_ne_zero_iff (m : ℕ) (i : Fin (m+m+1)) :
    nuclearLiftBaseEntries m i ≠ 0 ↔ i ≠ Fin.last (m+m) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [nuclearLiftBaseEntries]
  · simp [nuclearLiftBaseEntries,ne_of_gt (nuclearBaseEntries_pos m j)]

theorem nuclearLiftBase_rank (m : ℕ) : (nuclearLiftBase m).rank=m+m := by
  rw [nuclearLiftBase,Matrix.rank_diagonal,Fintype.card_subtype]
  have he : Finset.univ.filter (fun i : Fin (m+m+1) => nuclearLiftBaseEntries m i ≠ 0)=
      Finset.univ.erase (Fin.last (m+m)) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,and_true]
    exact nuclearLiftBaseEntries_ne_zero_iff m i
  rw [he]
  simp

theorem nuclearLiftSketch_coefficient (η : ℝ) (hη : 0 ≤ η) :
    Real.sqrt η/Real.sqrt (1-η)=Real.sqrt (η/(1-η)) :=
  (Real.sqrt_div hη (1-η)).symm

#print axioms nuclearLiftA_posDef
end NLA.RA08.Paper
