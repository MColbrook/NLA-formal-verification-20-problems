module

public import NLA.RA02.PaperLUZeroHistories
public import NLA.RA02.PaperHistoryContributions

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace NLA.RA02.Paper

def jointEmbeddingHistory {n k : ℕ} (p : (Fin k ↪ Fin n) × (Fin k ↪ Fin n)) :
    Fin k → Option (Fin n × Fin n) := fun i => some (p.1 i,p.2 i)

theorem jointEmbeddingHistory_injective {n k : ℕ} :
    Function.Injective (jointEmbeddingHistory (n:=n) (k:=k)) := by
  intro a b hab
  have h : ∀ i, (a.1 i,a.2 i) = (b.1 i,b.2 i) := fun i => Option.some.inj (congrFun hab i)
  apply Prod.ext
  · exact Function.Embedding.ext (fun i => congrArg Prod.fst (h i))
  · exact Function.Embedding.ext (fun i => congrArg Prod.snd (h i))

theorem lu_outside_distinct_contribution {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : Fin k → Option (Fin n × Fin n)) (hh : h ∉ Set.range jointEmbeddingHistory) :
    NLA.RA03.historyMass (complexify A) h *
      NLA.RA03.frobeniusSq (NLA.RA03.historyResidual (complexify A) h) = 0 := by
  by_cases hex : ∀ i, h i ≠ none
  · have hex' : ∀ i, ∃ p, h i = some p := fun i => Option.ne_none_iff_exists'.mp (hex i)
    choose g hg using hex'
    have heq : h = fun i => some (g i) := funext hg
    by_cases hr : Function.Injective (fun i => (g i).1)
    · by_cases hc : Function.Injective (fun i => (g i).2)
      · exact False.elim (hh ⟨(⟨fun i => (g i).1,hr⟩,⟨fun i => (g i).2,hc⟩), by
          funext i
          exact (hg i).symm⟩)
      · have hw : ¬((List.ofFn g).map Prod.snd).Nodup := by
          simpa only [List.map_ofFn, Function.comp_def, List.nodup_ofFn] using hc
        have hm : NLA.RA03.historyMass (complexify A) h = 0 := by
          rw [heq, luMass_as_list]
          simpa only [List.map_ofFn, Function.comp_def] using lu_repeated_col_mass A (List.ofFn g) hw
        rw [hm, zero_mul]
    · have hw : ¬((List.ofFn g).map Prod.fst).Nodup := by
        simpa only [List.map_ofFn, Function.comp_def, List.nodup_ofFn] using hr
      have hm : NLA.RA03.historyMass (complexify A) h = 0 := by
        rw [heq, luMass_as_list]
        simpa only [List.map_ofFn, Function.comp_def] using lu_repeated_row_mass A (List.ofFn g) hw
      rw [hm, zero_mul]
  · obtain ⟨i,hi⟩ := not_forall.mp hex
    have hnone : h i = none := not_ne_iff.mp hi
    have hm : none ∈ List.ofFn h := List.mem_ofFn.mpr ⟨i,hnone⟩
    rw [complexify_lu_path, realLUPath_as_list, lu_none_residual A _ hm, complexify_frobenius]
    simp

theorem lu_expectation_distinct {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    NLA.RA03.expectedError (complexify A) k =
      ∑ p : (Fin k ↪ Fin n) × (Fin k ↪ Fin n),
        NLA.RA03.historyMass (complexify A) (jointEmbeddingHistory p) *
          NLA.RA03.frobeniusSq (NLA.RA03.historyResidual (complexify A) (jointEmbeddingHistory p)) := by
  unfold NLA.RA03.expectedError
  symm
  apply Fintype.sum_of_injective jointEmbeddingHistory jointEmbeddingHistory_injective
  · exact lu_outside_distinct_contribution A
  · intro p
    rfl

theorem lu_expectation_determinant {k : ℕ} (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hA : AllSquareMinorsNonzero A) :
    NLA.RA03.expectedError (complexify A) k = A.det^2 *
      ∑ p : (Fin k ↪ Fin (k+1)) × (Fin k ↪ Fin (k+1)),
        (luNormalizerProduct A (List.ofFn (jointEmbeddingHistory p)))⁻¹ := by
  rw [lu_expectation_distinct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact (lu_terminal_contribution A hA p.1 p.2).trans (div_eq_mul_inv _ _)

#print axioms lu_expectation_determinant
end NLA.RA02.Paper
