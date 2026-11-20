module

public import NLA.IV04.PaperConstructedHullDefinitions
public import NLA.IV04.PaperConstructedBox

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace IV04.Paper

theorem even_regular_box_hull {n : ℕ} (hn : 0 < n) (he : Even n)
    (B : RationalMatrixBox n)
    (ht : ∀ A ∈ B.realizations, Tridiagonal A)
    (hu : ∀ A ∈ B.realizations, ∀ i j, j.val=i.val+1 → A i j=1)
    (hd : ∀ A ∈ B.realizations, 0 < A.det) :
    ∃ A ∈ B.realizations, IsGreatest (Matrix.det '' B.realizations) A.det ∧
      IsLeast (positiveFirstCoordinates n hn B.realizations) (1/A.det) ∧
      (positiveSolutions n hn B.realizations).Nonempty ∧
      Bornology.IsBounded (positiveSolutions n hn B.realizations) := by
  cases n with
  | zero => omega
  | succ n =>
    have ho : Odd n := by
      obtain ⟨k,hk⟩ := he
      refine ⟨k-1,?_⟩
      omega
    have hs : ∀ A ∈ B.realizations, UnitSuperdiagonal A := by
      intro A hA i
      exact hu A hA i.castSucc i.succ rfl
    have hrhs : positiveCornerRhs (n+1) hn=cornerRhs n := rfl
    have hsol : positiveSolutions (n+1) hn B.realizations=unitedSolutions B.realizations := by
      simp only [positiveSolutions,hrhs,unitedSolutions]
    have hfirst : positiveFirstCoordinates (n+1) hn B.realizations=firstCoordinateValues B.realizations := by
      have h0 : (⟨0,hn⟩ : Fin (n+1))=0 := by ext; simp
      simp only [positiveFirstCoordinates,hsol,firstCoordinateValues,h0]
    rw [hfirst,hsol]
    exact rational_regular_box_hull_transfer ho B ht hs hd

namespace IntegerPartition

theorem constructed_hull_endpoint (P : IntegerPartition) :
    ∃ A ∈ P.intervalBox.realizations, IsGreatest (Matrix.det '' P.intervalBox.realizations) A.det ∧
      IsLeast P.constructedFirstCoordinates (1/A.det) ∧
      P.constructedSolutions.Nonempty ∧ Bornology.IsBounded P.constructedSolutions := by
  exact even_regular_box_hull (layerCount_pos P) (layerCount_even P) P.intervalBox
    (intervalBox_tridiagonal P) (intervalBox_superdiagonal P) (intervalBox_regular P)

theorem constructed_hull_partition_threshold (P : IntegerPartition) :
    ∃ A ∈ P.intervalBox.realizations, IsLeast P.constructedFirstCoordinates (1/A.det) ∧
      (P.HasPartition ↔ 1/A.det ≤ 1/(P.threshold : ℝ)) ∧
      P.constructedSolutions.Nonempty ∧ Bornology.IsBounded P.constructedSolutions := by
  obtain ⟨A,hA,hmax,hfirst,hne,hbounded⟩ := constructed_hull_endpoint P
  have hd : 0 < A.det := intervalBox_regular P A hA
  have ht : (0 : ℝ) < P.threshold := by
    have hdelta : (0 : ℝ) < P.delta := by exact_mod_cast delta_pos P
    have hb : (P.delta : ℝ) ≤ 1/10 := by
      have hcast : (P.delta : ℝ) ≤ ((1/10 : ℚ) : ℝ) := Rat.cast_le.mpr (delta_le_tenth P)
      norm_num at hcast
      exact hcast
    simp only [threshold,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
    nlinarith
  have he : P.HasPartition ↔ (P.threshold : ℝ) ≤ A.det := by
    constructor
    · intro hp
      obtain ⟨B,hB,hdet⟩ := (intervalBox_partition_threshold P).mp hp
      exact hdet.trans (hmax.2 ⟨B,hB,rfl⟩)
    · intro hb
      exact (intervalBox_partition_threshold P).mpr ⟨A,hA,hb⟩
  refine ⟨A,hA,hfirst,?_,hne,hbounded⟩
  rw [he,one_div_le_one_div hd ht]

end IntegerPartition
end IV04.Paper
