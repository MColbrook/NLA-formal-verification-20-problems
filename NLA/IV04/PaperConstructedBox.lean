module

public import NLA.IV04.PaperConstructedBoxDefinitions
public import NLA.IV04.PaperCubeExtrema
public import NLA.IV04.PaperIntervalHull

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace IV04.Paper.IntegerPartition

theorem fixed_entry_bounds (P : IntegerPartition) (q : ℕ → ℝ) (i j : Fin P.layerCount)
    (h : ¬(i.val=j.val+1 ∧ i.val%4=2)) :
    (P.rationalLower i j : ℝ)=P.layerMatrix q i j ∧
      (P.rationalUpper i j : ℝ)=P.layerMatrix q i j := by
  have hu : P.rationalUpper i j=P.rationalLower i j := by simp [rationalUpper,h]
  rw [hu]
  suffices he : (P.rationalLower i j : ℝ)=P.layerMatrix q i j by exact ⟨he,he⟩
  by_cases hd : i=j
  · subst j
    simp [rationalLower,layerMatrix,continuantMatrix]
  · by_cases hupper : j.val=i.val+1
    · simp [rationalLower,layerMatrix,continuantMatrix,hd,hupper]
    · by_cases hlower : i.val=j.val+1
      · have h2 : i.val%4 ≠ 2 := by intro h2; exact h ⟨hlower,h2⟩
        simp only [rationalLower,layerMatrix,continuantMatrix,if_neg hd,if_neg hupper,if_pos hlower]
        dsimp [layerBeta]
        split_ifs <;> simp_all
      · simp [rationalLower,layerMatrix,continuantMatrix,hd,hupper,hlower]

theorem uncertain_entry_bounds (P : IntegerPartition) (k : Fin (P.m-1)) :
    P.rationalLower (P.uncertainRow k) (P.uncertainColumn k)=-1 ∧
      P.rationalUpper (P.uncertainRow k) (P.uncertainColumn k)=1 := by
  have hne : P.uncertainRow k ≠ P.uncertainColumn k := by
    intro he
    have h := congrArg Fin.val he
    dsimp [uncertainRow,uncertainColumn] at h
    omega
  have hmod : (4*k.val+2)%4=2 := by omega
  simp [rationalLower,rationalUpper,uncertainRow,uncertainColumn,hne,hmod]

theorem uncertain_position_indices (P : IntegerPartition) (i j : Fin P.layerCount)
    (h : i.val=j.val+1 ∧ i.val%4=2) :
    ∃ k : Fin (P.m-1), i=P.uncertainRow k ∧ j=P.uncertainColumn k := by
  have hi := i.isLt
  dsimp [layerCount] at hi
  have hk : i.val/4 < P.m-1 := by omega
  refine ⟨⟨i.val/4,hk⟩,?_,?_⟩ <;> apply Fin.ext <;>
    dsimp [uncertainRow,uncertainColumn] <;> omega

theorem layerMatrix_in_intervalBox (P : IntegerPartition) (q : ℕ → ℝ)
    (hq : P.InCube q) : P.layerMatrix q ∈ P.intervalBox.realizations := by
  intro i j
  change (P.rationalLower i j : ℝ) ≤ P.layerMatrix q i j ∧
    P.layerMatrix q i j ≤ (P.rationalUpper i j : ℝ)
  by_cases h : i.val=j.val+1 ∧ i.val%4=2
  · obtain ⟨k,rfl,rfl⟩ := uncertain_position_indices P i j h
    rw [uncertain_entry_value,(uncertain_entry_bounds P k).1,(uncertain_entry_bounds P k).2]
    simpa using hq k.val k.isLt
  · obtain ⟨hl,hu⟩ := fixed_entry_bounds P q i j h
    rw [hl,hu]
    exact ⟨le_rfl,le_rfl⟩

theorem parametersOf_in_cube (P : IntegerPartition) (A : Mat P.layerCount)
    (hA : A ∈ P.intervalBox.realizations) : P.InCube (P.parametersOf A) := by
  intro k hk
  have hb := hA (P.uncertainRow ⟨k,hk⟩) (P.uncertainColumn ⟨k,hk⟩)
  change (P.rationalLower _ _ : ℝ) ≤ _ ∧ _ ≤ (P.rationalUpper _ _ : ℝ) at hb
  rw [(uncertain_entry_bounds P ⟨k,hk⟩).1,(uncertain_entry_bounds P ⟨k,hk⟩).2] at hb
  simpa [parametersOf,hk] using hb

theorem intervalBox_matrix_recovery (P : IntegerPartition) (A : Mat P.layerCount)
    (hA : A ∈ P.intervalBox.realizations) : A=P.layerMatrix (P.parametersOf A) := by
  ext i j
  by_cases h : i.val=j.val+1 ∧ i.val%4=2
  · obtain ⟨k,rfl,rfl⟩ := uncertain_position_indices P i j h
    rw [uncertain_entry_value]
    simp [parametersOf,k.isLt]
  · have hb := hA i j
    change (P.rationalLower i j : ℝ) ≤ A i j ∧ A i j ≤ (P.rationalUpper i j : ℝ) at hb
    obtain ⟨hl,hu⟩ := fixed_entry_bounds P (P.parametersOf A) i j h
    rw [hl,hu] at hb
    exact le_antisymm hb.2 hb.1

theorem intervalBox_realizations_exact (P : IntegerPartition) :
    P.intervalBox.realizations={A | ∃ q : ℕ → ℝ, P.InCube q ∧ A=P.layerMatrix q} := by
  ext A
  constructor
  · intro hA
    exact ⟨P.parametersOf A,parametersOf_in_cube P A hA,intervalBox_matrix_recovery P A hA⟩
  · rintro ⟨q,hq,rfl⟩
    exact layerMatrix_in_intervalBox P q hq

theorem intervalBox_regular (P : IntegerPartition) (A : Mat P.layerCount)
    (hA : A ∈ P.intervalBox.realizations) : 0 < A.det := by
  rw [intervalBox_matrix_recovery P A hA]
  exact all_parameter_determinant_positive P _ (parametersOf_in_cube P A hA)

theorem intervalBox_partition_threshold (P : IntegerPartition) :
    P.HasPartition ↔ ∃ A ∈ P.intervalBox.realizations, (P.threshold : ℝ) ≤ A.det := by
  rw [partition_determinant_threshold P]
  constructor
  · rintro ⟨q,hq,hdet⟩
    exact ⟨P.layerMatrix q,layerMatrix_in_intervalBox P q hq,hdet⟩
  · rintro ⟨A,hA,hdet⟩
    refine ⟨P.parametersOf A,parametersOf_in_cube P A hA,?_⟩
    simpa only [← intervalBox_matrix_recovery P A hA] using hdet

theorem intervalBox_tridiagonal (P : IntegerPartition) (A : Mat P.layerCount)
    (hA : A ∈ P.intervalBox.realizations) : Tridiagonal A := by
  rw [intervalBox_matrix_recovery P A hA]
  exact continuantMatrix_tridiagonal _ _ _

theorem intervalBox_nonempty (P : IntegerPartition) : P.intervalBox.realizations.Nonempty :=
  rational_box_nonempty P.intervalBox

theorem intervalBox_compact (P : IntegerPartition) : IsCompact P.intervalBox.realizations :=
  rational_box_compact P.intervalBox

theorem intervalBox_superdiagonal (P : IntegerPartition) (A : Mat P.layerCount)
    (hA : A ∈ P.intervalBox.realizations) (i j : Fin P.layerCount)
    (hj : j.val=i.val+1) : A i j=1 := by
  rw [intervalBox_matrix_recovery P A hA]
  have hne : i ≠ j := by intro h; subst j; omega
  simp only [layerMatrix,continuantMatrix,if_neg hne,if_pos hj]

theorem intervalBox_attained_maximum (P : IntegerPartition) :
    ∃ A ∈ P.intervalBox.realizations,
      IsGreatest (Matrix.det '' P.intervalBox.realizations) A.det ∧
        (P.HasPartition ↔ (P.threshold : ℝ) ≤ A.det) := by
  obtain ⟨A,hA,hmax⟩ := (intervalBox_compact P).exists_isMaxOn
    (intervalBox_nonempty P) continuous_id.matrix_det.continuousOn
  refine ⟨A,hA,⟨⟨A,hA,rfl⟩,?_⟩,?_⟩
  · rintro d ⟨B,hB,rfl⟩
    exact hmax hB
  · constructor
    · intro hp
      obtain ⟨B,hB,hdet⟩ := (intervalBox_partition_threshold P).mp hp
      exact hdet.trans (hmax hB)
    · intro hdet
      exact (intervalBox_partition_threshold P).mpr ⟨A,hA,hdet⟩

theorem intervalBox_vertex_maximum (P : IntegerPartition) :
    ∃ q : ℕ → ℝ, P.IsVertex q ∧ P.InCube q ∧
      IsGreatest (Matrix.det '' P.intervalBox.realizations) (P.layerMatrix q).det := by
  obtain ⟨A,hA,hmax,_⟩ := intervalBox_attained_maximum P
  obtain ⟨q,hq,hdet⟩ := determinant_vertex_above P (P.parametersOf A) (parametersOf_in_cube P A hA)
  have hc : P.InCube q := by
    intro i hi
    rcases hq i hi with h | h <;> simp [h]
  have hqa := layerMatrix_in_intervalBox P q hc
  have he : (P.layerMatrix q).det=A.det := by
    have hb := hmax.2 ⟨P.layerMatrix q,hqa,rfl⟩
    rw [← intervalBox_matrix_recovery P A hA] at hdet
    exact le_antisymm hb hdet
  refine ⟨q,hq,hc,?_⟩
  rw [he]
  exact hmax

end IV04.Paper.IntegerPartition
