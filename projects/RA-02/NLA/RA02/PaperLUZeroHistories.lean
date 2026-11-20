module

public import NLA.RA02.PaperLUMass

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.RA02.Paper

theorem lu_zero_entry_mass {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n)
    (hij : A i j = 0) : NLA.RA03.pivotMass (complexify A) (some (i,j)) = 0 := by
  simp only [NLA.RA03.pivotMass]
  split_ifs <;> simp [complexify, hij]

theorem crossUpdate_zero_row {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i p q : Fin n)
    (hi : ∀ j, A i j = 0) : ∀ j, crossUpdate A p q i j = 0 := by
  intro j
  simp [crossUpdate, hi]

theorem crossUpdate_zero_col {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (j p q : Fin n)
    (hj : ∀ i, A i j = 0) : ∀ i, crossUpdate A p q i j = 0 := by
  intro i
  simp [crossUpdate, hj]

theorem crossUpdate_pivot_row {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n)
    (hpq : A p q ≠ 0) : ∀ j, crossUpdate A p q p j = 0 := by
  intro j
  simp [crossUpdate, mul_div_cancel_left₀ _ hpq]

theorem crossUpdate_pivot_col {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n)
    (hpq : A p q ≠ 0) : ∀ i, crossUpdate A p q i q = 0 := by
  intro i
  simp [crossUpdate, hpq]

theorem lu_zero_row_mass {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (hi : ∀ j, A i j = 0) (w : List (Fin n × Fin n))
    (hw : i ∈ w.map Prod.fst) : luListMass A (w.map some) = 0 := by
  induction w generalizing A with
  | nil => simp at hw
  | cons p w ih =>
    simp only [List.map_cons, List.mem_cons] at hw
    rw [List.map_cons, luListMass, realLUNext]
    rcases hw with hip | him
    · have hp : A p.1 p.2 = 0 := by rw [← hip]; exact hi p.2
      rw [lu_zero_entry_mass A p.1 p.2 hp, zero_mul]
    · rw [ih (crossUpdate A p.1 p.2) (crossUpdate_zero_row A i p.1 p.2 hi) him, mul_zero]

theorem lu_zero_col_mass {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (j : Fin n) (hj : ∀ i, A i j = 0) (w : List (Fin n × Fin n))
    (hw : j ∈ w.map Prod.snd) : luListMass A (w.map some) = 0 := by
  induction w generalizing A with
  | nil => simp at hw
  | cons p w ih =>
    simp only [List.map_cons, List.mem_cons] at hw
    rw [List.map_cons, luListMass, realLUNext]
    rcases hw with hjp | him
    · have hp : A p.1 p.2 = 0 := by rw [← hjp]; exact hj p.1
      rw [lu_zero_entry_mass A p.1 p.2 hp, zero_mul]
    · rw [ih (crossUpdate A p.1 p.2) (crossUpdate_zero_col A j p.1 p.2 hj) him, mul_zero]

theorem lu_repeated_row_mass {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (w : List (Fin n × Fin n)) (hw : ¬(w.map Prod.fst).Nodup) :
    luListMass A (w.map some) = 0 := by
  induction w generalizing A with
  | nil => simp at hw
  | cons p w ih =>
    rw [List.map_cons, luListMass, realLUNext]
    by_cases hp : A p.1 p.2 = 0
    · rw [lu_zero_entry_mass A p.1 p.2 hp, zero_mul]
    · by_cases hmem : p.1 ∈ w.map Prod.fst
      · rw [lu_zero_row_mass (crossUpdate A p.1 p.2) p.1 (crossUpdate_pivot_row A p.1 p.2 hp) w hmem, mul_zero]
      · have ht : ¬(w.map Prod.fst).Nodup := by simpa [List.nodup_cons, hmem] using hw
        rw [ih (crossUpdate A p.1 p.2) ht, mul_zero]

theorem lu_repeated_col_mass {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (w : List (Fin n × Fin n)) (hw : ¬(w.map Prod.snd).Nodup) :
    luListMass A (w.map some) = 0 := by
  induction w generalizing A with
  | nil => simp at hw
  | cons p w ih =>
    rw [List.map_cons, luListMass, realLUNext]
    by_cases hp : A p.1 p.2 = 0
    · rw [lu_zero_entry_mass A p.1 p.2 hp, zero_mul]
    · by_cases hmem : p.2 ∈ w.map Prod.snd
      · rw [lu_zero_col_mass (crossUpdate A p.1 p.2) p.2 (crossUpdate_pivot_col A p.1 p.2 hp) w hmem, mul_zero]
      · have ht : ¬(w.map Prod.snd).Nodup := by simpa [List.nodup_cons, hmem] using hw
        rw [ih (crossUpdate A p.1 p.2) ht, mul_zero]

theorem realLUListPath_zero {n : ℕ} (w : List (Option (Fin n × Fin n))) :
    realLUListPath (0 : Matrix (Fin n) (Fin n) ℝ) w = 0 := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    cases p with
    | none => exact ih
    | some p =>
      have hz : crossUpdate (0 : Matrix (Fin n) (Fin n) ℝ) p.1 p.2 = 0 := by
        ext i j
        simp [crossUpdate]
      change realLUListPath (crossUpdate 0 p.1 p.2) w = 0
      rw [hz, ih]

theorem lu_none_residual {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (w : List (Option (Fin n × Fin n))) (hw : none ∈ w) : realLUListPath A w = 0 := by
  induction w generalizing A with
  | nil => simp at hw
  | cons p w ih =>
    rcases List.mem_cons.mp hw with hp | him
    · subst p
      exact realLUListPath_zero w
    · exact ih (realLUNext A p) him

#print axioms lu_repeated_row_mass
end NLA.RA02.Paper
