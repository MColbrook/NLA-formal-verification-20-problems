module

public import NLA.MD06.NonbacktrackingWalkExposure.WordFiberDefinitions
public import NLA.MD06.NonbacktrackingWalkExposure.PortChoices

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration Reference.MD06Nonbacktracking
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_word_count_zero {n : ℕ} (p : Pairing n) (a b : Dart n) :
    WordCount p 0 a b = if a=b then 1 else 0 := by
  by_cases h : a=b
  · subst b;simp [WordCount,WordRun]
  · simp [WordCount,WordRun,h]

theorem actual_word_count_succ {n : ℕ} (p : Pairing n) (t : ℕ) (a b : Dart n) :
    WordCount p (t+1) a b = ∑ i : Fin 2, WordCount p t (PortChoice (p.val a) i) b := by
  simp only [WordCount]
  rw [Fintype.card_congr (WordFiberSplit p t a b),Fintype.card_sigma]

theorem actual_word_matrix_entry {n : ℕ} (p : Pairing n) (t : ℕ) (a b : Dart n) :
    (NonbacktrackingMatrix p ^ t) a b = (WordCount p t a b : ℝ) := by
  induction t generalizing a b with
  | zero =>
    rw [pow_zero,actual_word_count_zero]
    simp [Matrix.one_apply]
  | succ t ih =>
    rw [pow_succ',actual_binary_nonbacktracking_mul,ih,ih,actual_word_count_succ]
    simp [Fin.sum_univ_succ]

theorem actual_closed_word_trace {n : ℕ} (p : Pairing n) (t : ℕ) :
    Matrix.trace (NonbacktrackingMatrix p ^ t) = (ClosedWordCount p t : ℝ) := by
  simp [Matrix.trace,ClosedWordCount,actual_word_matrix_entry]

theorem actual_word_count_le {n : ℕ} (p : Pairing n) (t : ℕ) (a b : Dart n) :
    WordCount p t a b ≤ 2^t := by
  simpa [WordCount] using (Fintype.card_subtype_le (fun w : Fin t → Fin 2 => WordRun p a t w=b))

#print axioms actual_word_count_zero

#print axioms actual_word_count_succ

#print axioms actual_word_matrix_entry

#print axioms actual_closed_word_trace

#print axioms actual_word_count_le
end Reference.MD06WalkExposure
