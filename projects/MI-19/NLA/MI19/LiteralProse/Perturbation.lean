module

public import NLA.MI19.LiteralProse.Polynomials
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Filter Topology
namespace NLA.MI19.LiteralProse

theorem qPermanent_continuous {n : ℕ} (q : ℝ) :
    Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => qPermanent q A) := by
  unfold qPermanent qPermanentTerm
  fun_prop

theorem restrictedQPermanent_continuous {n : ℕ} (q : ℝ) (S : Finset (Fin n)) :
    Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => restrictedQPermanent q A S) := by
  unfold restrictedQPermanent qPermanentTerm
  fun_prop

theorem real_qPermanent {n : ℕ} (q : ℝ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, (A i j).im = 0) : (qPermanent q A).im = 0 := by
  have he : A = fun i j => ((A i j).re : ℂ) := by
    funext i j
    exact Complex.ext rfl (by simpa using hA i j)
  rw [he]
  unfold qPermanent qPermanentTerm
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_prod, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, Complex.ofReal_im]

theorem real_restrictedQPermanent {n : ℕ} (q : ℝ) (A : Matrix (Fin n) (Fin n) ℂ)
    (S : Finset (Fin n)) (hA : ∀ i j, (A i j).im = 0) :
    (restrictedQPermanent q A S).im = 0 := by
  have he : A = fun i j => ((A i j).re : ℂ) := by
    funext i j
    exact Complex.ext rfl (by simpa using hA i j)
  rw [he]
  unfold restrictedQPermanent qPermanentTerm
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_prod, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, Complex.ofReal_im]

theorem positive_definite_perturbations :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      (witness + (ε : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)).PosDef ∧
      qPermanent witnessQ (witness + (ε : ℂ) • 1) <
        restrictedQPermanent witnessQ (witness + (ε : ℂ) • 1) witnessSubset := by
  let A : ℝ → Matrix (Fin 4) (Fin 4) ℂ := fun ε => witness + (ε : ℂ) • 1
  have hA : Continuous A := by dsimp [A]; fun_prop
  have hc : Continuous (fun ε => (qPermanent witnessQ (A ε) -
      restrictedQPermanent witnessQ (A ε) witnessSubset).re) :=
    Complex.continuous_re.comp (((qPermanent_continuous witnessQ).comp hA).sub
      ((restrictedQPermanent_continuous witnessQ witnessSubset).comp hA))
  have hn : (qPermanent witnessQ (A 0) - restrictedQPermanent witnessQ (A 0) witnessSubset).re < 0 := by
    simpa [A,exact_gap] using strict_scalar_gap
  have he := (isOpen_lt hc continuous_const).mem_nhds hn
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ,hδ,?_⟩
  intro ε hε hεδ
  have hgap := hd (show ε ∈ Metric.ball (0 : ℝ) δ by simpa [Real.dist_eq,abs_of_pos hε] using hεδ)
  have ha : ∀ i j, (A ε i j).im = 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [A,witness]
  have hpos : ((ε : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (Complex.real_lt_real.mpr hε)
  refine ⟨Matrix.PosDef.posSemidef_add witness_posSemidef hpos,?_⟩
  · apply Complex.lt_def.mpr
    refine ⟨?_,?_⟩
    · simpa only [Set.mem_ofPred_eq, A, Complex.sub_re, sub_neg] using hgap
    · exact (real_qPermanent witnessQ (A ε) ha).trans
        (real_restrictedQPermanent witnessQ (A ε) witnessSubset ha).symm

end NLA.MI19.LiteralProse
