module

public import NLA.PF02.JointCompactness.Definitions
public import NLA.PF02.Normalization.Compactness

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02JointCompactness
open Matrix Reference.PF02Support Reference.PF02Normalization
open scoped BigOperators MatrixOrder

theorem normalized_constraint_set_isClosed (p q k : ℕ) :
    IsClosed (normalizedConstraintSet (p := p) (q := q) (k := k)) := by
  have hp := psd_set_isClosed k
  have ha : IsClosed {Z : (Matrix (Fin p) (Fin q) ℝ × FactorPair p q k) | ∀ i, (Z.2.1 i).PosSemidef} := by
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    have hf : Continuous (fun Z : (Matrix (Fin p) (Fin q) ℝ × FactorPair p q k) => Z.2.1 i) := by fun_prop
    exact hp.preimage hf
  have hb : IsClosed {Z : (Matrix (Fin p) (Fin q) ℝ × FactorPair p q k) | ∀ j, (Z.2.2 j).PosSemidef} := by
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro j
    have hf : Continuous (fun Z : (Matrix (Fin p) (Fin q) ℝ × FactorPair p q k) => Z.2.2 j) := by fun_prop
    exact hp.preimage hf
  have hs : IsClosed {Z : (Matrix (Fin p) (Fin q) ℝ × FactorPair p q k) | rowSum Z.2.1 = 1} :=
    isClosed_eq ((continuous_row_sum p k).comp (continuous_fst.comp continuous_snd)) continuous_const
  have ht : IsClosed {Z : (Matrix (Fin p) (Fin q) ℝ × FactorPair p q k) | ∀ i j, Matrix.trace (Z.2.1 i * Z.2.2 j) = Z.1 i j} := by
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro j
    apply isClosed_eq
    all_goals fun_prop
  exact ha.inter (hb.inter (hs.inter ht))

theorem joint_normalized_factor_set_isClosed {p q k : ℕ}
    (M : ℝ → Matrix (Fin p) (Fin q) ℝ) (hM : Continuous M) (a b : ℝ) :
    IsClosed (jointNormalizedFactorSet (k := k) M a b) := by
  have hc : Continuous (fun Z : ℝ × FactorPair p q k => (M Z.1, Z.2)) :=
    (hM.comp continuous_fst).prodMk continuous_snd
  exact (isClosed_Icc.preimage (show Continuous (fun Z : ℝ × FactorPair p q k => Z.1) from continuous_fst)).inter
    ((normalized_constraint_set_isClosed p q k).preimage hc)

theorem normalized_factor_entries_bound {p q k : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (F : FactorPair p q k)
    (hF : F ∈ normalizedFactorSet M) :
    (∀ i a b, |F.1 i a b| ≤ k) ∧ (∀ j a b, |F.2 j a b| ≤ ∑ i, M i j) := by
  rcases hF with ⟨hA, hB, hsum, htrace⟩
  have hpd : (rowSum F.1).PosDef := by rw [hsum]; exact Matrix.PosDef.one
  constructor
  · intro i a b
    simpa only [normalizedRow, rootSum, hsum, CFC.sqrt_one, inv_one, Matrix.one_mul, Matrix.mul_one]
      using normalized_row_entry_bound F.1 hA hpd i a b
  · intro j a b
    simpa only [normalizedColumn, rootSum, hsum, CFC.sqrt_one, Matrix.one_mul, Matrix.mul_one]
      using normalized_column_entry_bound M F.1 F.2 hA hB hpd htrace j a b

#print axioms normalized_constraint_set_isClosed
#print axioms joint_normalized_factor_set_isClosed
#print axioms normalized_factor_entries_bound
end Reference.PF02JointCompactness
