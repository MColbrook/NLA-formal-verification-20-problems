module

public import NLA.PF02.JointCompactness.Closed
public import Mathlib.Topology.Order.Compact

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02JointCompactness
open Matrix Reference.PF02Support Reference.PF02Normalization
open scoped BigOperators MatrixOrder

theorem joint_normalized_factor_set_isCompact {p q k : ℕ}
    (M : ℝ → Matrix (Fin p) (Fin q) ℝ) (hM : Continuous M) (a b : ℝ) :
    IsCompact (jointNormalizedFactorSet (k := k) M a b) := by
  classical
  by_cases hn : (Set.Icc a b).Nonempty
  · have hmax : ∀ j : Fin q, ∃ x ∈ Set.Icc a b,
        IsMaxOn (fun η => ∑ i, M η i j) (Set.Icc a b) x := by
      intro j
      apply isCompact_Icc.exists_isMaxOn hn
      apply Continuous.continuousOn
      fun_prop
    choose x hx hmax using hmax
    let c : Fin q → ℝ := fun j => ∑ i, M (x j) i j
    let RA : Set (Fin p → Mat (Fin k)) := {A | ∀ i u v, A i u v ∈ Set.Icc (-(k : ℝ)) k}
    let RB : Set (Fin q → Mat (Fin k)) := {B | ∀ j u v, B j u v ∈ Set.Icc (-(c j)) (c j)}
    have hca : IsCompact RA :=
      isCompact_pi_infinite fun i => isCompact_pi_infinite fun u => isCompact_pi_infinite fun v => isCompact_Icc
    have hcb : IsCompact RB :=
      isCompact_pi_infinite fun j => isCompact_pi_infinite fun u => isCompact_pi_infinite fun v => isCompact_Icc
    apply (isCompact_Icc.prod (hca.prod hcb)).of_isClosed_subset
      (joint_normalized_factor_set_isClosed M hM a b)
    intro Z hZ
    rcases hZ with ⟨hη, hF⟩
    have hbnd := normalized_factor_entries_bound (M Z.1) Z.2 hF
    refine ⟨hη, ?_, ?_⟩
    · intro i u v
      exact abs_le.mp (hbnd.1 i u v)
    · intro j u v
      exact abs_le.mp ((hbnd.2 j u v).trans (hmax j hη))
  · have he : jointNormalizedFactorSet (k := k) M a b = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro Z hZ
      exact hn ⟨Z.1, hZ.1⟩
    rw [he]
    exact isCompact_empty

theorem continuous_perturbed_gram {p k : ℕ} (F : Fin p → Mat (Fin k)) :
    Continuous (perturbedGram F) := by
  unfold perturbedGram
  fun_prop

theorem joint_perturbed_gram_isCompact {p k : ℕ} (F : Fin p → Mat (Fin k)) (a b : ℝ) :
    IsCompact (jointNormalizedFactorSet (k := k) (perturbedGram F) a b) :=
  joint_normalized_factor_set_isCompact (perturbedGram F) (continuous_perturbed_gram F) a b

#print axioms joint_normalized_factor_set_isCompact
#print axioms continuous_perturbed_gram
#print axioms joint_perturbed_gram_isCompact
end Reference.PF02JointCompactness
