module

public import NLA.PF02.UniformPositiveOrientation.NormalizedActual

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02GlobalOrientation Reference.PF02BlockConstruction Reference.PF02Normalization Set Filter
open scoped Topology

theorem actual_factor_normalization_continuous {p q k : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (hR : M.rank = k*(k+1)/2) :
    Continuous (fun F : NLA.PF02.Factorization M k =>
      (normalizedRow F.val.1,normalizedColumn F.val.1 F.val.2)) :=
  (continuousOn_normalization_pair p q k).comp_continuous continuous_subtype_val
    (fun F => actual_factor_row_sum_posDef M hR F)

theorem continuous_leading_orientation (r : ℕ) :
    Continuous (fun F : FactorPair (Fintype.card (BlockIndex r)) (Fintype.card (BlockIndex r)) (3+r) =>
      orientationPolynomial (leadingRows (r := r) F.1)) := by
  apply (continuous_orientation_polynomial (3+r)).comp
  unfold leadingRows Reference.PF02BlockSupportRecovery.blockRows
  fun_prop

theorem actual_continuous_normalized_fiber_sign {r : ℕ} {η : ℝ} (h : regularParameter r η) :
    Continuous (normalizedFiberSign (r := r) (η := η)) := by
  have hnorm : Continuous (fun F : NLA.PF02.Factorization (perturbedBlockGram r η) (3+r) =>
      normalizedRow F.val.1) :=
    continuous_fst.comp (actual_factor_normalization_continuous
      (p := Fintype.card (BlockIndex r)) (q := Fintype.card (BlockIndex r)) (k := 3+r)
      (perturbedBlockGram r η) h.1)
  have hlead : Continuous (fun A : Fin (Fintype.card (BlockIndex r)) → Matrix (Fin (3+r)) (Fin (3+r)) ℝ =>
      orientationPolynomial (leadingRows (r := r) A)) := by
    apply (continuous_orientation_polynomial (3+r)).comp
    unfold leadingRows Reference.PF02BlockSupportRecovery.blockRows
    fun_prop
  have hc : Continuous (fun F : NLA.PF02.Factorization (perturbedBlockGram r η) (3+r) =>
      orientationPolynomial (leadingRows (r := r) (normalizedRow F.val.1))) := hlead.comp hnorm
  apply continuous_iff_continuousAt.mpr
  intro F
  by_cases hp : 0 < orientationPolynomial (leadingRows (r := r) (normalizedRow F.val.1))
  · have he : ∀ᶠ G in 𝓝 F, 0 < orientationPolynomial (leadingRows (r := r) (normalizedRow G.val.1)) :=
      (isOpen_lt continuous_const hc).mem_nhds hp
    apply (continuousAt_const (y := true)).congr_of_eventuallyEq
    exact he.mono (fun G hG => by simp [normalizedFiberSign,hG])
  · have hn : orientationPolynomial (leadingRows (r := r) (normalizedRow F.val.1)) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hp) (actual_normalized_orientation_ne_zero h F)
    have he : ∀ᶠ G in 𝓝 F, orientationPolynomial (leadingRows (r := r) (normalizedRow G.val.1)) < 0 :=
      (isOpen_lt hc continuous_const).mem_nhds hn
    apply (continuousAt_const (y := false)).congr_of_eventuallyEq
    exact he.mono (fun G hG => by simp [normalizedFiberSign,not_lt_of_gt hG])

#print axioms actual_factor_normalization_continuous
#print axioms continuous_leading_orientation
#print axioms actual_continuous_normalized_fiber_sign
end Reference.PF02UniformPositiveOrientation
