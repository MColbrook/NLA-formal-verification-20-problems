module

public import NLA.MD06.LaplacianSpectralGap.BottomKernel
public import NLA.MD06.QuantitativeCorrection.QuantitativeCorrection

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Spectral
open Reference.MD06Correction Reference.MD06Actual Matrix
open scoped BigOperators

theorem actual_sorted_laplacian_gap_rayleigh_lower {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : G.Connected) (hn : 2 ≤ n) (z : Configuration n) (hz : (∑ i, z i) = 0) :
    LaplacianGap G hn * ‖z‖^2 ≤ LaplacianQuadratic G (fun i => z i) := by
  have hp : 0 < n := by omega
  have hc : (LaplacianEigenbasis G).repr z ⟨n-1,by omega⟩ = 0 :=
    (actual_connected_bottom_repr_zero_iff_mean_zero G hg hp z).mpr hz
  have he : (∑ i, ((LaplacianEigenbasis G).repr z i)^2) = ‖z‖^2 := by
    rw [← EuclideanSpace.real_norm_sq_eq,(LaplacianEigenbasis G).repr.norm_map]
  calc
    LaplacianGap G hn*‖z‖^2 = ∑ i, LaplacianGap G hn*((LaplacianEigenbasis G).repr z i)^2 := by
      rw [← he,Finset.mul_sum]
    _ ≤ ∑ i, LaplacianEigenvalues G i*((LaplacianEigenbasis G).repr z i)^2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i = (⟨n-1,by omega⟩ : Fin n)
      · subst i
        simp only [hc,zero_pow (by norm_num : 2 ≠ 0),mul_zero,le_refl]
      · have hive : i.val ≠ n-1 := fun h => hi (Fin.ext h)
        have hb : i ≤ (⟨n-2,by omega⟩ : Fin n) := by change i.val ≤ n-2;omega
        exact mul_le_mul_of_nonneg_right (actual_laplacian_eigenvalues_antitone G hb) (sq_nonneg _)
    _ = LaplacianQuadratic G (fun i => z i) := (actual_laplacian_diagonal_quadratic G z).symm

theorem actual_sorted_laplacian_gap_positive {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : G.Connected) (hn : 2 ≤ n) : 0 < LaplacianGap G hn := by
  have hp : 0 < n := by omega
  have hne : (⟨n-2,by omega⟩ : Fin n) ≠ ⟨n-1,by omega⟩ := by
    intro h
    have he := congrArg Fin.val h
    change n-2 = n-1 at he
    omega
  have hz := actual_connected_other_eigenbasis_mean_zero G hg hp ⟨n-2,by omega⟩ hne
  have ht := actual_connected_mean_zero_laplacian_positive G hg (LaplacianEigenbasis G ⟨n-2,by omega⟩)
    hz ((LaplacianEigenbasis G).orthonormal.ne_zero ⟨n-2,by omega⟩)
  rw [actual_laplacian_eigenvalue_quadratic] at ht
  exact ht

theorem actual_sorted_laplacian_gap_attained {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : G.Connected) (hn : 2 ≤ n) :
    ∃ z : Configuration n, (∑ i, z i) = 0 ∧ ‖z‖ = 1 ∧
      LaplacianQuadratic G (fun i => z i) = LaplacianGap G hn := by
  have hp : 0 < n := by omega
  have hne : (⟨n-2,by omega⟩ : Fin n) ≠ ⟨n-1,by omega⟩ := by
    intro h
    have he := congrArg Fin.val h
    change n-2 = n-1 at he
    omega
  exact ⟨LaplacianEigenbasis G ⟨n-2,by omega⟩,
    actual_connected_other_eigenbasis_mean_zero G hg hp _ hne,
    (LaplacianEigenbasis G).orthonormal.1 _,actual_laplacian_eigenvalue_quadratic G _⟩

theorem actual_sorted_gap_bound_implies_true_rayleigh_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : G.Connected) (hn : 2 ≤ n) (gamma : ℝ) (hgamma : gamma ≤ LaplacianGap G hn) :
    ∀ z : Configuration n, (∑ i, z i) = 0 →
      gamma * ‖z‖^2 ≤ LaplacianQuadratic G (fun i => z i) := by
  intro z hz
  exact (mul_le_mul_of_nonneg_right hgamma (sq_nonneg ‖z‖)).trans
    (actual_sorted_laplacian_gap_rayleigh_lower G hg hn z hz)

theorem actual_sorted_gap_rayleigh_bound_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : G.Connected) (hn : 2 ≤ n) (gamma : ℝ) :
    (∀ z : Configuration n, (∑ i, z i) = 0 →
      gamma * ‖z‖^2 ≤ LaplacianQuadratic G (fun i => z i)) ↔ gamma ≤ LaplacianGap G hn := by
  constructor
  · intro h
    obtain ⟨z,hz,hnorm,hq⟩ := actual_sorted_laplacian_gap_attained G hg hn
    have he := h z hz
    simpa only [hnorm,one_pow,mul_one,hq] using he
  · exact actual_sorted_gap_bound_implies_true_rayleigh_bound G hg hn gamma

theorem actual_sorted_gap_quantitative_correction {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : G.Connected) (hn : 2 ≤ n) (gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : gamma ≤ LaplacianGap G hn)
    (phi : Configuration n) (c : ℝ) (hc : 0 < c)
    (hcos : ∀ i j, G.Adj i j → c ≤ Real.cos (phi i-phi j))
    (hsmall : ‖GradientVector G phi‖ < c^2*gamma/(4*Real.sqrt 2)) :
    ∃ h : Configuration n, (∑ i, h i) = 0 ∧ ‖h‖ < c/(2*Real.sqrt 2) ∧
      (∀ i, Gradient G (PhaseLift (fun a => phi a+h a)) i = 0) ∧
      IsLocalMin (Energy G) (PhaseLift (fun a => phi a+h a)) ∧
      (∀ i j, G.Adj i j → c/2 ≤ Real.cos ((phi i+h i)-(phi j+h j))) ∧
      ∀ z : Configuration n, (∑ i, z i) = 0 →
        (c*gamma/2)*‖z‖^2 ≤ HessianQuadratic G (PhaseLift (fun a => phi a+h a)) (fun i => z i) :=
  actual_quantitative_correction_from_true_rayleigh_bound G gamma hgamma
    (actual_sorted_gap_bound_implies_true_rayleigh_bound G hg hn gamma hgap) phi c hc hcos hsmall

#print axioms actual_sorted_laplacian_gap_rayleigh_lower
#print axioms actual_sorted_laplacian_gap_positive
#print axioms actual_sorted_laplacian_gap_attained
#print axioms actual_sorted_gap_bound_implies_true_rayleigh_bound
#print axioms actual_sorted_gap_rayleigh_bound_iff
#print axioms actual_sorted_gap_quantitative_correction
end Reference.MD06Spectral
