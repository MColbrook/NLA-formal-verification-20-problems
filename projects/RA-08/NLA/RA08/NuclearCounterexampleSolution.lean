module

public import NLA.RA08.PaperNuclearCounterexample

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem verified_nuclear_spectralCombination_nonnegative {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) :
    nuclearNorm (spectralCombination d v)=∑ i, v i := by
  exact nuclear_spectralCombination_nonnegative d v hv

theorem verified_nuclear_truncation_last {n : ℕ} {A : RealMatrix (n+1)}
    (d : OrderedSpectralData A) :
    nuclearNorm (A-truncation d n)=d.eigenvalues (Fin.last n) := by
  exact nuclear_truncation_last d

theorem verified_nuclear_functionTruncation_last {n : ℕ} {A : RealMatrix (n+1)}
    (d : OrderedSpectralData A) (f : ℝ → ℝ)
    (hf : ∀ i, 0 ≤ f (d.eigenvalues i)) :
    nuclearNorm (functionalCalculus f A-functionTruncation d f n)=
      f (d.eigenvalues (Fin.last n)) := by
  exact nuclear_functionTruncation_last d f hf

theorem verified_nuclearLiftSmallest_eq_last (m : ℕ) (η t : ℝ)
    (d : OrderedSpectralData (nuclearLiftA m η t)) :
    nuclearLiftSmallest m η t=d.eigenvalues (Fin.last (m+m)) := by
  exact nuclearLiftSmallest_eq_last m η t d

theorem verified_nuclearLift_ordered_exists (m : ℕ) (η t : ℝ) (hη : η < 1) (ht : 0 < t) :
    Nonempty (OrderedSpectralData (nuclearLiftA m η t)) := by
  exact nuclearLift_ordered_exists m η t hη ht

theorem verified_nuclearLift_truncation_tail (m : ℕ) (η t : ℝ)
    (d : OrderedSpectralData (nuclearLiftA m η t)) :
    nuclearNorm (nuclearLiftA m η t-truncation d (m+m))=nuclearLiftSmallest m η t := by
  exact nuclearLift_truncation_tail m η t d

theorem verified_nuclearLift_clipping_tail (m : ℕ) (η t : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1/4)
    (d : OrderedSpectralData (nuclearLiftA m η t)) :
    nuclearNorm (functionalCalculus witnessFunction (nuclearLiftA m η t)-
      functionTruncation d witnessFunction (m+m))=nuclearLiftSmallest m η t := by
  exact nuclearLift_clipping_tail m η t hη0 hη1 ht0 ht1 d

theorem verified_frobeniusNorm_spectral_bound (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ A : RealMatrix n, frobeniusNorm A ≤ K*spectralNorm A := by
  exact frobeniusNorm_spectral_bound n

theorem verified_nuclearNorm_spectral_bound (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ A : RealMatrix n, nuclearNorm A ≤ K*spectralNorm A := by
  exact nuclearNorm_spectral_bound n

theorem verified_clipping_nuclear_quadratic_remainder {n : ℕ} (b : Fin n → ℝ)
    (hb : ∀ i, b i ≠ 1) (E : RealMatrix n) (hE : E.IsHermitian) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      nuclearNorm (functionalCalculus witnessFunction (Matrix.diagonal b+t • E)-
        functionalCalculus witnessFunction (Matrix.diagonal b)-t • clippingDerivative b E) ≤ C*t^2 := by
  exact clipping_nuclear_quadratic_remainder b hb E hE

theorem verified_clippingDividedDifference_symmetric (x y : ℝ) :
    clippingDividedDifference x y=clippingDividedDifference y x := by
  exact clippingDividedDifference_symmetric x y

theorem verified_clippingDerivative_isHermitian {n : ℕ} (b : Fin n → ℝ)
    (E : RealMatrix n) (hE : E.IsHermitian) : (clippingDerivative b E).IsHermitian := by
  exact clippingDerivative_isHermitian b E hE

theorem verified_nuclearLiftDerivative_prefix (m : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (i j : Fin (m+m)) :
    nuclearLiftDerivative m η i.castSucc j.castSucc=η*nuclearDerivative m i j := by
  exact nuclearLiftDerivative_prefix m η hη i j

theorem verified_nuclearLiftDerivative_last (m : ℕ) (η : ℝ) (hη : η ≤ 1) :
    nuclearLiftDerivative m η (Fin.last (m+m)) (Fin.last (m+m))=1-η := by
  exact nuclearLiftDerivative_last m η hη

theorem verified_nuclearLiftDerivative_isHermitian (m : ℕ) (η : ℝ) :
    (nuclearLiftDerivative m η).IsHermitian := by
  exact nuclearLiftDerivative_isHermitian m η

theorem verified_nuclearLiftOutput_isHermitian (m : ℕ) (η t : ℝ) :
    (nuclearLiftOutput m η t).IsHermitian := by
  exact nuclearLiftOutput_isHermitian m η t

theorem verified_nuclearLift_nuclear_remainder (m : ℕ) (η : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      nuclearNorm (nuclearLiftOutput m η t-t • nuclearLiftDerivative m η) ≤ C*t^2 := by
  exact nuclearLift_nuclear_remainder m η

theorem verified_nuclearLiftUnitary_unitary {n : ℕ} (R : RealMatrix n)
    (hR : R ∈ Matrix.unitaryGroup (Fin n) ℝ) :
    nuclearLiftUnitary R ∈ Matrix.unitaryGroup (Fin (n+1)) ℝ := by
  exact nuclearLiftUnitary_unitary R hR

theorem verified_nuclearLiftUnitary_trace {n : ℕ} (R : RealMatrix n) (G : RealMatrix (n+1)) :
    (nuclearLiftUnitary R*G).trace=
      (R*G.submatrix Fin.castSucc Fin.castSucc).trace+G (Fin.last n) (Fin.last n) := by
  exact nuclearLiftUnitary_trace R G

theorem verified_nuclearLiftDerivative_trace (m : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (nuclearLiftUnitary (functionalCalculus realSign (nuclearDerivative m))*
      nuclearLiftDerivative m η).trace=η*nuclearNorm (nuclearDerivative m)+1-η := by
  exact nuclearLiftDerivative_trace m η hη0 hη1

theorem verified_nuclearLiftDerivative_nuclear_lower (m : ℕ) (η : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    η*nuclearNorm (nuclearDerivative m)+1-η ≤ nuclearNorm (nuclearLiftDerivative m η) := by
  exact nuclearLiftDerivative_nuclear_lower m η hη0 hη1

theorem verified_nuclearLiftOutput_lower (m : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t →
      t*(η*nuclearNorm (nuclearDerivative m)+1-η)-K*t^2 ≤
        nuclearNorm (nuclearLiftOutput m η t) := by
  exact nuclearLiftOutput_lower m η hη0 hη1

theorem verified_nuclear_choose_eta (ε₀ : ℝ) (hε : 0 < ε₀) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ 1 < (1-η)*(1+ε₀) := by
  exact nuclear_choose_eta ε₀ hε

theorem verified_nuclear_small_time (η D K C ε₀ : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hε : 0 < ε₀) (hgap : 1 < (1-η)*(1+ε₀)) (hD : C < D) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1/4 ∧ ∀ a : ℝ, 0 < a →
      nuclearLiftTailLower η t ≤ a → a ≤ (1-η)*t →
      0 < t/a-1 ∧ t/a-1 < ε₀ ∧ t=(1+(t/a-1))*a ∧
      (1+C*(t/a-1))*a < t*(η*D+1-η)-K*t^2 := by
  exact nuclear_small_time η D K C ε₀ hη0 hη1 hK hC hε hgap hD

theorem verified_paper_nuclear_counterexample (C ε₀ : ℝ) (hC : 0 ≤ C) (hε : 0 < ε₀) :
    NuclearTransferFailure C ε₀ := by
  exact paper_nuclear_counterexample C ε₀ hC hε

#print axioms NLA.RA08.Paper.verified_nuclear_spectralCombination_nonnegative
#print axioms NLA.RA08.Paper.verified_nuclear_truncation_last
#print axioms NLA.RA08.Paper.verified_nuclear_functionTruncation_last
#print axioms NLA.RA08.Paper.verified_nuclearLiftSmallest_eq_last
#print axioms NLA.RA08.Paper.verified_nuclearLift_ordered_exists
#print axioms NLA.RA08.Paper.verified_nuclearLift_truncation_tail
#print axioms NLA.RA08.Paper.verified_nuclearLift_clipping_tail
#print axioms NLA.RA08.Paper.verified_frobeniusNorm_spectral_bound
#print axioms NLA.RA08.Paper.verified_nuclearNorm_spectral_bound
#print axioms NLA.RA08.Paper.verified_clipping_nuclear_quadratic_remainder
#print axioms NLA.RA08.Paper.verified_clippingDividedDifference_symmetric
#print axioms NLA.RA08.Paper.verified_clippingDerivative_isHermitian
#print axioms NLA.RA08.Paper.verified_nuclearLiftDerivative_prefix
#print axioms NLA.RA08.Paper.verified_nuclearLiftDerivative_last
#print axioms NLA.RA08.Paper.verified_nuclearLiftDerivative_isHermitian
#print axioms NLA.RA08.Paper.verified_nuclearLiftOutput_isHermitian
#print axioms NLA.RA08.Paper.verified_nuclearLift_nuclear_remainder
#print axioms NLA.RA08.Paper.verified_nuclearLiftUnitary_unitary
#print axioms NLA.RA08.Paper.verified_nuclearLiftUnitary_trace
#print axioms NLA.RA08.Paper.verified_nuclearLiftDerivative_trace
#print axioms NLA.RA08.Paper.verified_nuclearLiftDerivative_nuclear_lower
#print axioms NLA.RA08.Paper.verified_nuclearLiftOutput_lower
#print axioms NLA.RA08.Paper.verified_nuclear_choose_eta
#print axioms NLA.RA08.Paper.verified_nuclear_small_time
#print axioms NLA.RA08.Paper.verified_paper_nuclear_counterexample
end NLA.RA08.Paper
