module

public import NLA.RA08.PaperNuclearSmallest
public import NLA.RA08.PaperNuclearPinching
public import NLA.RA08.OrderedExistence
public import NLA.RA08.Spectral

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem nuclear_spectralCombination_nonnegative {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) :
    nuclearNorm (spectralCombination d v)=∑ i, v i := by
  have hp : (spectralCombination d v).PosSemidef := by
    simpa only [spectralCombination,Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.PosSemidef.diagonal hv).mul_mul_conjTranspose_same
        (d.orthogonal : RealMatrix n)
  rw [nuclearNorm_posSemidef _ hp]
  unfold spectralCombination
  rw [Matrix.trace_mul_cycle,spectral_transpose_mul,Matrix.one_mul,Matrix.trace_diagonal]

theorem nuclear_truncation_last {n : ℕ} {A : RealMatrix (n+1)}
    (d : OrderedSpectralData A) :
    nuclearNorm (A-truncation d n)=d.eigenvalues (Fin.last n) := by
  have he : A=spectralCombination d d.eigenvalues := d.reconstruct
  conv_lhs => arg 1; arg 1; rw [he]
  rw [truncation,spectralCombination_sub]
  rw [nuclear_spectralCombination_nonnegative d _ (fun i => by
    split_ifs <;> simp [d.nonnegative i])]
  rw [Fin.sum_univ_castSucc]
  simp

theorem nuclear_functionTruncation_last {n : ℕ} {A : RealMatrix (n+1)}
    (d : OrderedSpectralData A) (f : ℝ → ℝ)
    (hf : ∀ i, 0 ≤ f (d.eigenvalues i)) :
    nuclearNorm (functionalCalculus f A-functionTruncation d f n)=
      f (d.eigenvalues (Fin.last n)) := by
  rw [(functionalCalculus_spectral_proved d f).1,functionTruncation,
    spectralCombination_sub]
  rw [nuclear_spectralCombination_nonnegative d _ (fun i => by
    split_ifs <;> simp [hf i])]
  rw [Fin.sum_univ_castSucc]
  simp

theorem nuclearLiftSmallest_eq_last (m : ℕ) (η t : ℝ)
    (d : OrderedSpectralData (nuclearLiftA m η t)) :
    nuclearLiftSmallest m η t=d.eigenvalues (Fin.last (m+m)) := by
  apply le_antisymm
  · apply nuclearLiftSmallest_le_spectrum
    rw [selected_data_spectrum d]
    exact Set.mem_range_self _
  · unfold nuclearLiftSmallest
    apply le_csInf (nuclearLift_spectrum_nonempty m η t)
    intro r hr
    rw [selected_data_spectrum d] at hr
    obtain ⟨i,rfl⟩ := hr
    exact d.decreasing (Fin.le_last i)

theorem nuclearLift_ordered_exists (m : ℕ) (η t : ℝ) (hη : η < 1) (ht : 0 < t) :
    Nonempty (OrderedSpectralData (nuclearLiftA m η t)) :=
  orderedSpectral_exists_proved _ (nuclearLiftA_posDef m η t hη ht).posSemidef

theorem nuclearLift_truncation_tail (m : ℕ) (η t : ℝ)
    (d : OrderedSpectralData (nuclearLiftA m η t)) :
    nuclearNorm (nuclearLiftA m η t-truncation d (m+m))=nuclearLiftSmallest m η t := by
  rw [nuclear_truncation_last,nuclearLiftSmallest_eq_last m η t d]

theorem nuclearLift_clipping_tail (m : ℕ) (η t : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1/4)
    (d : OrderedSpectralData (nuclearLiftA m η t)) :
    nuclearNorm (functionalCalculus witnessFunction (nuclearLiftA m η t)-
      functionTruncation d witnessFunction (m+m))=nuclearLiftSmallest m η t := by
  rw [nuclear_functionTruncation_last d witnessFunction (fun i => by
    exact le_min (d.nonnegative i) (by norm_num)),← nuclearLiftSmallest_eq_last m η t d]
  unfold witnessFunction
  apply min_eq_left
  have h := nuclearLiftSmallest_upper m η t hη1
  have hα : (1-η)*t ≤ t := by nlinarith
  linarith

#print axioms nuclearLift_clipping_tail
end NLA.RA08.Paper
