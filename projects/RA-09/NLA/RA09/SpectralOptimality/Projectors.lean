module

public import NLA.RA09.SpectralOptimality.RealSelected
public import NLA.RA09.SpectralOptimality.ComplexSelected

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder
namespace RootRA09SpectralOptimality

theorem actual_real_orthogonal_projector {n : ℕ} {A : NLA.RA09.RealMatrix n}
    (d : NLA.RA09.OrderedSpectralData A) (k : ℕ) (hk : k ≤ n) :
    (selectedProjector d k).PosSemidef ∧
      selectedProjector d k * selectedProjector d k = selectedProjector d k ∧
      (selectedProjector d k).rank = k := by
  refine ⟨?_,actual_real_projector_idempotent d k,actual_real_projector_rank d k hk⟩
  apply NLA.RA09.spectralCombination_posSemidef
  intro i
  split_ifs <;> norm_num

theorem actual_complex_orthogonal_projector {n : ℕ} {A : NLA.RA09.ComplexPaper.ComplexMatrix n}
    (d : NLA.RA09.ComplexPaper.OrderedSpectralData A) (k : ℕ) (hk : k ≤ n) :
    (complexSelectedProjector d k).PosSemidef ∧
      complexSelectedProjector d k * complexSelectedProjector d k = complexSelectedProjector d k ∧
      (complexSelectedProjector d k).rank = k := by
  refine ⟨?_,actual_complex_projector_idempotent d k,actual_complex_projector_rank d k hk⟩
  apply NLA.RA09.ComplexPaper.spectralCombination_posSemidef
  intro i
  split_ifs <;> norm_num

#print axioms actual_real_orthogonal_projector
#print axioms actual_complex_orthogonal_projector
end RootRA09SpectralOptimality
