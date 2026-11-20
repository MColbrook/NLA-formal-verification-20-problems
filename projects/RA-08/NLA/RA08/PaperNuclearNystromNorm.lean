module

public import NLA.RA08.PaperNuclearNystromAlgebra
public import NLA.RA08.PaperNuclearPSD
public import NLA.RA08.PaperNuclearHomogeneity

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem nuclearLiftPerturbation_nuclearNorm (m : ℕ) (hm : 1 ≤ m) (η : ℝ)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) : nuclearNorm (nuclearLiftPerturbation m η)=1 :=
  nuclear_unit_outer_norm (nuclearLiftVector m η) (nuclearLiftVector_norm_sq m hm η hη hη1)

theorem nuclearLift_residual_nuclearNorm (m : ℕ) (hm : 1 ≤ m) (η t : ℝ)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (ht : 0 ≤ t) :
    nuclearNorm (nuclearLiftA m η t-nuclearLiftBase m)=t := by
  rw [nuclearLiftA,add_sub_cancel_left,nuclearNorm_hermitian_smul _
    (nuclearLiftPerturbation_posSemidef m η).isHermitian t,abs_of_nonneg ht,
    nuclearLiftPerturbation_nuclearNorm m hm η hη hη1,mul_one]

#print axioms nuclearLift_residual_nuclearNorm
end NLA.RA08.Paper
