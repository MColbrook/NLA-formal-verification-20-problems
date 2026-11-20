module

public import NLA.MI22.Commuting.EigenAction

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace NLA.MI22.Commuting

theorem scalar_mean_identity (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a^(1/2:ℝ) * (a^(-1/2:ℝ)*b*a^(-1/2:ℝ))^t * a^(1/2:ℝ) = a^(1-t)*b^t := by
  have hmid : (a^(-1/2:ℝ)*b*a^(-1/2:ℝ))^t = a^(-t)*b^t := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hb.le,
      ← Real.rpow_mul ha.le]
    calc
      a^((-1/2:ℝ)*t)*b^t*a^((-1/2:ℝ)*t) =
          (a^((-1/2:ℝ)*t)*a^((-1/2:ℝ)*t))*b^t := by ring
      _ = a^(-t)*b^t := by rw [← Real.rpow_add ha]; congr 2 <;> ring
  rw [hmid]
  calc
    a^(1/2:ℝ)*(a^(-t)*b^t)*a^(1/2:ℝ) =
        (a^(1/2:ℝ)*a^(-t)*a^(1/2:ℝ))*b^t := by ring
    _ = a^(1-t)*b^t := by rw [← Real.rpow_add ha, ← Real.rpow_add ha]; congr 2 <;> ring

#print axioms scalar_mean_identity
end NLA.MI22.Commuting
