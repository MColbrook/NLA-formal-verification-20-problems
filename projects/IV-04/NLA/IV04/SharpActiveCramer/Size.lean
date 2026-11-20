module

/- Polynomial exponent for the literal original-vertex Cramer bound. -/
public import NLA.IV04.SharpActiveCramer.Attainment
public import NLA.IV04.AffinePolyhedronSteps.GramSize

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04SharpActiveCramer
open Reference.IV04AffinePolyhedronSteps

theorem sharpCertificateBound_le_two_pow (n H L : ℕ) (hH : H≤2^L) :
    sharpCertificateBound n H≤2^(n*n+n*L) := by
  calc
    sharpCertificateBound n H=n.factorial*H^n := rfl
    _≤2^(n*n)*(2^L)^n :=
      Nat.mul_le_mul (factorial_le_two_pow_square n) (Nat.pow_le_pow_left hH n)
    _=_ := by rw [← pow_mul,← pow_add]; congr 1; ring

#print axioms sharpCertificateBound_le_two_pow
end Reference.IV04SharpActiveCramer
