module

/- An explicit polynomial exponent for the honest Gram determinant bound. -/
public import NLA.IV04.AffinePolyhedronSteps.GramBounds

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps

theorem factorial_le_two_pow_square (n : ℕ) : n.factorial ≤ 2^(n*n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs : n+1 ≤ 2^(n+1) := Nat.le_of_lt Nat.lt_two_pow_self
      calc
        (n+1).factorial = (n+1)*n.factorial := Nat.factorial_succ n
        _ ≤ 2^(n+1)*2^(n*n) := Nat.mul_le_mul hs ih
        _ = 2^(n+1+n*n) := (pow_add 2 (n+1) (n*n)).symm
        _ ≤ 2^((n+1)*(n+1)) := by
          apply Nat.pow_le_pow_right (by omega)
          nlinarith

theorem gramCertificateBound_le_two_pow (m n H L : ℕ) (hH : H ≤ 2^L) :
    gramCertificateBound m n H ≤ 2^(n*n+n*(m+2*L)) := by
  have hm : m ≤ 2^m := Nat.le_of_lt Nat.lt_two_pow_self
  have hbase : m*H^2 ≤ 2^(m+2*L) := by
    calc
      _ ≤ 2^m*(2^L)^2 := Nat.mul_le_mul hm (Nat.pow_le_pow_left hH 2)
      _ = _ := by rw [← pow_mul,← pow_add]; congr 1; omega
  calc
    gramCertificateBound m n H = n.factorial*(m*H^2)^n := rfl
    _ ≤ 2^(n*n)*(2^(m+2*L))^n :=
      Nat.mul_le_mul (factorial_le_two_pow_square n) (Nat.pow_le_pow_left hbase n)
    _ = _ := by rw [← pow_mul,← pow_add]; congr 1; ring

#print axioms factorial_le_two_pow_square
#print axioms gramCertificateBound_le_two_pow
end Reference.IV04AffinePolyhedronSteps
