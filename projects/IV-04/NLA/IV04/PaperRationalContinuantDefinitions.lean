module

public import PaperDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

abbrev RatMat (n : ℕ) := Matrix (Fin n) (Fin n) ℚ

def RationalTridiagonal {n : ℕ} (A : RatMat n) : Prop :=
  ∀ i j, i.val + 1 < j.val ∨ j.val + 1 < i.val → A i j = 0

/-- Actual rational tridiagonal matrix; the upper diagonal is arbitrary. -/
def rationalContinuantMatrix (n : ℕ) (a lower upper : ℕ → ℚ) : RatMat n := fun i j =>
  if i=j then a i.val else if j.val=i.val+1 then upper i.val
  else if i.val=j.val+1 then lower i.val else 0

def rationalContinuantValue (a lower upper : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | 1 => a 0
  | n+2 => a (n+1)*rationalContinuantValue a lower upper (n+1)-
      lower (n+1)*upper n*rationalContinuantValue a lower upper n

/-- Sequential recurrence carrying only the current and preceding values.
    This semantic definition is not a machine running-time certificate. -/
def rationalContinuantPair (a lower upper : ℕ → ℚ) : ℕ → ℚ × ℚ
  | 0 => (1,0)
  | n+1 =>
      let previous := rationalContinuantPair a lower upper n
      (a n*previous.1-lower n*upper (n-1)*previous.2,previous.1)

end IV04.Paper.Computational
