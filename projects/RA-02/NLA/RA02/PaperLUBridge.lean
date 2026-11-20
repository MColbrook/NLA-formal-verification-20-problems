module

public import NLA.RA02.PaperResidualUpdate
public import NLA.RA03.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.RA02.Paper

theorem complexify_eq_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : complexify A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) h
    exact Complex.ofReal_eq_zero.mp hh
  · rintro rfl
    rfl

theorem complexify_lu_step {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    NLA.RA03.pivotResidual (complexify A) (i,j) = complexify (crossUpdate A i j) := by
  by_cases hij : A i j = 0
  · ext a b
    simp [NLA.RA03.pivotResidual, complexify, crossUpdate, hij]
  · ext a b
    simp [NLA.RA03.pivotResidual, complexify, crossUpdate, hij]

theorem complexify_lu_next {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (p : Option (Fin n × Fin n)) :
    NLA.RA03.nextResidual (complexify A) p = complexify (realLUNext A p) := by
  cases p with
  | none => rfl
  | some p => exact complexify_lu_step A p.1 p.2

theorem complexify_lu_path {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : Fin k → NLA.RA03.Pivot n n) :
    NLA.RA03.historyResidual (complexify A) h = complexify (realLUPath A h) := by
  induction k generalizing A with
  | zero => rfl
  | succ k ih =>
    rw [NLA.RA03.historyResidual, complexify_lu_next, realLUPath, ih]

theorem complexify_frobenius {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    NLA.RA03.frobeniusSq (complexify A) = ∑ i, ∑ j, (A i j)^2 := by
  simp [NLA.RA03.frobeniusSq, complexify, Complex.normSq_ofReal, pow_two]

theorem complexify_joint_pivot_mass {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ≠ 0)
    (i j : Fin n) : NLA.RA03.pivotMass (complexify A) (some (i,j)) =
      (A i j)^2 / (∑ a, ∑ b, (A a b)^2) := by
  rw [NLA.RA03.pivotMass, if_neg ((complexify_eq_zero A).not.mpr hA), complexify_frobenius]
  simp [complexify, Complex.normSq_ofReal, pow_two]

theorem complexify_lu_residual_update {n s : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (rows cols : Fin s ↪ Fin n) (p q : Fin n) (hp : p ∉ Set.range rows) (hq : q ∉ Set.range cols)
    (hu : IsUnit (A.submatrix rows cols))
    (ha : IsUnit (A.submatrix (appendEmbedding rows p hp) (appendEmbedding cols q hq))) :
    NLA.RA03.pivotResidual (complexify (interpolatoryResidual A rows cols)) (p,q) =
      complexify (interpolatoryResidual A (appendEmbedding rows p hp) (appendEmbedding cols q hq)) := by
  rw [complexify_lu_step, residual_append_update A rows cols p q hp hq hu ha]

#print axioms complexify_lu_residual_update
end NLA.RA02.Paper
