module

public import NLA.RA02.PaperLUNonnegative
public import NLA.RA02.PaperLowerSemicontinuousProducts

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology Matrix
open Filter
namespace NLA.RA02.Paper

theorem continuous_lu_frobeniusSq {m n : ℕ} :
    Continuous (NLA.RA03.frobeniusSq (m:=m) (n:=n)) := by
  unfold NLA.RA03.frobeniusSq
  fun_prop

theorem lu_pivotMass_continuousAt_entry {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (p : Fin m × Fin n) (hp : A p.1 p.2 ≠ 0) :
    ContinuousAt (fun B => NLA.RA03.pivotMass B (some p)) A := by
  have hA : A ≠ 0 := by intro he; apply hp; simp [he]
  have hd : NLA.RA03.frobeniusSq A ≠ 0 := (lu_frobeniusSq_eq_zero_iff A).not.mpr hA
  have he : ContinuousAt (fun B : Matrix (Fin m) (Fin n) ℂ =>
      Complex.normSq (B p.1 p.2)) A :=
    (Complex.continuous_normSq.comp (continuous_id.matrix_elem p.1 p.2)).continuousAt
  have hc : ContinuousAt (fun B : Matrix (Fin m) (Fin n) ℂ =>
      Complex.normSq (B p.1 p.2)/NLA.RA03.frobeniusSq B) A :=
    he.div continuous_lu_frobeniusSq.continuousAt hd
  apply hc.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hA] with B hB
  simp [NLA.RA03.pivotMass,hB]

theorem lu_pivotResidual_continuousAt_entry {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (p : Fin m × Fin n) (hp : A p.1 p.2 ≠ 0) :
    ContinuousAt (fun B => NLA.RA03.pivotResidual B p) A := by
  have hc : ContinuousAt (fun B : Matrix (Fin m) (Fin n) ℂ =>
      fun i j => B i j - B i p.2 * B p.1 j / B p.1 p.2) A := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    have he : ∀ a b, ContinuousAt (fun B : Matrix (Fin m) (Fin n) ℂ => B a b) A := by
      intro a b
      exact (continuous_id.matrix_elem a b).continuousAt
    exact (he i j).sub (((he i p.2).mul (he p.1 j)).div (he p.1 p.2) hp)
  apply hc.congr_of_eventuallyEq
  have he : ContinuousAt (fun B : Matrix (Fin m) (Fin n) ℂ => B p.1 p.2) A :=
    (continuous_id.matrix_elem p.1 p.2).continuousAt
  filter_upwards [he.eventually (eventually_ne_nhds hp)] with B hB
  simp [NLA.RA03.pivotResidual,hB]

#print axioms lu_pivotResidual_continuousAt_entry
end NLA.RA02.Paper
