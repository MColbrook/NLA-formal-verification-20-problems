module

public import NLA.TR04.RecursiveTensorCompletion.ProcessCorrectness
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace Reference.RecursiveTensorCompletion
open Reference.RealSVDPackage

theorem verified_svdFrame_correct {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (r : ℕ) :
    (svdFrame A r).transpose*svdFrame A r=1 ∧
      ∀ Y : Tensor m ns, Y.rank ≤ r →
        tensorFrobeniusSq (A-svdFrame A r*(svdFrame A r).transpose*A) ≤ tensorFrobeniusSq (A-Y) := by
  exact svdFrame_correct A r

theorem verified_ttSVD_correct {m : ℕ} {ns : List ℕ}
    (A : Tensor m ns) (rs : List ℕ) (hlen : rs.length=ns.length) :
    feasible m ns (ttSVD m ns A rs) rs ∧
      ∀ Y : Tensor m ns, feasible m ns Y rs →
        tensorFrobeniusSq (A-ttSVD m ns A rs) ≤ (ns.length : ℝ)*tensorFrobeniusSq (A-Y) := by
  exact ttSVD_correct A rs hlen

theorem verified_completeFrame_correct {m k n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (U : Rect m k) (hU : U.transpose*U=1)
    (r1 : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hk : k ≤ r1) :
    feasible m (n::ns) (completeFrame A U rs) (r1::rs) ∧
      ∀ Y : Tensor m (n::ns), feasible m (n::ns) Y (r1::rs) →
        tensorFrobeniusSq (A-completeFrame A U rs) ≤ tensorFrobeniusSq (A-U*U.transpose*A) +
          (ns.length : ℝ)*tensorFrobeniusSq (U.transpose*(A-Y)) ∧
        tensorFrobeniusSq (A-completeFrame A U rs) ≤ tensorFrobeniusSq (A-U*U.transpose*A) +
          (ns.length : ℝ)*tensorFrobeniusSq (U*U.transpose*(A-Y)) := by
  exact completeFrame_correct A U hU r1 rs hlen hk

#print axioms Reference.RecursiveTensorCompletion.verified_svdFrame_correct
#print axioms Reference.RecursiveTensorCompletion.verified_ttSVD_correct
#print axioms Reference.RecursiveTensorCompletion.verified_completeFrame_correct
end Reference.RecursiveTensorCompletion
