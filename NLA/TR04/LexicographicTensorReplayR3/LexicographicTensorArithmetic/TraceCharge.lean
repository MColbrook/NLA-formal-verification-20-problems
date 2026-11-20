module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- The trace charge is extracted from execution, then bounded from actual tensor shapes. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorArithmetic.TTExecution

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.LexTensorArithmeticExecution
noncomputable section
open Reference.RealSVDPackage Reference.LexTensorCompletion

theorem modeCard_nil : modeCard []=1 := by
  change Fintype.card PUnit=1
  exact Fintype.card_punit
theorem modeCard_cons (n : ℕ) (ns : List ℕ) : modeCard (n::ns)=n*modeCard ns := by
  change Fintype.card (Fin n × ModeIndex ns)=n*Fintype.card (ModeIndex ns)
  simp

theorem actual_rowCount (m n : ℕ) : rowCount m n=m*n := by
  exact (Reference.LexicographicFeasibilityBridge.product_eq_rowCount m n).symm

theorem actual_ttSVD_trace_charge (m : ℕ) (ns : List ℕ) (A : Tensor m ns) (rs : List ℕ) :
    charge (ttRun m ns A rs)=ttCharge m ns rs := by
  induction ns generalizing m rs with
  | nil => simp only [ttRun,ttCharge,charge_pure]
  | cons n ns ih =>
    cases rs with
    | nil => simp only [ttRun,ttCharge,charge_pure]
    | cons r rs =>
      simp only [ttRun,charge_bind,frameRun_charge,tensorMulRun_charge,tensorCopyRun_charge,ih,ttCharge,modeCard]
      omega

theorem actual_completeFrame_trace_charge {m k n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (U : Rect m k) (rs : List ℕ) :
    charge (completionRun A U rs)=
      k*modeCard (n::ns)*(4*m+1)+rowCount k n*modeCard ns+
      ttCharge (rowCount k n) ns rs+k*modeCard (n::ns)+m*modeCard (n::ns)*(4*k+1) := by
  simp only [completionRun,charge_bind,tensorMulRun_charge,tensorCopyRun_charge,actual_ttSVD_trace_charge,modeCard]
  omega

theorem modeCard_pos (ns : List ℕ) (h : ∀ n∈ns,1≤n) : 1≤modeCard ns := by
  induction ns with
  | nil => rw [modeCard_nil]
  | cons n ns ih =>
    rw [modeCard_cons]
    have hn := h n (List.mem_cons_self)
    have hq := ih (fun a ha => h a (List.mem_cons_of_mem n ha))
    nlinarith

theorem actual_ttSVD_uniform_shape_charge (m : ℕ) (ns rs : List ℕ) (B : ℕ)
    (hB : 1≤B) (hmode : ∀ n∈ns,1≤n)
    (hsize : m*modeCard ns≤B) (hcols : modeCard ns≤B) :
    ttCharge m ns rs≤ns.length*40*B^3 := by
  induction ns generalizing m rs with
  | nil => simp [ttCharge]
  | cons n ns ih =>
    cases rs with
    | nil => simp [ttCharge]
    | cons r rs =>
      let k:=min r m
      let P:=modeCard (n::ns)
      let Q:=modeCard ns
      have hn : 1≤n := hmode n List.mem_cons_self
      have htail : ∀ a∈ns,1≤a := fun a ha => hmode a (List.mem_cons_of_mem n ha)
      have hq : 1≤Q := modeCard_pos ns htail
      have hp : 1≤P := modeCard_pos (n::ns) hmode
      have hPQ : P=n*Q := modeCard_cons n ns
      have hmP : m*P≤B := hsize
      have hP : P≤B := hcols
      have hm : m≤B := (by nlinarith : m≤m*P).trans hmP
      have hk : k≤m := Nat.min_le_right r m
      have hkB : k≤B := hk.trans hm
      have hkP : k*P≤B := (Nat.mul_le_mul_right P hk).trans hmP
      have hnextsize : rowCount k n*Q≤B := by
        rw [actual_rowCount,Nat.mul_assoc,← hPQ]
        exact hkP
      have hnextcols : Q≤B := (by nlinarith [hPQ] : Q≤P).trans hP
      have hi := ih (rowCount k n) rs htail hnextsize hnextcols
      have hBsq : B≤B^2 := by nlinarith
      have hBcube : B^2≤B^3 := by
        have hh:=Nat.mul_le_mul_left (B*B) hB
        simpa [pow_succ,pow_two,mul_assoc] using hh
      have hBcube' : B≤B^3 := hBsq.trans hBcube
      have hS : (m+P+1)^3≤27*B^3 := by
        calc
          _ ≤ (3*B)^3 := by gcongr;omega
          _ = 27*B^3 := by ring
      have hframe : m*k≤B^3 := (Nat.mul_le_mul hm hkB).trans (by simpa [pow_two] using hBcube)
      have hc : k*P*(4*m+1)≤5*B^3 := by
        calc
          _ ≤ B*(4*B+1) := Nat.mul_le_mul hkP (by omega)
          _ ≤ 5*B^2 := by nlinarith
          _ ≤ 5*B^3 := Nat.mul_le_mul_left 5 hBcube
      have hl : m*P*(4*k+1)≤5*B^3 := by
        calc
          _ ≤ B*(4*B+1) := Nat.mul_le_mul hmP (by omega)
          _ ≤ 5*B^2 := by nlinarith
          _ ≤ 5*B^3 := Nat.mul_le_mul_left 5 hBcube
      have hc1 : rowCount k n*Q≤B^3 := hnextsize.trans hBcube'
      have hc2 : k*P≤B^3 := hkP.trans hBcube'
      simp only [ttCharge,List.length_cons]
      change (m+P+1)^3+m*k+k*P*(4*m+1)+rowCount k n*Q+
        ttCharge (rowCount k n) ns rs+k*P+m*P*(4*k+1)≤(ns.length+1)*40*B^3
      nlinarith [hS,hframe,hc,hl,hc1,hc2,hi]

#print axioms actual_ttSVD_trace_charge
#print axioms actual_completeFrame_trace_charge
#print axioms actual_ttSVD_uniform_shape_charge
end
end Reference.LexTensorArithmeticExecution
