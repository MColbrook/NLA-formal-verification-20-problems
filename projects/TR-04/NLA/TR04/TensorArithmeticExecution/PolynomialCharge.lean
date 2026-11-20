module

/- Uniform polynomial counts follow from genuine shrinking dense unfolding dimensions. -/
public import NLA.TR04.TensorArithmeticExecution.TraceCharge

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.TensorArithmeticExecution
noncomputable section
open Reference.RealSVDPackage Reference.RecursiveTensorCompletion

def denseSize (m : ℕ) (ns : List ℕ) : ℕ := m*modeCard ns

theorem cube_dominates (B : ℕ) (hB : 1≤B) : B≤B^3 ∧ B^2≤B^3 := by
  have hsq : B≤B^2 := by nlinarith
  have hc : B^2≤B^3 := by
    have hh:=Nat.mul_le_mul_left (B*B) hB
    simpa [pow_succ,pow_two,mul_assoc] using hh
  exact ⟨hsq.trans hc,hc⟩

theorem dense_mul_shape_bound (q c B : ℕ) (hB : 1≤B) (hq : q≤B) (hc : c≤B) :
    q*(4*c+1)≤5*B^3 := by
  calc
    _ ≤ B*(4*B+1) := Nat.mul_le_mul hq (by omega)
    _ ≤ 5*B^2 := by nlinarith
    _ ≤ 5*B^3 := Nat.mul_le_mul_left 5 (cube_dominates B hB).2

theorem actual_completeFrame_uniform_shape_charge {m k n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (U : Rect m k) (rs : List ℕ) (B : ℕ)
    (hB : 1≤B) (hmode : ∀ a∈n::ns,1≤a) (hk : k≤m)
    (hsize : m*modeCard (n::ns)≤B) (hcols : modeCard (n::ns)≤B) :
    charge (completionRun A U rs)≤(ns.length*40+12)*B^3 := by
  let P:=modeCard (n::ns)
  let Q:=modeCard ns
  have hp : 1≤P := modeCard_pos _ hmode
  have htail : ∀ a∈ns,1≤a := fun a ha => hmode a (List.mem_cons_of_mem n ha)
  have hn : 1≤n := hmode n List.mem_cons_self
  have hmP : m*P≤B := hsize
  have hP : P≤B := hcols
  have hm : m≤B := (by nlinarith : m≤m*P).trans hmP
  have hkB : k≤B := hk.trans hm
  have hkP : k*P≤B := (Nat.mul_le_mul_right P hk).trans hmP
  have hPQ : P=n*Q := modeCard_cons n ns
  have hnextsize : rowCount k n*Q≤B := by
    rw [actual_rowCount,Nat.mul_assoc,← hPQ]
    exact hkP
  have hnextcols : Q≤B := (by nlinarith [hPQ] : Q≤P).trans hP
  have hi := actual_ttSVD_uniform_shape_charge (rowCount k n) ns rs B hB htail hnextsize hnextcols
  have hc := dense_mul_shape_bound (k*P) m B hB hkP hm
  have hl := dense_mul_shape_bound (m*P) k B hB hmP hkB
  have hc1 := hnextsize.trans (cube_dominates B hB).1
  have hc2 := hkP.trans (cube_dominates B hB).1
  rw [actual_completeFrame_trace_charge]
  change k*P*(4*m+1)+rowCount k n*Q+ttCharge (rowCount k n) ns rs+k*P+m*P*(4*k+1)≤(ns.length*40+12)*B^3
  nlinarith

theorem modeCard_ge_length (ns : List ℕ) (hmode : ∀ n∈ns,2≤n) : ns.length≤modeCard ns := by
  induction ns with
  | nil => simp [modeCard_nil]
  | cons n ns ih =>
    have hn : 2≤n := hmode n List.mem_cons_self
    have ht : ∀ a∈ns,2≤a := fun a ha => hmode a (List.mem_cons_of_mem n ha)
    have hi:=ih ht
    have hq := modeCard_pos ns (fun a ha => (by omega : 2≤a → 1≤a) (ht a ha))
    rw [List.length_cons,modeCard_cons]
    nlinarith

theorem actual_ttSVD_dense_polynomial_charge (m : ℕ) (ns : List ℕ) (A : Tensor m ns)
    (rs : List ℕ) (hm : 1≤m) (hmode : ∀ n∈ns,2≤n) :
    charge (ttRun m ns A rs)≤1080*(denseSize m ns)^4 := by
  let N:=denseSize m ns
  have hp:=modeCard_pos ns (fun a ha => (by omega : 2≤a → 1≤a) (hmode a ha))
  have hP : modeCard ns≤N := by dsimp [N,denseSize];nlinarith
  have hN : 1≤N := hp.trans hP
  have hl : ns.length≤N := (modeCard_ge_length ns hmode).trans hP
  rw [actual_ttSVD_trace_charge]
  have ht:=actual_ttSVD_uniform_shape_charge m ns rs (3*N) (by omega)
    (fun a ha => (by omega : 2≤a → 1≤a) (hmode a ha)) (by change N≤3*N;omega) (by omega)
  calc
    _ ≤ ns.length*40*(3*N)^3 := ht
    _ ≤ N*40*(3*N)^3 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right 40 hl)
    _ = 1080*N^4 := by ring

theorem actual_completeFrame_dense_polynomial_charge {m k n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (U : Rect m k) (rs : List ℕ) (hm : 1≤m)
    (hk : k≤m) (hmode : ∀ a∈n::ns,2≤a) :
    charge (completionRun A U rs)≤1404*(denseSize m (n::ns))^4 := by
  let N:=denseSize m (n::ns)
  have hp:=modeCard_pos (n::ns) (fun a ha => (by omega : 2≤a → 1≤a) (hmode a ha))
  have hP : modeCard (n::ns)≤N := by dsimp [N,denseSize];nlinarith
  have hN : 1≤N := hp.trans hP
  have hfull : ns.length+1≤modeCard (n::ns) := by simpa using modeCard_ge_length (n::ns) hmode
  have hl : ns.length≤N := (Nat.le_of_succ_le hfull).trans hP
  have hc:=actual_completeFrame_uniform_shape_charge A U rs (3*N) (by omega)
    (fun a ha => (by omega : 2≤a → 1≤a) (hmode a ha)) hk (by change N≤3*N;omega) (by omega)
  calc
    _ ≤ (ns.length*40+12)*(3*N)^3 := hc
    _ ≤ (N*40+12)*(3*N)^3 := Nat.mul_le_mul_right _ (by omega)
    _ ≤ (52*N)*(3*N)^3 := Nat.mul_le_mul_right _ (by omega)
    _ = 1404*N^4 := by ring

#print axioms actual_completeFrame_uniform_shape_charge
#print axioms actual_ttSVD_dense_polynomial_charge
#print axioms actual_completeFrame_dense_polynomial_charge
end
end Reference.TensorArithmeticExecution
