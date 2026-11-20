module

public import NLA.IV04.PaperSignedWordSharpBounds
public import NLA.IV04.PaperWordListSumSemantics
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

def signedDotPack (left right total : List Bool) : List Bool := pair left (pair right total)
def signedDotStep (state : List Bool) : List Bool :=
  let left := pairFst state
  let right := pairFst (pairSnd state)
  let total := pairSnd (pairSnd state)
  caseBit₀ (nonemptyFlag left)
    (signedDotPack (pairSnd left) (pairSnd right)
      (polynomialSignedAdd total (polynomialSignedMultiply (pairFst left) (pairFst right)))) state

def signedDotState (input : List Bool) : List Bool :=
  (signedDotStep^[input.length]) (signedDotPack (pairFst input) (pairSnd input) [false])
def polynomialSignedDot (input : List Bool) : List Bool := pairSnd (pairSnd (signedDotState input))

theorem signed_dot_step_pack (left right total : List Bool) :
    signedDotStep (signedDotPack left right total)=
      if left=[] then signedDotPack left right total else
        signedDotPack (pairSnd left) (pairSnd right)
          (polynomialSignedAdd total (polynomialSignedMultiply (pairFst left) (pairFst right))) := by
  simp only [signedDotStep,signedDotPack,pairFst_pair,pairSnd_pair]
  cases left <;> simp [nonemptyFlag,caseBit,caseBit₀]

theorem signed_dot_step_shape (left right total : List Bool) :
    ∃ l r t : List Bool, signedDotStep (signedDotPack left right total)=signedDotPack l r t ∧
      (signedDotPack l r t).length ≤ (signedDotPack left right total).length+3 := by
  rw [signed_dot_step_pack]
  split_ifs with he
  · exact ⟨left,right,total,rfl,Nat.le_add_right _ _⟩
  · refine ⟨_,_,_,rfl,?_⟩
    have hl := pair_projection_budget left
    have hr := pair_projection_budget right
    have hm := polynomial_signed_multiply_linear_length (pairFst left) (pairFst right)
    have ha := polynomial_signed_add_length total (polynomialSignedMultiply (pairFst left) (pairFst right))
    have ht : ∀ x : List Bool, x.tail.length ≤ x.length := fun x => by cases x <;> simp
    have htl := ht (pairFst left)
    have htr := ht (pairFst right)
    have htt := ht total
    have htm := ht (polynomialSignedMultiply (pairFst left) (pairFst right))
    simp only [signedDotPack,pair_length]
    omega

theorem signed_dot_iterate_shape (k : ℕ) (left right total : List Bool) :
    ∃ l r t : List Bool, (signedDotStep^[k]) (signedDotPack left right total)=signedDotPack l r t ∧
      (signedDotPack l r t).length ≤ (signedDotPack left right total).length+3*k := by
  induction k with
  | zero => exact ⟨left,right,total,rfl,le_refl _⟩
  | succ k ih =>
    obtain ⟨l,r,t,he,hl⟩ := ih
    obtain ⟨l',r',t',hs,hb⟩ := signed_dot_step_shape l r t
    refine ⟨l',r',t',?_,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · omega

theorem signed_dot_clock_length (k : ℕ) (input : List Bool) :
    ((signedDotStep^[k]) (signedDotPack (pairFst input) (pairSnd input) [false])).length ≤
      2*input.length+5+3*k := by
  obtain ⟨l,r,t,he,hl⟩ := signed_dot_iterate_shape k (pairFst input) (pairSnd input) [false]
  rw [he]
  have hp := pair_projection_budget input
  simp only [signedDotPack,pair_length,List.length_singleton] at hl ⊢
  omega

theorem signed_dot_step_cobham :
    Cobham fun v : Fin 1 → List Bool => signedDotStep (v 0) := by
  have hl := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have hr := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  have ht := Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  have hm := Cobham.comp₂ polynomial_signed_multiply_cobham (Cobham.fstBlockFn hl) (Cobham.fstBlockFn hr)
  have ha := Cobham.comp₂ polynomial_signed_add_cobham ht hm
  have hn := Cobham.comp₂ Cobham.pairing (Cobham.sndBlockFn hl)
    (Cobham.comp₂ Cobham.pairing (Cobham.sndBlockFn hr) ha)
  exact (Cobham.iteFn (Cobham.nonemptyFn hl) hn (.proj 0)).of_eq fun _ => rfl

theorem signed_dot_state_cobham :
    Cobham fun v : Fin 1 → List Bool => signedDotState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v => signedDotPack (pairFst (v 0)) (pairSnd (v 0)) [false]
  let step : (Fin 2 → List Bool) → List Bool := fun v => signedDotStep (v 0)
  let ruler : (Fin 2 → List Bool) → List Bool := fun v =>
    v 1 ++ v 1 ++ List.replicate 5 false ++ v 0 ++ v 0 ++ v 0
  have hi : Cobham initial := Cobham.comp₂ Cobham.pairing (Cobham.fstBlockFn (.proj 0))
    (Cobham.comp₂ Cobham.pairing (Cobham.sndBlockFn (.proj 0)) (.const [false]))
  have hs : Cobham step := (Cobham.comp signed_dot_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham ruler := Cobham.appendFn
    (Cobham.appendFn (Cobham.appendFn (Cobham.appendFn (Cobham.appendFn (.proj 1) (.proj 1))
      (.const (List.replicate 5 false))) (.proj 0)) (.proj 0)) (.proj 0)
  have hb : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((signedDotStep^[clock.length]) (signedDotPack (pairFst (v 0)) (pairSnd (v 0)) [false])).length ≤ _
    have h := signed_dot_clock_length clock.length (v 0)
    simp [ruler]
    omega
  have hit := Cobham.iterFn hi hs hr hb
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have ha : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i <;> simpa [args] using (Cobham.proj 0 : Cobham fun v : Fin 1 → List Bool => v 0)
  exact (Cobham.comp hit ha).of_eq fun _ => rfl

theorem polynomial_signed_dot_mem_fp : polynomialSignedDot ∈ FP :=
  CobhamFP_subset_FP ((Cobham.sndBlockFn (Cobham.sndBlockFn signed_dot_state_cobham)).of_eq fun _ => rfl)

def signedPayloadDot : List (List Bool) → List (List Bool) → ℤ
  | a::as, p::ps => signedWordValue a*signedWordValue p+signedPayloadDot as ps
  | _,_ => 0

theorem signed_dot_iterate_nil (k : ℕ) (right total : List Bool) :
    (signedDotStep^[k]) (signedDotPack [] right total)=signedDotPack [] right total := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,signed_dot_step_pack];simp

theorem signed_dot_iteration_value (k : ℕ) (left right : List (List Bool)) (total : List Bool)
    (hlen : left.length=right.length) (hk : left.length ≤ k) :
    signedWordValue (pairSnd (pairSnd ((signedDotStep^[k])
      (signedDotPack (payloadListCode left) (payloadListCode right) total))))=
      signedWordValue total+signedPayloadDot left right := by
  induction k generalizing left right total with
  | zero =>
    have hl : left=[] := by cases left <;> simp_all
    have hr : right=[] := by cases right <;> simp_all
    simp [hl,hr,payloadListCode,signedDotPack,signedPayloadDot]
  | succ k ih =>
    cases left with
    | nil =>
      have hr : right=[] := by cases right <;> simp_all
      subst right
      change signedWordValue (pairSnd (pairSnd ((signedDotStep^[k+1]) (signedDotPack [] [] total))))=signedWordValue total+0
      rw [signed_dot_iterate_nil]
      simp [signedDotPack]
    | cons a as =>
      cases right with
      | nil => simp at hlen
      | cons p ps =>
        have ht : as.length=ps.length := by simpa using hlen
        have hc : as.length ≤ k := by simp only [List.length_cons] at hk;omega
        rw [Function.iterate_succ_apply,signed_dot_step_pack]
        simp only [payloadListCode,payload_pair_ne_nil,if_false,pairFst_pair,pairSnd_pair]
        rw [ih as ps (polynomialSignedAdd total (polynomialSignedMultiply a p)) ht hc,
          polynomial_signed_add_value,polynomial_signed_multiply_value]
        simp [signedPayloadDot,add_assoc]

theorem polynomial_signed_dot_value (left right : List (List Bool)) (hlen : left.length=right.length) :
    signedWordValue (polynomialSignedDot (pair (payloadListCode left) (payloadListCode right)))=
      signedPayloadDot left right := by
  have hl := payload_list_count_length left
  have hp := pairFst_length_le (pair (payloadListCode left) (payloadListCode right))
  simp only [pairFst_pair] at hp
  have h := signed_dot_iteration_value (pair (payloadListCode left) (payloadListCode right)).length left right [false]
    hlen (by omega)
  simpa [polynomialSignedDot,signedDotState,pairFst_pair,pairSnd_pair,signedWordValue,firstBit,wordValue] using h

theorem signed_dot_actual_polytime : polynomialSignedDot ∈ FP ∧
    ∀ left right : List (List Bool), left.length=right.length →
      signedWordValue (polynomialSignedDot (pair (payloadListCode left) (payloadListCode right)))=
        signedPayloadDot left right :=
  ⟨polynomial_signed_dot_mem_fp,polynomial_signed_dot_value⟩
#print axioms signed_dot_actual_polytime
end IV04.Paper.Computational
