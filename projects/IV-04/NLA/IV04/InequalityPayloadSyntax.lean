module

public import NLA.IV04.InequalitySignedDot
public import NLA.IV04.PaperPayloadCountSemantics
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

def payloadSyntaxStep (state : List Bool) : List Bool :=
  let rest := pairFst state
  let valid := pairSnd state
  caseBit₀ (nonemptyFlag rest)
    (pair (pairSnd rest) (andBit valid (Cobham.eqFlag (pair (pairFst rest) (pairSnd rest)) rest))) state

def payloadSyntaxState (input : List Bool) : List Bool :=
  (payloadSyntaxStep^[input.length]) (pair input [true])
def payloadSyntaxVerdict (state : List Bool) : List Bool :=
  andBit (pairSnd state) (Cobham.eqFlag (pairFst state) [])
def polynomialPayloadSyntax (input : List Bool) : List Bool := payloadSyntaxVerdict (payloadSyntaxState input)

theorem payload_syntax_step_pair (rest valid : List Bool) :
    payloadSyntaxStep (pair rest valid)=if rest=[] then pair rest valid else
      pair (pairSnd rest) (andBit valid (Cobham.eqFlag (pair (pairFst rest) (pairSnd rest)) rest)) := by
  simp only [payloadSyntaxStep,pairFst_pair,pairSnd_pair]
  cases rest <;> simp [nonemptyFlag,caseBit,caseBit₀]

theorem payload_syntax_step_shape (rest valid : List Bool) :
    ∃ r v : List Bool, payloadSyntaxStep (pair rest valid)=pair r v ∧
      (pair r v).length ≤ (pair rest valid).length+1 := by
  rw [payload_syntax_step_pair]
  split_ifs with he
  · exact ⟨rest,valid,rfl,Nat.le_add_right _ _⟩
  · refine ⟨_,_,rfl,?_⟩
    have hp := pairSnd_length_le rest
    have hf := andBit_flag valid (Cobham.eqFlag (pair (pairFst rest) (pairSnd rest)) rest)
    rcases hf with hf | hf <;> rw [hf] <;> simp only [pair_length,List.length_singleton] <;> omega

theorem payload_syntax_iterate_length (k : ℕ) (rest valid : List Bool) :
    ∃ r v : List Bool, (payloadSyntaxStep^[k]) (pair rest valid)=pair r v ∧
      (pair r v).length ≤ (pair rest valid).length+k := by
  induction k with
  | zero => exact ⟨rest,valid,rfl,le_refl _⟩
  | succ k ih =>
    obtain ⟨r,v,he,hl⟩ := ih
    obtain ⟨r',v',hs,hb⟩ := payload_syntax_step_shape r v
    refine ⟨r',v',?_,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · omega

theorem payload_syntax_step_cobham :
    Cobham fun v : Fin 1 → List Bool => payloadSyntaxStep (v 0) := by
  have hr := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have hv := Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))
  have hc := Cobham.eqFlag_mem (Cobham.comp₂ Cobham.pairing (Cobham.fstBlockFn hr) (Cobham.sndBlockFn hr)) hr
  exact (Cobham.iteFn (Cobham.nonemptyFn hr)
    (Cobham.comp₂ Cobham.pairing (Cobham.sndBlockFn hr) (Cobham.andFn hv hc)) (.proj 0)).of_eq fun _ => rfl

theorem payload_syntax_state_cobham :
    Cobham fun v : Fin 1 → List Bool => payloadSyntaxState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v => pair (v 0) [true]
  let step : (Fin 2 → List Bool) → List Bool := fun v => payloadSyntaxStep (v 0)
  let ruler : (Fin 2 → List Bool) → List Bool := fun v => v 1 ++ v 1 ++ List.replicate 3 false ++ v 0
  have hi : Cobham initial := Cobham.comp₂ Cobham.pairing (.proj 0) (.const [true])
  have hs : Cobham step := (Cobham.comp payload_syntax_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham ruler := Cobham.appendFn (Cobham.appendFn (Cobham.appendFn (.proj 1) (.proj 1))
    (.const (List.replicate 3 false))) (.proj 0)
  have hb : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((payloadSyntaxStep^[clock.length]) (pair (v 0) [true])).length ≤ _
    obtain ⟨r,f,he,hl⟩ := payload_syntax_iterate_length clock.length (v 0) [true]
    rw [he]
    simp only [pair_length,List.length_singleton] at hl
    simp [ruler]
    omega
  have hit := Cobham.iterFn hi hs hr hb
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have ha : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i <;> simpa [args] using (Cobham.proj 0 : Cobham fun v : Fin 1 → List Bool => v 0)
  exact (Cobham.comp hit ha).of_eq fun _ => rfl

theorem polynomial_payload_syntax_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialPayloadSyntax (v 0) :=
  (Cobham.andFn (Cobham.sndBlockFn payload_syntax_state_cobham)
    (Cobham.eqFlag_mem (Cobham.fstBlockFn payload_syntax_state_cobham) (.const []))).of_eq fun _ => rfl

theorem polynomial_payload_syntax_mem_fp : polynomialPayloadSyntax ∈ FP :=
  CobhamFP_subset_FP polynomial_payload_syntax_cobham

theorem inequality_eq_flag_decide (left right : List Bool) :
    Cobham.eqFlag left right=[decide (left=right)] := by
  by_cases h : left=right
  · simp [h]
  · rcases Cobham.eqFlag_flag left right with he | he
    · exact False.elim (h ((Cobham.eqFlag_eq_true_iff left right).mp he))
    · simpa [h] using he

theorem payload_syntax_step_bool (rest : List Bool) (flag : Bool) :
    payloadSyntaxStep (pair rest [flag])=if rest=[] then pair rest [flag] else
      pair (pairSnd rest) [flag && decide (pair (pairFst rest) (pairSnd rest)=rest)] := by
  rw [payload_syntax_step_pair,inequality_eq_flag_decide]
  cases flag <;> by_cases h : pair (pairFst rest) (pairSnd rest)=rest <;>
    simp [h,andBit,caseBit₀]

theorem payload_syntax_iterate_nil (k : ℕ) (flag : Bool) :
    (payloadSyntaxStep^[k]) (pair [] [flag])=pair [] [flag] := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,payload_syntax_step_pair];simp

theorem payload_syntax_iteration_exact (k : ℕ) (rest : List Bool) (flag : Bool) :
    payloadSyntaxVerdict ((payloadSyntaxStep^[k]) (pair rest [flag]))=[true] ↔
      flag=true ∧ ∃ payloads : List (List Bool), payloads.length ≤ k ∧ payloadListCode payloads=rest := by
  induction k generalizing rest flag with
  | zero =>
    simp only [Function.iterate_zero,Function.id_def,payloadSyntaxVerdict,pairSnd_pair,pairFst_pair]
    rw [Cobham.andBit_eq_true_iff (by cases flag <;> simp) (Cobham.eqFlag_flag _ _),Cobham.eqFlag_eq_true_iff]
    constructor
    · rintro ⟨hf,hr⟩
      exact ⟨by simpa using hf,[],by simp,by simpa [payloadListCode] using hr.symm⟩
    · rintro ⟨hf,ps,hk,hr⟩
      have hp : ps=[] := by cases ps <;> simp_all
      exact ⟨by simp [hf],by simpa [hp,payloadListCode] using hr.symm⟩
  | succ k ih =>
    by_cases hn : rest=[]
    · subst rest
      rw [payload_syntax_iterate_nil]
      simp only [payloadSyntaxVerdict,pairSnd_pair,pairFst_pair]
      rw [Cobham.andBit_eq_true_iff (by cases flag <;> simp) (Cobham.eqFlag_flag _ _),Cobham.eqFlag_eq_true_iff]
      constructor
      · rintro ⟨hf,_⟩;exact ⟨by simpa using hf,[],by simp,rfl⟩
      · rintro ⟨hf,_⟩;exact ⟨by simp [hf],rfl⟩
    · rw [Function.iterate_succ_apply,payload_syntax_step_bool,if_neg hn,ih]
      simp only [Bool.and_eq_true,decide_eq_true_eq]
      constructor
      · rintro ⟨⟨hf,hc⟩,ps,hk,hcode⟩
        refine ⟨hf,pairFst rest::ps,by simp only [List.length_cons];omega,?_⟩
        simpa only [payloadListCode,hcode] using hc
      · rintro ⟨hf,ps,hk,hcode⟩
        cases ps with
        | nil => exact (hn (by simpa [payloadListCode] using hcode.symm)).elim
        | cons p ps =>
          have hr : rest=pair p (payloadListCode ps) := hcode.symm
          refine ⟨⟨hf,?_⟩,ps,by simp only [List.length_cons] at hk;omega,?_⟩
          · simp [hr]
          · simp [hr]

theorem polynomial_payload_syntax_exact (input : List Bool) :
    polynomialPayloadSyntax input=[true] ↔ ∃ payloads : List (List Bool), payloadListCode payloads=input := by
  rw [polynomialPayloadSyntax,payloadSyntaxState,payload_syntax_iteration_exact]
  simp only [true_and]
  constructor
  · rintro ⟨ps,_,he⟩;exact ⟨ps,he⟩
  · rintro ⟨ps,he⟩
    refine ⟨ps,?_,he⟩
    rw [←he]
    exact payload_list_count_length ps

theorem payload_syntax_actual_polytime : polynomialPayloadSyntax ∈ FP ∧
    ∀ input, polynomialPayloadSyntax input=[true] ↔
      ∃ payloads : List (List Bool), payloadListCode payloads=input :=
  ⟨polynomial_payload_syntax_mem_fp,polynomial_payload_syntax_exact⟩
#print axioms payload_syntax_actual_polytime
end IV04.Paper.Computational
