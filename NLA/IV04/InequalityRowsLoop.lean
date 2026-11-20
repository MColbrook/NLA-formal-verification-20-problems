module

public import NLA.IV04.InequalityRowVerifier
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

def inequalityRowAt (input : List Bool) : List Bool :=
  let query := pairFst input
  let row := pairSnd input
  andBit (Cobham.eqFlag (pair (pairFst row) (pairSnd row)) row)
    (polynomialInequalityRowVerifier
      (inequalityRowPack (pairFst row) (pairSnd row) (pairFst query) (pairSnd query)))

theorem inequality_row_at_flag (input : List Bool) :
    inequalityRowAt input=[true] ∨ inequalityRowAt input=[false] := andBit_flag _ _

theorem inequality_row_at_cobham :
    Cobham fun v : Fin 1 → List Bool => inequalityRowAt (v 0) := by
  have h0 := Cobham.proj (0 : Fin 1)
  have hq := Cobham.fstBlockFn h0
  have hr := Cobham.sndBlockFn h0
  have hc := Cobham.fstBlockFn hr
  have hb := Cobham.sndBlockFn hr
  have hp := Cobham.fstBlockFn hq
  have hd := Cobham.sndBlockFn hq
  have hpack := Cobham.comp₂ Cobham.pairing hc
    (Cobham.comp₂ Cobham.pairing hb (Cobham.comp₂ Cobham.pairing hp hd))
  exact (Cobham.andFn (Cobham.eqFlag_mem (Cobham.comp₂ Cobham.pairing hc hb) hr)
    (Cobham.comp (FP_subset_CobhamFP inequality_row_verifier_mem_fp) fun _ : Fin 1 => hpack)).of_eq fun _ => rfl

def inequalityRowsPack (rest query valid : List Bool) : List Bool := pair rest (pair query valid)
def inequalityRowsStep (state : List Bool) : List Bool :=
  let rest := pairFst state
  let query := pairFst (pairSnd state)
  let valid := pairSnd (pairSnd state)
  caseBit₀ (nonemptyFlag rest)
    (inequalityRowsPack (pairSnd rest) query
      (andBit valid (andBit (Cobham.eqFlag (pair (pairFst rest) (pairSnd rest)) rest)
        (inequalityRowAt (pair query (pairFst rest)))))) state

def inequalityRowsState (input : List Bool) : List Bool :=
  (inequalityRowsStep^[input.length]) (inequalityRowsPack (pairFst input) (pairSnd input) [true])
def inequalityRowsVerdict (state : List Bool) : List Bool :=
  andBit (pairSnd (pairSnd state)) (Cobham.eqFlag (pairFst state) [])

theorem inequality_rows_step_pack (rest query valid : List Bool) :
    inequalityRowsStep (inequalityRowsPack rest query valid)=if rest=[] then inequalityRowsPack rest query valid else
      inequalityRowsPack (pairSnd rest) query
        (andBit valid (andBit (Cobham.eqFlag (pair (pairFst rest) (pairSnd rest)) rest)
          (inequalityRowAt (pair query (pairFst rest))))) := by
  simp only [inequalityRowsStep,inequalityRowsPack,pairFst_pair,pairSnd_pair]
  cases rest <;> simp [nonemptyFlag,caseBit,caseBit₀]

theorem inequality_rows_step_shape (rest query valid : List Bool) :
    ∃ r v : List Bool, inequalityRowsStep (inequalityRowsPack rest query valid)=inequalityRowsPack r query v ∧
      (inequalityRowsPack r query v).length ≤ (inequalityRowsPack rest query valid).length+1 := by
  rw [inequality_rows_step_pack]
  split_ifs with he
  · exact ⟨rest,valid,rfl,Nat.le_add_right _ _⟩
  · refine ⟨_,_,rfl,?_⟩
    have hp := pairSnd_length_le rest
    have hf := andBit_flag valid (andBit (Cobham.eqFlag (pair (pairFst rest) (pairSnd rest)) rest)
      (inequalityRowAt (pair query (pairFst rest))))
    rcases hf with hf | hf <;> rw [hf] <;> simp only [inequalityRowsPack,pair_length,List.length_singleton] <;> omega

theorem inequality_rows_iterate_length (k : ℕ) (rest query valid : List Bool) :
    ∃ r v : List Bool, (inequalityRowsStep^[k]) (inequalityRowsPack rest query valid)=inequalityRowsPack r query v ∧
      (inequalityRowsPack r query v).length ≤ (inequalityRowsPack rest query valid).length+k := by
  induction k with
  | zero => exact ⟨rest,valid,rfl,le_refl _⟩
  | succ k ih =>
    obtain ⟨r,v,he,hl⟩ := ih
    obtain ⟨r',v',hs,hb⟩ := inequality_rows_step_shape r query v
    refine ⟨r',v',?_,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · omega

theorem inequality_rows_step_cobham :
    Cobham fun v : Fin 1 → List Bool => inequalityRowsStep (v 0) := by
  have h0 := Cobham.proj (0 : Fin 1)
  have hr := Cobham.fstBlockFn h0
  have hq := Cobham.fstBlockFn (Cobham.sndBlockFn h0)
  have hv := Cobham.sndBlockFn (Cobham.sndBlockFn h0)
  have hc := Cobham.eqFlag_mem (Cobham.comp₂ Cobham.pairing (Cobham.fstBlockFn hr) (Cobham.sndBlockFn hr)) hr
  have ha := Cobham.comp inequality_row_at_cobham fun _ : Fin 1 =>
    Cobham.comp₂ Cobham.pairing hq (Cobham.fstBlockFn hr)
  exact (Cobham.iteFn (Cobham.nonemptyFn hr)
    (Cobham.comp₂ Cobham.pairing (Cobham.sndBlockFn hr)
      (Cobham.comp₂ Cobham.pairing hq (Cobham.andFn hv (Cobham.andFn hc ha)))) (.proj 0)).of_eq fun _ => rfl

theorem inequality_rows_state_cobham :
    Cobham fun v : Fin 1 → List Bool => inequalityRowsState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v => inequalityRowsPack (pairFst (v 0)) (pairSnd (v 0)) [true]
  let step : (Fin 2 → List Bool) → List Bool := fun v => inequalityRowsStep (v 0)
  let ruler : (Fin 2 → List Bool) → List Bool := fun v => v 1 ++ v 1 ++ List.replicate 5 false ++ v 0
  have hi : Cobham initial := Cobham.comp₂ Cobham.pairing (Cobham.fstBlockFn (.proj 0))
    (Cobham.comp₂ Cobham.pairing (Cobham.sndBlockFn (.proj 0)) (.const [true]))
  have hs : Cobham step := (Cobham.comp inequality_rows_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham ruler := Cobham.appendFn (Cobham.appendFn (Cobham.appendFn (.proj 1) (.proj 1))
    (.const (List.replicate 5 false))) (.proj 0)
  have hb : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((inequalityRowsStep^[clock.length]) (inequalityRowsPack (pairFst (v 0)) (pairSnd (v 0)) [true])).length ≤ _
    obtain ⟨r,f,he,hl⟩ := inequality_rows_iterate_length clock.length (pairFst (v 0)) (pairSnd (v 0)) [true]
    rw [he]
    have hp := pair_projection_budget (v 0)
    simp only [inequalityRowsPack,pair_length,List.length_singleton] at hl ⊢
    simp [ruler]
    omega
  have hit := Cobham.iterFn hi hs hr hb
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have ha : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i <;> simpa [args] using (Cobham.proj 0 : Cobham fun v : Fin 1 → List Bool => v 0)
  exact (Cobham.comp hit ha).of_eq fun _ => rfl

theorem inequality_row_at_decide (input : List Bool) :
    inequalityRowAt input=[decide (inequalityRowAt input=[true])] := by
  rcases inequality_row_at_flag input with h | h <;> simp [h]

theorem inequality_rows_step_bool (rest query : List Bool) (flag : Bool) :
    inequalityRowsStep (inequalityRowsPack rest query [flag])=if rest=[] then inequalityRowsPack rest query [flag] else
      inequalityRowsPack (pairSnd rest) query
        [flag && (decide (pair (pairFst rest) (pairSnd rest)=rest) &&
          decide (inequalityRowAt (pair query (pairFst rest))=[true]))] := by
  rw [inequality_rows_step_pack,inequality_eq_flag_decide,inequality_row_at_decide]
  cases flag <;> cases decide (pair (pairFst rest) (pairSnd rest)=rest) <;>
    cases decide (inequalityRowAt (pair query (pairFst rest))=[true]) <;> simp [andBit,caseBit₀]

theorem inequality_rows_iterate_nil (k : ℕ) (query : List Bool) (flag : Bool) :
    (inequalityRowsStep^[k]) (inequalityRowsPack [] query [flag])=inequalityRowsPack [] query [flag] := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,inequality_rows_step_pack];simp

theorem inequality_rows_iteration_exact (k : ℕ) (rest query : List Bool) (flag : Bool) :
    inequalityRowsVerdict ((inequalityRowsStep^[k]) (inequalityRowsPack rest query [flag]))=[true] ↔
      flag=true ∧ ∃ rows : List (List Bool), rows.length ≤ k ∧ payloadListCode rows=rest ∧
        ∀ row ∈ rows, inequalityRowAt (pair query row)=[true] := by
  induction k generalizing rest flag with
  | zero =>
    simp only [Function.iterate_zero,Function.id_def,inequalityRowsVerdict,inequalityRowsPack,pairSnd_pair,pairFst_pair]
    rw [Cobham.andBit_eq_true_iff (by cases flag <;> simp) (Cobham.eqFlag_flag _ _),Cobham.eqFlag_eq_true_iff]
    constructor
    · rintro ⟨hf,hr⟩
      exact ⟨by simpa using hf,[],by simp,by simpa [payloadListCode] using hr.symm,by simp⟩
    · rintro ⟨hf,rs,hk,hr,_⟩
      have hp : rs=[] := by cases rs <;> simp_all
      exact ⟨by simp [hf],by simpa [hp,payloadListCode] using hr.symm⟩
  | succ k ih =>
    by_cases hn : rest=[]
    · subst rest
      rw [inequality_rows_iterate_nil]
      simp only [inequalityRowsVerdict,inequalityRowsPack,pairSnd_pair,pairFst_pair]
      rw [Cobham.andBit_eq_true_iff (by cases flag <;> simp) (Cobham.eqFlag_flag _ _),Cobham.eqFlag_eq_true_iff]
      constructor
      · rintro ⟨hf,_⟩;exact ⟨by simpa using hf,[],by simp,rfl,by simp⟩
      · rintro ⟨hf,_⟩;exact ⟨by simp [hf],rfl⟩
    · rw [Function.iterate_succ_apply,inequality_rows_step_bool,if_neg hn,ih]
      simp only [Bool.and_eq_true,decide_eq_true_eq]
      constructor
      · rintro ⟨⟨hf,hcanonical,hrow⟩,rs,hk,hcode,hall⟩
        refine ⟨hf,pairFst rest::rs,by simp only [List.length_cons];omega,?_,?_⟩
        · simpa only [payloadListCode,hcode] using hcanonical
        · intro row hmem
          rcases List.mem_cons.mp hmem with he | he
          · subst row;exact hrow
          · exact hall row he
      · rintro ⟨hf,rs,hk,hcode,hall⟩
        cases rs with
        | nil => exact (hn (by simpa [payloadListCode] using hcode.symm)).elim
        | cons row rs =>
          have hr : rest=pair row (payloadListCode rs) := hcode.symm
          refine ⟨⟨hf,by simp [hr],?_⟩,rs,by simp only [List.length_cons] at hk;omega,by simp [hr],?_⟩
          · simpa [hr] using hall row (by simp)
          · intro r hmem;exact hall r (by simp [hmem])

theorem inequality_rows_state_exact (input : List Bool) :
    inequalityRowsVerdict (inequalityRowsState input)=[true] ↔
      ∃ rows : List (List Bool), payloadListCode rows=pairFst input ∧
        ∀ row ∈ rows, inequalityRowAt (pair (pairSnd input) row)=[true] := by
  rw [inequalityRowsState,inequality_rows_iteration_exact]
  simp only [true_and]
  constructor
  · rintro ⟨rows,_,he,hall⟩;exact ⟨rows,he,hall⟩
  · rintro ⟨rows,he,hall⟩
    refine ⟨rows,?_,he,hall⟩
    have hp := payload_list_count_length rows
    have hproj := pairFst_length_le input
    rw [he] at hp
    omega

#print axioms inequality_rows_state_exact
end IV04.Paper.Computational
