module

public import NLA.RA02.PaperSurvivalDefinitions
public import NLA.RA02.PaperHistoryTrace
public import NLA.RA02.CarryEncoding

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace NLA.RA02.Paper

theorem surviving_iff_activated {r : ℕ} (h : Fin r ↪ Fin (r+1)) :
    SurvivingHistory h ↔ ∀ i : Fin r, h i = Fin.last r ∨ (h i).val ≤ i.val := by
  constructor
  · intro hs i
    by_cases he : h i = Fin.last r
    · exact Or.inl he
    · right
      by_contra hn
      have hv : (h i).val < r := by
        have hlt := (h i).isLt
        have hne : (h i).val ≠ r := fun hh => he (Fin.ext hh)
        omega
      let s : Fin r := ⟨(h i).val,hv⟩
      apply hs s
      refine ⟨⟨i.val, by change i.val < (h i).val; omega⟩, ?_⟩
      change h (⟨i.val, _⟩ : Fin r) = s.castSucc
      exact Fin.ext rfl
  · intro ha s
    rintro ⟨i,hi⟩
    have hh := ha (Fin.castLE s.isLt.le i)
    change h (Fin.castLE s.isLt.le i) = s.castSucc at hi
    rw [hi] at hh
    rcases hh with hh | hh
    · exact Fin.castSucc_ne_last s hh
    · have hlt := i.isLt
      change s.val ≤ i.val at hh
      omega

def retainedEmbedding (r : ℕ) (bits : Fin r → Bool) : Fin r ↪ Fin (r+1) :=
  ⟨NLA.RA02.retainedHistory r bits, List.nodup_ofFn.mp ((NLA.RA02.retained_history_count r).2.2 bits)⟩

theorem retainedEmbedding_survives (r : ℕ) (bits : Fin r → Bool) :
    SurvivingHistory (retainedEmbedding r bits) := by
  apply (surviving_iff_activated _).mpr
  intro i
  change (if bits i then NLA.RA02.carryLabel r bits i.val else i.castSucc) = Fin.last r ∨
    (if bits i then NLA.RA02.carryLabel r bits i.val else i.castSucc).val ≤ i.val
  cases hb : bits i with
  | false => simp [hb]
  | true =>
    simp only [hb, ↓reduceIte]
    rcases NLA.RA02.carryLabel_bounds r bits i.val i.isLt.le with hh | hh
    · exact Or.inl hh
    · exact Or.inr hh.le

theorem surviving_is_retained {r : ℕ} (h : Fin r ↪ Fin (r+1)) (hs : SurvivingHistory h) :
    ∃ bits : Fin r → Bool, retainedEmbedding r bits = h := by
  let bits : Fin r → Bool := fun i => decide (h i ≠ i.castSucc)
  have ha := (surviving_iff_activated h).mp hs
  have hh : ∀ m : ℕ, ∀ hm : m < r, NLA.RA02.retainedHistory r bits ⟨m,hm⟩ = h ⟨m,hm⟩ := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      let s : Fin r := ⟨m,hm⟩
      by_cases he : h s = s.castSucc
      · simp [NLA.RA02.retainedHistory, bits, s, he]
      · have hpref : NLA.RA02.retainedPrefix r bits m = List.ofFn (historyPrefix h hm.le) := by
          unfold NLA.RA02.retainedPrefix
          apply List.ext_getElem
          · simp [Nat.min_eq_left hm.le]
          · intro i hi hj
            have him : i < m := by simpa using hj
            simpa [historyPrefix] using ih i him (lt_trans him hm)
        have hnot : h s ∉ NLA.RA02.retainedPrefix r bits m := by
          rw [hpref]
          intro hmem
          obtain ⟨i,hi⟩ := List.mem_ofFn.mp hmem
          have heq := h.injective hi
          have hv := congrArg Fin.val heq
          change i.val = m at hv
          omega
        have hinit : h s ∈ NLA.RA02.initialLabels r (m+1) := by
          rcases ha s with hlast | hval
          · simp [NLA.RA02.initialLabels, hlast]
          · simp only [NLA.RA02.initialLabels, Finset.mem_filter, Finset.mem_univ, true_and]
            left
            change (h s).val < m+1
            change (h s).val ≤ m at hval
            omega
        rw [NLA.RA02.initialLabels_succ r m hm] at hinit
        have hprev : h s ∈ NLA.RA02.initialLabels r m := (Finset.mem_insert.mp hinit).resolve_left he
        have hcarry : h s = NLA.RA02.carryLabel r bits m := by
          by_contra hc
          apply hnot
          apply List.mem_toFinset.mp
          rw [NLA.RA02.retained_prefix_set r bits m hm.le]
          exact Finset.mem_erase.mpr ⟨hc,hprev⟩
        have hbit : bits s = true := by simp [bits, he]
        change (if bits s then NLA.RA02.carryLabel r bits m else s.castSucc) = h s
        rw [hbit]
        exact hcarry.symm
  refine ⟨bits, ?_⟩
  apply Function.Embedding.ext
  intro i
  exact hh i.val i.isLt

#print axioms surviving_is_retained
end NLA.RA02.Paper
