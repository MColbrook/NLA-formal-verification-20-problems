module

public import NLA.NM04.PositiveMargins.Schur
public import NLA.NM04.PositiveMargins.Cofactors
public import NLA.NM04.PositiveMargins.Action
public import NLA.NM04.RankOneBordered
public import NLA.NM04.SchurBordered
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

namespace NLA.NM04.PositiveMargins
noncomputable section
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable

theorem actual_minor_relation {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (S : Rect m n) (a : Fin m → ℝ) (b : Fin n → ℝ) (τ : ℝ)
    (hx : S (firstIndex hm) (firstIndex hn) ≠ 0)
    (ha0 : a (firstIndex hm) ≠ 0) (hb0 : b (firstIndex hn) ≠ 0)
    (hS : Margins S a b) (ha : ∑ i, a i = τ) (I : Index m n) :
    a (firstIndex hm) * b (firstIndex hn) * minor (tailMatrix S) I +
      action (fun i : Tail m => a i.val) (fun j : Tail n => b j.val) τ
        (delta S hm hn) I = 0 := by
  let T := schurTail S hm hn
  let x := S (firstIndex hm) (firstIndex hn)
  let a0 := a (firstIndex hm)
  let b0 := b (firstIndex hn)
  let aTail := fun i : Tail m => a i.val
  let bTail := fun j : Tail n => b j.val
  have htotal : (∑ i : Tail m, ∑ j : Tail n, T i j) = τ - a0 * b0 / x :=
    (schur_margins hm hn S a b τ hx hS ha).2.2
  have hdelta : delta S hm hn = fun J => x * minor T J :=
    funext (fun J => schur_bordered_minor hm hn S hx J)
  have hminor : minor (tailMatrix S) I = minor T I + (x / (a0 * b0)) *
      (lower aTail bTail (minor T) I -
        ((∑ s : I.1.2, bTail s) * minor T I + column bTail (minor T) I) -
        ((∑ s : I.1.1, aTail s) * minor T I + row aTail (minor T) I) +
        (τ - a0 * b0 / x) * minor T I - raising (minor T) I) := by
    calc
      _ = minor (T + (x / (a0 * b0)) • Matrix.vecMulVec
          (fun i => aTail i - ∑ j, T i j) (fun j => bTail j - ∑ i, T i j)) I :=
        congrArg (fun U : Matrix (Tail m) (Tail n) ℝ => minor U I)
          (schur_reconstruction hm hn S a b τ hx ha0 hb0 hS ha)
      _ = _ := by
        rw [universal_rank_one_update, weighted_direction, htotal]
  rw [hminor, hdelta, action_smul]
  unfold action diagonal
  dsimp only [aTail, bTail, a0, b0, x]
  field_simp [hx, ha0, hb0]
  ring

#print axioms actual_minor_relation
end
end NLA.NM04.PositiveMargins
