module

public import Mathlib

@[expose] public section

/-!
# Exact interval-matrix complexity claims

The first theorem gives NP-completeness of determinant threshold decision and
NP-hardness of exact determinant-range output on the specified rational
tridiagonal interval matrices. The second gives NP-hardness of the full solution
hull output. The definitions below retain the original binary encodings,
machine model, polynomial-time reductions and real interval semantics.
The corresponding Solution imports the complete proved development.
-/

/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
section
/- Source module: NLA.IV04.Complexitylib.Encoding.Delimit -/
namespace Complexity
/-- Frame a binary string as a self-delimiting block: each payload bit is doubled
    (`false ↦ [false, false]`, `true ↦ [true, true]`) and the block is terminated by the
    separator `[false, true]`, which no run of doubled bits can produce. -/
def delimit (x : List Bool) : List Bool :=
  (x.flatMap fun b => [b, b]) ++ [false, true]
end Complexity
end

section
/- Source module: NLA.IV04.Complexitylib.Encoding.Pairing -/
namespace Complexity
/-- Encode a pair of binary strings as a single binary string.
    Each bit of `x` is doubled (`false ↦ [false, false]`, `true ↦ [true, true]`),
    followed by the separator `[false, true]`, followed by `y` verbatim.
    The output has length `2|x| + 2 + |y|` (`pair_length`) and the encoding is
    injective (`pair_inj`). Machine-level cost is recorded elsewhere: `pair` of
    two `FP` functions is in `FP` (`mem_FP_pair`), and `x ↦ pair (f x) x` has
    an explicit bound (`TM.pairWithInputTM_computesInTime`); no linear-time
    bound for `pair` itself is stated. -/
def pair (x y : List Bool) : List Bool :=
  delimit x ++ y
end Complexity
end

section
/- Source module: NLA.IV04.PaperWordAdderDefinitions -/
set_option autoImplicit false
namespace IV04.Paper.Computational
/-- The first output bit, with false for an empty word. -/
def firstBit (bits : List Bool) : Bool := bits.headD false
end IV04.Paper.Computational
end

section
/- Source module: PaperDefinitions -/
set_option autoImplicit false
noncomputable section
namespace IV04.Paper
/-- Real square matrices of order n. -/
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
end IV04.Paper
end
end

section
/- Source module: NLA.IV04.PaperEncodingDefinitions -/
set_option autoImplicit false
namespace IV04.Paper
/-- Unary length followed by the canonical least-significant-first payload. -/
def naturalCode (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits
/-- Read true bits up to a false terminator, returning their count and the unused suffix. -/
def readUnary : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0,rest)
  | true :: rest => do
      let (n,tail) ← readUnary rest
      return (n+1,tail)
/-- Read a unary payload length and that many least-significant-first binary digits. -/
def readNatural (bits : List Bool) : Option (ℕ × List Bool) := do
  let (n,tail) ← readUnary bits
  if n ≤ tail.length then
    return ((tail.take n).foldr Nat.bit 0,tail.drop n)
  else none
/-- Encode a rational by its sign, absolute numerator and positive denominator. -/
def rationalCode (q : ℚ) : List Bool :=
  decide (q.num < 0) :: (naturalCode q.num.natAbs ++ naturalCode q.den)
/-- Read sign, numerator and denominator fields using rational division, with the unused suffix. -/
def readRational : List Bool → Option (ℚ × List Bool)
  | [] => none
  | sign :: rest => do
      let (num,tail) ← readNatural rest
      let (den,last) ← readNatural tail
      let signed : ℤ := if sign then -(num : ℤ) else (num : ℤ)
      return ((signed : ℚ)/(den : ℚ),last)
namespace IntegerPartition
end IntegerPartition
end IV04.Paper
end

section
/- Source module: NLA.IV04.Complexitylib.Models.TuringMachine -/
namespace Complexity
/-- The tape alphabet Γ = {0, 1, □, ▷}. -/
inductive Γ where
  | zero | one | blank | start
  deriving Repr, DecidableEq
instance : Fintype Γ where
  elems := {.zero, .one, .blank, .start}
  complete := fun x => by cases x <;> simp
instance : Inhabited Γ := ⟨Γ.blank⟩
/-- The writable alphabet Γw = {0, 1, □}. The start symbol `▷` cannot be written by a
    transition function — this is enforced structurally by using `Γw` in the output of `δ`. -/
inductive Γw where
  | zero | one | blank
  deriving Repr, DecidableEq
instance : Fintype Γw where
  elems := {.zero, .one, .blank}
  complete := fun x => by cases x <;> simp
/-- Embed a writable symbol into the full alphabet. -/
@[simp] def Γw.toΓ : Γw → Γ
  | .zero => .zero
  | .one => .one
  | .blank => .blank
instance : Coe Γw Γ where coe := Γw.toΓ
/-- Convert a boolean to an alphabet symbol. -/
def Γ.ofBool : Bool → Γ
  | false => .zero
  | true => .one
/-- Three-way tape head direction: left, right, or stay. -/
inductive Dir3 where
  | left | right | stay
  deriving Repr, DecidableEq
instance : Fintype Dir3 where
  elems := {.left, .right, .stay}
  complete := fun x => by cases x <;> simp
/-- A one-sided infinite tape: a head position and the contents of every cell.
    Cell 0 is the leftmost cell. The head cannot move left of cell 0 (moving
    left at position 0 is a no-op via `Nat` subtraction), and writing at cell 0
    is a no-op.

    The structure itself allows any symbol in any cell. The left-end marker `▷`
    at cell 0 is an invariant of the semantics, not of the type: `Tape.init`
    places it, machines write only symbols of `Γw` (never `▷`), and writes at
    cell 0 are ignored, so every tape reachable from an initial configuration
    satisfies `Tape.StartInvariant`. Statements about arbitrary tapes that need
    the marker must assume that invariant. -/
@[ext]
structure Tape where
  head : ℕ
  cells : ℕ → Γ
namespace Tape
/-- Read the symbol under the head. -/
def read (t : Tape) : Γ := t.cells t.head
/-- Write a symbol at the head position. Writing at cell 0 is a no-op,
    preserving the start symbol `▷`. -/
def write (t : Tape) (s : Γ) : Tape :=
  if t.head = 0 then t
  else { t with cells := Function.update t.cells t.head s }
/-- Move the head according to a three-way direction.
    Moving left at position 0 stays at 0 (`Nat` subtraction saturates). -/
def move (t : Tape) (d : Dir3) : Tape :=
  match d with
  | .left => { t with head := t.head - 1 }
  | .right => { t with head := t.head + 1 }
  | .stay => t
/-- The tape contains output `y : List Bool` starting at cell 1:
    cells 1 through |y| match `y`, and cell |y| + 1 is blank.
    Output is the binary string written on the output tape after `▷`. -/
def HasOutput (t : Tape) (y : List Bool) : Prop :=
  (∀ (i : ℕ) (h : i < y.length),
    t.cells (i + 1) = Γ.ofBool (y[i]'h)) ∧
  t.cells (y.length + 1) = Γ.blank
instance decidableHasOutput (t : Tape) (y : List Bool) : Decidable (t.HasOutput y) :=
  if h : (∀ i : Fin y.length, t.cells (i.val + 1) = Γ.ofBool (y[i.val]'i.isLt)) ∧
         t.cells (y.length + 1) = Γ.blank
  then isTrue ⟨fun i hi => h.1 ⟨i, hi⟩, h.2⟩
  else isFalse (fun ⟨h1, h2⟩ => h ⟨fun i => h1 i.val i.isLt, h2⟩)
/-- Write a symbol and move in one step. -/
abbrev writeAndMove (t : Tape) (s : Γ) (d : Dir3) : Tape :=
  (t.write s).move d
end Tape
/-- Initialize a tape: `▷` at cell 0, `contents` at cells 1, 2, ..., `□` elsewhere.
    Head starts at position 0 (on `▷`). -/
def Tape.init (contents : List Γ) : Tape where
  head := 0
  cells := fun i =>
    if i = 0 then Γ.start
    else (contents[i - 1]?).getD Γ.blank
/-- A language is a set of binary strings. -/
abbrev Language := Set (List Bool)
/-- A configuration of a Turing machine with `n` work tapes:
    a read-only input tape, `n` read-write work tapes, and a read-write output tape. -/
structure Cfg (n : ℕ) (Q : Type) where
  state : Q
  input : Tape
  work : Fin n → Tape
  output : Tape
namespace Cfg
/-- Initial configuration for any TM: input on the input tape, all tapes start with `▷`. -/
abbrev init (qstart : Q) (x : List Bool) : Cfg n Q :=
  { state := qstart
    input := Tape.init (x.map Γ.ofBool)
    work := fun _ => Tape.init []
    output := Tape.init [] }
/-- A configuration is halted when its state equals the halt state. -/
abbrev isHalted (qhalt : Q) (c : Cfg n Q) : Prop :=
  c.state = qhalt
end Cfg
/-- A deterministic Turing machine with `n` work tapes.

    The machine has a read-only input tape, `n` read-write work tapes, and a read-write
    output tape. The transition function reads `Γ` from all tape heads but writes only
    `Γw` (excluding `▷`) to work and output tapes. `Q` is finite. -/
structure TM (n : ℕ) where
  Q : Type
  [decEq : DecidableEq Q]
  [finQ : Fintype Q]
  qstart : Q
  qhalt : Q
  δ : Q → Γ → (Fin n → Γ) → Γ →
      Q × (Fin n → Γw) × Γw × Dir3 × (Fin n → Dir3) × Dir3
  δ_right_of_start : ∀ (q : Q) (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ),
    let (_, _, _, inDir, workDirs, outDir) := δ q iHead wHeads oHead
    (iHead = Γ.start → inDir = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → workDirs i = Dir3.right) ∧
    (oHead = Γ.start → outDir = Dir3.right)
attribute [instance] TM.decEq TM.finQ
/-- A nondeterministic Turing machine with two transition functions.

    The same structure is used for probabilistic TMs — only the acceptance
    criterion differs (existential for NTM, counting for PTM). `Q` is finite. -/
structure NTM (n : ℕ) where
  Q : Type
  [decEq : DecidableEq Q]
  [finQ : Fintype Q]
  qstart : Q
  qhalt : Q
  δ : Bool → Q → Γ → (Fin n → Γ) → Γ →
      Q × (Fin n → Γw) × Γw × Dir3 × (Fin n → Dir3) × Dir3
  δ_right_of_start : ∀ (b : Bool) (q : Q) (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ),
    let (_, _, _, inDir, workDirs, outDir) := δ b q iHead wHeads oHead
    (iHead = Γ.start → inDir = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → workDirs i = Dir3.right) ∧
    (oHead = Γ.start → outDir = Dir3.right)
attribute [instance] NTM.decEq NTM.finQ
namespace TM
variable {n : ℕ}
/-- Step a deterministic TM by one step. Returns `none` if halted. -/
def step (tm : TM n) (c : Cfg n tm.Q) : Option (Cfg n tm.Q) :=
  if c.state = tm.qhalt then none
  else
    let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
      tm.δ c.state c.input.read (fun i => (c.work i).read) c.output.read
    some
      { state := q'
        input := c.input.move inDir
        work := fun i => (c.work i).writeAndMove (workWrites i) (workDirs i)
        output := c.output.writeAndMove outWrite outDir }
/-- Initial configuration: input on the input tape, all tapes start with `▷`. -/
abbrev initCfg (tm : TM n) (x : List Bool) : Cfg n tm.Q :=
  Cfg.init tm.qstart x
/-- A configuration is halted when its state is `qhalt`. -/
abbrev halted (tm : TM n) (c : Cfg n tm.Q) : Prop :=
  Cfg.isHalted tm.qhalt c
/-- Reachability in exactly `t` steps. -/
inductive reachesIn (tm : TM n) : ℕ → Cfg n tm.Q → Cfg n tm.Q → Prop where
  | zero : reachesIn tm 0 c c
  | step : tm.step c = some c'' → reachesIn tm t c'' c' → reachesIn tm (t + 1) c c'
/-- DTM computes function `f` in time `T(n)`:
    for every input `x`, the machine halts within `T(|x|)` steps with `f(x)`
    written on the output tape. -/
def ComputesInTime (tm : TM n) (f : List Bool → List Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x, ∃ c' t, t ≤ T x.length ∧ tm.reachesIn t (tm.initCfg x) c' ∧ tm.halted c' ∧
    c'.output.HasOutput (f x)
end TM
namespace NTM
variable {n : ℕ}
/-- Execute an NTM for `T` steps with a fixed choice sequence.
    Stops early if the machine reaches `qhalt`. -/
def trace (tm : NTM n) :
    (T : ℕ) → (Fin T → Bool) → Cfg n tm.Q → Cfg n tm.Q
  | 0, _, c => c
  | T + 1, choices, c =>
    if c.state = tm.qhalt then c
    else
      let b := choices ⟨0, Nat.zero_lt_succ T⟩
      let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
        tm.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read
      let c' : Cfg n tm.Q :=
        { state := q'
          input := c.input.move inDir
          work := fun i => (c.work i).writeAndMove (workWrites i) (workDirs i)
          output := c.output.writeAndMove outWrite outDir }
      tm.trace T (fun i => choices ⟨i.val + 1, by omega⟩) c'
/-- Initial configuration: input on the input tape, all tapes start with `▷`. -/
abbrev initCfg (tm : NTM n) (x : List Bool) : Cfg n tm.Q :=
  Cfg.init tm.qstart x
/-- A configuration is halted when its state is `qhalt`. -/
abbrev halted (tm : NTM n) (c : Cfg n tm.Q) : Prop :=
  Cfg.isHalted tm.qhalt c
/-- NTM accepts `x` within `T` steps: there exists a choice sequence of length `T`
    leading to `qhalt` with output cell 1 = `1`. -/
def AcceptsInTime (tm : NTM n) (x : List Bool) (T : ℕ) : Prop :=
  ∃ choices : Fin T → Bool,
    let c' := tm.trace T choices (tm.initCfg x)
    tm.halted c' ∧ c'.output.cells 1 = Γ.one
/-- All computation paths of the NTM halt within `T(|x|)` steps, for every
    input `x` and every choice sequence. This is the core time-boundedness
    condition shared by `DecidesInTime`, `BPTIME`, and `NTM.IsPPT`. -/
def AllPathsHaltIn (tm : NTM n) (T : ℕ → ℕ) : Prop :=
  ∀ x (choices : Fin (T x.length) → Bool),
    tm.halted (tm.trace (T x.length) choices (tm.initCfg x))
/-- NTM decides `L` within time bound `T(n)`:
    all computation paths halt within `T(|x|)` steps, and accepting paths exist
    iff `x ∈ L` (AB Definition 2.1). -/
def DecidesInTime (tm : NTM n) (L : Language) (T : ℕ → ℕ) : Prop :=
  tm.AllPathsHaltIn T ∧
  (∀ x, x ∈ L ↔ tm.AcceptsInTime x (T x.length))
end NTM
end Complexity
end

section
/- Source module: NLA.IV04.Complexitylib.Asymptotics -/
open Asymptotics Filter
namespace Complexity
/-- `f` grows at most as fast as `g` asymptotically: `f(n) = O(g(n))` as `n → ∞`.
    Lifts Mathlib's `Asymptotics.IsBigO` to `ℕ → ℕ` functions, avoiding
    repeated `Nat.cast` coercions in complexity class definitions.

    Unfolding: `f =O g ↔ ∃ C, ∀ᶠ n in atTop, ↑(f n) ≤ C * ↑(g n)`. -/
def BigO (f g : ℕ → ℕ) : Prop :=
  (fun n => (f n : ℝ)) =O[atTop] (fun n => (g n : ℝ))
@[inherit_doc BigO]
scoped infixl:50 " =O " => BigO
end Complexity
end

section
/- Source module: NLA.IV04.Complexitylib.Classes.Time -/
namespace Complexity
/-- `NTIME(T)` is the class of languages decidable by a nondeterministic TM in
    time `O(T(n))` (AB Definition 2.1). The machine may have any number of
    work tapes. -/
def NTIME (T : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : NTM k) (f : ℕ → ℕ),
    tm.DecidesInTime L f ∧ f =O T}
end Complexity
end

section
/- Source module: NLA.IV04.Complexitylib.Classes.NP -/
namespace Complexity
/-- **NP** is the class of languages decidable by a nondeterministic TM in
    polynomial time: `NP = ⋃_k NTIME(n^k)`. -/
def NP : Set Language :=
  ⋃ k : ℕ, NTIME (· ^ k)
end Complexity
end

section
/- Source module: NLA.IV04.Complexitylib.Classes.P.Defs -/
namespace Complexity
/-- **FP** is the class of functions computable by a deterministic TM in
    polynomial time. -/
def FP : Set (List Bool → List Bool) :=
  {f | ∃ (d k : ℕ) (tm : TM k) (T : ℕ → ℕ),
    tm.ComputesInTime f T ∧ T =O (· ^ d)}
end Complexity
end

section
/- Source module: NLA.IV04.PaperRationalListParserDefinitions -/
set_option autoImplicit false
namespace IV04.Paper.Computational
/-- Semantic reference; the requested count is a natural value, not a runtime certificate. -/
def readRationals : ℕ → List Bool → Option (List ℚ × List Bool)
  | 0, input => some ([],input)
  | count+1, input => do
      let (value,tail) ← IV04.Paper.readRational input
      let (values,last) ← readRationals count tail
      return (value :: values,last)
end IV04.Paper.Computational
end

section
/- Source module: NLA.IV04.PaperMatrixCoefficientInputDefinitions -/
set_option autoImplicit false
namespace IV04.Paper.Computational
/-- Semantic reference to the manuscript's natural and rational decoders. -/
def readMatrixRationals (input : List Bool) : Option (ℕ × List ℚ × List Bool) := do
  let (n,rest) ← IV04.Paper.readNatural input
  let (values,tail) ← readRationals (2*n*n+1) rest
  return (n,values,tail)
end IV04.Paper.Computational
end

section
/- Source module: NLA.IV04.PaperMatrixDenseSupportReference -/
set_option autoImplicit false
namespace IV04.Paper.Computational
/-- Check that both row-major endpoint tables vanish outside the three central diagonals. -/
def rationalDenseEndpointAll (n : ℕ) : ℕ → ℕ → List (ℚ × ℚ) → Prop
  | _, _, [] => True
  | i, j, (lower,upper)::rows =>
      ((i ≤ j+1 ∧ j ≤ i+1) ∨ (lower=0 ∧ upper=0)) ∧
      rationalDenseEndpointAll n (if n ≤ j+1 then i+1 else i) (if n ≤ j+1 then 0 else j+1) rows
end IV04.Paper.Computational
end

section
/- Source module: NLA.IV04.PaperRealIntervalVertexDefinitions -/
set_option autoImplicit false
namespace IV04.Paper.Computational
noncomputable section
/-- The real lower endpoint at row-major index i*n+j, using zero as the list default. -/
def boxLowerReal (n : ℕ) (pairs : List (ℚ × ℚ)) (i j : Fin n) : ℝ :=
  (pairs.getD (i.val*n+j.val) (0,0)).1
/-- The real upper endpoint at row-major index i*n+j, using zero as the list default. -/
def boxUpperReal (n : ℕ) (pairs : List (ℚ × ℚ)) (i j : Fin n) : ℝ :=
  (pairs.getD (i.val*n+j.val) (0,0)).2
/-- All real matrices in the literal dense row-major rational interval box. -/
def realDenseIntervalBox (n : ℕ) (pairs : List (ℚ × ℚ)) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | ∀ i j, boxLowerReal n pairs i j ≤ A i j ∧ A i j ≤ boxUpperReal n pairs i j}
/-- The actual determinant threshold task quantifies over every real interval realization. -/
def rationalMatrixDeterminantDecisionLanguage : Set (List Bool) :=
  {matrix | ∃ (n : ℕ) (pairs : List (ℚ × ℚ)) (threshold : ℚ),
    readMatrixRationals matrix=some (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],[]) ∧
    pairs.length=n*n ∧ (∀ row ∈ pairs, row.1 ≤ row.2) ∧ rationalDenseEndpointAll n 0 0 pairs ∧
    ∃ A ∈ realDenseIntervalBox n pairs, (threshold : ℝ) ≤ A.det}
end
end IV04.Paper.Computational
end

section
/- Source module: NLA.IV04.Complexitylib.Classes.NP.Reduction -/
namespace Complexity
/-- **Polynomial-time many-one reduction.** `MapReducesPoly L L'` (written
    `L ≤ₚ L'`) holds when there is a polynomial-time computable function `f`
    (`f ∈ FP`) with `x ∈ L ↔ f x ∈ L'` for every input `x`. -/
def MapReducesPoly (L L' : Language) : Prop :=
  ∃ f : List Bool → List Bool, f ∈ FP ∧ ∀ x, x ∈ L ↔ f x ∈ L'
@[inherit_doc] infix:50 " ≤ₚ " => MapReducesPoly
/-- **NP-hardness.** `L` is NP-hard when every language in `NP` reduces to `L`
    in polynomial time. -/
def NPHard (L : Language) : Prop := ∀ L' ∈ NP, L' ≤ₚ L
/-- **NP-completeness.** `L` is NP-complete when it is in `NP` and NP-hard. -/
def NPComplete (L : Language) : Prop := L ∈ NP ∧ NPHard L
end Complexity
end

section
/- Source module: NLA.IV04.PaperConstructedHullDefinitions -/
set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace IV04.Paper
/-- The fixed right-hand side minus the last coordinate vector. -/
def positiveCornerRhs (n : ℕ) (hn : 0 < n) : Fin n → ℝ :=
  Pi.single ⟨n-1,Nat.sub_lt hn (by decide)⟩ (-1)
/-- The union of solution sets A*x = -e_last over matrices A in S. -/
def positiveSolutions (n : ℕ) (hn : 0 < n) (S : Set (Mat n)) : Set (Fin n → ℝ) :=
  {x | ∃ A ∈ S, A.mulVec x=positiveCornerRhs n hn}
namespace IntegerPartition
end IntegerPartition
end IV04.Paper
end
end

section
/- Source module: NLA.IV04.PaperExactOutputHardnessDefinitions -/
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity
/-- One literal call to an output task, with polynomial-time bit programs before and after it. -/
def PolynomialOneQueryReduction (L : Set (List Bool))
    (task : List Bool → List Bool → Prop) : Prop :=
  ∃ query : List Bool → List Bool, query ∈ FP ∧
    ∃ finish : List Bool → List Bool, finish ∈ FP ∧
      (∀ input, ∃ answer, task (query input) answer) ∧
      ∀ input answer, task (query input) answer →
        (firstBit (finish (pair input answer)) = true ↔ input ∈ L)
/-- Every NP language has a polynomial-time one-query reduction to this exact output relation. -/
def NPHardOutputTask (task : List Bool → List Bool → Prop) : Prop :=
  ∀ L ∈ NP, PolynomialOneQueryReduction L task
noncomputable section
/-- Two complete rational fields are the actual minimum and maximum determinants. -/
def ExactDeterminantRangeOutput (matrix answer : List Bool) : Prop :=
  ∃ (n : ℕ) (pairs : List (ℚ × ℚ)),
    readMatrixRationals matrix = some (n,pairs.flatMap (fun row => [row.1,row.2]) ++ [0],[]) ∧
    pairs.length = n*n ∧ (∀ row ∈ pairs, row.1 ≤ row.2) ∧ rationalDenseEndpointAll n 0 0 pairs ∧
    ∃ (lo hi : ℚ) (tail : List Bool),
      IV04.Paper.readRational answer = some (lo,tail) ∧
      IV04.Paper.readRational tail = some (hi,[]) ∧
      IsLeast (Matrix.det '' realDenseIntervalBox n pairs) (lo : ℝ) ∧
      IsGreatest (Matrix.det '' realDenseIntervalBox n pairs) (hi : ℝ)
end
end IV04.Paper.Computational
end

section
/- Source module: NLA.IV04.PaperFullHullProjectionDefinitions -/
set_option autoImplicit false
namespace IV04.Paper.Computational
noncomputable section
/-- Complete finite solution-hull output: literal lower/upper rational endpoints for every coordinate. -/
def ExactFullHullOutput (matrix answer : List Bool) : Prop :=
  ∃ (n : ℕ) (hn : 0 < n) (pairs bounds : List (ℚ × ℚ)),
    readMatrixRationals matrix = some (n,pairs.flatMap (fun row => [row.1,row.2]) ++ [0],[]) ∧
    pairs.length = n*n ∧ (∀ row ∈ pairs, row.1 ≤ row.2) ∧ rationalDenseEndpointAll n 0 0 pairs ∧
    (∀ A ∈ realDenseIntervalBox n pairs, A.det ≠ 0 ∧
      ∀ i j : Fin n, j.val = i.val+1 → A i j = 1) ∧
    (IV04.Paper.positiveSolutions n hn (realDenseIntervalBox n pairs)).Nonempty ∧
    Bornology.IsBounded (IV04.Paper.positiveSolutions n hn (realDenseIntervalBox n pairs)) ∧
    bounds.length = n ∧
    answer = bounds.flatMap (fun row => IV04.Paper.rationalCode row.1 ++ IV04.Paper.rationalCode row.2) ∧
    ∀ i : Fin n,
      IsLeast ((fun x : Fin n → ℝ => x i) ''
        IV04.Paper.positiveSolutions n hn (realDenseIntervalBox n pairs))
        ((bounds.getD i.val (0,0)).1 : ℝ) ∧
      IsGreatest ((fun x : Fin n → ℝ => x i) ''
        IV04.Paper.positiveSolutions n hn (realDenseIntervalBox n pairs))
        ((bounds.getD i.val (0,0)).2 : ℝ)
end
end IV04.Paper.Computational
end

section
/- Source module: NLA.IV04.PaperDeterminantHeadlineDefinitions -/
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity
noncomputable section
/-- A complete rational tridiagonal packet whose entire real interval family is regular
and has every superdiagonal entry fixed to one. -/
def RegularUnitMatrixPacket (matrix : List Bool) : Prop :=
  ∃ (n : ℕ) (pairs : List (ℚ × ℚ)) (threshold : ℚ),
    readMatrixRationals matrix =
      some (n,pairs.flatMap (fun row => [row.1,row.2]) ++ [threshold],[]) ∧
    pairs.length = n*n ∧ (∀ row ∈ pairs, row.1 ≤ row.2) ∧
    rationalDenseEndpointAll n 0 0 pairs ∧
    ∀ A ∈ realDenseIntervalBox n pairs, A.det ≠ 0 ∧
      ∀ i j : Fin n, j.val = i.val+1 → A i j = 1
/-- The determinant threshold language restricted to the regular unit-superdiagonal promise. -/
def regularUnitMatrixDeterminantDecisionLanguage : Set (List Bool) :=
  {matrix | matrix ∈ rationalMatrixDeterminantDecisionLanguage ∧ RegularUnitMatrixPacket matrix}
/-- Exact determinant-range output on a matrix satisfying the regular unit-superdiagonal promise. -/
def RegularUnitDeterminantRangeOutput (matrix answer : List Bool) : Prop :=
  ExactDeterminantRangeOutput matrix answer ∧ RegularUnitMatrixPacket matrix
end
end IV04.Paper.Computational
end

section
/- Source module: NLA.IV04.DeterminantHeadlineChallenge -/
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity
theorem actual_paper_iv_det :
  NPComplete rationalMatrixDeterminantDecisionLanguage ∧
  NPHard regularUnitMatrixDeterminantDecisionLanguage ∧
  NPHardOutputTask RegularUnitDeterminantRangeOutput := by sorry
end IV04.Paper.Computational
end

section
/- Source module: NLA.IV04.FullHullHardnessChallenge -/
set_option autoImplicit false
namespace Reference.IV04FullHullHardness
open Complexity IV04.Paper.Computational
theorem iv_hull_literal_np_hard : NPHardOutputTask ExactFullHullOutput := by
  sorry
end Reference.IV04FullHullHardness
end
