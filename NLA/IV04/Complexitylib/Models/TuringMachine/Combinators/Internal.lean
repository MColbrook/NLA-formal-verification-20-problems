/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import NLA.IV04.Complexitylib.Models.TuringMachine.Combinators.Internal.Complement
public import NLA.IV04.Complexitylib.Models.TuringMachine.Combinators.Internal.Seq
public import NLA.IV04.Complexitylib.Models.TuringMachine.Combinators.Internal.If
public import NLA.IV04.Complexitylib.Models.TuringMachine.Combinators.Internal.Loop
public import NLA.IV04.Complexitylib.Models.TuringMachine.Combinators.Internal.Retarget
public import NLA.IV04.Complexitylib.Models.TuringMachine.Combinators.Internal.Scanner
public import NLA.IV04.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import NLA.IV04.Complexitylib.Models.TuringMachine.Combinators.Internal.Union

@[expose] public section

/-!
# Combinator proof internals (aggregation)

This file aggregates the proof-internal modules for the Turing machine
combinators (`Complement`, `Seq`, `If`, `Loop`, `Retarget`, `Scanner`,
`Generic`, `Union`). It contains no definitions of its own; it exists so
that the surface module `Combinators.lean` can pull in all combinator
proof internals with a single import.
-/
