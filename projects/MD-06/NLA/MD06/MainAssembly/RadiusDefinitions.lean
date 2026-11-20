module

public import Mathlib.Data.Nat.Log

@[expose] public section

namespace Reference.MD06MainAssembly
def PaperRadius (ell : Nat) : Nat := 29+Nat.clog 2 ell
end Reference.MD06MainAssembly
