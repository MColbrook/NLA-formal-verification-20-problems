module

public import NLA.IV04.PaperDenseContinuantProjectionDefinitions
public import NLA.IV04.PaperCountedOutputDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def rowProjectionReferenceRow (n i : ℕ) (words : List (List Bool)) : List Bool :=
  integerContinuantRow (words.getD (i*n+i) [])
    (if i=0 then [false] else words.getD (i*n+(i-1)) [])
    (if i=0 then [false] else words.getD ((i-1)*n+i) [])

def denseContinuantReferenceRows (n : ℕ) (words : List (List Bool)) : List (List Bool) :=
  (List.range n).map (fun i => rowProjectionReferenceRow n i words)

end IV04.Paper.Computational
