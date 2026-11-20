module

public import NLA.MD06.BoundedExcessPatterns.EventDefinitions
public import NLA.MD06.CubicConfiguration.Definitions
public import Mathlib.Data.Sym.Sym2.Order
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06GraphExcessEncoding
open Reference.MD06CubicConfiguration Reference.MD06BoundedExcess
attribute [local instance] Classical.propDecidable

abbrev GraphEdge {n : ℕ} (p : SimpleConfiguration n) (S : Finset (Fin n)) :=
  {uv : S × S // uv.1 < uv.2 ∧
    (configurationGraph p).Adj uv.1.val uv.2.val}

noncomputable instance graphEdgeFintype {n : ℕ} (p : SimpleConfiguration n)
    (S : Finset (Fin n)) : Fintype (GraphEdge p S) := Fintype.ofFinite _

def EdgeDarts {n : ℕ} {p : SimpleConfiguration n} {S : Finset (Fin n)}
    (e : GraphEdge p S) : Dart n × Dart n :=
  let x : Dart n := (e.val.1.val,Classical.choose e.property.2)
  (x,p.val.val x)

def InducedPattern {n : ℕ} (p : SimpleConfiguration n) (S : Finset (Fin n)) :
    Finset (Dart n × Dart n) := Finset.univ.image (EdgeDarts (p:=p) (S:=S))

def GraphHasBoundedExcess {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ) : Prop :=
  ∃ S : Finset (Fin n), S.card ≤ M ∧
    S.card+1 ≤ (G.induce (S : Set (Fin n))).edgeFinset.card

end Reference.MD06GraphExcessEncoding
