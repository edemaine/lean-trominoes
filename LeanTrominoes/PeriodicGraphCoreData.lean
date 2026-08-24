/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFCoreData

/-! # Core data for periodic incidence graphs -/

namespace LeanTrominoes

/-- One undirected protoedge.  At lattice translate `z`, it joins
`(source, z)` to `(target, z + offset)`. -/
structure PeriodicEdge (Vertex : Type*) where
  source : Vertex
  target : Vertex
  offset : Cell
  deriving DecidableEq, Repr

/-- The two colors of vertices in a CNF incidence graph. -/
inductive CNFVertex (Variable : Type*)
  | variable (atom : Variable)
  | clause (index : Nat)
  deriving DecidableEq, Repr

namespace PeriodicCNF

/-- A clause orbit is placed at the first literal's offset.  Empty clauses
have no incidence edges, so their arbitrary anchor is irrelevant. -/
def clauseAnchor {Variable : Type*}
    (clause : PeriodicClause Variable) : Cell :=
  (clause.head?.map PeriodicLiteral.offset).getD (0, 0)

/-- The incidence edge belonging to one literal occurrence. -/
def incidenceEdge {Variable : Type*}
    (clauseIndex : Nat) (anchor : Cell)
    (literal : PeriodicLiteral Variable) :
    PeriodicEdge (CNFVertex Variable) where
  source := .clause clauseIndex
  target := .variable literal.atom
  offset := Cell.sub literal.offset anchor

end PeriodicCNF
end LeanTrominoes
