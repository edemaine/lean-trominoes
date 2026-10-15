/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.Incidence
import LeanTrominoes.SAT.ExactOne.PeriodicExactOneCNF
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalDrawing

/-! # Orientation constraints on arbitrary periodic colored graphs

One Boolean per edge orbit and translate specifies its direction. Source
and target incidences use opposite polarities, with the target value read at
the edge's source translate. Loops contribute both incidences. The finite
CNF compiler imposes exact-one at monochromatic vertices and equal inward
values at trichromatic vertices.
-/
namespace LeanTrominoes.TrichromaticGraphOrientation
open Gadget PeriodicOneInThree

/-- `true` marks a trichromatic vertex; `false` marks a monochromatic one.
Vertex names are the indices of this table. -/
abbrev Input := List Bool × List (PeriodicEdge Nat × WireColor)
abbrev End := Nat × PeriodicLiteral Nat × WireColor

def edgeEnds (tagged : (PeriodicEdge Nat × WireColor) × Nat) : List End :=
  [(tagged.1.1.source,(⟨tagged.2,(0,0),false⟩,tagged.1.2)),
   (tagged.1.1.target,(⟨tagged.2,Cell.sub (0,0) tagged.1.1.offset,true⟩,tagged.1.2))]

def ends (input : Input) : List End := input.2.zipIdx.flatMap edgeEnds

def endsAt (input : Input) (vertex : Nat) : List End :=
  (ends input).filter fun incidence => incidence.1 = vertex

def incoming (input : Input) (vertex : Nat) : PeriodicClause Nat :=
  (endsAt input vertex).map fun incidence => incidence.2.1

def colors (input : Input) (vertex : Nat) : List WireColor :=
  (endsAt input vertex).map fun incidence => incidence.2.2

def IsWellFormed (input : Input) : Prop :=
  (∀ edge ∈ input.2, edge.1.source < input.1.length ∧ edge.1.target < input.1.length) ∧
    ∀ vertex < input.1.length,
      (colors input vertex).length = 3 ∧
        if input.1.getD vertex false then
          ∀ color : WireColor, (colors input vertex).count color = 1
        else ∃ color : WireColor, ∀ c ∈ colors input vertex, c = color

def IsLocal (input : Input) : Prop := ∀ edge ∈ input.2, edge.1.span ≤ 1

/-- Coherence means all three inward values agree, so the indegree is zero
or three whenever the graph is well formed. -/
def Coherent (a : Nat → Cell → Bool) (cell : Cell) (literals : PeriodicClause Nat) : Prop :=
  ∀ l ∈ literals, ∀ r ∈ literals, l.Holds a cell ↔ r.Holds a cell

def IsOrientation (input : Input) (a : Nat → Cell → Bool) : Prop :=
  ∀ cell vertex, vertex < input.1.length →
    if input.1.getD vertex false then Coherent a cell (incoming input vertex)
    else ClauseHolds a cell (incoming input vertex)

def HasOrientation (input : Input) : Prop := ∃ a, IsOrientation input a

def Problem (input : Input) : Prop := IsWellFormed input ∧ HasOrientation input

def coherenceClauses (literals : PeriodicClause Nat) : List (PeriodicClause Nat) :=
  literals.flatMap fun l => literals.map fun r => [negate l,r]

def vertexClauses (input : Input) (vertex : Nat) : List (PeriodicClause Nat) :=
  if input.1.getD vertex false then coherenceClauses (incoming input vertex)
  else PeriodicExactOneCNF.clause (incoming input vertex)

def formula (input : Input) : PeriodicCNF Nat :=
  ⟨(List.range input.1.length).flatMap (vertexClauses input)⟩

private theorem negate_holds (a : Nat → Cell → Bool) (cell : Cell) (l : PeriodicLiteral Nat) :
    (negate l).Holds a cell ↔ ¬ l.Holds a cell := by
  simp only [PeriodicLiteral.Holds,negate]
  cases a l.atom (Cell.add cell l.offset) <;> cases l.value <;> decide

theorem coherenceClauses_correct (a : Nat → Cell → Bool) (cell : Cell)
    (literals : PeriodicClause Nat) :
    (∀ c ∈ coherenceClauses literals, c.Holds a cell) ↔ Coherent a cell literals := by
  simp only [coherenceClauses,List.forall_mem_flatMap,List.forall_mem_map,
    PeriodicClause.Holds,List.mem_cons,List.not_mem_nil,exists_eq_or_imp,negate_holds,
    or_false,exists_eq_left]
  constructor
  · intro h l hl r hr
    exact ⟨fun holds => (h l hl r hr).resolve_left (not_not.mpr holds),
      fun holds => (h r hr l hl).resolve_left (not_not.mpr holds)⟩
  · intro h l hl r hr
    exact not_or_of_imp ((h l hl r hr).mp)

theorem formula_satisfies_iff (input : Input) (a : Nat → Cell → Bool) :
    (formula input).Satisfies a ↔ IsOrientation input a := by
  simp only [formula,PeriodicCNF.Satisfies,List.forall_mem_flatMap,List.mem_range]
  apply forall_congr'
  intro cell
  apply forall_congr'
  intro vertex
  apply imp_congr_right
  intro _
  dsimp only [vertexClauses]
  split <;> simp only [coherenceClauses_correct,PeriodicExactOneCNF.clause_correct]

theorem formula_satisfiable_iff (input : Input) :
    (formula input).Satisfiable ↔ HasOrientation input :=
  exists_congr (formula_satisfies_iff input)

end LeanTrominoes.TrichromaticGraphOrientation
