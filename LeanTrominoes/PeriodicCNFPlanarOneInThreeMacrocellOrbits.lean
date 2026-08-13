/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarOneInThreePlacements
import LeanTrominoes.PeriodicMacrocellOrbitGeometry

/-!
# Macrocell orbits of the planar exact-one placements

The two clause-replacement layers store auxiliary protovariables in the
anchor gauge of their source clause.  These lemmas express those stored
positions, as well as inherited variables, modulo the refined physical
period.  The resulting interface composes independently of the chosen
logical clause anchors.
-/

namespace LeanTrominoes

namespace PeriodicOneInThreePositioned

/-- Figure Nine clause offset measured from the origin of its source
macrocell. -/
def generatedClauseLocalPosition (generatedIndex : Nat) : Cell :=
  PlanarOneInThree.generatedClausePosition (0, 0) generatedIndex

/-- Every generated Figure Nine clause is exactly the macrocell point
selected by its local clause index. -/
theorem generatedClausePosition_eq_macrocellPosition
    (sourcePosition : Cell) (generatedIndex : Nat) :
    PlanarOneInThree.generatedClausePosition
        sourcePosition generatedIndex =
      Cell.macrocellPosition 12 sourcePosition
        (generatedClauseLocalPosition generatedIndex) := by
  simp [generatedClauseLocalPosition,
    PlanarOneInThree.generatedClausePosition,
    Cell.macrocellPosition, PlanarOneInThree.gadgetScale,
    Cell.add, Cell.scale]

/-- In particular, every generated clause belongs to the corresponding
source-clause macrocell orbit for any ambient physical period. -/
theorem generatedClausePosition_inMacrocellOrbit
    (period : Nat) (sourcePosition : Cell) (generatedIndex : Nat) :
    Cell.InMacrocellOrbit 12 period sourcePosition
      (generatedClauseLocalPosition generatedIndex)
      (PlanarOneInThree.generatedClausePosition
        sourcePosition generatedIndex) := by
  refine ⟨(0, 0), ?_⟩
  simpa [Cell.add, Cell.scale] using
    generatedClausePosition_eq_macrocellPosition
      sourcePosition generatedIndex

/-- The outer presentation index of a clause in one Figure Nine block is
the local index used to select its geometric clause offset. -/
theorem clauseGadget_position_eq_generatedClausePosition
    {Variable : Type*}
    (sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable)
    {clause : PositionedPeriodicClause (OneInThreeVariable Variable)}
    {generatedIndex : Nat}
    (clauseMember :
      (clause, generatedIndex) ∈
        (clauseGadget sourceClauseIndex sourceClause).zipIdx) :
    clause.position =
      PlanarOneInThree.generatedClausePosition
        sourceClause.position generatedIndex := by
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  unfold clauseGadget at clauseLookup
  rw [List.getElem?_map, List.getElem?_zipIdx] at clauseLookup
  simp only [Option.map_eq_some_iff] at clauseLookup
  rcases clauseLookup with ⟨taggedClause, taggedLookup, clauseEqual⟩
  rcases taggedLookup with
    ⟨generatedClause, generatedClauseLookup, taggedEqual⟩
  subst taggedClause
  simpa using
    congrArg PositionedPeriodicClause.position clauseEqual.symm

/-- A Figure Nine block has at most the six local clause positions reserved
by its geometry. -/
theorem clauseGadget_length_le_six
    {Variable : Type*}
    (sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable) :
    (clauseGadget sourceClauseIndex sourceClause).length ≤ 6 := by
  rcases sourceClause with ⟨sourcePosition, literals⟩
  cases literals with
  | nil =>
      simp [clauseGadget, PeriodicOneInThree.clauseClauses,
        PeriodicOneInThree.disjunctionGadget]
  | cons first rest =>
      cases rest with
      | nil =>
          simp [clauseGadget, PeriodicOneInThree.clauseClauses,
            PeriodicOneInThree.disjunctionGadget]
      | cons second tail =>
          cases tail with
          | nil =>
              simp [clauseGadget, PeriodicOneInThree.clauseClauses,
                PeriodicOneInThree.disjunctionGadget]
          | cons third tail =>
              simp [clauseGadget, PeriodicOneInThree.clauseClauses,
                PeriodicOneInThree.disjunctionGadget]

/-- An inherited Figure Nine variable occupies the origin of the refined
macrocell over its source variable. -/
theorem placement_inherited_inMacrocellOrbit
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    Cell.InMacrocellOrbit 12 sourcePlacement.period
      (sourcePlacement.position atom) (0, 0)
      ((placement source sourcePlacement).position (.inl atom)) := by
  refine ⟨(0, 0), ?_⟩
  simp [placement, Cell.macrocellPosition,
    PlanarOneInThree.gadgetScale, Cell.add, Cell.scale]

/-- A Figure Nine auxiliary lies at its declared local point over the source
clause, up to the whole-period translation selecting its anchor gauge. -/
theorem placement_auxiliary_inMacrocellOrbit
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (kind : OneInThreeAux) :
    Cell.InMacrocellOrbit 12 sourcePlacement.period
      (source.clausePosition clauseIndex)
      (auxiliaryLocalPosition kind)
      ((placement source sourcePlacement).position
        (.inr ((clauseIndex, clause), kind))) := by
  refine ⟨Cell.sub (0, 0) (PeriodicOneInThree.anchor clause), ?_⟩
  cases sourceEq : source.clausePosition clauseIndex with
  | mk sourceX sourceY =>
  cases localEq : auxiliaryLocalPosition kind with
  | mk localX localY =>
  cases anchorEq : PeriodicOneInThree.anchor clause with
  | mk anchorX anchorY =>
  simp [placement, auxiliaryOccurrencePosition,
    Cell.macrocellPosition, PlanarOneInThree.gadgetScale,
    Cell.add, Cell.sub, Cell.scale, sourceEq, localEq, anchorEq]
  constructor <;> ring

end PeriodicOneInThreePositioned

namespace PeriodicOneInThreeNoUnitsPositioned

/-- Unit-elimination clause offset selected by the source arity and local
generated-clause index. -/
def generatedClauseLocalPosition
    {Variable : Type*} (literals : PeriodicClause Variable)
    (generatedIndex : Nat) : Cell :=
  generatedClausePosition
    (⟨(0, 0), literals⟩ : PositionedPeriodicClause Variable)
    generatedIndex

/-- Every clause generated by unit elimination is exactly its source-clause
macrocell point. -/
theorem generatedClausePosition_eq_macrocellPosition
    {Variable : Type*}
    (source : PositionedPeriodicClause Variable)
    (generatedIndex : Nat) :
    generatedClausePosition source generatedIndex =
      Cell.macrocellPosition 6 source.position
        (generatedClauseLocalPosition source.literals generatedIndex) := by
  rcases source with ⟨⟨sourceX, sourceY⟩, literals⟩
  cases literals with
  | nil =>
      cases generatedIndex with
      | zero => rfl
      | succ generatedIndex =>
          cases generatedIndex with
          | zero => rfl
          | succ generatedIndex => rfl
  | cons first rest =>
      cases rest with
      | nil =>
          cases generatedIndex with
          | zero => rfl
          | succ generatedIndex => rfl
      | cons second tail => rfl

/-- Thus each unit-elimination output clause lies in the macrocell orbit of
its source exact-one clause. -/
theorem generatedClausePosition_inMacrocellOrbit
    {Variable : Type*} (period : Nat)
    (source : PositionedPeriodicClause Variable)
    (generatedIndex : Nat) :
    Cell.InMacrocellOrbit 6 period source.position
      (generatedClauseLocalPosition source.literals generatedIndex)
      (generatedClausePosition source generatedIndex) := by
  refine ⟨(0, 0), ?_⟩
  simpa [Cell.add, Cell.scale] using
    generatedClausePosition_eq_macrocellPosition source generatedIndex

/-- The presentation index inside one unit-elimination block is exactly the
index selecting the generated clause's local offset. -/
theorem clauseGadget_position_eq_generatedClausePosition
    {Variable : Type*}
    (sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable)
    {clause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable)}
    {generatedIndex : Nat}
    (clauseMember :
      (clause, generatedIndex) ∈
        (clauseGadget sourceClauseIndex sourceClause).zipIdx) :
    clause.position = generatedClausePosition sourceClause generatedIndex := by
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  unfold clauseGadget at clauseLookup
  rw [List.getElem?_map, List.getElem?_zipIdx] at clauseLookup
  simp only [Option.map_eq_some_iff] at clauseLookup
  rcases clauseLookup with ⟨taggedClause, taggedLookup, clauseEqual⟩
  rcases taggedLookup with
    ⟨generatedClause, generatedClauseLookup, taggedEqual⟩
  subst taggedClause
  simpa using
    congrArg PositionedPeriodicClause.position clauseEqual.symm

/-- Unit elimination retains every old variable at the origin of its new
macrocell. -/
theorem placement_inherited_inMacrocellOrbit
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    Cell.InMacrocellOrbit 6 sourcePlacement.period
      (sourcePlacement.position atom) (0, 0)
      ((placement source sourcePlacement).position (.inl atom)) := by
  refine ⟨(0, 0), ?_⟩
  simp [placement, Cell.macrocellPosition, gadgetScale,
    Cell.add, Cell.scale]

/-- A unit-elimination auxiliary lies at its declared local point over its
source clause, modulo the anchor-gauge period translation. -/
theorem placement_auxiliary_inMacrocellOrbit
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (kind : OneInThreeNoUnitAux) :
    Cell.InMacrocellOrbit 6 sourcePlacement.period
      (source.clausePosition clauseIndex)
      (auxiliaryLocalPosition kind)
      ((placement source sourcePlacement).position
        (.inr ((clauseIndex, clause), kind))) := by
  refine ⟨Cell.sub (0, 0) (PeriodicOneInThree.anchor clause), ?_⟩
  cases sourceEq : source.clausePosition clauseIndex with
  | mk sourceX sourceY =>
  cases localEq : auxiliaryLocalPosition kind with
  | mk localX localY =>
  cases anchorEq : PeriodicOneInThree.anchor clause with
  | mk anchorX anchorY =>
  simp [placement, auxiliaryOccurrencePosition,
    Cell.macrocellPosition, gadgetScale,
    Cell.add, Cell.sub, Cell.scale, sourceEq, localEq, anchorEq]
  constructor <;> ring

end PeriodicOneInThreeNoUnitsPositioned

end LeanTrominoes
