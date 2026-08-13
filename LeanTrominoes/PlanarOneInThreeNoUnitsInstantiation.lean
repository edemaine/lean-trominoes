/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawingRenaming
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation
import LeanTrominoes.PlanarOneInThreeNoUnitsDrawing

/-!
# Instantiating the certified unit-elimination drawings

This file renames each finite `6 × 6` unit-elimination template to the actual
source atoms and clause-scoped auxiliaries, then translates it into an
arbitrary positioned source-clause refinement cell.  The instantiated
embedded formula is exactly the real positioned output after forgetting only
the periodic literal offsets.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnits

open PlanarThreeSAT

/-- Rename full ternary-template roles to source atoms or scoped
unit-elimination auxiliaries. -/
def threeVariableMap {Variable : Type*}
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second third : Variable) :
    UnitEliminationVariable →
      OneInThreeNoUnitVariable Variable
  | .sourceFirst => .inl first
  | .sourceSecond => .inl second
  | .sourceThird => .inl third
  | .first =>
      .inr ((clauseIndex, source.literals), .first)
  | .second =>
      .inr ((clauseIndex, source.literals), .second)
  | .third =>
      .inr ((clauseIndex, source.literals), .third)

/-- Local placement of the three present source ports and all auxiliary
roles. -/
def threeLocalPosition {Variable : Type*} [DecidableEq Variable]
    (first second third : Variable) :
    OneInThreeNoUnitVariable Variable → Cell
  | .inl atom =>
      if atom = first then (3, 0)
      else if atom = second then (0, 3)
      else if atom = third then (6, 3)
      else (0, 0)
  | .inr (_, kind) =>
      PeriodicOneInThreeNoUnitsPositioned.auxiliaryLocalPosition kind

/-- Instantiated retained ternary drawing for an arbitrary positioned
periodic source clause. -/
def instantiatedThreeDrawing {Variable : Type*}
    [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second third : PeriodicLiteral Variable) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeNoUnitVariable Variable) :=
  ((threeDrawingFor
      first.value second.value third.value).rename
    (threeVariableMap clauseIndex source
      first.atom second.atom third.atom)
    (threeLocalPosition
      first.atom second.atom third.atom)).translate
        (Cell.scale
          PeriodicOneInThreeNoUnitsPositioned.gadgetScale
          source.position)

/-- The instantiated ternary formula is the actual positioned output after
forgetting periodic literal offsets. -/
theorem instantiatedThreeDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second third : PeriodicLiteral Variable)
    (sourceLiterals :
      source.literals = [first, second, third]) :
    (instantiatedThreeDrawing clauseIndex source
      first second third).formula =
      (PeriodicOneInThreeNoUnitsPositioned.clauseGadget
        clauseIndex source).map embedPositionedClause := by
  rcases source with ⟨sourcePosition, sourceLiterals'⟩
  dsimp at sourceLiterals ⊢
  subst sourceLiterals'
  rfl

/-- The ternary role map is injective when its source atoms are pairwise
distinct. -/
theorem threeVariableMap_injective
    {Variable : Type*}
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second third : Variable)
    (firstNeSecond : first ≠ second)
    (firstNeThird : first ≠ third)
    (secondNeThird : second ≠ third) :
    Function.Injective
      (threeVariableMap clauseIndex source
        first second third) := by
  intro left right equal
  cases left <;> cases right <;>
    simp_all [threeVariableMap]

theorem threeLocalPosition_map
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second third : Variable)
    (firstNeSecond : first ≠ second)
    (firstNeThird : first ≠ third)
    (secondNeThird : second ≠ third)
    (role : UnitEliminationVariable) :
    threeLocalPosition first second third
        (threeVariableMap clauseIndex source
          first second third role) =
      variablePosition role := by
  cases role <;>
    simp [threeLocalPosition, threeVariableMap,
      variablePosition, Ne.symm firstNeSecond,
      Ne.symm firstNeThird, Ne.symm secondNeThird]

theorem instantiatedThreeDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second third : PeriodicLiteral Variable)
    (firstNeSecond : first.atom ≠ second.atom)
    (firstNeThird : first.atom ≠ third.atom)
    (secondNeThird : second.atom ≠ third.atom) :
    (instantiatedThreeDrawing clauseIndex source
      first second third).IsValid := by
  apply EmbeddedCNFIncidenceDrawing.isValid_translate
  apply EmbeddedCNFIncidenceDrawing.isValid_rename
  · intro left _leftMember right _rightMember equal
    exact threeVariableMap_injective clauseIndex source
      first.atom second.atom third.atom
      firstNeSecond firstNeThird secondNeThird equal
  · intro role _roleMember
    exact threeLocalPosition_map clauseIndex source
      first.atom second.atom third.atom
      firstNeSecond firstNeThird secondNeThird role
  · exact threeDrawingFor_isValid
      first.value second.value third.value

/-! ## Retained binary source clauses -/

def twoVariableMap {Variable : Type*}
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second : Variable) :
    UnitEliminationVariable →
      OneInThreeNoUnitVariable Variable
  | .sourceFirst => .inl first
  | .sourceSecond => .inl second
  | .sourceThird => .inl first
  | .first =>
      .inr ((clauseIndex, source.literals), .first)
  | .second =>
      .inr ((clauseIndex, source.literals), .second)
  | .third =>
      .inr ((clauseIndex, source.literals), .third)

def twoLocalPosition {Variable : Type*} [DecidableEq Variable]
    (first second : Variable) :
    OneInThreeNoUnitVariable Variable → Cell
  | .inl atom =>
      if atom = first then (3, 0)
      else if atom = second then (0, 3)
      else (0, 0)
  | .inr (_, kind) =>
      PeriodicOneInThreeNoUnitsPositioned.auxiliaryLocalPosition kind

def instantiatedTwoDrawing {Variable : Type*}
    [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second : PeriodicLiteral Variable) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeNoUnitVariable Variable) :=
  ((twoDrawingFor first.value second.value).rename
    (twoVariableMap clauseIndex source
      first.atom second.atom)
    (twoLocalPosition first.atom second.atom)).translate
        (Cell.scale
          PeriodicOneInThreeNoUnitsPositioned.gadgetScale
          source.position)

theorem instantiatedTwoDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second : PeriodicLiteral Variable)
    (sourceLiterals : source.literals = [first, second]) :
    (instantiatedTwoDrawing clauseIndex source
      first second).formula =
      (PeriodicOneInThreeNoUnitsPositioned.clauseGadget
        clauseIndex source).map embedPositionedClause := by
  rcases source with ⟨sourcePosition, sourceLiterals'⟩
  dsimp at sourceLiterals ⊢
  subst sourceLiterals'
  rfl

theorem instantiatedTwoDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second : PeriodicLiteral Variable)
    (firstNeSecond : first.atom ≠ second.atom) :
    (instantiatedTwoDrawing clauseIndex source
      first second).IsValid := by
  apply EmbeddedCNFIncidenceDrawing.isValid_translate
  apply EmbeddedCNFIncidenceDrawing.isValid_rename
  · intro left leftMember right rightMember equal
    simp [EmbeddedCNFIncidenceDrawing.variableVertices,
      twoDrawingFor, twoFormulaFor, clause]
      at leftMember rightMember
    cases left <;> cases right <;>
      simp_all [twoVariableMap]
  · intro role roleMember
    simp [EmbeddedCNFIncidenceDrawing.variableVertices,
      twoDrawingFor, twoFormulaFor, clause]
      at roleMember
    cases role <;>
      simp_all [twoLocalPosition, twoVariableMap,
        twoDrawingFor, variablePosition,
        Ne.symm firstNeSecond]
  · exact twoDrawingFor_isValid first.value second.value

/-! ## Unit source clauses -/

def unitVariableMap {Variable : Type*}
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first : Variable) :
    UnitEliminationVariable →
      OneInThreeNoUnitVariable Variable
  | .sourceFirst | .sourceSecond | .sourceThird => .inl first
  | .first =>
      .inr ((clauseIndex, source.literals), .first)
  | .second =>
      .inr ((clauseIndex, source.literals), .second)
  | .third =>
      .inr ((clauseIndex, source.literals), .third)

def unitLocalPosition {Variable : Type*} [DecidableEq Variable]
    (first : Variable) :
    OneInThreeNoUnitVariable Variable → Cell
  | .inl atom => if atom = first then (3, 0) else (0, 0)
  | .inr (_, kind) =>
      PeriodicOneInThreeNoUnitsPositioned.auxiliaryLocalPosition kind

def instantiatedUnitDrawing {Variable : Type*}
    [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first : PeriodicLiteral Variable) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeNoUnitVariable Variable) :=
  (unitDrawingFor first.value).rename
      (unitVariableMap clauseIndex source first.atom)
      (unitLocalPosition first.atom)
    |>.translate
      (Cell.scale
        PeriodicOneInThreeNoUnitsPositioned.gadgetScale
        source.position)

theorem instantiatedUnitDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first : PeriodicLiteral Variable)
    (sourceLiterals : source.literals = [first]) :
    (instantiatedUnitDrawing clauseIndex source first).formula =
      (PeriodicOneInThreeNoUnitsPositioned.clauseGadget
        clauseIndex source).map embedPositionedClause := by
  rcases source with ⟨sourcePosition, sourceLiterals'⟩
  dsimp at sourceLiterals ⊢
  subst sourceLiterals'
  rfl

theorem instantiatedUnitDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first : PeriodicLiteral Variable) :
    (instantiatedUnitDrawing clauseIndex source first).IsValid := by
  apply EmbeddedCNFIncidenceDrawing.isValid_translate
  apply EmbeddedCNFIncidenceDrawing.isValid_rename
  · intro left leftMember right rightMember equal
    simp [EmbeddedCNFIncidenceDrawing.variableVertices,
      unitDrawingFor, unitFormulaFor, clause]
      at leftMember rightMember
    cases left <;> cases right <;>
      simp_all [unitVariableMap]
  · intro role roleMember
    simp [EmbeddedCNFIncidenceDrawing.variableVertices,
      unitDrawingFor, unitFormulaFor, clause]
      at roleMember
    cases role <;>
      simp_all [unitLocalPosition, unitVariableMap,
        unitDrawingFor, variablePosition]
  · exact unitDrawingFor_isValid first.value

/-! ## Empty source clauses -/

def emptyVariableMap {Variable : Type*}
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable) :
    UnitEliminationVariable →
      OneInThreeNoUnitVariable Variable
  | .sourceFirst | .sourceSecond | .sourceThird | .first =>
      .inr ((clauseIndex, source.literals), .first)
  | .second =>
      .inr ((clauseIndex, source.literals), .second)
  | .third =>
      .inr ((clauseIndex, source.literals), .third)

def emptyLocalPosition {Variable : Type*} :
    OneInThreeNoUnitVariable Variable → Cell
  | .inl _ => (0, 0)
  | .inr (_, kind) =>
      PeriodicOneInThreeNoUnitsPositioned.auxiliaryLocalPosition kind

def instantiatedEmptyDrawing {Variable : Type*}
    [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeNoUnitVariable Variable) :=
  emptyDrawing.rename
      (emptyVariableMap clauseIndex source)
      emptyLocalPosition
    |>.translate
      (Cell.scale
        PeriodicOneInThreeNoUnitsPositioned.gadgetScale
        source.position)

theorem instantiatedEmptyDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (sourceLiterals : source.literals = []) :
    (instantiatedEmptyDrawing clauseIndex source).formula =
      (PeriodicOneInThreeNoUnitsPositioned.clauseGadget
        clauseIndex source).map embedPositionedClause := by
  rcases source with ⟨sourcePosition, sourceLiterals'⟩
  dsimp at sourceLiterals ⊢
  subst sourceLiterals'
  rfl

theorem instantiatedEmptyDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable) :
    (instantiatedEmptyDrawing clauseIndex source).IsValid := by
  apply EmbeddedCNFIncidenceDrawing.isValid_translate
  apply EmbeddedCNFIncidenceDrawing.isValid_rename
  · intro left leftMember right rightMember equal
    simp [EmbeddedCNFIncidenceDrawing.variableVertices,
      emptyDrawing, emptyFormula, clause]
      at leftMember rightMember
    cases left <;> cases right <;>
      simp_all [emptyVariableMap]
  · intro role roleMember
    simp [EmbeddedCNFIncidenceDrawing.variableVertices,
      emptyDrawing, emptyFormula, clause]
      at roleMember
    cases role <;>
      simp_all [emptyLocalPosition, emptyVariableMap,
        emptyDrawing, variablePosition]
  · exact emptyDrawing_isValid

end PlanarOneInThreeNoUnits
end LeanTrominoes
