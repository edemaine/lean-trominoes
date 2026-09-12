/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineMetadataParentProfileCoordinates

/-! # Actual composed clause positions from their finite template coordinates -/

namespace LeanTrominoes.PlanarOneInThreeNoUnitsFigureNine
open PlanarThreeSAT PeriodicCNF

/-- Stored clause positions are the finite template positions translated by
the same source macrocell origin used by the instantiated drawing. -/
theorem unitEliminationClausesFrom_positions {Variable : Type} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat) (sourceClause : PositionedPeriodicClause Variable)
    (width : sourceClause.literals.length ≤ 3) :
    (unitEliminationClausesFrom figureNineClauseStart
      (PeriodicOneInThreePositioned.clauseGadget sourceClauseIndex sourceClause)).map PositionedPeriodicClause.position =
      (templateDrawing sourceClause).formula.map fun clause =>
        Cell.add (Cell.scale composedGadgetScale sourceClause.position) clause.position := by
  have positions := congrArg (List.map EmbeddedClause.position)
    (unitEliminationClausesFrom_embed sourceClauseIndex figureNineClauseStart sourceClause)
  rw [← instantiatedDrawing_formula sourceClauseIndex figureNineClauseStart sourceClause width,
    instantiatedDrawing_eq] at positions
  simpa only [EmbeddedCNFIncidenceDrawing.translate, EmbeddedCNFIncidenceDrawing.renameToImage,
    EmbeddedCNFIncidenceDrawing.rename, List.map_map, Function.comp_def,
    PlanarOneInThreeNoUnits.embedPositionedClause, EmbeddedClause.translate, EmbeddedClause.rename, EmbeddedClause.map, id_eq] using positions

/-- The finite profile and local clause ordinal determine the local offset. -/
def templateClausePosition (profile : UnaryProgramClauseProfile.ClauseProfile) (index : Nat) : Cell :=
  (((templateDrawingOfClauseProfile profile).formula[index]?).map EmbeddedClause.position).getD (0, 0)

/-- A genuine local clause has the stored position prescribed by its finite
profile and index; out-of-range fallbacks never enter the equation. -/
theorem localClause_position_eq_template {Variable : Type} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat) (sourceClause : PositionedPeriodicClause Variable)
    (nonempty : sourceClause.literals ≠ []) (width : sourceClause.literals.length ≤ 3)
    (clause : PositionedPeriodicClause (OneInThreeNoUnitVariable (OneInThreeVariable Variable)))
    (localClauseIndex : Nat)
    (member : (clause, localClauseIndex) ∈ (unitEliminationClausesFrom figureNineClauseStart
      (PeriodicOneInThreePositioned.clauseGadget sourceClauseIndex sourceClause)).zipIdx) :
    clause.position = Cell.add (Cell.scale composedGadgetScale sourceClause.position)
      (templateClausePosition (FormulaShapeOfFormula.clauseProfile
        (ClauseProfileOccurrenceSplit.literalProfiles sourceClause.literals)) localClauseIndex) := by
  have positions := congrArg (fun values : List Cell => values[localClauseIndex]?)
    (unitEliminationClausesFrom_positions sourceClauseIndex figureNineClauseStart sourceClause width)
  rw [List.getElem?_map, List.mk_mem_zipIdx_iff_getElem?.mp member, Option.map_some,
    List.getElem?_map] at positions
  unfold templateClausePosition
  rw [templateDrawingOfClauseProfile_clauseProfile_literalProfiles sourceClause nonempty width]
  cases lookup : (templateDrawing sourceClause).formula[localClauseIndex]? with
  | none => simp only [lookup, Option.map_none, Option.some_ne_none] at positions
  | some localClause =>
    rw [lookup, Option.map_some] at positions
    simpa only [lookup, Option.map_some, Option.getD_some] using Option.some.inj positions

/-- Complete metadata therefore exposes the exact affine clause position. -/
theorem ClauseMetadata.position_eq_template {Variable : Type} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable) (metadata : ClauseMetadata Variable)
    (member : metadata ∈ formulaClauseMetadata source)
    (nonempty : metadata.sourceClause.literals ≠ []) (width : metadata.sourceClause.literals.length ≤ 3) :
    metadata.clause.position = Cell.add (Cell.scale composedGadgetScale metadata.sourceClause.position)
      (templateClausePosition metadata.parentProfileCoordinate.profile metadata.localClauseIndex) := by
  exact localClause_position_eq_template metadata.sourceClauseIndex metadata.figureNineClauseStart
    metadata.sourceClause nonempty width metadata.clause metadata.localClauseIndex
    (formulaClauseMetadata_valid source member).2

end LeanTrominoes.PlanarOneInThreeNoUnitsFigureNine
