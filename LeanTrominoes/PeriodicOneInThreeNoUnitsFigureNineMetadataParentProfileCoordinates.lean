/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineClauseProfileTemplate
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineIndex

/-! # Parent-profile coordinates of composed Figure 9 metadata -/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PeriodicCNF
open PeriodicCNF.ClauseProfileOccurrenceSplit
open PeriodicCNF.FormulaShapeOfFormula
open PeriodicCNF.UnaryProgramClauseProfile

/-- The canonical parent profile and local generated-clause index retained
by one composed Figure 9 metadata entry. -/
structure ParentProfileCoordinate where
  profile : ClauseProfile
  clauseIndex : Nat
  deriving DecidableEq, Inhabited

/-- Project the parent-profile coordinate from one metadata entry. -/
def ClauseMetadata.parentProfileCoordinate {Variable : Type}
    (metadata : ClauseMetadata Variable) : ParentProfileCoordinate :=
  ⟨clauseProfile (literalProfiles metadata.sourceClause.literals),
    metadata.localClauseIndex⟩

/-- Parent-profile coordinates prescribed by one finite Figure 9 template. -/
def expectedParentProfileCoordinates
    (profile : ClauseProfile) : List ParentProfileCoordinate :=
  (templateDrawingOfClauseProfile profile).formula.zipIdx.map
    fun taggedClause => ⟨profile, taggedClause.2⟩

/-- The concrete composed block and its canonical finite template contain
the same number of generated final clauses. -/
theorem unitEliminationClausesFrom_length_eq_template
    {Variable : Type} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClause : PositionedPeriodicClause Variable)
    (sourceNonempty : sourceClause.literals ≠ [])
    (sourceWidth : sourceClause.literals.length ≤ 3) :
    (unitEliminationClausesFrom figureNineClauseStart
      (PeriodicOneInThreePositioned.clauseGadget
        sourceClauseIndex sourceClause)).length =
      (templateDrawingOfClauseProfile
        (clauseProfile
          (literalProfiles sourceClause.literals))).formula.length := by
  have embeddedEq :=
    unitEliminationClausesFrom_embed
      sourceClauseIndex figureNineClauseStart sourceClause
  have instantiatedFormulaEq :=
    instantiatedDrawing_formula
      sourceClauseIndex figureNineClauseStart sourceClause sourceWidth
  have instantiatedEq :=
    instantiatedDrawing_eq
      sourceClauseIndex figureNineClauseStart sourceClause
  have templateEq :=
    templateDrawingOfClauseProfile_clauseProfile_literalProfiles
      sourceClause sourceNonempty sourceWidth
  calc
    _ = ((unitEliminationClausesFrom figureNineClauseStart
          (PeriodicOneInThreePositioned.clauseGadget
            sourceClauseIndex sourceClause)).map
              PlanarOneInThreeNoUnits.embedPositionedClause).length := by
      exact (List.length_map
        PlanarOneInThreeNoUnits.embedPositionedClause).symm
    _ = (composedClauseGadget sourceClauseIndex
          figureNineClauseStart sourceClause).length := by
      exact congrArg List.length embeddedEq
    _ = (instantiatedDrawing sourceClauseIndex
          figureNineClauseStart sourceClause).formula.length := by
      rw [instantiatedFormulaEq]
    _ = (templateDrawing sourceClause).formula.length := by
      rw [instantiatedEq]
      simp [PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.renameToImage,
        PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.rename,
        PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.translate]
    _ = _ := by rw [← templateEq]

/-- One source clause's metadata block carries exactly the finite template's
parent profile and zero-based local clause indices. -/
theorem clauseMetadataFor_map_parentProfileCoordinate
    {Variable : Type} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClause : PositionedPeriodicClause Variable)
    (sourceNonempty : sourceClause.literals ≠ [])
    (sourceWidth : sourceClause.literals.length ≤ 3) :
    (clauseMetadataFor sourceClauseIndex figureNineClauseStart
      sourceClause).map ClauseMetadata.parentProfileCoordinate =
        expectedParentProfileCoordinates
          (clauseProfile (literalProfiles sourceClause.literals)) := by
  let profile := clauseProfile (literalProfiles sourceClause.literals)
  have lengthEq :=
    unitEliminationClausesFrom_length_eq_template
      sourceClauseIndex figureNineClauseStart sourceClause
      sourceNonempty sourceWidth
  unfold clauseMetadataFor expectedParentProfileCoordinates
    ClauseMetadata.parentProfileCoordinate
  simp only [List.map_map]
  apply List.ext_getElem
  · simpa only [List.length_map, List.length_zipIdx] using lengthEq
  · intro index leftLt rightLt
    simp only [List.getElem_map, List.getElem_zipIdx]
    rfl

/-- Metadata over any suffix has the parent-profile coordinate stream
obtained by concatenating its source clauses' finite template schedules. -/
theorem formulaClauseMetadataFrom_map_parentProfileCoordinate
    {Variable : Type} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClauses : List (PositionedPeriodicClause Variable))
    (clausesNonempty :
      ∀ clause ∈ sourceClauses, clause.literals ≠ [])
    (clausesWidth :
      ∀ clause ∈ sourceClauses, clause.literals.length ≤ 3) :
    (formulaClauseMetadataFrom sourceClauseIndex figureNineClauseStart
      sourceClauses).map ClauseMetadata.parentProfileCoordinate =
        sourceClauses.flatMap fun sourceClause =>
          expectedParentProfileCoordinates
            (clauseProfile (literalProfiles sourceClause.literals)) := by
  induction sourceClauses generalizing
      sourceClauseIndex figureNineClauseStart with
  | nil => rfl
  | cons sourceClause rest induction =>
      rw [formulaClauseMetadataFrom, List.map_append, List.flatMap_cons]
      rw [clauseMetadataFor_map_parentProfileCoordinate
        sourceClauseIndex figureNineClauseStart sourceClause
        (clausesNonempty sourceClause (by simp))
        (clausesWidth sourceClause (by simp))]
      rw [induction
        (sourceClauseIndex + 1)
        (figureNineClauseStart +
          (PeriodicOneInThreePositioned.clauseGadget
            sourceClauseIndex sourceClause).length)
        (by
          intro clause clauseMember
          exact clausesNonempty clause (by simp [clauseMember]))
        (by
          intro clause clauseMember
          exact clausesWidth clause (by simp [clauseMember]))]

/-- Across a complete nonempty width-three source, composed metadata exposes
exactly the concatenated finite parent-profile coordinate schedule. -/
theorem formulaClauseMetadata_map_parentProfileCoordinate
    {Variable : Type} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceNonempty :
      ∀ clause ∈ source.clauses, clause.literals ≠ [])
    (sourceWidth : source.erase.WidthAtMost 3) :
    (formulaClauseMetadata source).map
        ClauseMetadata.parentProfileCoordinate =
      source.clauses.flatMap fun sourceClause =>
        expectedParentProfileCoordinates
          (clauseProfile (literalProfiles sourceClause.literals)) := by
  unfold formulaClauseMetadata
  exact
    formulaClauseMetadataFrom_map_parentProfileCoordinate
      0 0 source.clauses sourceNonempty (by
        intro clause clauseMember
        exact sourceWidth clause.literals (by
          change clause.literals ∈
            source.clauses.map PositionedPeriodicClause.literals
          exact List.mem_map.mpr ⟨clause, clauseMember, rfl⟩))

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
