/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQuery
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRepresentativeClauseDescriptor
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRawRoutes

/-! # Fallback semantics of final copied-clause queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- If every incidence of a retained clause rejects the direct atlas, then
evaluating its exact final query recovers its canonical retained-metadata
descriptor. -/
theorem
    retainedFinalCopiedClauseDescriptorOfQuery_eq_representative_of_choices_none
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseLookup :
      (deduplicatedClauses formula)[clauseIndex]? = some clause)
    (choicesNone :
      ∀ taggedLiteral ∈ clause.zipIdx,
        retainedFinalDirectSourceRouteChoice?
            formula clauseIndex taggedLiteral.2 = none) :
    retainedFinalCopiedClauseDescriptorOfQuery
        (retainedFinalCopiedClauseQueryOfLiterals
          formula clauseIndex clause) =
      representativeClauseDescriptor formula clause := by
  unfold retainedFinalCopiedClauseQueryOfLiterals
  rw [retainedFinalCopiedClauseDescriptorOfQuery_ofList]
  rw [← clauseToken_eq_representativeClauseDescriptor_of_lookup
    formula clause clauseIndex clauseLookup]
  apply congrArg FormulaShapeDirectionOrdering.Token.clause
  unfold FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
    FormulaShapeDirectionOrdering.annotatedLiterals
  apply congrArg
    FormulaShapeDirectionOrdering.DirectedClauseProfile.ofList
  simp only [List.map_map]
  apply List.map_congr_left
  intro taggedLiteral taggedLiteralMember
  apply Prod.ext
  · rfl
  · simp only [Function.comp_apply]
    unfold retainedFinalCopiedSourceDirectionQuery
    rw [choicesNone taggedLiteral taggedLiteralMember]
    simp only [retainedFinalCopiedSourceDirectionOfQuery]
    rw [AxisDirection.polylineFirstDirection_scalePolyline
      retainedAngularFanSourceClearanceFactor
      (by native_decide)]
    exact
      (incidenceRoutes_firstDirection_eq_representativeRoute
          formula clauseIndex taggedLiteral.2).trans
        (representativeRoute_firstDirection_eq_rawRepresentativeRoute
          formula clauseIndex taggedLiteral.2)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
