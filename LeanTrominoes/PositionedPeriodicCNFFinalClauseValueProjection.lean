/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileOccurrenceSplitSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineFinalClauseOrderingData
import LeanTrominoes.PeriodicCNFPlanarThreeSATThreePositioned

/-! # Projecting final clause values through positioned erasure -/

namespace LeanTrominoes
namespace PeriodicCNF

open ClauseProfileOccurrenceSplit
open FormulaShapeFigureNineFinalClauseOrdering
open UnaryProgramClauseProfile

/-- Exact profile literals for an erased positioned formula remain exact
after projecting literal values and applying the final Figure 9 permutation
inside every clause. -/
theorem positioned_reorderedLiteralValues_eq_of_profiles
    {Variable : Type}
    (formula : PositionedPeriodicCNF Variable)
    (profiles : List ClauseProfile)
    (correct : profiles.map ClauseProfile.literals =
      formula.erase.clauses.map literalProfiles) :
    (profiles.map fun profile =>
        reorderList (profile.literals.map LiteralProfile.value)) =
      (formula.clauses.map fun clause =>
        reorderList (clause.literals.map PeriodicLiteral.value)) := by
  have projected := congrArg
    (List.map fun literals =>
      reorderList (literals.map LiteralProfile.value))
    correct
  simpa only [PositionedPeriodicCNF.erase, List.map_map,
    Function.comp_def, literalProfiles] using projected

end PeriodicCNF
end LeanTrominoes
