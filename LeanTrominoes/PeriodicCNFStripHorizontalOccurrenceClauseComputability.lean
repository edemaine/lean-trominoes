/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceSourceRouteData

/-! # Computability of the normalized occurrence-clause query -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRoutedPlacementVariableDecidableEq

theorem horizontalOccurrenceRouteSomeSource_primrec :
    Primrec fun input : HorizontalOccurrenceRouteSomeInput =>
      input.1.1.1 :=
  Primrec.fst.comp (Primrec.fst.comp Primrec.fst)

theorem horizontalOccurrenceClauseComputed_primrec :
    Primrec horizontalOccurrenceClauseComputed := by
  have formula : Primrec fun input : HorizontalOccurrenceRouteSomeInput =>
      horizontalNormalizedRoutedFormulaComputed input.1.1.1 :=
    horizontalNormalizedRoutedFormulaComputed_primrec.comp
      horizontalOccurrenceRouteSomeSource_primrec
  have clauses : Primrec fun input : HorizontalOccurrenceRouteSomeInput =>
      (horizontalNormalizedRoutedFormulaComputed input.1.1.1).clauses :=
    PositionedPeriodicCNF.clauses_primrec.comp formula
  have index : Primrec fun input : HorizontalOccurrenceRouteSomeInput =>
      input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have selected : Primrec fun input : HorizontalOccurrenceRouteSomeInput =>
      (horizontalNormalizedRoutedFormulaComputed input.1.1.1).clauses[
        input.2.2.1]? :=
    Primrec.list_getElem?.comp clauses index
  have literals : Primrec fun input : HorizontalOccurrenceRouteSomeInput =>
      ((horizontalNormalizedRoutedFormulaComputed input.1.1.1).clauses[
        input.2.2.1]?).map PositionedPeriodicClause.literals :=
    Primrec.option_map selected
      (PositionedPeriodicClause.literals_primrec.comp Primrec.snd).to₂
  exact (Primrec.option_getD.comp literals
    (Primrec.const [])).of_eq fun _ => rfl

end PeriodicCNFStripReduction
end LeanTrominoes
