/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.DirectedClauseProfileCheck
import LeanTrominoes.Common.List.ListRangeGetD
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderCopiedSourcePositionSemantics

/-! # Inherited source selection from copied Figure 9 blocks -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderInheritedSourceSelection

open PeriodicCNF.FormulaShapeDirectionOrdering
open HorizontalRoutedRouteHeader
open HorizontalRoutedRouteHeaderCopiedSourcePosition

/-- Retain exactly the values aligned with inherited scope controls. -/
def selectedInheritedValues {Value : Type} :
    List AtomScopeControl → List Value → List Value
  | [], _ => []
  | _, [] => []
  | .inherited _ :: scopes, value :: values =>
      value :: selectedInheritedValues scopes values
  | .parentLocal _ :: scopes, _ :: values =>
      selectedInheritedValues scopes values

def inheritedSourceSelectionCheck (profile : DirectedClauseProfile) : Bool :=
  decide ((selectedInheritedValues
    (HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock profile)
    ((HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock profile).map scopeOffset)).Nodup) &&
  decide ((selectedInheritedValues
    (HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock profile)
    ((HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock profile).map scopeOffset)).Forall fun offset => offset < sourceWordCount profile)

end HorizontalRoutedRouteHeaderInheritedSourceSelection
end PeriodicCNFStripReduction
end LeanTrominoes

end
