/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DirectedClauseProfileCheck
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderPresentationAtomScopeCompiler
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.SignedUnaryCoordinateRefinementCompiler

/-! # One inherited first-literal route per parent clause -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction.FirstParentInheritedRoute
open Computability Turing
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open HorizontalRoutedRouteHeader HorizontalRoutedRouteHeaderPresentationAtomScope

/-- The same row must carry both the inherited atom and its source route. -/
def eligible (profile : DirectedClauseProfile) (header : Header) : Bool :=
  match header.figurePrefix with
  | .local _ => false
  | .inherited slot _ =>
    decide (presentationSlotAt profile slot = .first) &&
      decide (remapScopeControl profile (outputAtomScopeControl header) = .inherited .first)

def index (profile : DirectedClauseProfile) : Nat :=
  (sourceClauseHeaders profile).findIdx (eligible profile)

def selectedHeader (profile : DirectedClauseProfile) : Header :=
  (sourceClauseHeaders profile).getD (index profile) default

def firstParentSelectorCheck (profile : DirectedClauseProfile) : Bool :=
  decide (index profile < (sourceClauseHeaders profile).length) &&
  eligible profile (selectedHeader profile)

end LeanTrominoes.PeriodicCNFStripReduction.FirstParentInheritedRoute
end
