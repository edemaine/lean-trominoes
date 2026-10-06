/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DirectedClauseProfileCheck
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderCopiedLocalAtomCodeCompiler

/-! # Local final-atom occurrence bounds in one routed parent block -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderPresentationAtomScope

open PeriodicCNF.FormulaShapeDirectionOrdering
open HorizontalRoutedRouteHeader

/-- Represented parent-relative atoms at the parent-local positions of one
final routed block. -/
def parentLocalAtoms (profile : DirectedClauseProfile) :
    List ParentRelativeAtom :=
  (clauseBlock profile).filterMap fun scope =>
    match scope with
    | .inherited _ => none
    | .parentLocal control => some control.representedAtom

def localOccurrenceBoundsCheck (profile : DirectedClauseProfile) : Bool :=
  (decide (0 < (clauseBlock profile).length) &&
  ((parentLocalAtoms profile).all fun atom =>
    decide ((parentLocalAtoms profile).count atom ≤ 3))) &&
  ((clauseBlock profile).all fun scope =>
    match scope with
    | .inherited _ => true
    | .parentLocal control => decide ((clauseBlock profile).count (.parentLocal control) ≤ 3))

end HorizontalRoutedRouteHeaderPresentationAtomScope
end PeriodicCNFStripReduction
end LeanTrominoes
