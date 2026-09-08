/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrences
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedCopiedSourceBlockSelection

/-! # Copied literal values projected from coherent source occurrences -/

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open HorizontalRoutedRouteHeader
open HorizontalRoutedRouteHeaderPresentationAtomScope
open HorizontalRoutedRouteHeaderCopiedSourcePosition

/-- Read the presentation-relative literal value from the occurrence's own
parent row. Parent-local records retain the copied compiler's first-slot
fallback; only inherited records use this value as their identity. -/
def sourceOccurrenceCopiedValue (rows : List (List Nat)) (occurrence : SourceOccurrence) : Nat :=
  (rows.getD occurrence.parentClauseIndex []).getD
    (scopeOffset (remapScopeControl occurrence.profile (outputAtomScopeControl occurrence.header))) 0

private theorem sourceOccurrencesFrom_map_copiedValue_blocks
    (preceding : List (List Nat)) (start : Nat)
    (blocks : List (DirectedClauseProfile × List Nat))
    (tails : List (List (List AxisDirection))) :
    (sourceOccurrencesFrom preceding.length start
        (blocks.map (fun block => Token.clause block.1)) tails).map
        (sourceOccurrenceCopiedValue (preceding ++ blocks.map Prod.snd)) =
      blocks.flatMap (fun block => (clauseBlock block.1).map
        (fun control => block.2.getD (scopeOffset control) 0)) := by
  induction blocks generalizing preceding start tails with
  | nil => rfl
  | cons block blocks ih =>
      have rowLookup : (preceding ++ block.2 :: blocks.map Prod.snd).getD preceding.length [] = block.2 := by
        simp only [List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_refl preceding.length), Nat.sub_self,
          List.getElem?_cons_zero, Option.getD_some]
      simp only [List.map_cons, sourceOccurrencesFrom, List.map_append, List.map_map,
        List.flatMap_cons, clauseBlock]
      apply congrArg₂ List.append
      · simp only [sourceOccurrenceCopiedValue, Function.comp_def, rowLookup]
      · have shifted := ih (preceding ++ [block.2]) (start + generatedClauseCount block.1) tails.tail
        simpa only [List.length_append, List.length_singleton, List.append_assoc,
          List.singleton_append, clauseBlock, List.map_map] using shifted

/-- Clause-local values and coherent occurrence records use the same parent,
profile, and header at every output index, independently of tail-table data. -/
theorem sourceOccurrences_map_copiedValue_blocks
    (blocks : List (DirectedClauseProfile × List Nat))
    (tails : List (List (List AxisDirection))) :
    (sourceOccurrences (blocks.map (fun block => Token.clause block.1)) tails).map
        (sourceOccurrenceCopiedValue (blocks.map Prod.snd)) =
      blocks.flatMap (fun block => (clauseBlock block.1).map
        (fun control => block.2.getD (scopeOffset control) 0)) := by
  simpa only [List.length_nil, List.nil_append, sourceOccurrences] using
    sourceOccurrencesFrom_map_copiedValue_blocks [] 0 blocks tails

/-- A correctly sized copied candidate column selects exactly the value
stored at each coherent occurrence's own parent and remapped source slot. -/
theorem selectedValues_eq_sourceOccurrences_map_copiedValue
    (blocks : List (DirectedClauseProfile × List Nat))
    (tails : List (List (List AxisDirection)))
    (lengths : ∀ block ∈ blocks, block.2.length = sourceWordCount block.1) :
    selectedValues (blocks.map (fun block => Token.clause block.1)) (blocks.flatMap Prod.snd) =
      (sourceOccurrences (blocks.map (fun block => Token.clause block.1)) tails).map
        (sourceOccurrenceCopiedValue (blocks.map Prod.snd)) := by
  rw [selectedValues_clauseBlocks blocks lengths, sourceOccurrences_map_copiedValue_blocks]

/-- A genuine parent lookup and remapped inherited-slot lookup identify the
selected value with the code of that exact literal atom. -/
theorem sourceOccurrenceCopiedValue_eq_literal
    {Atom : Type} (clauses : List (PositionedPeriodicClause Atom))
    (atomValue : Atom → Nat) (occurrence : SourceOccurrence)
    (clause : PositionedPeriodicClause Atom) (literal : PeriodicLiteral Atom)
    (slot : PeriodicCNF.ClauseProfilePolarityRouteOperation.SourceLiteralSlot)
    (parentLookup : clauses[occurrence.parentClauseIndex]? = some clause)
    (scope : outputAtomScopeControl occurrence.header = .inherited slot)
    (literalLookup : clause.literals[
      PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader.sourceSlotNat
        (presentationSlotAt occurrence.profile slot)]? = some literal) :
    sourceOccurrenceCopiedValue
        (clauses.map (fun parent => parent.literals.map (fun entry => atomValue entry.atom))) occurrence =
      atomValue literal.atom := by
  simp only [sourceOccurrenceCopiedValue, List.getD_eq_getElem?_getD, List.getElem?_map,
    parentLookup, Option.map_some, Option.getD_some, scope, remapScopeControl, scopeOffset,
    literalLookup]

end LeanTrominoes.PeriodicCNFStripReduction
