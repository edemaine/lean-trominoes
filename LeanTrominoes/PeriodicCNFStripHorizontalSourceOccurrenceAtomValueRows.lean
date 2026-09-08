/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripHorizontalSourceOccurrenceCopiedValues

/-! # Clause value rows for complete inherited-code streams -/

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open HorizontalRoutedRouteHeader HorizontalRoutedRouteHeaderPresentationAtomScope

/-- Actual inherited literal values of one parent, together with the unused
value emitted in its inherited column at parent-local occurrences. -/
structure SourceOccurrenceAtomValueRow where
  literals : List Nat
  localFallback : Nat

instance : Inhabited SourceOccurrenceAtomValueRow := ⟨⟨[], 0⟩⟩

def SourceOccurrenceAtomValueRow.value (row : SourceOccurrenceAtomValueRow) : AtomScopeControl → Nat
  | .inherited slot => row.literals.getD (sourceSlotNat slot) 0
  | .parentLocal _ => row.localFallback

/-- Read the complete inherited column from the occurrence's own parent row
and presentation-relative scope. -/
def sourceOccurrenceAtomValue (rows : List SourceOccurrenceAtomValueRow) (occurrence : SourceOccurrence) : Nat :=
  (rows.getD occurrence.parentClauseIndex default).value
    (remapScopeControl occurrence.profile (outputAtomScopeControl occurrence.header))

private theorem sourceOccurrencesFrom_map_atomValueRows
    (preceding : List SourceOccurrenceAtomValueRow) (start : Nat)
    (blocks : List (DirectedClauseProfile × SourceOccurrenceAtomValueRow))
    (tails : List (List (List AxisDirection))) :
    (sourceOccurrencesFrom preceding.length start
        (blocks.map (fun block => Token.clause block.1)) tails).map
        (sourceOccurrenceAtomValue (preceding ++ blocks.map Prod.snd)) =
      blocks.flatMap (fun block => (clauseBlock block.1).map block.2.value) := by
  induction blocks generalizing preceding start tails with
  | nil => rfl
  | cons block blocks ih =>
      have rowLookup : (preceding ++ block.2 :: blocks.map Prod.snd).getD preceding.length default = block.2 := by
        simp only [List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_refl preceding.length), Nat.sub_self,
          List.getElem?_cons_zero, Option.getD_some]
      simp only [List.map_cons, sourceOccurrencesFrom, List.map_append, List.map_map,
        List.flatMap_cons, clauseBlock]
      apply congrArg₂ List.append
      · simp only [sourceOccurrenceAtomValue, Function.comp_def, rowLookup]
      · have shifted := ih (preceding ++ [block.2]) (start + generatedClauseCount block.1) tails.tail
        simpa only [List.length_append, List.length_singleton, List.append_assoc,
          List.singleton_append, clauseBlock, List.map_map] using shifted

/-- Every complete code is read from the same parent, profile, and header as
its coherent source record, including parent-local fallback positions. -/
theorem sourceOccurrences_map_atomValueRows
    (blocks : List (DirectedClauseProfile × SourceOccurrenceAtomValueRow))
    (tails : List (List (List AxisDirection))) :
    (sourceOccurrences (blocks.map (fun block => Token.clause block.1)) tails).map
        (sourceOccurrenceAtomValue (blocks.map Prod.snd)) =
      blocks.flatMap (fun block => (clauseBlock block.1).map block.2.value) := by
  simpa only [List.length_nil, List.nil_append, sourceOccurrences] using
    sourceOccurrencesFrom_map_atomValueRows [] 0 blocks tails

/-- At an inherited occurrence, the fallback field is irrelevant: the value
is the ordinary lookup in that same parent's actual literal row. -/
theorem sourceOccurrenceAtomValue_eq_copiedValue_of_inherited
    (rows : List SourceOccurrenceAtomValueRow) (occurrence : SourceOccurrence)
    (slot : SourceLiteralSlot)
    (scope : outputAtomScopeControl occurrence.header = .inherited slot) :
    sourceOccurrenceAtomValue rows occurrence =
      sourceOccurrenceCopiedValue (rows.map SourceOccurrenceAtomValueRow.literals) occurrence := by
  simp only [sourceOccurrenceAtomValue, sourceOccurrenceCopiedValue, scope, remapScopeControl,
    SourceOccurrenceAtomValueRow.value, HorizontalRoutedRouteHeaderCopiedSourcePosition.scopeOffset,
    List.getD_eq_getElem?_getD, List.getElem?_map]
  cases rows[occurrence.parentClauseIndex]? <;> rfl

end LeanTrominoes.PeriodicCNFStripReduction
