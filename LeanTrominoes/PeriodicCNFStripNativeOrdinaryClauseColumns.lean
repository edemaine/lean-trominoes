/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeOrdinaryOffsetColumns
import LeanTrominoes.CanonicalLiteralOffsetRecovery

/-! # Compiling canonical clause positions from their first incidence -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing PeriodicCNF UnaryColumn DelimitedDirectionDisplacement PositionedIncidenceRows
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance ordinaryClauseColumnStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance ordinaryClauseColumnVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 200000

def nativeOrdinaryClauseColumn [Inhabited encoding.Γ] (horizontal positive : Bool) :
    Compiler (nativeOrdinaryRows decider) (fun s row => SignedUnaryCoordinateRefinement.field positive
      (component horizontal (PositionedPeriodicCNF.canonicalClausePosition (nativeOrdinaryPlacement decider s) row.1.1))) := by
  let vp := nativeOrdinaryFirstColumn decider _ (nativeOrdinaryVariableColumn decider horizontal true)
  let vn := nativeOrdinaryFirstColumn decider _ (nativeOrdinaryVariableColumn decider horizontal false)
  let dp := nativeOrdinaryFirstColumn decider _ (nativeOrdinaryDisplacementColumn decider horizontal true)
  let dn := nativeOrdinaryFirstColumn decider _ (nativeOrdinaryDisplacementColumn decider horizontal false)
  let p := add vp dn
  let n := add vn dp
  let physical : Compiler (nativeOrdinaryRows decider) (fun s row =>
      if positive then
        (firstValue (fun r => SignedUnaryCoordinateRefinement.field true
          (component horizontal ((nativeOrdinaryPlacement decider s).position r.2.1.atom))) row +
         firstValue (fun r => SignedUnaryCoordinateRefinement.field false
          (displacement horizontal (Gadget.unitSubdivisionDirections (nativeOrdinaryRoutes decider s r.1.2 r.2.2)))) row) -
        (firstValue (fun r => SignedUnaryCoordinateRefinement.field false
          (component horizontal ((nativeOrdinaryPlacement decider s).position r.2.1.atom))) row +
         firstValue (fun r => SignedUnaryCoordinateRefinement.field true
          (displacement horizontal (Gadget.unitSubdivisionDirections (nativeOrdinaryRoutes decider s r.1.2 r.2.2)))) row)
      else
        (firstValue (fun r => SignedUnaryCoordinateRefinement.field false
          (component horizontal ((nativeOrdinaryPlacement decider s).position r.2.1.atom))) row +
         firstValue (fun r => SignedUnaryCoordinateRefinement.field true
          (displacement horizontal (Gadget.unitSubdivisionDirections (nativeOrdinaryRoutes decider s r.1.2 r.2.2)))) row) -
        (firstValue (fun r => SignedUnaryCoordinateRefinement.field true
          (component horizontal ((nativeOrdinaryPlacement decider s).position r.2.1.atom))) row +
         firstValue (fun r => SignedUnaryCoordinateRefinement.field false
          (displacement horizontal (Gadget.unitSubdivisionDirections (nativeOrdinaryRoutes decider s r.1.2 r.2.2)))) row)) := by
    cases positive
    · exact sub n p
    · exact sub p n
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  clear physical vp vn dp dn p n
  apply List.map_congr_left
  intro row member
  have hm := (mem_rows _ row).1 member
  obtain ⟨literal, rest, literalsEq⟩ := List.exists_cons_of_ne_nil
    (nativeOrdinaryClauses_nonempty decider s row.1.1 (List.fst_mem_of_mem_zipIdx hm.1))
  have firstMember : (row.1, (literal, 0)) ∈ nativeOrdinaryRows decider s := by
    apply (mem_rows _ _).2
    refine ⟨hm.1, ?_⟩
    rw [literalsEq, List.zipIdx_cons]
    exact List.mem_cons_self
  have endpoints := nativeOrdinaryRoute_endpoints decider s (row.1, (literal, 0)) firstMember
  have recovered := canonical_offset_scaled horizontal (nativeOrdinaryPlacement decider s) row.1.1 literal
    (nativeOrdinaryRoutes decider s row.1.2 0) endpoints.1 endpoints.2
    (nativeOrdinaryRoute_unitSteps decider s (row.1, (literal, 0)) firstMember)
  have anchor : clauseAnchor row.1.1.literals = literal.offset := by simp [clauseAnchor, literalsEq]
  have zero : component horizontal (Cell.sub literal.offset literal.offset) = 0 := by
    cases horizontal <;> simp [component, Cell.sub]
  rw [anchor, zero, mul_zero] at recovered
  have firstEq (value : Row OrdinaryVariable → Nat) : firstValue value row = value (row.1, (literal, 0)) :=
    firstValue_cons value row literal rest literalsEq
  cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte, firstEq,
    SignedUnaryCoordinateRefinement.field] <;> omega

end LeanTrominoes.PeriodicCNFStripReduction
end
