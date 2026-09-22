/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CanonicalLiteralOffsetRecovery
import LeanTrominoes.UnaryColumnExactSignedDivision

/-! # Compiling anchored literal offsets from incidence geometry columns -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Computability Turing DelimitedDirectionDisplacement
variable {Symbol Index Variable : Type} [Fintype Symbol] [Inhabited Symbol]
    {rows : List Symbol → List Index}

/-- Six signed coordinate columns and the drawing period suffice to emit the
native signed offset field. All geometric premises are required only on actual rows. -/
def canonicalLiteralOffsetCompiler (horizontal : Bool)
    (placement : List Symbol → PeriodicVariablePlacement Variable)
    (clause : List Symbol → Index → PositionedPeriodicClause Variable)
    (literal : List Symbol → Index → PeriodicLiteral Variable)
    (route : List Symbol → Index → List Cell)
    (cp : Compiler rows (fun s i => (component horizontal
      (PositionedPeriodicCNF.canonicalClausePosition (placement s) (clause s i))).toNat))
    (cn : Compiler rows (fun s i => (-component horizontal
      (PositionedPeriodicCNF.canonicalClausePosition (placement s) (clause s i))).toNat))
    (dp : Compiler rows (fun s i => (displacement horizontal
      (Gadget.unitSubdivisionDirections (route s i))).toNat))
    (dn : Compiler rows (fun s i => (-displacement horizontal
      (Gadget.unitSubdivisionDirections (route s i))).toNat))
    (vp : Compiler rows (fun s i => (component horizontal
      ((placement s).position (literal s i).atom)).toNat))
    (vn : Compiler rows (fun s i => (-component horizontal
      ((placement s).position (literal s i).atom)).toNat))
    (period : ScalarCompiler (fun s => (placement s).period))
    (positive : ∀ s, 0 < (placement s).period)
    (head : ∀ s i, i ∈ rows s → (route s i).head? = some
      (PositionedPeriodicCNF.canonicalClausePosition (placement s) (clause s i)))
    (last : ∀ s i, i ∈ rows s → (route s i).getLast? = some
      (PositionedPeriodicCNF.canonicalLiteralPosition (placement s) (clause s i) (literal s i)))
    (unitSteps : ∀ s i, i ∈ rows s → (route s i).IsChain AxisDirection.IsUnitAxisStep) :
    Compiler rows (fun s i => Encodable.encode (component horizontal
      (Cell.sub (literal s i).offset (PeriodicCNF.clauseAnchor (clause s i).literals)))) := by
  apply exactSignedDivide (add (add cp dp) vn) (add (add cn dn) vp) period positive
  intro s i hi
  have recovered := canonical_offset_scaled horizontal (placement s) (clause s i) (literal s i)
    (route s i) (head s i hi) (last s i hi) (unitSteps s i hi)
  simp only [Nat.cast_add]
  omega

end LeanTrominoes.UnaryColumn
end
