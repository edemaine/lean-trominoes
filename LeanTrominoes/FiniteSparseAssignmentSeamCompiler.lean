/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GadgetSparseAssignmentTokens
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.TM2ComputableInPolyTimeCongr
import LeanTrominoes.TM2CompositionMachine

/-! # Move the finite seam with a two-state assignment-token transducer -/
noncomputable section
namespace LeanTrominoes.FiniteSparseAssignmentSeamCompiler
open _root_.Computability Turing GadgetSparseAssignmentTokens
open FiniteStateTransducer

def shift (assignment : Cell × Gadget.OrthogonalCellType) : Cell × Gadget.OrthogonalCellType :=
  ((assignment.1.1-1,assignment.1.2-1),assignment.2)

/-- Discard the first unit in each coordinate field. -/
def transition : Bool → Token → Bool × List Token
  | true,.coordinateUnit => (false,[])
  | false,.coordinateUnit => (false,[.coordinateUnit])
  | _,.fieldEnd => (true,[.fieldEnd])
  | _,.cellType cell => (true,[.cellType cell])

def output : List Token → List Token :=
  FiniteStateTransducer.output true transition (fun _ => [])

private theorem scan_units (count : Nat) (tail : List Token) :
    scan transition false (List.replicate count .coordinateUnit++tail)=
      ((scan transition false tail).1,
        List.replicate count .coordinateUnit++(scan transition false tail).2) := by
  induction count with
  | zero => simp
  | succ count ih =>
      simp only [List.replicate_succ,List.cons_append,scan,transition]
      rw [ih]
      rfl

private theorem scan_positive_units (count : Nat) (tail : List Token) :
    scan transition true (List.replicate (count+1) .coordinateUnit++tail)=
      ((scan transition false tail).1,
        List.replicate count .coordinateUnit++(scan transition false tail).2) := by
  rw [List.replicate_succ,List.cons_append]
  simp only [scan,transition,List.nil_append]
  exact scan_units count tail

private theorem scan_record (x y : Nat) (cell : Gadget.OrthogonalCellType) (tail : List Token) :
    scan transition true
      (List.replicate (x+1) .coordinateUnit++
        .fieldEnd::(List.replicate (y+1) .coordinateUnit++ .cellType cell::tail))=
      ((scan transition true tail).1,
        (List.replicate x .coordinateUnit++
          .fieldEnd::(List.replicate y .coordinateUnit++[.cellType cell]))++
        (scan transition true tail).2) := by
  rw [scan_positive_units]
  simp only [scan,transition]
  rw [scan_positive_units]
  simp [scan,transition,List.append_assoc]

private theorem scan_assignment (assignment : Cell × Gadget.OrthogonalCellType)
    (positive : 0<assignment.1.1 ∧ 0<assignment.1.2) (tail : List Token) :
    scan transition true (assignmentTokens assignment++tail)=
      ((scan transition true tail).1,
        assignmentTokens (shift assignment)++(scan transition true tail).2) := by
  have xEq : assignment.1.1.toNat=(assignment.1.1-1).toNat+1 := by omega
  have yEq : assignment.1.2.toNat=(assignment.1.2-1).toNat+1 := by omega
  simp only [assignmentTokens,shift,List.append_assoc,List.cons_append,List.nil_append]
  rw [xEq,yEq]
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using
    scan_record (assignment.1.1-1).toNat (assignment.1.2-1).toNat assignment.2 tail

/-- Positive coordinates make the token subtraction exact over integer cells. -/
theorem output_assignmentsTokens (assignments : List (Cell × Gadget.OrthogonalCellType))
    (positive : ∀ assignment∈assignments,0<assignment.1.1 ∧ 0<assignment.1.2) :
    output (assignmentsTokens assignments)=assignmentsTokens (assignments.map shift) := by
  have scanEq : scan transition true (assignmentsTokens assignments)=
      (true,assignmentsTokens (assignments.map shift)) := by
    induction assignments with
    | nil => rfl
    | cons assignment assignments ih =>
        change scan transition true (assignmentTokens assignment++assignmentsTokens assignments)=
          (true,assignmentTokens (shift assignment)++assignmentsTokens (assignments.map shift))
        rw [scan_assignment assignment (positive assignment (by simp)),
          ih (fun a member => positive a (by simp [member]))]
  simp only [output,FiniteStateTransducer.output,scanEq,List.append_nil]

def computableInPolyTime : TM2ComputableInPolyTime id id output :=
  FiniteStateTransducer.computableInPolyTime true transition (fun _ => [])

/-- The final finite drawing records are emitted from the original source
by composing the drawing emitter with the seam transducer. -/
def ofEmitter {Source Symbol : Type} [Fintype Symbol]
    (encodeSource : Source → List Symbol)
    (assignments : Source → List (Cell × Gadget.OrthogonalCellType))
    (emitter : TM2ComputableInPolyTime encodeSource id
      (fun source => assignmentsTokens (assignments source)))
    (positive : ∀ source assignment,assignment∈assignments source →
      0<assignment.1.1 ∧ 0<assignment.1.2) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => assignmentsTokens ((assignments source).map shift)) := by
  let compiler := TM2CompositionMachine.computableInPolyTime emitter computableInPolyTime
  exact compiler.of_eq (fun source => output_assignmentsTokens _ (positive source))
end LeanTrominoes.FiniteSparseAssignmentSeamCompiler
