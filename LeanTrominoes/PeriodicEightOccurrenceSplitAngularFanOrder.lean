import LeanTrominoes.PeriodicCNFPlanarEightOccurrenceSplitPositioned
import LeanTrominoes.PeriodicEightOccurrenceSplitTerminalPortGeometry
import LeanTrominoes.PeriodicThreeSATThreeAngularOrderSorted

/-!
# Angular-list indices as Figure 7 fan ports

The local occurrence-splitting fan consumes the terminal-ray order as a
numbered list.  This file identifies that number with all three presentations
used by the construction:

* the occurrence's `idxOf` position in its chosen order;
* the east-first Figure 7 port assigned to the copied source incidence; and
* the corresponding positioned variable vertex inside the split macrocell.

For the angular order, it also records that increasing list indices follow
the actual polar order of the source terminal rays.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicThreeSATThree

/-- In a chosen occurrence order, an in-range entry has its displayed list
index as its first index. -/
theorem occurrenceOrder_idxOf_getElem
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (order : OccurrenceOrder source)
    (atom : Variable) (index : Nat)
    (indexLt : index < (order.copies atom).length) :
    (order.copies atom).idxOf
        (order.copies atom)[index] = index :=
  (order.copies_nodup atom).idxOf_getElem index indexLt

/-- Every displayed entry of an atom's occurrence order names that same
source atom. -/
theorem occurrenceOrder_getElem_fst
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (order : OccurrenceOrder source)
    (atom : Variable) (index : Nat)
    (indexLt : index < (order.copies atom).length) :
    (order.copies atom)[index].1 = atom :=
  order.copy_fst atom (List.getElem_mem indexLt)

/-- East-first port assignment sends the entry at index `index` to exactly
the `index`th Figure 7 port. -/
theorem angularOrderedOccurrencePort_getElem
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (order : OccurrenceOrder source)
    (atom : Variable) (index : Nat)
    (indexLt : index < (order.copies atom).length) :
    angularOrderedOccurrencePort order
        (order.copies atom)[index] =
      angularPortOfIndex index := by
  unfold angularOrderedOccurrencePort
  rw [occurrenceOrder_getElem_fst order atom index indexLt,
    occurrenceOrder_idxOf_getElem order atom index indexLt]

/-- For a fitting eight-slot order, the assigned port's cyclic rank is the
entry's list index. -/
theorem angularOrderedOccurrencePort_getElem_angularRank
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (order : OccurrenceOrder source)
    (fits : FitsEightSlots order)
    (atom : Variable) (index : Nat)
    (indexLt : index < (order.copies atom).length) :
    (angularOrderedOccurrencePort order
        (order.copies atom)[index]).angularRank = index := by
  rw [angularOrderedOccurrencePort_getElem
    order atom index indexLt]
  exact angularRank_angularPortOfIndex
    (indexLt.trans_le (fits atom))

/-- The selected split variable for an indexed source incidence occupies the
matching east-first Figure 7 vertex in its source-variable macrocell. -/
theorem angularOccurrenceCopyPosition_getElem
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source)
    (atom : Variable) (index : Nat)
    (indexLt : index < (order.copies atom).length) :
    PeriodicEightOccurrenceSplitPositioned.occurrenceVariablePosition
        sourcePlacement
        (copy atom
          (angularOrderedOccurrencePort order
            (order.copies atom)[index])) =
      Cell.add
        (PeriodicEightOccurrenceSplitPositioned.macroOrigin
          sourcePlacement atom)
        (OccurrenceSplitRing.variablePosition
          (angularPortOfIndex index)) := by
  rw [angularOrderedOccurrencePort_getElem
    order atom index indexLt]
  exact
    PeriodicEightOccurrenceSplitPositioned.occurrenceVariablePosition_copy
      sourcePlacement atom (angularPortOfIndex index)

/-- Earlier entries in an angular occurrence list precede later entries in
the actual polar order of their source terminal rays. -/
theorem angularOccurrenceVariables_getElem_angleLE
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable)
    (first second : Nat)
    (firstLt :
      first <
        (angularOccurrenceVariables source routes atom).length)
    (secondLt :
      second <
        (angularOccurrenceVariables source routes atom).length)
    (before : first < second) :
    occurrenceAngleLE routes
        (angularOccurrenceVariables source routes atom)[first]
        (angularOccurrenceVariables source routes atom)[second] =
      true := by
  simpa using
    (angularOccurrenceVariables_pairwise
      source routes atom).rel_get_of_lt
        (a := ⟨first, firstLt⟩)
        (b := ⟨second, secondLt⟩)
        before

/-- Specialization of the generic port-index law to the occurrence order
obtained by sorting arbitrary terminal rays. -/
theorem angularOccurrenceOrder_port_getElem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) (index : Nat)
    (indexLt :
      index <
        (angularOccurrenceVariables source routes atom).length) :
    angularOrderedOccurrencePort
        (angularOccurrenceOrder source routes)
        (angularOccurrenceVariables source routes atom)[index] =
      angularPortOfIndex index := by
  exact angularOrderedOccurrencePort_getElem
    (angularOccurrenceOrder source routes)
    atom index indexLt

end PeriodicEightOccurrenceSplit
end LeanTrominoes
