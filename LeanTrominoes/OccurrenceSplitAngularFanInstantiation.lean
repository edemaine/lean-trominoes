import LeanTrominoes.EmbeddedCNFIncidenceDrawingRenaming
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation
import LeanTrominoes.OccurrenceSplitAngularFanDrawing
import LeanTrominoes.PeriodicCNFPlanarEightOccurrenceSplitPositioned

/-!
# Instantiating an angular Figure 7 fan

The certified angular fan uses the finite variable type `RingVertex` and
local coordinates.  This file renames its real ports and separator to the
actual implication-ring copies and translates it to the macrocell of a
positioned source variable.

The instantiated drawing's total variable placement is proved equal to the
placement used by the semantic positioned occurrence split.  Thus its spoke
suffixes and implication-ring routes can be spliced directly into the global
periodic incidence drawing.
-/

namespace LeanTrominoes
namespace OccurrenceSplitRing

open PlanarThreeSAT
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

/-- Pull the positioned split-copy placement back to local coordinates
around one source-variable macrocell. -/
def angularFanLocalVariablePosition
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    (occurrence : ThreeOccurrenceVariable Variable) : Cell :=
  Cell.sub
    (occurrenceVariablePosition sourcePlacement occurrence)
    (macroOrigin sourcePlacement atom)

/-- On every ring copy of the selected source atom, the pulled-back
placement is exactly the corresponding local ring vertex. -/
@[simp]
theorem angularFanLocalVariablePosition_ringCopy
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (vertex : RingVertex) :
    angularFanLocalVariablePosition sourcePlacement atom
        (ringCopy atom vertex) =
      ringVariablePosition vertex := by
  cases vertex with
  | separator =>
      apply Prod.ext <;>
        simp [angularFanLocalVariablePosition,
          occurrenceVariablePosition, ringCopy,
          ringVertexOfIndex, ringVariablePosition,
          separatorPosition, Cell.add, Cell.sub]
  | port port =>
      change
        angularFanLocalVariablePosition sourcePlacement atom
            (copy atom port) =
          variablePosition port
      rw [angularFanLocalVariablePosition,
        occurrenceVariablePosition_copy]
      apply Prod.ext <;>
        simp [Cell.add, Cell.sub]

/-- Rename the local port template to the actual copies of one source
variable, without moving its geometry yet. -/
def renamedAngularFanDrawing
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (count : Nat) :
    EmbeddedCNFIncidenceDrawing
      (ThreeOccurrenceVariable Variable) :=
  (angularFanDrawing count).rename
    (ringCopy atom)
    (angularFanLocalVariablePosition sourcePlacement atom)

/-- Place one renamed fan at the positioned macrocell of its source
variable. -/
def instantiatedAngularFanDrawing
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (count : Nat) :
    EmbeddedCNFIncidenceDrawing
      (ThreeOccurrenceVariable Variable) :=
  (renamedAngularFanDrawing
    sourcePlacement atom count).translate
      (macroOrigin sourcePlacement atom)

/-- After translation, the instantiated fan uses exactly the total variable
placement of the positioned fixed-eight split. -/
theorem instantiatedAngularFanDrawing_variablePosition
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (count : Nat) :
    (instantiatedAngularFanDrawing
      sourcePlacement atom count).variablePosition =
        occurrenceVariablePosition sourcePlacement := by
  funext occurrence
  apply Prod.ext <;>
    simp [instantiatedAngularFanDrawing,
      renamedAngularFanDrawing,
      EmbeddedCNFIncidenceDrawing.translate,
      EmbeddedCNFIncidenceDrawing.rename,
      angularFanLocalVariablePosition,
      Cell.add, Cell.sub]

/-- Every fitting instantiated fan inherits the complete local geometric
certificate. -/
theorem instantiatedAngularFanDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (count : Nat)
    (fits : count ≤ 8) :
    (instantiatedAngularFanDrawing
      sourcePlacement atom count).IsValid := by
  apply
    EmbeddedCNFIncidenceDrawing.isValid_translate
      (offset := macroOrigin sourcePlacement atom)
  apply
    EmbeddedCNFIncidenceDrawing.isValid_rename
      (variableMap := ringCopy atom)
      (targetPosition :=
        angularFanLocalVariablePosition
          sourcePlacement atom)
  · intro first _firstMember second _secondMember equal
    exact ringCopy_injective atom equal
  · intro vertex _vertexMember
    exact angularFanLocalVariablePosition_ringCopy
      sourcePlacement atom vertex
  · exact angularFanDrawing_isValid count fits

/-- The angular fan has exactly `count` selected spoke ports. -/
@[simp]
theorem angularFanPorts_length (count : Nat) :
    (angularFanPorts count).length = count := by
  simp [angularFanPorts]

/-- The selected spoke at an in-range presentation index is the east-first
port with that same index. -/
theorem angularFanPorts_getElem
    (count index : Nat) (indexLt : index < count) :
    (angularFanPorts count)[index]'(
      by simpa only [angularFanPorts_length] using indexLt) =
      angularPortOfIndex index := by
  simp [angularFanPorts]

/-- Consequently the renamed fan contains, for every angular-list index, the
selected spoke clause naming the exact semantic occurrence copy. -/
theorem renamedAngularFanDrawing_spokeClause_mem
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (count index : Nat)
    (indexLt : index < count) :
    (spokeClause (angularPortOfIndex index)).rename
        (ringCopy atom) ∈
      (renamedAngularFanDrawing
        sourcePlacement atom count).formula := by
  apply List.mem_map.mpr
  refine
    ⟨spokeClause (angularPortOfIndex index), ?_, rfl⟩
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨angularPortOfIndex index, ?_, rfl⟩
  exact List.mem_map.mpr
    ⟨index, List.mem_range.mpr indexLt, rfl⟩

/-- The instantiated selected spoke's unique literal is the expected
fixed-eight copy. -/
@[simp]
theorem renamedAngularFanSpokeClause_literals
    {Variable : Type*}
    (atom : Variable) (index : Nat) :
    ((spokeClause (angularPortOfIndex index)).rename
      (ringCopy atom)).literals =
        [(copy atom (angularPortOfIndex index), true)] := by
  rfl

end OccurrenceSplitRing
end LeanTrominoes
