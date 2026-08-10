import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumerationComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncode

/-!
# Computability of the encoded planar exact-one to 3DM reduction

The typed Dyer--Frieze enumeration is converted to the natural-number
`PeriodicThreeDM` interface by computing every colored reference and its
first position in the corresponding finite color class.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

set_option maxHeartbeats 2000000

/-! ## Computable structure representations -/

def referenceEquivData {Element : Type*} :
    Reference Element ≃ Element × Cell where
  toFun reference := (reference.atom, reference.offset)
  invFun data := ⟨data.1, data.2⟩
  left_inv reference := by cases reference; rfl
  right_inv data := by rcases data with ⟨atom, offset⟩; rfl

noncomputable instance referencePrimcodable
    {Element : Type*} [Primcodable Element] :
    Primcodable (Reference Element) :=
  Primcodable.ofEquiv (Element × Cell) referenceEquivData

theorem referenceEquivData_primrec
    {Element : Type*} [Primcodable Element] :
    Primrec (@referenceEquivData Element) :=
  Primrec.of_equiv

theorem referenceEquivData_symm_primrec
    {Element : Type*} [Primcodable Element] :
    Primrec (@referenceEquivData Element).symm :=
  Primrec.of_equiv_symm

theorem reference_atom_primrec
    {Element : Type*} [Primcodable Element] :
    Primrec (Reference.atom : Reference Element → Element) :=
  (Primrec.fst.comp referenceEquivData_primrec).of_eq fun _ => rfl

theorem reference_offset_primrec
    {Element : Type*} [Primcodable Element] :
    Primrec (Reference.offset : Reference Element → Cell) :=
  (Primrec.snd.comp referenceEquivData_primrec).of_eq fun _ => rfl

def tripleReferencesEquivData {Variable : Type*} :
    TripleReferences Variable ≃
      Reference (RedElement Variable) ×
        Reference (GreenElement Variable) ×
          Reference (BlueElement Variable) where
  toFun references :=
    (references.red, references.green, references.blue)
  invFun data := ⟨data.1, data.2.1, data.2.2⟩
  left_inv references := by cases references; rfl
  right_inv data := by rcases data with ⟨red, green, blue⟩; rfl

noncomputable instance tripleReferencesPrimcodable
    {Variable : Type*} [Primcodable Variable] :
    Primcodable (TripleReferences Variable) :=
  Primcodable.ofEquiv _ tripleReferencesEquivData

theorem tripleReferencesEquivData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (@tripleReferencesEquivData Variable) :=
  Primrec.of_equiv

theorem tripleReferencesEquivData_symm_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (@tripleReferencesEquivData Variable).symm :=
  Primrec.of_equiv_symm

theorem tripleReferences_red_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (TripleReferences.red :
      TripleReferences Variable → Reference (RedElement Variable)) :=
  (Primrec.fst.comp tripleReferencesEquivData_primrec).of_eq fun _ => rfl

theorem tripleReferences_green_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (TripleReferences.green :
      TripleReferences Variable → Reference (GreenElement Variable)) :=
  ((Primrec.fst.comp Primrec.snd).comp
    tripleReferencesEquivData_primrec).of_eq fun _ => rfl

theorem tripleReferences_blue_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (TripleReferences.blue :
      TripleReferences Variable → Reference (BlueElement Variable)) :=
  ((Primrec.snd.comp Primrec.snd).comp
    tripleReferencesEquivData_primrec).of_eq fun _ => rfl

/-! ## Occurrence metadata used by connector references -/

theorem nextUsedSlot_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        (PeriodicCNF Variable × Variable) × OccurrenceSlot =>
      nextUsedSlot data.1.1 data.1.2 data.2 := by
  let Input := (PeriodicCNF Variable × Variable) × OccurrenceSlot
  have slots : Primrec fun data : Input =>
      usedSlots data.1.1 data.1.2 :=
    usedSlots_primrec.comp Primrec.fst
  have index : Primrec fun data : Input =>
      (usedSlots data.1.1 data.1.2).idxOf data.2 :=
    Primrec.list_idxOf.comp Primrec.snd slots
  have nextIndex : Primrec fun data : Input =>
      ((usedSlots data.1.1 data.1.2).idxOf data.2 + 1) %
        (usedSlots data.1.1 data.1.2).length :=
    Primrec.nat_mod.comp
      (Primrec.nat_add.comp index (Primrec.const 1))
      (Primrec.list_length.comp slots)
  have selected : Primrec fun data : Input =>
      (usedSlots data.1.1 data.1.2)[
        ((usedSlots data.1.1 data.1.2).idxOf data.2 + 1) %
          (usedSlots data.1.1 data.1.2).length]? :=
    Primrec.list_getElem?.comp slots nextIndex
  exact (Primrec.option_getD.comp selected Primrec.snd).of_eq fun data => by
    unfold nextUsedSlot
    by_cases empty : (usedSlots data.1.1 data.1.2).isEmpty
    · have slotsEmpty : usedSlots data.1.1 data.1.2 = [] :=
        List.isEmpty_iff.mp empty
      simp [slotsEmpty]
    · simp [empty]

theorem occurrencePolarity_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        (PeriodicCNF Variable × Variable) × OccurrenceSlot =>
      occurrencePolarity data.1.1 data.1.2 data.2 := by
  have someCase : Primrec₂ fun
      (_data : (PeriodicCNF Variable × Variable) × OccurrenceSlot)
      (tagged : TaggedOccurrence Variable) => tagged.1.value :=
    PeriodicThreeCNF.literal_value_primrec.comp
      (Primrec.fst.comp Primrec.snd)
  exact (Primrec.option_casesOn occurrenceAt_primrec
    (Primrec.const false) someCase).of_eq fun data => by
      generalize found : occurrenceAt data.1.1 data.1.2 data.2 = value
      cases value <;> simp [occurrencePolarity, found]

theorem occurrenceReverseOffset_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        (PeriodicCNF Variable × Variable) × OccurrenceSlot =>
      occurrenceReverseOffset data.1.1 data.1.2 data.2 := by
  have someCase : Primrec₂ fun
      (_data : (PeriodicCNF Variable × Variable) × OccurrenceSlot)
      (tagged : TaggedOccurrence Variable) =>
      PeriodicOneInThreeToThreeDM.reverseOffset tagged.1.offset :=
    (Primrec.pair
      (LeanTrominoes.Computability.int_negate_primrec.comp
        (Primrec.fst.comp
          (PeriodicThreeCNF.literal_offset_primrec.comp
            (Primrec.fst.comp Primrec.snd))))
      (LeanTrominoes.Computability.int_negate_primrec.comp
        (Primrec.snd.comp
          (PeriodicThreeCNF.literal_offset_primrec.comp
            (Primrec.fst.comp Primrec.snd)))))
  exact (Primrec.option_casesOn occurrenceAt_primrec
    (Primrec.const ((0, 0) : Cell)) someCase).of_eq fun data => by
      generalize found : occurrenceAt data.1.1 data.1.2 data.2 = value
      cases value <;> simp [occurrenceReverseOffset, found]

theorem firstCycleLinkSlot_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        (PeriodicCNF Variable × Variable) × OccurrenceSlot =>
      firstCycleLinkSlot data.1.1 data.1.2 data.2 :=
  (Primrec.cond occurrencePolarity_primrec Primrec.snd
    nextUsedSlot_primrec).of_eq fun data => by
      simp [firstCycleLinkSlot]

theorem secondCycleLinkSlot_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        (PeriodicCNF Variable × Variable) × OccurrenceSlot =>
      secondCycleLinkSlot data.1.1 data.1.2 data.2 :=
  (Primrec.cond occurrencePolarity_primrec nextUsedSlot_primrec
    Primrec.snd).of_eq fun data => by
      simp [secondCycleLinkSlot]

/-! ## Typed reference calculation -/

theorem terminalGroupOfLiteralIndex_primrec :
    Primrec terminalGroupOfLiteralIndex := by
  have zero : PrimrecPred fun n : Nat => n = 0 :=
    Primrec.eq.comp Primrec.id (Primrec.const 0)
  have one : PrimrecPred fun n : Nat => n = 1 :=
    Primrec.eq.comp Primrec.id (Primrec.const 1)
  exact (Primrec.ite zero
    (Primrec.const X3CClauseTerminalGroup.top)
    (Primrec.ite one
      (Primrec.const X3CClauseTerminalGroup.left)
      (Primrec.const X3CClauseTerminalGroup.right))).of_eq fun n => by
        rcases n with _ | _ | n <;> rfl

theorem redClauseTerminal_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        (PeriodicCNF Variable × Variable) × OccurrenceSlot =>
      redClauseTerminal data.1.1 data.1.2 data.2 := by
  have clauseIndex := occurrenceClauseIndex_primrec
    (Variable := Variable)
  have group : Primrec fun data :
      (PeriodicCNF Variable × Variable) × OccurrenceSlot =>
      terminalGroupOfLiteralIndex
        (occurrenceLiteralIndex data.1.1 data.1.2 data.2) :=
    terminalGroupOfLiteralIndex_primrec.comp occurrenceLiteralIndex_primrec
  exact (redElement_clauseTerminal_primrec.comp
    (Primrec.pair clauseIndex group)).of_eq fun _ => rfl

theorem greenClauseTerminal_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        (PeriodicCNF Variable × Variable) × OccurrenceSlot =>
      greenClauseTerminal data.1.1 data.1.2 data.2 := by
  have group : Primrec fun data :
      (PeriodicCNF Variable × Variable) × OccurrenceSlot =>
      terminalGroupOfLiteralIndex
        (occurrenceLiteralIndex data.1.1 data.1.2 data.2) :=
    terminalGroupOfLiteralIndex_primrec.comp occurrenceLiteralIndex_primrec
  exact (greenElement_clauseTerminal_primrec.comp
    (Primrec.pair occurrenceClauseIndex_primrec group)).of_eq fun _ => rfl

theorem blueClauseTerminal_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        (PeriodicCNF Variable × Variable) × OccurrenceSlot =>
      blueClauseTerminal data.1.1 data.1.2 data.2 := by
  have group : Primrec fun data :
      (PeriodicCNF Variable × Variable) × OccurrenceSlot =>
      terminalGroupOfLiteralIndex
        (occurrenceLiteralIndex data.1.1 data.1.2 data.2) :=
    terminalGroupOfLiteralIndex_primrec.comp occurrenceLiteralIndex_primrec
  exact (blueElement_clauseTerminal_primrec.comp
    (Primrec.pair occurrenceClauseIndex_primrec group)).of_eq fun _ => rfl

theorem ordinaryRedElement_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        ((PeriodicCNF Variable × Variable) × OccurrenceSlot) ×
          VariableOccurrenceElement =>
      ordinaryRedElement data.1.1.1 data.1.1.2 data.1.2 data.2 := by
  let Base := (PeriodicCNF Variable × Variable) × OccurrenceSlot
  let Input := Base × VariableOccurrenceElement
  have atom : Primrec fun data : Input => data.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have firstSlot : Primrec fun data : Input =>
      firstCycleLinkSlot data.1.1.1 data.1.1.2 data.1.2 :=
    firstCycleLinkSlot_primrec.comp Primrec.fst
  have secondSlot : Primrec fun data : Input =>
      secondCycleLinkSlot data.1.1.1 data.1.1.2 data.1.2 :=
    secondCycleLinkSlot_primrec.comp Primrec.fst
  have first : Primrec fun data : Input =>
      RedElement.cycleLink data.1.1.2
        (firstCycleLinkSlot data.1.1.1 data.1.1.2 data.1.2) :=
    redElement_cycleLink_primrec.comp (Primrec.pair atom firstSlot)
  have second : Primrec fun data : Input =>
      RedElement.cycleLink data.1.1.2
        (secondCycleLinkSlot data.1.1.1 data.1.1.2 data.1.2) :=
    redElement_cycleLink_primrec.comp (Primrec.pair atom secondSlot)
  have terminal : Primrec fun data : Input =>
      redClauseTerminal data.1.1.1 data.1.1.2 data.1.2 :=
    redClauseTerminal_primrec.comp Primrec.fst
  have isFirst : PrimrecPred fun data : Input =>
      data.2 = VariableOccurrenceElement.leftContinuation :=
    Primrec.eq.comp Primrec.snd
      (Primrec.const VariableOccurrenceElement.leftContinuation)
  have isSecond : PrimrecPred fun data : Input =>
      data.2 = VariableOccurrenceElement.rightContinuation :=
    Primrec.eq.comp Primrec.snd
      (Primrec.const VariableOccurrenceElement.rightContinuation)
  exact (Primrec.ite isFirst first
    (Primrec.ite isSecond second terminal)).of_eq fun data => by
      cases data.2 <;> rfl

theorem ordinaryGreenElement_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        ((PeriodicCNF Variable × Variable) × OccurrenceSlot) ×
          VariableOccurrenceElement =>
      ordinaryGreenElement data.1.1.1 data.1.1.2 data.1.2 data.2 := by
  let Base := (PeriodicCNF Variable × Variable) × OccurrenceSlot
  let Input := Base × VariableOccurrenceElement
  have atomSlot : Primrec fun data : Input =>
      (data.1.1.2, data.1.2) :=
    Primrec.pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)
  have cycle : Primrec fun data : Input =>
      GreenElement.ordinaryInternal data.1.1.2 data.1.2
        OrdinaryInternal.cycleShared :=
    greenElement_ordinaryInternal_primrec.comp
      (Primrec.pair atomSlot
        (Primrec.const OrdinaryInternal.cycleShared))
  have auxiliary : Primrec fun data : Input =>
      GreenElement.ordinaryInternal data.1.1.2 data.1.2
        OrdinaryInternal.auxiliaryShared :=
    greenElement_ordinaryInternal_primrec.comp
      (Primrec.pair atomSlot
        (Primrec.const OrdinaryInternal.auxiliaryShared))
  have terminal : Primrec fun data : Input =>
      greenClauseTerminal data.1.1.1 data.1.1.2 data.1.2 :=
    greenClauseTerminal_primrec.comp Primrec.fst
  have isCycle : PrimrecPred fun data : Input =>
      data.2 = VariableOccurrenceElement.cycleShared :=
    Primrec.eq.comp Primrec.snd
      (Primrec.const VariableOccurrenceElement.cycleShared)
  have isAuxiliary : PrimrecPred fun data : Input =>
      data.2 = VariableOccurrenceElement.auxiliaryShared :=
    Primrec.eq.comp Primrec.snd
      (Primrec.const VariableOccurrenceElement.auxiliaryShared)
  exact (Primrec.ite isCycle cycle
    (Primrec.ite isAuxiliary auxiliary terminal)).of_eq fun data => by
      cases data.2 <;> rfl

theorem ordinaryBlueElement_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        ((PeriodicCNF Variable × Variable) × OccurrenceSlot) ×
          VariableOccurrenceElement =>
      ordinaryBlueElement data.1.1.1 data.1.1.2 data.1.2 data.2 := by
  let Base := (PeriodicCNF Variable × Variable) × OccurrenceSlot
  let Input := Base × VariableOccurrenceElement
  have atomSlot : Primrec fun data : Input =>
      (data.1.1.2, data.1.2) :=
    Primrec.pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)
  have cycle : Primrec fun data : Input =>
      BlueElement.ordinaryInternal data.1.1.2 data.1.2
        OrdinaryInternal.cycleShared :=
    blueElement_ordinaryInternal_primrec.comp
      (Primrec.pair atomSlot
        (Primrec.const OrdinaryInternal.cycleShared))
  have auxiliary : Primrec fun data : Input =>
      BlueElement.ordinaryInternal data.1.1.2 data.1.2
        OrdinaryInternal.auxiliaryShared :=
    blueElement_ordinaryInternal_primrec.comp
      (Primrec.pair atomSlot
        (Primrec.const OrdinaryInternal.auxiliaryShared))
  have terminal : Primrec fun data : Input =>
      blueClauseTerminal data.1.1.1 data.1.1.2 data.1.2 :=
    blueClauseTerminal_primrec.comp Primrec.fst
  have isCycle : PrimrecPred fun data : Input =>
      data.2 = VariableOccurrenceElement.cycleShared :=
    Primrec.eq.comp Primrec.snd
      (Primrec.const VariableOccurrenceElement.cycleShared)
  have isAuxiliary : PrimrecPred fun data : Input =>
      data.2 = VariableOccurrenceElement.auxiliaryShared :=
    Primrec.eq.comp Primrec.snd
      (Primrec.const VariableOccurrenceElement.auxiliaryShared)
  exact (Primrec.ite isCycle cycle
    (Primrec.ite isAuxiliary auxiliary terminal)).of_eq fun data => by
      cases data.2 <;> rfl

theorem fixedRedRedElement_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        ((PeriodicCNF Variable × Variable) × OccurrenceSlot) ×
          FixedRedConnectorRed =>
      fixedRedRedElement data.1.1.1 data.1.1.2 data.1.2 data.2 := by
  let Base := (PeriodicCNF Variable × Variable) × OccurrenceSlot
  let Input := Base × FixedRedConnectorRed
  have atom : Primrec fun data : Input => data.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have firstSlot := firstCycleLinkSlot_primrec (Variable := Variable)
  have secondSlot := secondCycleLinkSlot_primrec (Variable := Variable)
  have leftTop : Primrec fun data : Input =>
      RedElement.cycleLink data.1.1.2
        (secondCycleLinkSlot data.1.1.1 data.1.1.2 data.1.2) :=
    redElement_cycleLink_primrec.comp
      (Primrec.pair atom (secondSlot.comp Primrec.fst))
  have leftBottom : Primrec fun data : Input =>
      RedElement.cycleLink data.1.1.2
        (firstCycleLinkSlot data.1.1.1 data.1.1.2 data.1.2) :=
    redElement_cycleLink_primrec.comp
      (Primrec.pair atom (firstSlot.comp Primrec.fst))
  have atomSlot : Primrec fun data : Input =>
      (data.1.1.2, data.1.2) :=
    Primrec.pair atom (Primrec.snd.comp Primrec.fst)
  have internal (element : FixedRedInternalRed) :
      Primrec fun data : Input =>
        RedElement.fixedRedInternal data.1.1.2 data.1.2 element :=
    redElement_fixedRedInternal_primrec.comp
      (Primrec.pair atomSlot (Primrec.const element))
  have terminal : Primrec fun data : Input =>
      redClauseTerminal data.1.1.1 data.1.1.2 data.1.2 :=
    redClauseTerminal_primrec.comp Primrec.fst
  have isTop : PrimrecPred fun data : Input =>
      data.2 = FixedRedConnectorRed.leftTopPort :=
    Primrec.eq.comp Primrec.snd
      (Primrec.const FixedRedConnectorRed.leftTopPort)
  have isBottom : PrimrecPred fun data : Input =>
      data.2 = FixedRedConnectorRed.leftBottomPort :=
    Primrec.eq.comp Primrec.snd
      (Primrec.const FixedRedConnectorRed.leftBottomPort)
  have isMiddle : PrimrecPred fun data : Input =>
      data.2 = FixedRedConnectorRed.middleRung :=
    Primrec.eq.comp Primrec.snd
      (Primrec.const FixedRedConnectorRed.middleRung)
  have isAuxiliary : PrimrecPred fun data : Input =>
      data.2 = FixedRedConnectorRed.topAuxiliary :=
    Primrec.eq.comp Primrec.snd
      (Primrec.const FixedRedConnectorRed.topAuxiliary)
  exact (Primrec.ite isTop leftTop
    (Primrec.ite isBottom leftBottom
      (Primrec.ite isMiddle (internal .middleRung)
        (Primrec.ite isAuxiliary
          (internal .topAuxiliary) terminal)))).of_eq fun data => by
            cases data.2 <;> rfl

theorem fixedRedGreenElement_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        ((PeriodicCNF Variable × Variable) × OccurrenceSlot) ×
          FixedRedConnectorGreen =>
      fixedRedGreenElement data.1.1.1 data.1.1.2 data.1.2 data.2 := by
  let Base := (PeriodicCNF Variable × Variable) × OccurrenceSlot
  let Input := Base × FixedRedConnectorGreen
  have atomSlot : Primrec fun data : Input =>
      (data.1.1.2, data.1.2) :=
    Primrec.pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)
  have internal (element : FixedRedInternalGreen) :
      Primrec fun data : Input =>
        GreenElement.fixedRedInternal data.1.1.2 data.1.2 element :=
    greenElement_fixedRedInternal_primrec.comp
      (Primrec.pair atomSlot (Primrec.const element))
  have terminal : Primrec fun data : Input =>
      greenClauseTerminal data.1.1.1 data.1.1.2 data.1.2 :=
    greenClauseTerminal_primrec.comp Primrec.fst
  have isLeft : PrimrecPred fun data : Input =>
      data.2 = FixedRedConnectorGreen.leftRung :=
    Primrec.eq.comp Primrec.snd
      (Primrec.const FixedRedConnectorGreen.leftRung)
  have isTop : PrimrecPred fun data : Input =>
      data.2 = FixedRedConnectorGreen.topRightLink :=
    Primrec.eq.comp Primrec.snd
      (Primrec.const FixedRedConnectorGreen.topRightLink)
  have isBottom : PrimrecPred fun data : Input =>
      data.2 = FixedRedConnectorGreen.bottomRightLink :=
    Primrec.eq.comp Primrec.snd
      (Primrec.const FixedRedConnectorGreen.bottomRightLink)
  exact (Primrec.ite isLeft
      (internal FixedRedInternalGreen.leftRung)
    (Primrec.ite isTop
      (internal FixedRedInternalGreen.topRightLink)
      (Primrec.ite isBottom
        (internal FixedRedInternalGreen.bottomRightLink)
        terminal))).of_eq fun data => by cases data.2 <;> rfl

theorem fixedRedBlueElement_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        ((PeriodicCNF Variable × Variable) × OccurrenceSlot) ×
          FixedRedConnectorBlue =>
      fixedRedBlueElement data.1.1.1 data.1.1.2 data.1.2 data.2 := by
  let Base := (PeriodicCNF Variable × Variable) × OccurrenceSlot
  let Input := Base × FixedRedConnectorBlue
  have atomSlot : Primrec fun data : Input =>
      (data.1.1.2, data.1.2) :=
    Primrec.pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)
  have internal (element : FixedRedInternalBlue) :
      Primrec fun data : Input =>
        BlueElement.fixedRedInternal data.1.1.2 data.1.2 element :=
    blueElement_fixedRedInternal_primrec.comp
      (Primrec.pair atomSlot (Primrec.const element))
  have terminal : Primrec fun data : Input =>
      blueClauseTerminal data.1.1.1 data.1.1.2 data.1.2 :=
    blueClauseTerminal_primrec.comp Primrec.fst
  have isTop : PrimrecPred fun data : Input =>
      data.2 = FixedRedConnectorBlue.topLeftLink :=
    Primrec.eq.comp Primrec.snd
      (Primrec.const FixedRedConnectorBlue.topLeftLink)
  have isBottom : PrimrecPred fun data : Input =>
      data.2 = FixedRedConnectorBlue.bottomLeftLink :=
    Primrec.eq.comp Primrec.snd
      (Primrec.const FixedRedConnectorBlue.bottomLeftLink)
  have isRight : PrimrecPred fun data : Input =>
      data.2 = FixedRedConnectorBlue.rightRung :=
    Primrec.eq.comp Primrec.snd
      (Primrec.const FixedRedConnectorBlue.rightRung)
  exact (Primrec.ite isTop
      (internal FixedRedInternalBlue.topLeftLink)
    (Primrec.ite isBottom
      (internal FixedRedInternalBlue.bottomLeftLink)
      (Primrec.ite isRight
        (internal FixedRedInternalBlue.rightRung)
        terminal))).of_eq fun data => by cases data.2 <;> rfl


private theorem ordinaryRedReference_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        (((PeriodicCNF Variable × Variable) × OccurrenceSlot) ×
          VariableOccurrenceVariant) × VariableOccurrenceTriple =>
      (ordinaryTripleReferences data.1.1.1.1 data.1.1.1.2
        data.1.1.2 data.1.2 data.2).red := by
  let Base := (PeriodicCNF Variable × Variable) × OccurrenceSlot
  let Input := (Base × VariableOccurrenceVariant) ×
    VariableOccurrenceTriple
  have name : Primrec fun data : Input =>
      (data.2.references data.1.2).red :=
    (Primrec.dom_finite fun data :
      VariableOccurrenceVariant × VariableOccurrenceTriple =>
      (data.2.references data.1).red).comp
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have atom : Primrec fun data : Input =>
      ordinaryRedElement data.1.1.1.1 data.1.1.1.2 data.1.1.2
        (data.2.references data.1.2).red :=
    ordinaryRedElement_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) name)
  have connector : PrimrecPred fun data : Input =>
      (data.2.references data.1.2).red =
        VariableOccurrenceElement.connectorRed :=
    Primrec.eq.comp name
      (Primrec.const VariableOccurrenceElement.connectorRed)
  have offset : Primrec fun data : Input =>
      if (data.2.references data.1.2).red =
          VariableOccurrenceElement.connectorRed then
        occurrenceReverseOffset data.1.1.1.1 data.1.1.1.2 data.1.1.2
      else (0, 0) :=
    Primrec.ite connector
      (occurrenceReverseOffset_primrec.comp
        (Primrec.fst.comp Primrec.fst))
      (Primrec.const ((0, 0) : Cell))
  exact (referenceEquivData_symm_primrec.comp
    (Primrec.pair atom offset)).of_eq fun _ => rfl

private theorem ordinaryGreenReference_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        (((PeriodicCNF Variable × Variable) × OccurrenceSlot) ×
          VariableOccurrenceVariant) × VariableOccurrenceTriple =>
      (ordinaryTripleReferences data.1.1.1.1 data.1.1.1.2
        data.1.1.2 data.1.2 data.2).green := by
  let Base := (PeriodicCNF Variable × Variable) × OccurrenceSlot
  let Input := (Base × VariableOccurrenceVariant) ×
    VariableOccurrenceTriple
  have name : Primrec fun data : Input =>
      (data.2.references data.1.2).green :=
    (Primrec.dom_finite fun data :
      VariableOccurrenceVariant × VariableOccurrenceTriple =>
      (data.2.references data.1).green).comp
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have atom : Primrec fun data : Input =>
      ordinaryGreenElement data.1.1.1.1 data.1.1.1.2 data.1.1.2
        (data.2.references data.1.2).green :=
    ordinaryGreenElement_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) name)
  have connector : PrimrecPred fun data : Input =>
      (data.2.references data.1.2).green =
        VariableOccurrenceElement.connectorGreen :=
    Primrec.eq.comp name
      (Primrec.const VariableOccurrenceElement.connectorGreen)
  have offset : Primrec fun data : Input =>
      if (data.2.references data.1.2).green =
          VariableOccurrenceElement.connectorGreen then
        occurrenceReverseOffset data.1.1.1.1 data.1.1.1.2 data.1.1.2
      else (0, 0) :=
    Primrec.ite connector
      (occurrenceReverseOffset_primrec.comp
        (Primrec.fst.comp Primrec.fst))
      (Primrec.const ((0, 0) : Cell))
  exact (referenceEquivData_symm_primrec.comp
    (Primrec.pair atom offset)).of_eq fun _ => rfl

private theorem ordinaryBlueReference_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        (((PeriodicCNF Variable × Variable) × OccurrenceSlot) ×
          VariableOccurrenceVariant) × VariableOccurrenceTriple =>
      (ordinaryTripleReferences data.1.1.1.1 data.1.1.1.2
        data.1.1.2 data.1.2 data.2).blue := by
  let Base := (PeriodicCNF Variable × Variable) × OccurrenceSlot
  let Input := (Base × VariableOccurrenceVariant) ×
    VariableOccurrenceTriple
  have name : Primrec fun data : Input =>
      (data.2.references data.1.2).blue :=
    (Primrec.dom_finite fun data :
      VariableOccurrenceVariant × VariableOccurrenceTriple =>
      (data.2.references data.1).blue).comp
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have atom : Primrec fun data : Input =>
      ordinaryBlueElement data.1.1.1.1 data.1.1.1.2 data.1.1.2
        (data.2.references data.1.2).blue :=
    ordinaryBlueElement_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) name)
  have connector : PrimrecPred fun data : Input =>
      (data.2.references data.1.2).blue =
        VariableOccurrenceElement.connectorBlue :=
    Primrec.eq.comp name
      (Primrec.const VariableOccurrenceElement.connectorBlue)
  have offset : Primrec fun data : Input =>
      if (data.2.references data.1.2).blue =
          VariableOccurrenceElement.connectorBlue then
        occurrenceReverseOffset data.1.1.1.1 data.1.1.1.2 data.1.1.2
      else (0, 0) :=
    Primrec.ite connector
      (occurrenceReverseOffset_primrec.comp
        (Primrec.fst.comp Primrec.fst))
      (Primrec.const ((0, 0) : Cell))
  exact (referenceEquivData_symm_primrec.comp
    (Primrec.pair atom offset)).of_eq fun _ => rfl

theorem ordinaryTripleReferences_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        (((PeriodicCNF Variable × Variable) × OccurrenceSlot) ×
          VariableOccurrenceVariant) × VariableOccurrenceTriple =>
      ordinaryTripleReferences data.1.1.1.1 data.1.1.1.2
        data.1.1.2 data.1.2 data.2 :=
  (tripleReferencesEquivData_symm_primrec.comp
    (Primrec.pair ordinaryRedReference_primrec
      (Primrec.pair ordinaryGreenReference_primrec
        ordinaryBlueReference_primrec))).of_eq fun _ => rfl

theorem fixedRedTripleReferences_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        ((PeriodicCNF Variable × Variable) × OccurrenceSlot) ×
          FixedRedConnectorTriple =>
      fixedRedTripleReferences data.1.1.1 data.1.1.2
        data.1.2 data.2 := by
  let Base := (PeriodicCNF Variable × Variable) × OccurrenceSlot
  let Input := Base × FixedRedConnectorTriple
  have redName : Primrec fun data : Input => data.2.references.red :=
    (Primrec.dom_finite fun triple : FixedRedConnectorTriple =>
      triple.references.red).comp Primrec.snd
  have greenName : Primrec fun data : Input => data.2.references.green :=
    (Primrec.dom_finite fun triple : FixedRedConnectorTriple =>
      triple.references.green).comp Primrec.snd
  have blueName : Primrec fun data : Input => data.2.references.blue :=
    (Primrec.dom_finite fun triple : FixedRedConnectorTriple =>
      triple.references.blue).comp Primrec.snd
  have terminalOffset : Primrec fun data : Input =>
      occurrenceReverseOffset data.1.1.1 data.1.1.2 data.1.2 :=
    occurrenceReverseOffset_primrec.comp Primrec.fst
  have redAtom : Primrec fun data : Input =>
      fixedRedRedElement data.1.1.1 data.1.1.2 data.1.2
        data.2.references.red :=
    fixedRedRedElement_primrec.comp
      (Primrec.pair Primrec.fst redName)
  have redConnector : PrimrecPred fun data : Input =>
      data.2.references.red = FixedRedConnectorRed.connectorPort :=
    Primrec.eq.comp redName
      (Primrec.const FixedRedConnectorRed.connectorPort)
  have redOffset := Primrec.ite redConnector terminalOffset
    (Primrec.const ((0, 0) : Cell))
  have red : Primrec fun data : Input =>
      Reference.mk
        (fixedRedRedElement data.1.1.1 data.1.1.2 data.1.2
          data.2.references.red)
        (if data.2.references.red = FixedRedConnectorRed.connectorPort then
          occurrenceReverseOffset data.1.1.1 data.1.1.2 data.1.2
        else (0, 0)) :=
    referenceEquivData_symm_primrec.comp
      (Primrec.pair redAtom redOffset)
  have greenAtom : Primrec fun data : Input =>
      fixedRedGreenElement data.1.1.1 data.1.1.2 data.1.2
        data.2.references.green :=
    fixedRedGreenElement_primrec.comp
      (Primrec.pair Primrec.fst greenName)
  have greenConnector : PrimrecPred fun data : Input =>
      data.2.references.green = FixedRedConnectorGreen.connectorPort :=
    Primrec.eq.comp greenName
      (Primrec.const FixedRedConnectorGreen.connectorPort)
  have greenOffset := Primrec.ite greenConnector terminalOffset
    (Primrec.const ((0, 0) : Cell))
  have green : Primrec fun data : Input =>
      Reference.mk
        (fixedRedGreenElement data.1.1.1 data.1.1.2 data.1.2
          data.2.references.green)
        (if data.2.references.green =
            FixedRedConnectorGreen.connectorPort then
          occurrenceReverseOffset data.1.1.1 data.1.1.2 data.1.2
        else (0, 0)) :=
    referenceEquivData_symm_primrec.comp
      (Primrec.pair greenAtom greenOffset)
  have blueAtom : Primrec fun data : Input =>
      fixedRedBlueElement data.1.1.1 data.1.1.2 data.1.2
        data.2.references.blue :=
    fixedRedBlueElement_primrec.comp
      (Primrec.pair Primrec.fst blueName)
  have blueConnector : PrimrecPred fun data : Input =>
      data.2.references.blue = FixedRedConnectorBlue.connectorPort :=
    Primrec.eq.comp blueName
      (Primrec.const FixedRedConnectorBlue.connectorPort)
  have blueOffset := Primrec.ite blueConnector terminalOffset
    (Primrec.const ((0, 0) : Cell))
  have blue : Primrec fun data : Input =>
      Reference.mk
        (fixedRedBlueElement data.1.1.1 data.1.1.2 data.1.2
          data.2.references.blue)
        (if data.2.references.blue =
            FixedRedConnectorBlue.connectorPort then
          occurrenceReverseOffset data.1.1.1 data.1.1.2 data.1.2
        else (0, 0)) :=
    referenceEquivData_symm_primrec.comp
      (Primrec.pair blueAtom blueOffset)
  exact (tripleReferencesEquivData_symm_primrec.comp
    (Primrec.pair red (Primrec.pair green blue))).of_eq fun _ => rfl

theorem clauseTripleReferences_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data : Nat × X3CClauseSet =>
      clauseTripleReferences (Variable := Variable) data.1 data.2 := by
  have terminalGroup : Primrec (X3CClauseTerminal.group :
      X3CClauseTerminal → X3CClauseTerminalGroup) :=
    (Primrec.fst.comp
      (Primrec.of_equiv : Primrec x3cClauseTerminalEquivData)).of_eq
        fun _ => rfl
  have redElement : Primrec fun data : Nat × X3CClauseElement =>
      clauseRedElement (Variable := Variable) data.1 data.2 := by
    let Input := Nat × X3CClauseElement
    have encoded : Primrec fun data : Input =>
        x3cClauseElementEquivData data.2 :=
      (Primrec.of_equiv : Primrec x3cClauseElementEquivData).comp
        Primrec.snd
    have internal : Primrec₂ fun (data : Input)
        (_value : X3CClauseInternal) =>
        RedElement.clauseInternal (Variable := Variable) data.1 :=
      (redElement_clauseInternal_primrec.comp
        (Primrec.fst.comp Primrec.fst)).to₂
    have terminal : Primrec₂ fun (data : Input)
        (value : X3CClauseTerminal) =>
        RedElement.clauseTerminal (Variable := Variable)
          data.1 value.group :=
      redElement_clauseTerminal_primrec.comp
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (terminalGroup.comp Primrec.snd))
    exact (Primrec.sumCasesOn encoded internal terminal).of_eq
      fun data => by cases data.2 <;> rfl
  have greenElement : Primrec fun data : Nat × X3CClauseElement =>
      clauseGreenElement (Variable := Variable) data.1 data.2 := by
    let Input := Nat × X3CClauseElement
    have encoded : Primrec fun data : Input =>
        x3cClauseElementEquivData data.2 :=
      (Primrec.of_equiv : Primrec x3cClauseElementEquivData).comp
        Primrec.snd
    have internal : Primrec₂ fun (data : Input)
        (_value : X3CClauseInternal) =>
        GreenElement.clauseInternal (Variable := Variable) data.1 :=
      (greenElement_clauseInternal_primrec.comp
        (Primrec.fst.comp Primrec.fst)).to₂
    have terminal : Primrec₂ fun (data : Input)
        (value : X3CClauseTerminal) =>
        GreenElement.clauseTerminal (Variable := Variable)
          data.1 value.group :=
      greenElement_clauseTerminal_primrec.comp
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (terminalGroup.comp Primrec.snd))
    exact (Primrec.sumCasesOn encoded internal terminal).of_eq
      fun data => by cases data.2 <;> rfl
  have blueElement : Primrec fun data : Nat × X3CClauseElement =>
      clauseBlueElement (Variable := Variable) data.1 data.2 := by
    let Input := Nat × X3CClauseElement
    have encoded : Primrec fun data : Input =>
        x3cClauseElementEquivData data.2 :=
      (Primrec.of_equiv : Primrec x3cClauseElementEquivData).comp
        Primrec.snd
    have internal : Primrec₂ fun (data : Input)
        (_value : X3CClauseInternal) =>
        BlueElement.clauseInternal (Variable := Variable) data.1 :=
      (blueElement_clauseInternal_primrec.comp
        (Primrec.fst.comp Primrec.fst)).to₂
    have terminal : Primrec₂ fun (data : Input)
        (value : X3CClauseTerminal) =>
        BlueElement.clauseTerminal (Variable := Variable)
          data.1 value.group :=
      blueElement_clauseTerminal_primrec.comp
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (terminalGroup.comp Primrec.snd))
    exact (Primrec.sumCasesOn encoded internal terminal).of_eq
      fun data => by cases data.2 <;> rfl
  have redName : Primrec fun data : Nat × X3CClauseSet =>
      data.2.coloredReferences.red :=
    (Primrec.dom_finite fun set : X3CClauseSet =>
      set.coloredReferences.red).comp Primrec.snd
  have greenName : Primrec fun data : Nat × X3CClauseSet =>
      data.2.coloredReferences.green :=
    (Primrec.dom_finite fun set : X3CClauseSet =>
      set.coloredReferences.green).comp Primrec.snd
  have blueName : Primrec fun data : Nat × X3CClauseSet =>
      data.2.coloredReferences.blue :=
    (Primrec.dom_finite fun set : X3CClauseSet =>
      set.coloredReferences.blue).comp Primrec.snd
  have redAtom : Primrec fun data : Nat × X3CClauseSet =>
      clauseRedElement (Variable := Variable) data.1
        data.2.coloredReferences.red :=
    redElement.comp (Primrec.pair Primrec.fst redName)
  have greenAtom : Primrec fun data : Nat × X3CClauseSet =>
      clauseGreenElement (Variable := Variable) data.1
        data.2.coloredReferences.green :=
    greenElement.comp (Primrec.pair Primrec.fst greenName)
  have blueAtom : Primrec fun data : Nat × X3CClauseSet =>
      clauseBlueElement (Variable := Variable) data.1
        data.2.coloredReferences.blue :=
    blueElement.comp (Primrec.pair Primrec.fst blueName)
  have red : Primrec fun data : Nat × X3CClauseSet =>
      Reference.mk
        (clauseRedElement (Variable := Variable) data.1
          data.2.coloredReferences.red) (0, 0) :=
    referenceEquivData_symm_primrec.comp
      (Primrec.pair redAtom (Primrec.const ((0, 0) : Cell)))
  have green : Primrec fun data : Nat × X3CClauseSet =>
      Reference.mk
        (clauseGreenElement (Variable := Variable) data.1
          data.2.coloredReferences.green) (0, 0) :=
    referenceEquivData_symm_primrec.comp
      (Primrec.pair greenAtom (Primrec.const ((0, 0) : Cell)))
  have blue : Primrec fun data : Nat × X3CClauseSet =>
      Reference.mk
        (clauseBlueElement (Variable := Variable) data.1
          data.2.coloredReferences.blue) (0, 0) :=
    referenceEquivData_symm_primrec.comp
      (Primrec.pair blueAtom (Primrec.const ((0, 0) : Cell)))
  exact (tripleReferencesEquivData_symm_primrec.comp
    (Primrec.pair red (Primrec.pair green blue))).of_eq fun _ => rfl

theorem tripleReferences_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data : PeriodicCNF Variable × Triple Variable =>
      tripleReferences data.1 data.2 := by
  let OrdinaryData :=
    ((Variable × OccurrenceSlot) × VariableOccurrenceVariant) ×
      VariableOccurrenceTriple
  let FixedData :=
    (Variable × OccurrenceSlot) × FixedRedConnectorTriple
  let ClauseData := Nat × X3CClauseSet
  let Input := PeriodicCNF Variable × Triple Variable
  have encoded : Primrec fun data : Input => tripleEquivData data.2 :=
    (Primrec.of_equiv : Primrec (@tripleEquivData Variable)).comp
      Primrec.snd
  have ordinaryCase : Primrec₂ fun (data : Input)
      (ordinary : OrdinaryData) =>
      ordinaryTripleReferences data.1 ordinary.1.1.1
        ordinary.1.1.2 ordinary.1.2 ordinary.2 := by
    change Primrec fun combined : Input × OrdinaryData =>
      ordinaryTripleReferences combined.1.1 combined.2.1.1.1
        combined.2.1.1.2 combined.2.1.2 combined.2.2
    have source : Primrec fun combined : Input × OrdinaryData =>
        combined.1.1 :=
      Primrec.fst.comp Primrec.fst
    have atom : Primrec fun combined : Input × OrdinaryData =>
        combined.2.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp
        (Primrec.fst.comp Primrec.snd))
    have slot : Primrec fun combined : Input × OrdinaryData =>
        combined.2.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp
        (Primrec.fst.comp Primrec.snd))
    have variant : Primrec fun combined : Input × OrdinaryData =>
        combined.2.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
    have triple : Primrec fun combined : Input × OrdinaryData =>
        combined.2.2 :=
      Primrec.snd.comp Primrec.snd
    exact ordinaryTripleReferences_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.pair (Primrec.pair source atom) slot)
          variant)
        triple)
  have restCase : Primrec₂ fun (data : Input)
      (rest : Sum FixedData ClauseData) =>
      match rest with
      | .inl fixed =>
          fixedRedTripleReferences data.1 fixed.1.1 fixed.1.2 fixed.2
      | .inr clause =>
          clauseTripleReferences (Variable := Variable)
            clause.1 clause.2 := by
    change Primrec fun combined : Input × Sum FixedData ClauseData =>
      match combined.2 with
      | .inl fixed =>
          fixedRedTripleReferences combined.1.1
            fixed.1.1 fixed.1.2 fixed.2
      | .inr clause =>
          clauseTripleReferences (Variable := Variable)
            clause.1 clause.2
    have fixedCase : Primrec₂ fun (data :
        Input × Sum FixedData ClauseData) (fixed : FixedData) =>
        fixedRedTripleReferences data.1.1
          fixed.1.1 fixed.1.2 fixed.2 := by
      change Primrec fun combined :
          (Input × Sum FixedData ClauseData) × FixedData =>
        fixedRedTripleReferences combined.1.1.1
          combined.2.1.1 combined.2.1.2 combined.2.2
      exact fixedRedTripleReferences_primrec.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.pair
              (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
              (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
            (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.snd.comp Primrec.snd))
    have clauseCase : Primrec₂ fun
        (_data : Input × Sum FixedData ClauseData)
        (clause : ClauseData) =>
        clauseTripleReferences (Variable := Variable)
          clause.1 clause.2 := by
      change Primrec fun combined :
          (Input × Sum FixedData ClauseData) × ClauseData =>
        clauseTripleReferences (Variable := Variable)
          combined.2.1 combined.2.2
      exact clauseTripleReferences_primrec.comp Primrec.snd
    exact (Primrec.sumCasesOn Primrec.snd fixedCase clauseCase).of_eq
      fun combined => by cases combined.2 <;> rfl
  exact (Primrec.sumCasesOn encoded ordinaryCase restCase).of_eq
    fun data => by cases data.2 <;> rfl


/-! ## Natural-number encoding -/

theorem encodeReference_primrec
    {Element : Type*} [Primcodable Element] [DecidableEq Element] :
    Primrec fun data : List Element × Reference Element =>
      encodeReference data.1 data.2 := by
  have atom : Primrec fun data : List Element × Reference Element =>
      data.2.atom :=
    reference_atom_primrec.comp Primrec.snd
  have index : Primrec fun data : List Element × Reference Element =>
      data.1.idxOf data.2.atom :=
    Primrec.list_idxOf.comp atom Primrec.fst
  have offset : Primrec fun data : List Element × Reference Element =>
      data.2.offset :=
    reference_offset_primrec.comp Primrec.snd
  exact (PeriodicThreeDMReference.equivData_symm_primrec.comp
    (Primrec.pair index offset)).of_eq fun _ => rfl

theorem encodedTriple_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data : PeriodicCNF Variable × Triple Variable =>
      (problem data.1).encodeTriple data.2 := by
  let Input := PeriodicCNF Variable × Triple Variable
  have references : Primrec fun data : Input =>
      tripleReferences data.1 data.2 :=
    tripleReferences_primrec
  have redReference : Primrec fun data : Input =>
      (tripleReferences data.1 data.2).red :=
    tripleReferences_red_primrec.comp references
  have red : Primrec fun data : Input =>
      encodeReference (redElements data.1)
        (tripleReferences data.1 data.2).red :=
    encodeReference_primrec.comp
      (Primrec.pair (redElements_primrec.comp Primrec.fst) redReference)
  have greenReference : Primrec fun data : Input =>
      (tripleReferences data.1 data.2).green :=
    tripleReferences_green_primrec.comp references
  have green : Primrec fun data : Input =>
      encodeReference (greenElements data.1)
        (tripleReferences data.1 data.2).green :=
    encodeReference_primrec.comp
      (Primrec.pair
        (greenElements_primrec.comp Primrec.fst) greenReference)
  have blueReference : Primrec fun data : Input =>
      (tripleReferences data.1 data.2).blue :=
    tripleReferences_blue_primrec.comp references
  have blue : Primrec fun data : Input =>
      encodeReference (blueElements data.1)
        (tripleReferences data.1 data.2).blue :=
    encodeReference_primrec.comp
      (Primrec.pair (blueElements_primrec.comp Primrec.fst) blueReference)
  exact (PeriodicThreeDMTriple.equivData_symm_primrec.comp
    (Primrec.pair red (Primrec.pair green blue))).of_eq fun _ => rfl

/-- The planar exact-one to natural-number periodic 3DM map is primitive
recursive. -/
theorem encodedProblem_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (encodedProblem :
      PeriodicCNF Variable → PeriodicThreeDM) := by
  have redCount : Primrec fun source : PeriodicCNF Variable =>
      (redElements source).length :=
    Primrec.list_length.comp redElements_primrec
  have greenCount : Primrec fun source : PeriodicCNF Variable =>
      (greenElements source).length :=
    Primrec.list_length.comp greenElements_primrec
  have blueCount : Primrec fun source : PeriodicCNF Variable =>
      (blueElements source).length :=
    Primrec.list_length.comp blueElements_primrec
  have encodedTriples : Primrec fun source : PeriodicCNF Variable =>
      (triples source).map fun triple =>
        (problem source).encodeTriple triple :=
    Primrec.list_map triples_primrec encodedTriple_primrec.to₂
  exact (PeriodicThreeDM.equivData_symm_primrec.comp
    (Primrec.pair redCount
      (Primrec.pair greenCount
        (Primrec.pair blueCount encodedTriples)))).of_eq fun _ => rfl

/-- The planar exact-one to natural-number periodic 3DM map is computable. -/
theorem encodedProblem_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable (encodedProblem :
      PeriodicCNF Variable → PeriodicThreeDM) :=
  encodedProblem_primrec.to_comp

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
