/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeToThreeDMEnumerationComputability
import LeanTrominoes.PeriodicOneInThreeToThreeDMReductionCorrectness
import LeanTrominoes.PeriodicOneInThreeNoUnitsComputability

/-!
# Computability of the exact-one to encoded periodic 3DM reduction

The typed color-class and triple enumerations are combined here with the
reference calculation and `List.idxOf` numbering.  The result is a
primitive-recursive map from a periodic exact-one formula to the complete
natural-number `PeriodicThreeDM` presentation.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- Product representation of a typed periodic reference. -/
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
  (Primrec.fst.comp referenceEquivData_primrec).of_eq
    fun _ => rfl

theorem reference_offset_primrec
    {Element : Type*} [Primcodable Element] :
    Primrec (Reference.offset : Reference Element → Cell) :=
  (Primrec.snd.comp referenceEquivData_primrec).of_eq
    fun _ => rfl

/-- Product representation of all three typed references. -/
def tripleReferencesEquivData {Variable : Type*} :
    TripleReferences Variable ≃
      Reference (RedElement Variable) ×
        Reference (GreenElement Variable) ×
          Reference (BlueElement Variable) where
  toFun references :=
    (references.red, references.green, references.blue)
  invFun data := ⟨data.1, data.2.1, data.2.2⟩
  left_inv references := by cases references; rfl
  right_inv data := by
    rcases data with ⟨red, green, blue⟩
    rfl

noncomputable instance tripleReferencesPrimcodable
    {Variable : Type*} [Primcodable Variable] :
    Primcodable (TripleReferences Variable) :=
  Primcodable.ofEquiv
    (Reference (RedElement Variable) ×
      Reference (GreenElement Variable) ×
        Reference (BlueElement Variable))
    tripleReferencesEquivData

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
      TripleReferences Variable →
        Reference (RedElement Variable)) :=
  (Primrec.fst.comp
    tripleReferencesEquivData_primrec).of_eq fun _ => rfl

theorem tripleReferences_green_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (TripleReferences.green :
      TripleReferences Variable →
        Reference (GreenElement Variable)) :=
  ((Primrec.fst.comp Primrec.snd).comp
    tripleReferencesEquivData_primrec).of_eq fun _ => rfl

theorem tripleReferences_blue_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (TripleReferences.blue :
      TripleReferences Variable →
        Reference (BlueElement Variable)) :=
  ((Primrec.snd.comp Primrec.snd).comp
    tripleReferencesEquivData_primrec).of_eq fun _ => rfl

theorem variableTripleSlot_primrec :
    Primrec variableTripleSlot :=
  Primrec.dom_finite variableTripleSlot

theorem variableTripleValue_primrec :
    Primrec variableTripleValue :=
  Primrec.dom_finite variableTripleValue

theorem variableTripleRed_primrec :
    Primrec fun triple : PlanarThreeDM.VariableTriple =>
      triple.references.red :=
  Primrec.dom_finite fun triple :
      PlanarThreeDM.VariableTriple =>
    triple.references.red

theorem variableTripleGreen_primrec :
    Primrec fun triple : PlanarThreeDM.VariableTriple =>
      triple.references.green :=
  Primrec.dom_finite fun triple :
      PlanarThreeDM.VariableTriple =>
    triple.references.green

theorem reverseOffset_primrec :
    Primrec reverseOffset := by
  exact Primrec.pair
    (LeanTrominoes.Computability.int_negate_primrec.comp
      Primrec.fst)
    (LeanTrominoes.Computability.int_negate_primrec.comp
      Primrec.snd)

theorem variableBlueElement_primrec
    {Variable : Type*} [Primcodable Variable]
    [DecidableEq Variable] :
    Primrec fun input :
        (PeriodicCNF Variable × Variable) ×
          PlanarThreeDM.VariableTriple =>
      variableBlueElement input.1.1 input.1.2
        input.2 := by
  let Input :=
    (PeriodicCNF Variable × Variable) ×
      PlanarThreeDM.VariableTriple
  have slot : Primrec fun input : Input =>
      variableTripleSlot input.2 :=
    variableTripleSlot_primrec.comp Primrec.snd
  have occurrence : Primrec fun input : Input =>
      occurrenceAt input.1.1 input.1.2
        (variableTripleSlot input.2) :=
    occurrenceAt_primrec.comp
      (Primrec.pair Primrec.fst slot)
  have unused : Primrec fun input : Input =>
      BlueElement.unused input.1.2
        (variableTripleSlot input.2) :=
    blueElement_unused_primrec.comp
      (Primrec.pair
        (Primrec.snd.comp Primrec.fst) slot)
  have used : Primrec₂ fun (input : Input)
      (tagged : TaggedOccurrence Variable) =>
      if variableTripleValue input.2 =
          tagged.1.value then
        BlueElement.clause (Variable := Variable)
          tagged.2.1
      else
        BlueElement.complement (Variable := Variable)
          tagged.2.1
          tagged.2.2 := by
    change Primrec fun combined :
        Input × TaggedOccurrence Variable =>
      if variableTripleValue combined.1.2 =
          combined.2.1.value then
        BlueElement.clause (Variable := Variable)
          combined.2.2.1
      else
        BlueElement.complement (Variable := Variable)
          combined.2.2.1
          combined.2.2.2
    have agrees : PrimrecPred fun combined :
        Input × TaggedOccurrence Variable =>
      variableTripleValue combined.1.2 =
        combined.2.1.value :=
      Primrec.eq.comp
        (variableTripleValue_primrec.comp
          (Primrec.snd.comp Primrec.fst))
        (PeriodicThreeCNF.literal_value_primrec.comp
          (Primrec.fst.comp Primrec.snd))
    have clause : Primrec fun combined :
        Input × TaggedOccurrence Variable =>
        BlueElement.clause combined.2.2.1 :=
      (blueElement_clause_primrec
        (Variable := Variable)).comp
          (Primrec.fst.comp
            (Primrec.snd.comp Primrec.snd))
    have complement : Primrec fun combined :
        Input × TaggedOccurrence Variable =>
        BlueElement.complement combined.2.2.1
          combined.2.2.2 :=
      (blueElement_complement_primrec
        (Variable := Variable)).comp
          (Primrec.snd.comp Primrec.snd)
    exact Primrec.ite agrees clause complement
  exact (Primrec.option_casesOn occurrence unused used).of_eq
    fun input => by
      cases occurrence :
          occurrenceAt input.1.1 input.1.2
            (variableTripleSlot input.2) <;>
        simp [variableBlueElement, occurrence]

theorem variableBlueOffset_primrec
    {Variable : Type*} [Primcodable Variable]
    [DecidableEq Variable] :
    Primrec fun input :
        (PeriodicCNF Variable × Variable) ×
          PlanarThreeDM.VariableTriple =>
      variableBlueOffset input.1.1 input.1.2
        input.2 := by
  let Input :=
    (PeriodicCNF Variable × Variable) ×
      PlanarThreeDM.VariableTriple
  have slot : Primrec fun input : Input =>
      variableTripleSlot input.2 :=
    variableTripleSlot_primrec.comp Primrec.snd
  have occurrence : Primrec fun input : Input =>
      occurrenceAt input.1.1 input.1.2
        (variableTripleSlot input.2) :=
    occurrenceAt_primrec.comp
      (Primrec.pair Primrec.fst slot)
  have used : Primrec₂ fun (_input : Input)
      (tagged : TaggedOccurrence Variable) =>
      reverseOffset tagged.1.offset := by
    change Primrec fun combined :
        Input × TaggedOccurrence Variable =>
      reverseOffset combined.2.1.offset
    exact reverseOffset_primrec.comp
      (PeriodicThreeCNF.literal_offset_primrec.comp
        (Primrec.fst.comp Primrec.snd))
  exact (Primrec.option_casesOn occurrence
    (Primrec.const ((0, 0) : Cell)) used).of_eq
      fun input => by
        unfold variableBlueOffset
        cases occurrenceAt input.1.1 input.1.2
          (variableTripleSlot input.2) <;> rfl

theorem variableTripleReferences_primrec
    {Variable : Type*} [Primcodable Variable]
    [DecidableEq Variable] :
    Primrec fun input :
        (PeriodicCNF Variable × Variable) ×
          PlanarThreeDM.VariableTriple =>
      variableTripleReferences input.1.1 input.1.2
        input.2 := by
  let Input :=
    (PeriodicCNF Variable × Variable) ×
      PlanarThreeDM.VariableTriple
  have redAtom : Primrec fun input : Input =>
      RedElement.variable input.1.2
        input.2.references.red :=
    redElement_variable_primrec.comp
      (Primrec.pair
        (Primrec.snd.comp Primrec.fst)
        (variableTripleRed_primrec.comp Primrec.snd))
  have red : Primrec fun input : Input =>
      Reference.mk
        (RedElement.variable input.1.2
          input.2.references.red) (0, 0) :=
    referenceEquivData_symm_primrec.comp
      (Primrec.pair redAtom
        (Primrec.const ((0, 0) : Cell)))
  have greenAtom : Primrec fun input : Input =>
      GreenElement.variable input.1.2
        input.2.references.green :=
    greenElement_variable_primrec.comp
      (Primrec.pair
        (Primrec.snd.comp Primrec.fst)
        (variableTripleGreen_primrec.comp Primrec.snd))
  have green : Primrec fun input : Input =>
      Reference.mk
        (GreenElement.variable input.1.2
          input.2.references.green) (0, 0) :=
    referenceEquivData_symm_primrec.comp
      (Primrec.pair greenAtom
        (Primrec.const ((0, 0) : Cell)))
  have blueAtom : Primrec fun input : Input =>
      variableBlueElement input.1.1 input.1.2 input.2 :=
    variableBlueElement_primrec
  have blueOffset : Primrec fun input : Input =>
      variableBlueOffset input.1.1 input.1.2 input.2 :=
    variableBlueOffset_primrec
  have blue : Primrec fun input : Input =>
      Reference.mk
        (variableBlueElement input.1.1 input.1.2
          input.2)
        (variableBlueOffset input.1.1 input.1.2
          input.2) :=
    referenceEquivData_symm_primrec.comp
      (Primrec.pair blueAtom blueOffset)
  exact
    (tripleReferencesEquivData_symm_primrec.comp
      (Primrec.pair red
        (Primrec.pair green blue))).of_eq fun _ => rfl

theorem clauseAuxiliaryReferences_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : Nat × Nat =>
      clauseAuxiliaryReferences
        (Variable := Variable) input.1 input.2 := by
  have redAtom : Primrec fun input : Nat × Nat =>
      RedElement.clause (Variable := Variable) input.1 :=
    (redElement_clause_primrec
      (Variable := Variable)).comp Primrec.fst
  have red : Primrec fun input : Nat × Nat =>
      Reference.mk
        (RedElement.clause (Variable := Variable)
          input.1) (0, 0) :=
    referenceEquivData_symm_primrec.comp
      (Primrec.pair redAtom
        (Primrec.const ((0, 0) : Cell)))
  have greenAtom : Primrec fun input : Nat × Nat =>
      GreenElement.clause (Variable := Variable) input.1 :=
    (greenElement_clause_primrec
      (Variable := Variable)).comp Primrec.fst
  have green : Primrec fun input : Nat × Nat =>
      Reference.mk
        (GreenElement.clause (Variable := Variable)
          input.1) (0, 0) :=
    referenceEquivData_symm_primrec.comp
      (Primrec.pair greenAtom
        (Primrec.const ((0, 0) : Cell)))
  have blueAtom : Primrec fun input : Nat × Nat =>
      BlueElement.complement (Variable := Variable)
        input.1 input.2 :=
    blueElement_complement_primrec
  have blue : Primrec fun input : Nat × Nat =>
      Reference.mk
        (BlueElement.complement (Variable := Variable)
          input.1 input.2) (0, 0) :=
    referenceEquivData_symm_primrec.comp
      (Primrec.pair blueAtom
        (Primrec.const ((0, 0) : Cell)))
  exact
    (tripleReferencesEquivData_symm_primrec.comp
      (Primrec.pair red
        (Primrec.pair green blue))).of_eq fun _ => rfl

theorem tripleReferences_primrec
    {Variable : Type*} [Primcodable Variable]
    [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable × Triple Variable =>
      tripleReferences input.1 input.2 := by
  let Input := PeriodicCNF Variable × Triple Variable
  have encoded : Primrec fun input : Input =>
      tripleEquivData input.2 :=
    (Primrec.of_equiv :
      Primrec (@tripleEquivData Variable)).comp Primrec.snd
  have variableCase : Primrec₂ fun
      (input : Input)
      (data : Variable × PlanarThreeDM.VariableTriple) =>
      variableTripleReferences input.1 data.1 data.2 := by
    change Primrec fun combined :
        Input ×
          (Variable × PlanarThreeDM.VariableTriple) =>
      variableTripleReferences combined.1.1
        combined.2.1 combined.2.2
    exact variableTripleReferences_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
  have clauseCase : Primrec₂ fun
      (_input : Input)
      (data : Nat × Nat) =>
      clauseAuxiliaryReferences
        (Variable := Variable) data.1 data.2 := by
    change Primrec fun combined :
        Input × (Nat × Nat) =>
      clauseAuxiliaryReferences
        (Variable := Variable)
        combined.2.1 combined.2.2
    exact clauseAuxiliaryReferences_primrec.comp Primrec.snd
  exact (Primrec.sumCasesOn encoded variableCase
    clauseCase).of_eq fun input => by
      cases input.2 <;> rfl

theorem encodeReference_primrec
    {Element : Type*} [Primcodable Element]
    [DecidableEq Element] :
    Primrec fun input : List Element × Reference Element =>
      encodeReference input.1 input.2 := by
  have atom : Primrec fun input :
      List Element × Reference Element =>
      input.2.atom :=
    reference_atom_primrec.comp Primrec.snd
  have index : Primrec fun input :
      List Element × Reference Element =>
      input.1.idxOf input.2.atom :=
    Primrec.list_idxOf.comp atom Primrec.fst
  have offset : Primrec fun input :
      List Element × Reference Element =>
      input.2.offset :=
    reference_offset_primrec.comp Primrec.snd
  exact
    (PeriodicThreeDMReference.equivData_symm_primrec.comp
      (Primrec.pair index offset)).of_eq fun _ => rfl

theorem encodedTriple_primrec
    {Variable : Type*} [Primcodable Variable]
    [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable × Triple Variable =>
      (problem input.1).encodeTriple input.2 := by
  let Input := PeriodicCNF Variable × Triple Variable
  have references : Primrec fun input : Input =>
      tripleReferences input.1 input.2 :=
    tripleReferences_primrec
  have redReference : Primrec fun input : Input =>
      (tripleReferences input.1 input.2).red :=
    tripleReferences_red_primrec.comp references
  have red : Primrec fun input : Input =>
      encodeReference (redElements input.1)
        (tripleReferences input.1 input.2).red :=
    encodeReference_primrec.comp
      (Primrec.pair
        (redElements_primrec.comp Primrec.fst)
        redReference)
  have greenReference : Primrec fun input : Input =>
      (tripleReferences input.1 input.2).green :=
    tripleReferences_green_primrec.comp references
  have green : Primrec fun input : Input =>
      encodeReference (greenElements input.1)
        (tripleReferences input.1 input.2).green :=
    encodeReference_primrec.comp
      (Primrec.pair
        (greenElements_primrec.comp Primrec.fst)
        greenReference)
  have blueReference : Primrec fun input : Input =>
      (tripleReferences input.1 input.2).blue :=
    tripleReferences_blue_primrec.comp references
  have blue : Primrec fun input : Input =>
      encodeReference (blueElements input.1)
        (tripleReferences input.1 input.2).blue :=
    encodeReference_primrec.comp
      (Primrec.pair
        (blueElements_primrec.comp Primrec.fst)
        blueReference)
  exact
    (PeriodicThreeDMTriple.equivData_symm_primrec.comp
      (Primrec.pair red
        (Primrec.pair green blue))).of_eq fun _ => rfl

/-- The complete exact-one to natural-number periodic 3DM map is primitive
recursive. -/
theorem encodedProblem_primrec
    {Variable : Type*} [Primcodable Variable]
    [DecidableEq Variable] :
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
  have encodedTriples :
      Primrec fun source : PeriodicCNF Variable =>
        (triples source).map fun triple =>
          (problem source).encodeTriple triple :=
    Primrec.list_map triples_primrec
      encodedTriple_primrec.to₂
  exact
    (PeriodicThreeDM.equivData_symm_primrec.comp
      (Primrec.pair redCount
        (Primrec.pair greenCount
          (Primrec.pair blueCount
            encodedTriples)))).of_eq fun _ => rfl

/-- The complete exact-one to natural-number periodic 3DM map is computable. -/
theorem encodedProblem_computable
    {Variable : Type*} [Primcodable Variable]
    [DecidableEq Variable] :
    Computable (encodedProblem :
      PeriodicCNF Variable → PeriodicThreeDM) :=
  encodedProblem_primrec.to_comp

/-- Unit elimination followed by natural-number 3DM encoding is primitive
recursive. -/
theorem unitFreeEncodedProblem_primrec
    {Variable : Type*} [Primcodable Variable]
    [DecidableEq Variable] :
    Primrec (unitFreeEncodedProblem :
      PeriodicCNF Variable → PeriodicThreeDM) :=
  encodedProblem_primrec.comp
    PeriodicOneInThreeNoUnits.formula_primrec

/-- Unit elimination followed by natural-number 3DM encoding is computable. -/
theorem unitFreeEncodedProblem_computable
    {Variable : Type*} [Primcodable Variable]
    [DecidableEq Variable] :
    Computable (unitFreeEncodedProblem :
      PeriodicCNF Variable → PeriodicThreeDM) :=
  unitFreeEncodedProblem_primrec.to_comp

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
