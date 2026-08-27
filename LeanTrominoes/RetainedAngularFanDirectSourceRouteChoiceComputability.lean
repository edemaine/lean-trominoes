/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedClauseMetadataComputability
import LeanTrominoes.PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputability
import LeanTrominoes.RetainedAngularFanDirectSourceRouteChoice

/-!
# Computable encodings for coordinated direct-source route choices

The local coordinated-route atlas has a finite clause kind, but its literal
index has a kind-dependent bound.  This module encodes that dependent index
as a primitive-recursive subtype, then lifts the encoding to the positioned
route choice used by the final retained router.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

set_option maxHeartbeats 400000

/-! ## Finite atlas kinds -/

noncomputable instance : Primcodable RetainedDirectClauseKind :=
  Primcodable.ofEquiv
    (Fin (Fintype.card RetainedDirectClauseKind))
    (Fintype.equivFin RetainedDirectClauseKind)

/-- The number of local atlas entries in a direct clause is primitive
recursive (the clause-kind domain is finite). -/
theorem retainedDirectSourcePrefixChoices_length_primrec :
    Primrec fun kind : RetainedDirectClauseKind =>
      (retainedDirectSourcePrefixChoices kind).length :=
  Primrec.dom_finite _

/-! ## Dependent atlas indices -/

/-- Proof-free data underlying one dependent direct-atlas index. -/
abbrev RetainedDirectSourceAtlasIndexData :=
  { data : RetainedDirectClauseKind × Nat //
      data.2 < (retainedDirectSourcePrefixChoices data.1).length }

theorem retainedDirectSourceAtlasIndexData_valid_primrec :
    PrimrecPred fun data : RetainedDirectClauseKind × Nat =>
      data.2 < (retainedDirectSourcePrefixChoices data.1).length :=
  Primrec.nat_lt.comp Primrec.snd
    (retainedDirectSourcePrefixChoices_length_primrec.comp Primrec.fst)

noncomputable instance :
    Primcodable RetainedDirectSourceAtlasIndexData :=
  Primcodable.subtype retainedDirectSourceAtlasIndexData_valid_primrec

private theorem retainedDirectSourcePrefixChoices_length_le_three_computability :
    ∀ kind : RetainedDirectClauseKind,
      (retainedDirectSourcePrefixChoices kind).length ≤ 3 := by
  native_decide

noncomputable instance : Finite RetainedDirectSourceAtlasIndexData := by
  apply Finite.of_injective (fun data =>
    ((data.1.1,
      ⟨data.1.2,
        lt_of_lt_of_le data.2
          (retainedDirectSourcePrefixChoices_length_le_three_computability
            data.1.1)⟩) :
      RetainedDirectClauseKind × Fin 3))
  intro first second equality
  apply Subtype.ext
  exact congrArg (fun data : RetainedDirectClauseKind × Fin 3 =>
    (data.1, data.2.val)) equality

/-- Package a clause kind and its dependent finite literal index as ordinary
subtype data. -/
def retainedDirectSourceAtlasIndexData
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) :
    RetainedDirectSourceAtlasIndexData :=
  ⟨(kind, index.val), index.isLt⟩

/-! ## Positioned choices -/

private abbrev RetainedDirectSourceRouteChoiceData :=
  Cell × RetainedDirectSourceAtlasIndexData

def RetainedDirectSourceRouteChoice.equivData :
    RetainedDirectSourceRouteChoice ≃
      RetainedDirectSourceRouteChoiceData where
  toFun choice :=
    (choice.origin,
      retainedDirectSourceAtlasIndexData choice.kind choice.index)
  invFun data := {
    origin := data.1
    kind := data.2.1.1
    index := ⟨data.2.1.2, data.2.2⟩
  }
  left_inv choice := by cases choice; rfl
  right_inv data := by rcases data with ⟨origin, ⟨⟨kind, index⟩, bound⟩⟩; rfl

noncomputable instance : Primcodable RetainedDirectSourceRouteChoice :=
  Primcodable.ofEquiv RetainedDirectSourceRouteChoiceData
    RetainedDirectSourceRouteChoice.equivData

namespace RetainedDirectSourceRouteChoice

theorem equivData_primrec :
    Primrec equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec :
    Primrec equivData.symm :=
  Primrec.of_equiv_symm

theorem origin_primrec :
    Primrec RetainedDirectSourceRouteChoice.origin :=
  Primrec.fst.comp equivData_primrec

theorem kind_primrec :
    Primrec RetainedDirectSourceRouteChoice.kind :=
  Primrec.fst.comp
    (Primrec.subtype_val
      (hp := retainedDirectSourceAtlasIndexData_valid_primrec) |>.comp
        (Primrec.snd.comp equivData_primrec))

theorem index_val_primrec :
    Primrec fun choice : RetainedDirectSourceRouteChoice =>
      choice.index.val :=
  Primrec.snd.comp
    (Primrec.subtype_val
      (hp := retainedDirectSourceAtlasIndexData_valid_primrec) |>.comp
        (Primrec.snd.comp equivData_primrec))

/-- The positioned complete route selected by a choice and occurrence slot
is primitive recursive.  Its local atlas component has a finite domain; only
the final component-origin translation is unbounded. -/
theorem completeRoute_primrec :
    Primrec₂ RetainedDirectSourceRouteChoice.completeRoute := by
  change Primrec fun input :
      RetainedDirectSourceRouteChoice × RetainedTerminalSlot =>
      input.1.completeRoute input.2
  have atlasIndex : Primrec fun input :
      RetainedDirectSourceRouteChoice × RetainedTerminalSlot =>
      (RetainedDirectSourceRouteChoice.equivData input.1).2 :=
    Primrec.snd.comp
      (equivData_primrec.comp Primrec.fst)
  have localInput : Primrec fun input :
      RetainedDirectSourceRouteChoice × RetainedTerminalSlot =>
      ((RetainedDirectSourceRouteChoice.equivData input.1).2,
        input.2) :=
    Primrec.pair atlasIndex Primrec.snd
  have localRoute : Primrec fun input :
      RetainedDirectSourceAtlasIndexData × RetainedTerminalSlot =>
      retainedDirectSourceFanCompleteRouteAt
        input.1.1.1 ⟨input.1.1.2, input.1.2⟩ input.2 :=
    Primrec.dom_finite _
  have positionedOffset : Primrec fun input :
      RetainedDirectSourceRouteChoice × RetainedTerminalSlot =>
      retainedDirectSourceFanPositioningOffset input.1.origin :=
    Computability.cell_scale_primrec.comp
      (Primrec.const (retainedTerminalFanTotalRefinement : Int))
      (Computability.cell_scale_primrec.comp
        (Primrec.const (4 : Int))
        (origin_primrec.comp Primrec.fst))
  exact (PeriodicOrthocrossing.translatePolyline_primrec.comp
    positionedOffset (localRoute.comp localInput)).of_eq fun input => by
      rfl

end RetainedDirectSourceRouteChoice

/-! ## Checked construction -/

abbrev RetainedDirectSourceRouteChoiceRawData :=
  (Cell × RetainedDirectClauseKind) × Nat

theorem retainedDirectSourceRouteChoiceRawData_valid_primrec :
    PrimrecPred fun input : RetainedDirectSourceRouteChoiceRawData =>
      input.2 <
        (retainedDirectSourcePrefixChoices input.1.2).length :=
  Primrec.nat_lt.comp Primrec.snd
    (retainedDirectSourcePrefixChoices_length_primrec.comp
      (Primrec.snd.comp Primrec.fst))

theorem retainedDirectSourcePrefixChoices_length_pos :
    ∀ kind : RetainedDirectClauseKind,
      0 < (retainedDirectSourcePrefixChoices kind).length := by
  native_decide

/-- Total version of checked construction, reducing an arbitrary natural
index modulo the nonempty selected atlas profile. -/
def retainedDirectSourceRouteChoiceFromData
    (origin : Cell)
    (kind : RetainedDirectClauseKind)
    (index : Nat) :
    RetainedDirectSourceRouteChoice := {
  origin := origin
  kind := kind
  index :=
    ⟨index % (retainedDirectSourcePrefixChoices kind).length,
      Nat.mod_lt index
        (retainedDirectSourcePrefixChoices_length_pos kind)⟩
}

theorem retainedDirectSourceRouteChoiceFromData_primrec :
    Primrec fun input : RetainedDirectSourceRouteChoiceRawData =>
      retainedDirectSourceRouteChoiceFromData
        input.1.1 input.1.2 input.2 := by
  have length : Primrec fun input :
      RetainedDirectSourceRouteChoiceRawData =>
      (retainedDirectSourcePrefixChoices input.1.2).length :=
    retainedDirectSourcePrefixChoices_length_primrec.comp
      (Primrec.snd.comp Primrec.fst)
  have reduced : Primrec fun input :
      RetainedDirectSourceRouteChoiceRawData =>
      input.2 %
        (retainedDirectSourcePrefixChoices input.1.2).length :=
    Primrec.nat_mod.comp Primrec.snd length
  have rawIndex : Primrec fun input :
      RetainedDirectSourceRouteChoiceRawData =>
      (input.1.2,
        input.2 %
          (retainedDirectSourcePrefixChoices input.1.2).length) :=
    Primrec.pair (Primrec.snd.comp Primrec.fst) reduced
  have atlasIndex : Primrec fun input :
      RetainedDirectSourceRouteChoiceRawData =>
      (⟨(input.1.2,
          input.2 %
            (retainedDirectSourcePrefixChoices input.1.2).length),
        Nat.mod_lt input.2
          (retainedDirectSourcePrefixChoices_length_pos input.1.2)⟩ :
        RetainedDirectSourceAtlasIndexData) :=
    Primrec.subtype_mk
      (hp := retainedDirectSourceAtlasIndexData_valid_primrec)
      rawIndex
  exact (RetainedDirectSourceRouteChoice.equivData_symm_primrec.comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst) atlasIndex)).of_eq
      fun _ => rfl

/-- Construct a choice from proof-free data when its literal index belongs
to the selected local atlas profile. -/
def retainedDirectSourceRouteChoiceFromData?
    (origin : Cell)
    (kind : RetainedDirectClauseKind)
    (index : Nat) :
    Option RetainedDirectSourceRouteChoice :=
  if bound : index < (retainedDirectSourcePrefixChoices kind).length then
    some { origin := origin, kind := kind, index := ⟨index, bound⟩ }
  else
    none

/-- Checked construction of a dependent direct-route choice is primitive
recursive. -/
theorem retainedDirectSourceRouteChoiceFromData?_primrec :
    Primrec fun input : RetainedDirectSourceRouteChoiceRawData =>
      retainedDirectSourceRouteChoiceFromData?
        input.1.1 input.1.2 input.2 := by
  refine (Primrec.ite
    retainedDirectSourceRouteChoiceRawData_valid_primrec
    (Primrec.option_some_iff.mpr
      retainedDirectSourceRouteChoiceFromData_primrec)
    (Primrec.const none)).of_eq ?_
  intro input
  by_cases bound : input.2 <
      (retainedDirectSourcePrefixChoices input.1.2).length
  · simp [retainedDirectSourceRouteChoiceFromData?,
      retainedDirectSourceRouteChoiceFromData, bound,
      Nat.mod_eq_of_lt]
  · simp [retainedDirectSourceRouteChoiceFromData?, bound]

/-! ## Raw metadata selector -/

private theorem finOfNatMod_primrec
    (bound : Nat) (positive : 0 < bound) :
    Primrec fun index : Nat =>
      (⟨index % bound, Nat.mod_lt index positive⟩ : Fin bound) := by
  let boundedPred : PrimrecPred fun index : Nat => index < bound :=
    Primrec.nat_lt.comp Primrec.id (Primrec.const bound)
  let Bounded := { index : Nat // index < bound }
  letI : Primcodable Bounded := Primcodable.subtype boundedPred
  have reduced : Primrec fun index : Nat => index % bound :=
    Primrec.nat_mod.comp Primrec.id (Primrec.const bound)
  have bounded : Primrec fun index : Nat =>
      (⟨index % bound, Nat.mod_lt index positive⟩ : Bounded) :=
    Primrec.subtype_mk (hp := boundedPred) reduced
  have convert : Primrec (Fin.equivSubtype (n := bound)).symm :=
    Primrec.of_equiv_symm
  exact convert.comp bounded

/-- Total crossover kind selected by an arbitrary natural presentation
index.  Checked callers use it only below `26`. -/
def retainedDirectCrossoverKindFromNat
    (index : Nat) : RetainedDirectClauseKind :=
  .crossover ⟨index % 26, Nat.mod_lt index (by omega)⟩

theorem retainedDirectCrossoverKindFromNat_primrec :
    Primrec retainedDirectCrossoverKindFromNat := by
  have finiteIndex := finOfNatMod_primrec 26 (by omega)
  have constructor : Primrec fun index : Fin 26 =>
      RetainedDirectClauseKind.crossover index :=
    Primrec.dom_finite _
  exact constructor.comp finiteIndex

/-- Total duplicator kind selected by an arbitrary local-clause index.
Checked callers use it only below `2`. -/
def retainedDirectDuplicatorKindFromNat
    (arm : PlanarThreeSAT.DuplicatorArm) (index : Nat) :
    RetainedDirectClauseKind :=
  .duplicator arm ⟨index % 2, Nat.mod_lt index (by omega)⟩

theorem retainedDirectDuplicatorKindFromNat_primrec :
    Primrec₂ retainedDirectDuplicatorKindFromNat := by
  have finiteIndex := finOfNatMod_primrec 2 (by omega)
  have data : Primrec fun input :
      PlanarThreeSAT.DuplicatorArm × Nat =>
      ((input.1, ⟨input.2 % 2, Nat.mod_lt input.2 (by omega)⟩) :
        PlanarThreeSAT.DuplicatorArm × Fin 2) :=
    Primrec.pair Primrec.fst (finiteIndex.comp Primrec.snd)
  have constructor : Primrec fun input :
      PlanarThreeSAT.DuplicatorArm × Fin 2 =>
      RetainedDirectClauseKind.duplicator input.1 input.2 :=
    Primrec.dom_finite _
  exact constructor.comp data

theorem retainedDirectRoutedClauseArmIndex_val_primrec :
    Primrec fun arm : PlanarThreeSAT.DuplicatorArm =>
      (retainedDirectRoutedClauseArmIndex arm).val :=
  Primrec.dom_finite _

/-- Proof-free version of the raw direct-source selector.  The modulo-based
kind constructors are protected by the same explicit bounds as the original
dependent definition. -/
def retainedDirectSourceRouteChoiceComputed?
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (literalIndex : Nat) :
    Option RetainedDirectSourceRouteChoice :=
  match source with
  | .crossover crossing localClauseIndex =>
      if localClauseIndex < 26 then
        retainedDirectSourceRouteChoiceFromData?
          (crossingMacroOrigin crossing)
          (retainedDirectCrossoverKindFromNat localClauseIndex)
          literalIndex
      else
        none
  | .carrier _ _ => none
  | .bend _ _ => none
  | .routedClause site =>
      match (routedClausePortLiterals formula site)[literalIndex]? with
      | none => none
      | some port =>
          retainedDirectSourceRouteChoiceFromData?
            (routedClauseOrigin formula site)
            .routedClause
            (retainedDirectRoutedClauseArmIndex port.1).val
  | .routedVariable site _ arm _ localClauseIndex =>
      if localClauseIndex < 2 then
        retainedDirectSourceRouteChoiceFromData?
          (routedVariableOrigin formula site)
          (retainedDirectDuplicatorKindFromNat arm localClauseIndex)
          literalIndex
      else
        none

theorem retainedDirectSourceRouteChoiceComputed?_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (literalIndex : Nat) :
    retainedDirectSourceRouteChoiceComputed?
        formula source literalIndex =
      retainedDirectSourceRouteChoice?
        formula source literalIndex := by
  cases source with
  | crossover crossing localClauseIndex =>
      by_cases localLt : localClauseIndex < 26
      · have kindEq :
            retainedDirectCrossoverKindFromNat localClauseIndex =
              .crossover ⟨localClauseIndex, localLt⟩ := by
          apply congrArg RetainedDirectClauseKind.crossover
          apply Fin.ext
          simp [Nat.mod_eq_of_lt localLt]
        simp only [retainedDirectSourceRouteChoiceComputed?,
          retainedDirectSourceRouteChoice?, dif_pos localLt]
        rw [kindEq]
        rw [if_pos localLt]
        unfold retainedDirectSourceRouteChoiceFromData?
        rfl
      · simp [retainedDirectSourceRouteChoiceComputed?,
          retainedDirectSourceRouteChoice?, localLt]
  | carrier link localClauseIndex =>
      rfl
  | bend routeBend localClauseIndex =>
      rfl
  | routedClause site =>
      by_cases literalLt : literalIndex <
          (routedClausePortLiterals formula site).length
      · have lookup := List.getElem?_eq_getElem literalLt
        rw [retainedDirectSourceRouteChoiceComputed?, lookup]
        simp only [retainedDirectSourceRouteChoice?]
        rw [dif_pos literalLt]
        simp [retainedDirectSourceRouteChoiceFromData?]
      · have lookup :
            (routedClausePortLiterals formula site)[literalIndex]? = none :=
          List.getElem?_eq_none (Nat.le_of_not_gt literalLt)
        simp [retainedDirectSourceRouteChoiceComputed?,
          retainedDirectSourceRouteChoice?, literalLt]
  | routedVariable site armIndex arm link localClauseIndex =>
      by_cases localLt : localClauseIndex < 2
      · have kindEq :
            retainedDirectDuplicatorKindFromNat arm localClauseIndex =
              .duplicator arm ⟨localClauseIndex, localLt⟩ := by
          apply congrArg (RetainedDirectClauseKind.duplicator arm)
          apply Fin.ext
          simp [Nat.mod_eq_of_lt localLt]
        simp only [retainedDirectSourceRouteChoiceComputed?,
          retainedDirectSourceRouteChoice?, dif_pos localLt]
        rw [kindEq]
        rw [if_pos localLt]
        unfold retainedDirectSourceRouteChoiceFromData?
        rfl
      · simp [retainedDirectSourceRouteChoiceComputed?,
          retainedDirectSourceRouteChoice?, localLt]

private def retainedDirectCrossoverRouteChoice?
    (input : (CrossingRecord × Nat) × Nat) :
    Option RetainedDirectSourceRouteChoice :=
  if input.1.2 < 26 then
    retainedDirectSourceRouteChoiceFromData?
      (crossingMacroOrigin input.1.1)
      (retainedDirectCrossoverKindFromNat input.1.2)
      input.2
  else
    none

private theorem retainedDirectCrossoverRouteChoice?_primrec :
    Primrec retainedDirectCrossoverRouteChoice? := by
  have localLt : PrimrecPred fun input : (CrossingRecord × Nat) × Nat =>
      input.1.2 < 26 :=
    Primrec.nat_lt.comp
      (Primrec.snd.comp Primrec.fst) (Primrec.const 26)
  have raw : Primrec fun input : (CrossingRecord × Nat) × Nat =>
      ((crossingMacroOrigin input.1.1,
          retainedDirectCrossoverKindFromNat input.1.2), input.2) :=
    Primrec.pair
      (Primrec.pair
        (crossingMacroOrigin_primrec.comp
          (Primrec.fst.comp Primrec.fst))
        (retainedDirectCrossoverKindFromNat_primrec.comp
          (Primrec.snd.comp Primrec.fst)))
      Primrec.snd
  exact (Primrec.ite localLt
    (retainedDirectSourceRouteChoiceFromData?_primrec.comp raw)
    (Primrec.const none)).of_eq fun input => by
      simp [retainedDirectCrossoverRouteChoice?]

private abbrev RetainedDirectRoutedClauseChoiceInput
    (Variable : Type*) :=
  (PeriodicCNF Variable × ClauseRouteSite) × Nat

private def retainedDirectRoutedClauseRouteChoice?
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedDirectRoutedClauseChoiceInput Variable) :
    Option RetainedDirectSourceRouteChoice :=
  match (routedClausePortLiterals input.1.1 input.1.2)[input.2]? with
  | none => none
  | some port =>
      retainedDirectSourceRouteChoiceFromData?
        (routedClauseOrigin input.1.1 input.1.2)
        .routedClause
        (retainedDirectRoutedClauseArmIndex port.1).val

private theorem retainedDirectRoutedClauseRouteChoice?_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedDirectRoutedClauseRouteChoice?
      (Variable := Variable)) := by
  have ports : Primrec fun input :
      RetainedDirectRoutedClauseChoiceInput Variable =>
      routedClausePortLiterals input.1.1 input.1.2 :=
    (PeriodicOrthocrossing.routedClausePortLiterals_primrec
      (Variable := Variable)).comp Primrec.fst
  have lookup : Primrec fun input :
      RetainedDirectRoutedClauseChoiceInput Variable =>
      (routedClausePortLiterals input.1.1 input.1.2)[input.2]? :=
    Primrec.list_getElem?.comp ports Primrec.snd
  have somePort : Primrec₂ fun
      (input : RetainedDirectRoutedClauseChoiceInput Variable)
      (port : PlanarThreeSAT.DuplicatorArm × Bool) =>
      retainedDirectSourceRouteChoiceFromData?
        (routedClauseOrigin input.1.1 input.1.2)
        .routedClause
        (retainedDirectRoutedClauseArmIndex port.1).val := by
    change Primrec fun combined :
        RetainedDirectRoutedClauseChoiceInput Variable ×
          (PlanarThreeSAT.DuplicatorArm × Bool) =>
      retainedDirectSourceRouteChoiceFromData?
        (routedClauseOrigin combined.1.1.1 combined.1.1.2)
        .routedClause
        (retainedDirectRoutedClauseArmIndex combined.2.1).val
    have raw : Primrec fun combined :
        RetainedDirectRoutedClauseChoiceInput Variable ×
          (PlanarThreeSAT.DuplicatorArm × Bool) =>
        ((routedClauseOrigin combined.1.1.1 combined.1.1.2,
            RetainedDirectClauseKind.routedClause),
          (retainedDirectRoutedClauseArmIndex combined.2.1).val) :=
      Primrec.pair
        (Primrec.pair
          ((PeriodicOrthocrossing.routedClauseOrigin_primrec
            (Variable := Variable)).comp
              (Primrec.pair
                (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
                (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
          (Primrec.const RetainedDirectClauseKind.routedClause))
        (retainedDirectRoutedClauseArmIndex_val_primrec.comp
          (Primrec.fst.comp Primrec.snd))
    exact retainedDirectSourceRouteChoiceFromData?_primrec.comp raw
  exact (Primrec.option_casesOn lookup
    (Primrec.const none) somePort).of_eq fun input => by
      unfold retainedDirectRoutedClauseRouteChoice?
      cases (routedClausePortLiterals
        input.1.1 input.1.2)[input.2]? <;> rfl

private abbrev RetainedDirectRoutedVariableChoiceInput
    (Variable : Type*) :=
  (PeriodicCNF Variable ×
    DrawingPlanarSATClauseSource.RoutedVariableData Variable) × Nat

private def retainedDirectRoutedVariableRouteChoice?
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedDirectRoutedVariableChoiceInput Variable) :
    Option RetainedDirectSourceRouteChoice :=
  if input.1.2.2 < 2 then
    retainedDirectSourceRouteChoiceFromData?
      (routedVariableOrigin input.1.1 input.1.2.1.1.1.1)
      (retainedDirectDuplicatorKindFromNat
        input.1.2.1.1.2 input.1.2.2)
      input.2
  else
    none

private theorem retainedDirectRoutedVariableRouteChoice?_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedDirectRoutedVariableRouteChoice?
      (Variable := Variable)) := by
  have localLt : PrimrecPred fun input :
      RetainedDirectRoutedVariableChoiceInput Variable =>
      input.1.2.2 < 2 :=
    Primrec.nat_lt.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.const 2)
  have origin : Primrec fun input :
      RetainedDirectRoutedVariableChoiceInput Variable =>
      routedVariableOrigin input.1.1 input.1.2.1.1.1.1 :=
    routedVariableOrigin_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp
        (Primrec.fst.comp
          (Primrec.fst.comp
            (Primrec.fst.comp
              (Primrec.snd.comp Primrec.fst)))))
  have kind : Primrec fun input :
      RetainedDirectRoutedVariableChoiceInput Variable =>
      retainedDirectDuplicatorKindFromNat
        input.1.2.1.1.2 input.1.2.2 :=
    retainedDirectDuplicatorKindFromNat_primrec.comp
      (Primrec.snd.comp
        (Primrec.fst.comp
          (Primrec.fst.comp
            (Primrec.snd.comp Primrec.fst))))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have raw : Primrec fun input :
      RetainedDirectRoutedVariableChoiceInput Variable =>
      ((routedVariableOrigin input.1.1 input.1.2.1.1.1.1,
          retainedDirectDuplicatorKindFromNat
            input.1.2.1.1.2 input.1.2.2), input.2) :=
    Primrec.pair (Primrec.pair origin kind) Primrec.snd
  exact (Primrec.ite localLt
    (retainedDirectSourceRouteChoiceFromData?_primrec.comp raw)
    (Primrec.const none)).of_eq fun input => by
      simp [retainedDirectRoutedVariableRouteChoice?]

private abbrev RetainedDirectSourceRestThree (Variable : Type*) :=
  ClauseRouteSite ⊕
    DrawingPlanarSATClauseSource.RoutedVariableData Variable

private abbrev RetainedDirectSourceRestTwo (Variable : Type*) :=
  (RouteBend × Nat) ⊕ RetainedDirectSourceRestThree Variable

private abbrev RetainedDirectSourceRestOne (Variable : Type*) :=
  (PlanarThreeSAT.EqualityLink CarrierNode × Nat) ⊕
    RetainedDirectSourceRestTwo Variable

private abbrev RetainedDirectSourceData (Variable : Type*) :=
  (CrossingRecord × Nat) ⊕ RetainedDirectSourceRestOne Variable

private def retainedDirectSourceRouteChoiceComputedFromData?
    {Variable : Type*} [DecidableEq Variable]
    (input : (PeriodicCNF Variable ×
      RetainedDirectSourceData Variable) × Nat) :
    Option RetainedDirectSourceRouteChoice :=
  match input.1.2 with
  | .inl crossing =>
      retainedDirectCrossoverRouteChoice? (crossing, input.2)
  | .inr (.inl _) => none
  | .inr (.inr (.inl _)) => none
  | .inr (.inr (.inr (.inl site))) =>
      retainedDirectRoutedClauseRouteChoice?
        ((input.1.1, site), input.2)
  | .inr (.inr (.inr (.inr data))) =>
      retainedDirectRoutedVariableRouteChoice?
        ((input.1.1, data), input.2)

private def retainedDirectSourceRestThreeRouteChoice?
    {Variable : Type*} [DecidableEq Variable]
    (input : (PeriodicCNF Variable ×
      RetainedDirectSourceRestThree Variable) × Nat) :
    Option RetainedDirectSourceRouteChoice :=
  match input.1.2 with
  | .inl site =>
      retainedDirectRoutedClauseRouteChoice?
        ((input.1.1, site), input.2)
  | .inr data =>
      retainedDirectRoutedVariableRouteChoice?
        ((input.1.1, data), input.2)

private theorem retainedDirectSourceRestThreeRouteChoice?_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedDirectSourceRestThreeRouteChoice?
      (Variable := Variable)) := by
  let Input := (PeriodicCNF Variable ×
    RetainedDirectSourceRestThree Variable) × Nat
  have source : Primrec fun input : Input => input.1.2 :=
    Primrec.snd.comp Primrec.fst
  have clause : Primrec₂ fun (input : Input)
      (site : ClauseRouteSite) =>
      retainedDirectRoutedClauseRouteChoice?
        ((input.1.1, site), input.2) := by
    change Primrec fun combined : Input × ClauseRouteSite =>
      retainedDirectRoutedClauseRouteChoice?
        ((combined.1.1.1, combined.2), combined.1.2)
    exact retainedDirectRoutedClauseRouteChoice?_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
  have routedVariableChoice : Primrec₂ fun (input : Input)
      (data : DrawingPlanarSATClauseSource.RoutedVariableData Variable) =>
      retainedDirectRoutedVariableRouteChoice?
        ((input.1.1, data), input.2) := by
    change Primrec fun combined : Input ×
        DrawingPlanarSATClauseSource.RoutedVariableData Variable =>
      retainedDirectRoutedVariableRouteChoice?
        ((combined.1.1.1, combined.2), combined.1.2)
    exact retainedDirectRoutedVariableRouteChoice?_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
  exact (Primrec.sumCasesOn source clause routedVariableChoice).of_eq fun input => by
    unfold retainedDirectSourceRestThreeRouteChoice?
    cases input.1.2 <;> rfl

private def retainedDirectSourceRestTwoRouteChoice?
    {Variable : Type*} [DecidableEq Variable]
    (input : (PeriodicCNF Variable ×
      RetainedDirectSourceRestTwo Variable) × Nat) :
    Option RetainedDirectSourceRouteChoice :=
  match input.1.2 with
  | .inl _ => none
  | .inr rest =>
      retainedDirectSourceRestThreeRouteChoice?
        ((input.1.1, rest), input.2)

private theorem retainedDirectSourceRestTwoRouteChoice?_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedDirectSourceRestTwoRouteChoice?
      (Variable := Variable)) := by
  let Input := (PeriodicCNF Variable ×
    RetainedDirectSourceRestTwo Variable) × Nat
  have source : Primrec fun input : Input => input.1.2 :=
    Primrec.snd.comp Primrec.fst
  have bend : Primrec₂ fun (_input : Input)
      (_data : RouteBend × Nat) =>
      (none : Option RetainedDirectSourceRouteChoice) :=
    Primrec.const none
  have direct : Primrec₂ fun (input : Input)
      (rest : RetainedDirectSourceRestThree Variable) =>
      retainedDirectSourceRestThreeRouteChoice?
        ((input.1.1, rest), input.2) := by
    change Primrec fun combined : Input ×
        RetainedDirectSourceRestThree Variable =>
      retainedDirectSourceRestThreeRouteChoice?
        ((combined.1.1.1, combined.2), combined.1.2)
    exact retainedDirectSourceRestThreeRouteChoice?_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
  exact (Primrec.sumCasesOn source bend direct).of_eq fun input => by
    unfold retainedDirectSourceRestTwoRouteChoice?
    cases input.1.2 <;> rfl

private def retainedDirectSourceRestOneRouteChoice?
    {Variable : Type*} [DecidableEq Variable]
    (input : (PeriodicCNF Variable ×
      RetainedDirectSourceRestOne Variable) × Nat) :
    Option RetainedDirectSourceRouteChoice :=
  match input.1.2 with
  | .inl _ => none
  | .inr rest =>
      retainedDirectSourceRestTwoRouteChoice?
        ((input.1.1, rest), input.2)

private theorem retainedDirectSourceRestOneRouteChoice?_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedDirectSourceRestOneRouteChoice?
      (Variable := Variable)) := by
  let Input := (PeriodicCNF Variable ×
    RetainedDirectSourceRestOne Variable) × Nat
  have source : Primrec fun input : Input => input.1.2 :=
    Primrec.snd.comp Primrec.fst
  have carrier : Primrec₂ fun (_input : Input)
      (_data : PlanarThreeSAT.EqualityLink CarrierNode × Nat) =>
      (none : Option RetainedDirectSourceRouteChoice) :=
    Primrec.const none
  have afterCarrier : Primrec₂ fun (input : Input)
      (rest : RetainedDirectSourceRestTwo Variable) =>
      retainedDirectSourceRestTwoRouteChoice?
        ((input.1.1, rest), input.2) := by
    change Primrec fun combined : Input ×
        RetainedDirectSourceRestTwo Variable =>
      retainedDirectSourceRestTwoRouteChoice?
        ((combined.1.1.1, combined.2), combined.1.2)
    exact retainedDirectSourceRestTwoRouteChoice?_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
  exact (Primrec.sumCasesOn source carrier afterCarrier).of_eq fun input => by
    unfold retainedDirectSourceRestOneRouteChoice?
    cases input.1.2 <;> rfl

private theorem retainedDirectSourceRouteChoiceComputedFromData?_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedDirectSourceRouteChoiceComputedFromData?
      (Variable := Variable)) := by
  let Input := (PeriodicCNF Variable ×
    RetainedDirectSourceData Variable) × Nat
  have source : Primrec fun input : Input => input.1.2 :=
    Primrec.snd.comp Primrec.fst
  have crossover : Primrec₂ fun (input : Input)
      (data : CrossingRecord × Nat) =>
      retainedDirectCrossoverRouteChoice? (data, input.2) := by
    change Primrec fun combined : Input × (CrossingRecord × Nat) =>
      retainedDirectCrossoverRouteChoice? (combined.2, combined.1.2)
    exact retainedDirectCrossoverRouteChoice?_primrec.comp
      (Primrec.pair Primrec.snd
        (Primrec.snd.comp Primrec.fst))
  have restOne : Primrec₂ fun (input : Input)
      (rest : RetainedDirectSourceRestOne Variable) =>
      retainedDirectSourceRestOneRouteChoice?
        ((input.1.1, rest), input.2) := by
    change Primrec fun combined : Input ×
        RetainedDirectSourceRestOne Variable =>
      retainedDirectSourceRestOneRouteChoice?
        ((combined.1.1.1, combined.2), combined.1.2)
    exact retainedDirectSourceRestOneRouteChoice?_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
  exact (Primrec.sumCasesOn source crossover restOne).of_eq
    fun input => by
      unfold retainedDirectSourceRouteChoiceComputedFromData?
      unfold retainedDirectSourceRestOneRouteChoice?
      unfold retainedDirectSourceRestTwoRouteChoice?
      unfold retainedDirectSourceRestThreeRouteChoice?
      cases input.1.2 with
      | inl _ => rfl
      | inr rest =>
          cases rest with
          | inl _ => rfl
          | inr rest =>
              cases rest with
              | inl _ => rfl
              | inr rest => cases rest <;> rfl

/-- The raw checked direct-source selector is primitive recursive. -/
theorem retainedDirectSourceRouteChoice?_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input :
        (PeriodicCNF Variable × DrawingPlanarSATClauseSource Variable) × Nat =>
      retainedDirectSourceRouteChoice?
        input.1.1 input.1.2 input.2 := by
  have prepared : Primrec fun input :
      (PeriodicCNF Variable × DrawingPlanarSATClauseSource Variable) × Nat =>
      ((input.1.1,
        DrawingPlanarSATClauseSource.equivData input.1.2), input.2) :=
    Primrec.pair
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst)
        (DrawingPlanarSATClauseSource.equivData_primrec.comp
          (Primrec.snd.comp Primrec.fst)))
      Primrec.snd
  refine (retainedDirectSourceRouteChoiceComputedFromData?_primrec.comp
    prepared).of_eq ?_
  rintro ⟨⟨formula, source⟩, literalIndex⟩
  rw [← retainedDirectSourceRouteChoiceComputed?_eq]
  cases source <;> rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes
