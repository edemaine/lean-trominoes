import LeanTrominoes.PeriodicCNFPlanarRetainedClauseMetadataComputability
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

theorem retainedDirectSourcePrefixChoices_length_le_three :
    ∀ kind : RetainedDirectClauseKind,
      (retainedDirectSourcePrefixChoices kind).length ≤ 3 := by
  native_decide

noncomputable instance : Finite RetainedDirectSourceAtlasIndexData := by
  apply Finite.of_injective (fun data =>
    ((data.1.1,
      ⟨data.1.2,
        lt_of_lt_of_le data.2
          (retainedDirectSourcePrefixChoices_length_le_three data.1.1)⟩) :
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

end PeriodicEightOccurrenceSplit
end LeanTrominoes
