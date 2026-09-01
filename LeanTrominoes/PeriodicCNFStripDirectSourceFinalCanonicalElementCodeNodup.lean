/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalElementCodeSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalUniqueFanQueryKeySemantics

/-! # Uniqueness of direct final canonical element codes -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicPlanarOneInThreeToThreeDM PlanarThreeDM

/-- Pair finite identity keys with each item's structural tags. -/
def directSourceFinalZippedTagPairs {Item : Type}
    (items : List Item) (keys : List Nat) (tags : Item → List Nat) :
    List (Nat × Nat) :=
  (List.zipWith (fun item key =>
    (tags item).map fun tag => (key, tag)) items keys).flatten

private theorem directSourceFinalZippedTagPairs_base_mem
    {Item : Type} (items : List Item) (keys : List Nat)
    (tags : Item → List Nat) (pair : Nat × Nat)
    (member : pair ∈ directSourceFinalZippedTagPairs items keys tags) :
    pair.1 ∈ keys := by
  induction items generalizing keys with
  | nil => simp [directSourceFinalZippedTagPairs] at member
  | cons item items induction =>
      cases keys with
      | nil => simp [directSourceFinalZippedTagPairs] at member
      | cons key keys =>
          change pair ∈
            (tags item).map (fun tag => (key, tag)) ++
              directSourceFinalZippedTagPairs items keys tags at member
          rw [List.mem_append] at member
          rcases member with headMember | tailMember
          · rcases List.mem_map.mp headMember with ⟨tag, _, rfl⟩
            simp
          · simp [induction keys tailMember]

private theorem directSourceFinalZippedTagPairs_property
    {Item : Type} (items : List Item) (keys : List Nat)
    (tags : Item → List Nat) (property : Nat → Prop)
    (tagProperty : ∀ item tag, tag ∈ tags item → property tag) :
    ∀ pair ∈ directSourceFinalZippedTagPairs items keys tags,
      property pair.2 := by
  intro pair member
  induction items generalizing keys with
  | nil => simp [directSourceFinalZippedTagPairs] at member
  | cons item items induction =>
      cases keys with
      | nil => simp [directSourceFinalZippedTagPairs] at member
      | cons key keys =>
          change pair ∈
            (tags item).map (fun tag => (key, tag)) ++
              directSourceFinalZippedTagPairs items keys tags at member
          rw [List.mem_append] at member
          rcases member with headMember | tailMember
          · rcases List.mem_map.mp headMember with ⟨tag, tagMember, rfl⟩
            exact tagProperty item tag tagMember
          · exact induction keys tailMember

private theorem directSourceFinalZippedTagPairs_nodup
    {Item : Type} (items : List Item) (keys : List Nat)
    (tags : Item → List Nat)
    (keysNodup : keys.Nodup)
    (tagsNodup : ∀ item, (tags item).Nodup) :
    (directSourceFinalZippedTagPairs items keys tags).Nodup := by
  induction items generalizing keys with
  | nil => simp [directSourceFinalZippedTagPairs]
  | cons item items induction =>
      cases keys with
      | nil => simp [directSourceFinalZippedTagPairs]
      | cons key keys =>
          have keyParts := List.nodup_cons.mp keysNodup
          change ((tags item).map (fun tag => (key, tag)) ++
            directSourceFinalZippedTagPairs items keys tags).Nodup
          rw [List.nodup_append]
          refine ⟨?_, induction keys keyParts.2, ?_⟩
          · exact (tagsNodup item).map fun first second equal => by
              exact congrArg Prod.snd equal
          · intro first firstMember second secondMember equal
            rcases List.mem_map.mp firstMember with
              ⟨tag, _tagMember, rfl⟩
            have secondBaseMember :=
              directSourceFinalZippedTagPairs_base_mem
                items keys tags second secondMember
            have baseEq : key = second.1 := congrArg Prod.fst equal
            exact keyParts.1 (by simpa [baseEq] using secondBaseMember)

/-- Variable-local structural tags contributed by one grouped occurrence. -/
def directSourceFinalVariableElementTagBlock
    (color : WireColor) (pair : GroupedVariableFanSlot) : List Nat :=
  let base := directSourceFinalVariableElementColorTagBase color
  match pair.1.kind (groupedVariableFanSiteSlot pair.2) with
  | .fixedRed => [base, base + 1, base + 2]
  | .fixedGreen | .fixedBlue => [base]

/-- Four clause structural tags for one color. -/
def directSourceFinalClauseElementTagBlock (color : WireColor) : List Nat :=
  let base := directSourceFinalClauseElementColorTagBase color
  [base, base + 1, base + 2, base + 3]

def directSourceFinalVariableElementAllowedTags : WireColor → List Nat
  | .red => [0, 1, 2]
  | .green => [4, 5, 6]
  | .blue => [8, 9, 10]

def directSourceFinalClauseElementAllowedTags : WireColor → List Nat
  | .red => [16, 17, 18, 19]
  | .green => [20, 21, 22, 23]
  | .blue => [24, 25, 26, 27]

def directSourceFinalOneColorElementAllowedTags (color : WireColor) :
    List Nat :=
  directSourceFinalVariableElementAllowedTags color ++
    directSourceFinalClauseElementAllowedTags color

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Identity/tag pairs for all variable-local elements of one color. -/
def directSourceFinalVariableElementCodePairs
    (color : WireColor) (symbols : List encoding.Γ) : List (Nat × Nat) :=
  directSourceFinalZippedTagPairs
    (directSourceFinalGroupedVariableFanSlots decider symbols)
    (directSourceFinalUniqueFanQueryKeys decider symbols)
    (directSourceFinalVariableElementTagBlock color)

/-- Identity/tag pairs for all clause elements of one color. -/
def directSourceFinalClauseElementCodePairs
    (color : WireColor) (symbols : List encoding.Γ) : List (Nat × Nat) :=
  let indices := List.range
    (directSourceFinalClauseIndexPlaceholders decider symbols).length
  directSourceFinalZippedTagPairs indices indices
    (fun _ => directSourceFinalClauseElementTagBlock color)

def directSourceFinalOneColorElementCodePairs
    (color : WireColor) (symbols : List encoding.Γ) : List (Nat × Nat) :=
  directSourceFinalVariableElementCodePairs decider color symbols ++
    directSourceFinalClauseElementCodePairs decider color symbols

def directSourceFinalCanonicalElementCodePairs
    (symbols : List encoding.Γ) : List (Nat × Nat) :=
  directSourceFinalOneColorElementCodePairs decider .red symbols ++
    directSourceFinalOneColorElementCodePairs decider .green symbols ++
    directSourceFinalOneColorElementCodePairs decider .blue symbols

/-- Encode one bounded structural tag below its identity's stride-32 base. -/
def directSourceFinalElementCodeOfPair (pair : Nat × Nat) : Nat :=
  pair.1 * directSourceFinalElementCodeStride + pair.2

private theorem variableElementCodePairs_map
    (color : WireColor) (pairs : List GroupedVariableFanSlot)
    (keys : List Nat) :
    (directSourceFinalZippedTagPairs pairs keys
      (directSourceFinalVariableElementTagBlock color)).map
        directSourceFinalElementCodeOfPair =
      (List.zipWith (directSourceFinalVariableElementCodeBlock color)
        pairs keys).flatten := by
  induction pairs generalizing keys with
  | nil => simp [directSourceFinalZippedTagPairs]
  | cons pair pairs induction =>
      cases keys with
      | nil => simp [directSourceFinalZippedTagPairs]
      | cons key keys =>
          rw [show directSourceFinalZippedTagPairs (pair :: pairs)
              (key :: keys) (directSourceFinalVariableElementTagBlock color) =
            (directSourceFinalVariableElementTagBlock color pair).map
                (fun tag => (key, tag)) ++
              directSourceFinalZippedTagPairs pairs keys
                (directSourceFinalVariableElementTagBlock color) by rfl,
            List.map_append, induction keys]
          cases color <;>
            cases kindEq : pair.1.kind
              (groupedVariableFanSiteSlot pair.2) <;>
            simp [directSourceFinalVariableElementTagBlock,
              directSourceFinalVariableElementCodeBlock,
              directSourceFinalVariableElementCodeCandidateBlock,
              directSourceFinalElementCodeOfPair,
              directSourceFinalElementCodeStride,
              directSourceFinalVariableElementColorTagBase, kindEq]

private theorem clauseElementCodePairs_map
    (color : WireColor) (indices : List Nat) :
    (directSourceFinalZippedTagPairs indices indices
      (fun _ => directSourceFinalClauseElementTagBlock color)).map
        directSourceFinalElementCodeOfPair =
      indices.flatMap (directSourceFinalClauseElementCodeBlock color) := by
  induction indices with
  | nil => simp [directSourceFinalZippedTagPairs]
  | cons index indices induction =>
      rw [show directSourceFinalZippedTagPairs (index :: indices)
              (index :: indices)
              (fun _ => directSourceFinalClauseElementTagBlock color) =
            (directSourceFinalClauseElementTagBlock color).map
                (fun tag => (index, tag)) ++
              directSourceFinalZippedTagPairs indices indices
                (fun _ => directSourceFinalClauseElementTagBlock color) by rfl,
          List.map_append, induction]
      cases color <;>
        simp [directSourceFinalClauseElementTagBlock,
          directSourceFinalClauseElementCodeBlock,
          directSourceFinalElementCodeOfPair,
          directSourceFinalElementCodeStride,
          directSourceFinalClauseElementColorTagBase]

theorem directSourceFinalCanonicalElementCodePairs_map
    (symbols : List encoding.Γ) :
    (directSourceFinalCanonicalElementCodePairs decider symbols).map
        directSourceFinalElementCodeOfPair =
      directSourceFinalCanonicalElementCodes decider symbols := by
  unfold directSourceFinalCanonicalElementCodePairs
    directSourceFinalOneColorElementCodePairs
    directSourceFinalVariableElementCodePairs
    directSourceFinalClauseElementCodePairs
    directSourceFinalCanonicalElementCodes
    directSourceFinalGreenBlueElementCodes
    directSourceFinalOneColorElementCodes
  simp only [List.map_append]
  rw [variableElementCodePairs_map,
    variableElementCodePairs_map,
    variableElementCodePairs_map,
    directSourceFinalCanonicalVariableElementCodes_eq_zipWith,
    directSourceFinalCanonicalVariableElementCodes_eq_zipWith,
    directSourceFinalCanonicalVariableElementCodes_eq_zipWith]
  rw [clauseElementCodePairs_map,
    clauseElementCodePairs_map,
    clauseElementCodePairs_map]
  rw [directSourceFinalClauseElementCodes_eq_flatMap,
    directSourceFinalClauseElementCodes_eq_flatMap,
    directSourceFinalClauseElementCodes_eq_flatMap]
  simp [List.append_assoc]

private theorem variableElementCodePairs_allowed
    (color : WireColor) (symbols : List encoding.Γ) :
    ∀ pair ∈ directSourceFinalVariableElementCodePairs
        decider color symbols,
      pair.2 ∈ directSourceFinalVariableElementAllowedTags color := by
  apply directSourceFinalZippedTagPairs_property
  intro item tag tagMember
  cases color <;>
    cases kindEq : item.1.kind (groupedVariableFanSiteSlot item.2) <;>
    simp_all [directSourceFinalVariableElementTagBlock,
      directSourceFinalVariableElementAllowedTags,
      directSourceFinalVariableElementColorTagBase]

private theorem clauseElementCodePairs_allowed
    (color : WireColor) (symbols : List encoding.Γ) :
    ∀ pair ∈ directSourceFinalClauseElementCodePairs
        decider color symbols,
      pair.2 ∈ directSourceFinalClauseElementAllowedTags color := by
  apply directSourceFinalZippedTagPairs_property
  intro item tag tagMember
  cases color <;>
    simpa [directSourceFinalClauseElementTagBlock,
      directSourceFinalClauseElementAllowedTags,
      directSourceFinalClauseElementColorTagBase] using tagMember

private theorem variableElementCodePairs_nodup
    (color : WireColor) (symbols : List encoding.Γ) :
    (directSourceFinalVariableElementCodePairs
      decider color symbols).Nodup := by
  apply directSourceFinalZippedTagPairs_nodup
  · exact directSourceFinalUniqueFanQueryKeys_nodup decider symbols
  · intro item
    cases color <;>
      cases kindEq : item.1.kind (groupedVariableFanSiteSlot item.2) <;>
      simp [directSourceFinalVariableElementTagBlock, kindEq]

private theorem clauseElementCodePairs_nodup
    (color : WireColor) (symbols : List encoding.Γ) :
    (directSourceFinalClauseElementCodePairs
      decider color symbols).Nodup := by
  unfold directSourceFinalClauseElementCodePairs
  apply directSourceFinalZippedTagPairs_nodup
  · exact List.nodup_range
  · intro item
    cases color <;>
      simp [directSourceFinalClauseElementTagBlock]

private theorem nodup_append_of_allowed_tags
    (first second : List (Nat × Nat))
    (firstTags secondTags : List Nat)
    (firstNodup : first.Nodup) (secondNodup : second.Nodup)
    (firstAllowed : ∀ pair ∈ first, pair.2 ∈ firstTags)
    (secondAllowed : ∀ pair ∈ second, pair.2 ∈ secondTags)
    (disjoint : ∀ tag ∈ firstTags, tag ∉ secondTags) :
    (first ++ second).Nodup := by
  rw [List.nodup_append]
  refine ⟨firstNodup, secondNodup, ?_⟩
  intro firstPair firstMember secondPair secondMember equal
  have tagEq : firstPair.2 = secondPair.2 := congrArg Prod.snd equal
  exact disjoint firstPair.2 (firstAllowed firstPair firstMember)
    (by simpa [← tagEq] using secondAllowed secondPair secondMember)

private theorem oneColorElementCodePairs_allowed
    (color : WireColor) (symbols : List encoding.Γ) :
    ∀ pair ∈ directSourceFinalOneColorElementCodePairs
        decider color symbols,
      pair.2 ∈ directSourceFinalOneColorElementAllowedTags color := by
  intro pair member
  rw [directSourceFinalOneColorElementCodePairs,
    List.mem_append] at member
  rcases member with variableMember | clauseMember
  · exact List.mem_append_left _
      (variableElementCodePairs_allowed
        decider color symbols pair variableMember)
  · exact List.mem_append_right _
      (clauseElementCodePairs_allowed
        decider color symbols pair clauseMember)

private theorem oneColorElementCodePairs_nodup
    (color : WireColor) (symbols : List encoding.Γ) :
    (directSourceFinalOneColorElementCodePairs
      decider color symbols).Nodup := by
  unfold directSourceFinalOneColorElementCodePairs
  apply nodup_append_of_allowed_tags
    (firstTags := directSourceFinalVariableElementAllowedTags color)
    (secondTags := directSourceFinalClauseElementAllowedTags color)
  · exact variableElementCodePairs_nodup decider color symbols
  · exact clauseElementCodePairs_nodup decider color symbols
  · exact variableElementCodePairs_allowed decider color symbols
  · exact clauseElementCodePairs_allowed decider color symbols
  · cases color <;>
      decide

theorem directSourceFinalCanonicalElementCodePairs_nodup
    (symbols : List encoding.Γ) :
    (directSourceFinalCanonicalElementCodePairs
      decider symbols).Nodup := by
  unfold directSourceFinalCanonicalElementCodePairs
  have redGreen :
      (directSourceFinalOneColorElementCodePairs decider .red symbols ++
        directSourceFinalOneColorElementCodePairs
          decider .green symbols).Nodup := by
    apply nodup_append_of_allowed_tags
      (firstTags := directSourceFinalOneColorElementAllowedTags .red)
      (secondTags := directSourceFinalOneColorElementAllowedTags .green)
    · exact oneColorElementCodePairs_nodup decider .red symbols
    · exact oneColorElementCodePairs_nodup decider .green symbols
    · exact oneColorElementCodePairs_allowed decider .red symbols
    · exact oneColorElementCodePairs_allowed decider .green symbols
    · decide
  apply nodup_append_of_allowed_tags
    (firstTags := directSourceFinalOneColorElementAllowedTags .red ++
      directSourceFinalOneColorElementAllowedTags .green)
    (secondTags := directSourceFinalOneColorElementAllowedTags .blue)
  · exact redGreen
  · exact oneColorElementCodePairs_nodup decider .blue symbols
  · intro pair member
    rw [List.mem_append] at member ⊢
    rcases member with redMember | greenMember
    · exact Or.inl
        (oneColorElementCodePairs_allowed
          decider .red symbols pair redMember)
    · exact Or.inr
        (oneColorElementCodePairs_allowed
          decider .green symbols pair greenMember)
  · exact oneColorElementCodePairs_allowed decider .blue symbols
  · decide

private theorem directSourceFinalElementCodeOfPair_injective_of_tags_lt
    (first second : Nat × Nat)
    (firstTagLt : first.2 < directSourceFinalElementCodeStride)
    (secondTagLt : second.2 < directSourceFinalElementCodeStride)
    (equal : directSourceFinalElementCodeOfPair first =
      directSourceFinalElementCodeOfPair second) :
    first = second := by
  have tagEq : first.2 = second.2 := by
    have residues := congrArg
      (fun value : Nat => value % directSourceFinalElementCodeStride) equal
    simpa [directSourceFinalElementCodeOfPair, Nat.add_mod,
      Nat.mod_eq_of_lt firstTagLt,
      Nat.mod_eq_of_lt secondTagLt] using residues
  apply Prod.ext
  · unfold directSourceFinalElementCodeOfPair
      directSourceFinalElementCodeStride at equal
    omega
  · exact tagEq

/-- All canonical direct-source structural element codes are globally
duplicate-free. -/
@[simp] theorem directSourceFinalCanonicalElementCodes_nodup
    (symbols : List encoding.Γ) :
    (directSourceFinalCanonicalElementCodes decider symbols).Nodup := by
  rw [← directSourceFinalCanonicalElementCodePairs_map]
  apply (directSourceFinalCanonicalElementCodePairs_nodup
    decider symbols).map_on
  intro first firstMember second secondMember equal
  apply directSourceFinalElementCodeOfPair_injective_of_tags_lt
    first second
  · unfold directSourceFinalCanonicalElementCodePairs at firstMember
    simp only [List.mem_append] at firstMember
    rcases firstMember with (redMember | greenMember) | blueMember
    · have member := oneColorElementCodePairs_allowed
        decider .red symbols first redMember
      simp [directSourceFinalOneColorElementAllowedTags,
        directSourceFinalVariableElementAllowedTags,
        directSourceFinalClauseElementAllowedTags,
        directSourceFinalElementCodeStride] at member ⊢
      omega
    · have member := oneColorElementCodePairs_allowed
        decider .green symbols first greenMember
      simp [directSourceFinalOneColorElementAllowedTags,
        directSourceFinalVariableElementAllowedTags,
        directSourceFinalClauseElementAllowedTags,
        directSourceFinalElementCodeStride] at member ⊢
      omega
    · have member := oneColorElementCodePairs_allowed
        decider .blue symbols first blueMember
      simp [directSourceFinalOneColorElementAllowedTags,
        directSourceFinalVariableElementAllowedTags,
        directSourceFinalClauseElementAllowedTags,
        directSourceFinalElementCodeStride] at member ⊢
      omega
  · unfold directSourceFinalCanonicalElementCodePairs at secondMember
    simp only [List.mem_append] at secondMember
    rcases secondMember with (redMember | greenMember) | blueMember
    · have member := oneColorElementCodePairs_allowed
        decider .red symbols second redMember
      simp [directSourceFinalOneColorElementAllowedTags,
        directSourceFinalVariableElementAllowedTags,
        directSourceFinalClauseElementAllowedTags,
        directSourceFinalElementCodeStride] at member ⊢
      omega
    · have member := oneColorElementCodePairs_allowed
        decider .green symbols second greenMember
      simp [directSourceFinalOneColorElementAllowedTags,
        directSourceFinalVariableElementAllowedTags,
        directSourceFinalClauseElementAllowedTags,
        directSourceFinalElementCodeStride] at member ⊢
      omega
    · have member := oneColorElementCodePairs_allowed
        decider .blue symbols second blueMember
      simp [directSourceFinalOneColorElementAllowedTags,
        directSourceFinalVariableElementAllowedTags,
        directSourceFinalClauseElementAllowedTags,
        directSourceFinalElementCodeStride] at member ⊢
      omega
  · exact equal

end LeanTrominoes.PeriodicCNFStripReduction

end
