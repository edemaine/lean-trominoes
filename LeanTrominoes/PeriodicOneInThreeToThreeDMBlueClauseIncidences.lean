import LeanTrominoes.PeriodicOneInThreeToThreeDMClauseIncidences

/-!
# Main clause-blue incidences

The main blue element of a clause is shared by the literal-side port of every
variable occurrence in that clause.  This file classifies those incidences
directly from the three occurrence slots of each six-cycle variable gadget.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

namespace OccurrenceSlot

/-- The two complementary variable triples exposed by one occurrence slot. -/
def triples (slot : OccurrenceSlot) :
    List PlanarThreeDM.VariableTriple :=
  [slot.trueTriple, slot.falseTriple]

end OccurrenceSlot

/-- The global six-triple order is the concatenation of the three
occurrence-pair orders. -/
theorem allVariableTriples_eq_slotTriples :
    allVariableTriples =
      OccurrenceSlot.all.flatMap OccurrenceSlot.triples := by
  rfl

/-- The possible main-clause incidence contributed by one variable slot. -/
def mainClauseIncidenceAt {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) (clauseIndex : Nat) :
    List (Incidence Variable) :=
  match occurrenceAt source atom slot with
  | none => []
  | some tagged =>
      if tagged.2.1 = clauseIndex then
        [⟨.variable atom (slot.literalTriple tagged.1.value),
          reverseOffset tagged.1.offset⟩]
      else
        []

/-- Main-clause incidences from all three slots of one variable gadget. -/
def mainClauseIncidencesForAtom {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (clauseIndex : Nat) :
    List (Incidence Variable) :=
  OccurrenceSlot.all.flatMap fun slot =>
    mainClauseIncidenceAt source atom slot clauseIndex

/-- Complete main-clause incidence list in the construction's stable
variable/slot order. -/
def mainClauseIncidences {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (clauseIndex : Nat) :
    List (Incidence Variable) :=
  (occurringVariables source).flatMap fun atom =>
    mainClauseIncidencesForAtom source atom clauseIndex

/-- Filtering one complementary port pair at a main clause-blue element gives
the literal-side port exactly when that slot contains an occurrence of the
selected clause. -/
theorem variablePair_filterMap_clause {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot) (clauseIndex : Nat) :
    ((OccurrenceSlot.triples slot).map
        (Triple.variable atom)).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom = BlueElement.clause clauseIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) =
      mainClauseIncidenceAt source atom slot clauseIndex := by
  cases lookup : occurrenceAt source atom slot with
  | none =>
      cases slot <;>
        simp [OccurrenceSlot.triples, mainClauseIncidenceAt,
          tripleReferences, variableTripleReferences,
          variableBlueElement, variableBlueOffset, lookup]
  | some tagged =>
      rcases tagged with ⟨literal, taggedClauseIndex,
        taggedLiteralIndex⟩
      rcases literal with ⟨literalAtom, offset, value⟩
      cases value <;>
        cases slot <;>
        by_cases same : taggedClauseIndex = clauseIndex <;>
        simp [OccurrenceSlot.triples, mainClauseIncidenceAt,
          OccurrenceSlot.literalTriple, tripleReferences,
          variableTripleReferences, variableBlueElement,
          variableBlueOffset, lookup, same]

/-- Filtering the six triples of one variable gadget at a main clause-blue
element gives the three-slot presentation above. -/
theorem variableBlock_filterMap_clause {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (clauseIndex : Nat) :
    (allVariableTriples.map (Triple.variable atom)).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom = BlueElement.clause clauseIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) =
      mainClauseIncidencesForAtom source atom clauseIndex := by
  rw [allVariableTriples_eq_slotTriples, List.map_flatMap,
    filterMap_flatMap]
  simp_rw [variablePair_filterMap_clause]
  rfl

/-- Clause-auxiliary triples never meet a main clause-blue element. -/
theorem blueClauseAuxiliaries_filterMap_clause_nil {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex : Nat) :
    (clauseAuxiliaryTriples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom = BlueElement.clause clauseIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) = [] := by
  simp [clauseAuxiliaryTriples, tripleReferences,
    clauseAuxiliaryReferences]

/-- The actual typed main clause-blue element exposes precisely the
literal-side variable ports assigned to that clause. -/
theorem problem_blueIncidences_clause {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex : Nat) :
    (problem source).blueIncidences (.clause clauseIndex) =
      mainClauseIncidences source clauseIndex := by
  rw [TypedPeriodicThreeDM.blueIncidences]
  change
    (triples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom = BlueElement.clause clauseIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) = _
  rw [triples, List.filterMap_append,
    blueClauseAuxiliaries_filterMap_clause_nil, List.append_nil,
    variableTriples, filterMap_flatMap]
  simp_rw [variableBlock_filterMap_clause]
  rfl

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
