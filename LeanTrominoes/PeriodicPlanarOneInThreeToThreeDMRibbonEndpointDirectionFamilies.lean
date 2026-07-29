import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonEndpointDirectionSeparation

/-!
# Finite families of ribbon endpoint directions

The endpoint fans at one source vertex must be chosen together: separate
one-bend choices for individual strands need not form a planar fan.  This
file packages the finite occurrence families seen at a source variable and
in one finite clause orbit.  Their endpoint directions are genuine and
duplicate-free, exactly the combinatorial input needed by a coordinated
local fan template.  The clause-orbit fan is translated to the distinct
physical clause copies selected by literal offsets.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-! ## Variable endpoint families -/

/-- All active occurrence entries of one occurring source variable, in the
stable occurrence-slot order. -/
def activeVariableOccurrenceEntries
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable)
    (atomMember : atom ∈ occurringVariables source) :
    List (ActiveOccurrenceEntry source) :=
  (usedSlots source atom).attach.map fun slot =>
    ⟨(atom, slot.1),
      (mem_occurrenceEntries_iff source atom slot.1).mpr
        ⟨atomMember, slot.2⟩⟩

/-- Membership in the variable-local family is exactly equality of the
variable component. -/
theorem mem_activeVariableOccurrenceEntries_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable)
    (atomMember : atom ∈ occurringVariables source)
    (entry : ActiveOccurrenceEntry source) :
    entry ∈ activeVariableOccurrenceEntries source atom atomMember ↔
      entry.1.1 = atom := by
  constructor
  · intro member
    rcases List.mem_map.mp member with
      ⟨slot, _slotMember, equal⟩
    have valueEqual := congrArg Subtype.val equal
    exact (Prod.mk.inj valueEqual).1.symm
  · intro atomEqual
    let slot : {slot // slot ∈ usedSlots source atom} :=
      ⟨entry.1.2, by simpa [atomEqual] using entry.slot_mem⟩
    apply List.mem_map.mpr
    refine ⟨slot, List.mem_attach _ _, ?_⟩
    apply Subtype.ext
    exact Prod.ext atomEqual.symm rfl

/-- Every active occurrence appears in the family of its own variable. -/
theorem ActiveOccurrenceEntry.mem_activeVariableOccurrenceEntries
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (entry : ActiveOccurrenceEntry source) :
    entry ∈
      activeVariableOccurrenceEntries
        source entry.1.1 entry.atom_mem :=
  (mem_activeVariableOccurrenceEntries_iff
    source entry.1.1 entry.atom_mem entry).mpr rfl

/-- A variable-local occurrence family contains no duplicate entries. -/
theorem activeVariableOccurrenceEntries_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable)
    (atomMember : atom ∈ occurringVariables source) :
    (activeVariableOccurrenceEntries
      source atom atomMember).Nodup := by
  apply
    ((usedSlots_nodup source atom).attach.map
      (fun first second equal => ?_))
  apply Subtype.ext
  exact (Prod.mk.inj (congrArg Subtype.val equal)).2

/-- There are at most three active occurrence entries at one variable. -/
theorem activeVariableOccurrenceEntries_length_le_three
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable)
    (atomMember : atom ∈ occurringVariables source) :
    (activeVariableOccurrenceEntries
      source atom atomMember).length ≤ 3 := by
  simp only [activeVariableOccurrenceEntries, List.length_map,
    List.length_attach, usedSlots]
  exact List.length_filter_le _ allOccurrenceSlots

/-- Cardinal directions of all occurrence routes leaving one source
variable, in occurrence-slot order. -/
noncomputable def variableRibbonEndpointDirections
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (atom : Variable)
    (atomMember : atom ∈ occurringVariables source.erase) :
    List AxisDirection :=
  (activeVariableOccurrenceEntries
      source.erase atom atomMember).map fun entry =>
    occurrenceSourceVariableDirection
      presentation.toPlanarIncidencePresentation entry

/-- Every direction in a variable endpoint family is a genuine cardinal
direction. -/
theorem variableRibbonEndpointDirections_genuine
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (atom : Variable)
    (atomMember : atom ∈ occurringVariables source.erase) :
    ∀ direction ∈
        variableRibbonEndpointDirections
          presentation atom atomMember,
      direction.IsGenuine := by
  intro direction member
  rcases List.mem_map.mp member with
    ⟨entry, _entryMember, rfl⟩
  exact occurrenceSourceVariableDirection_isGenuine
    presentation.toPlanarIncidencePresentation entry

/-- Distinct occurrence entries at one variable advertise distinct outgoing
directions, so the finite direction family is duplicate-free. -/
theorem variableRibbonEndpointDirections_nodup
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (atom : Variable)
    (atomMember : atom ∈ occurringVariables source.erase) :
    (variableRibbonEndpointDirections
      presentation atom atomMember).Nodup := by
  unfold variableRibbonEndpointDirections
  apply
    (activeVariableOccurrenceEntries_nodup
      source.erase atom atomMember).map_on
  intro first firstMember second secondMember directionsEqual
  by_contra different
  have firstAtom :=
    (mem_activeVariableOccurrenceEntries_iff
      source.erase atom atomMember first).mp firstMember
  have secondAtom :=
    (mem_activeVariableOccurrenceEntries_iff
      source.erase atom atomMember second).mp secondMember
  have directionsDifferent :=
    occurrenceSourceVariableDirections_ne_of_same_variable
      presentation different (firstAtom.trans secondAtom.symm)
  exact directionsDifferent directionsEqual

/-! ## Clause endpoint families -/

/-- Lifted source-grid target at which one active occurrence route reaches
its clause. -/
noncomputable def occurrenceSourceClauseTarget
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) : Cell :=
  let data := occurrenceSpliceData presentation entry
  PositionedPeriodicCNF.variableToClauseTarget
    placement data.positionedClause data.tagged.1

/-- The finite clause-orbit index attached to an active occurrence agrees
with the metadata-rich incidence selected by its splice data. -/
theorem occurrenceClauseIndex_eq_indexedClauseIndex
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    let data := occurrenceSpliceData presentation entry
    occurrenceClauseIndex source.erase entry.1.1 entry.1.2 =
      data.indexed.1.clauseIndex := by
  let data := occurrenceSpliceData presentation entry
  calc
    occurrenceClauseIndex source.erase entry.1.1 entry.1.2 =
        data.tagged.2.1 :=
      occurrenceClauseIndex_of_occurrenceAt
        source.erase entry.1.1 entry.1.2
        data.tagged data.occurrenceLookup
    _ = data.indexed.1.clauseIndex := by
      simpa [incidenceTaggedOccurrence] using
        congrArg (fun tagged => tagged.2.1) data.metadataEq.symm

/-- All active occurrences belonging to one finite clause orbit.  Different
literal offsets merely translate the same fan to different physical copies,
so the orbit index—not a base route's absolute endpoint—is the correct
finite grouping key. -/
def activeClauseOccurrenceEntries
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat) :
    List (ActiveOccurrenceEntry source) :=
  (occurrenceEntries source).attach.filter fun entry =>
    occurrenceClauseIndex source entry.1.1 entry.1.2 = clauseIndex

/-- Membership in a clause-orbit family is exactly equality of the stored
clause index. -/
theorem mem_activeClauseOccurrenceEntries_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (entry : ActiveOccurrenceEntry source) :
    entry ∈ activeClauseOccurrenceEntries source clauseIndex ↔
      occurrenceClauseIndex source entry.1.1 entry.1.2 =
        clauseIndex := by
  simp [activeClauseOccurrenceEntries]

/-- Every active occurrence appears in the family of its source clause
orbit. -/
theorem ActiveOccurrenceEntry.mem_activeClauseOccurrenceEntries
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (entry : ActiveOccurrenceEntry source) :
    entry ∈
      activeClauseOccurrenceEntries source
        (occurrenceClauseIndex source entry.1.1 entry.1.2) :=
  (mem_activeClauseOccurrenceEntries_iff source _ entry).mpr rfl

/-- A clause-orbit occurrence family contains no duplicate entries. -/
theorem activeClauseOccurrenceEntries_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat) :
    (activeClauseOccurrenceEntries source clauseIndex).Nodup := by
  exact
    (occurrenceEntries_nodup source).attach.filter _

/-- Cardinal directions of all occurrence routes entering translated copies
of one clause orbit. -/
noncomputable def clauseRibbonEndpointDirections
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (clauseIndex : Nat) :
    List AxisDirection :=
  (activeClauseOccurrenceEntries
      source.erase clauseIndex).map fun entry =>
    occurrenceSourceClauseDirection
      presentation.toPlanarIncidencePresentation entry

/-- Every direction in a clause endpoint family is a genuine cardinal
direction. -/
theorem clauseRibbonEndpointDirections_genuine
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (clauseIndex : Nat) :
    ∀ direction ∈
        clauseRibbonEndpointDirections presentation clauseIndex,
      direction.IsGenuine := by
  intro direction member
  rcases List.mem_map.mp member with
    ⟨entry, _entryMember, rfl⟩
  exact occurrenceSourceClauseDirection_isGenuine
    presentation.toPlanarIncidencePresentation entry

/-- Distinct occurrence entries at one lifted clause target advertise
distinct incoming directions, so this direction family is duplicate-free. -/
theorem clauseRibbonEndpointDirections_nodup
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (clauseIndex : Nat) :
    (clauseRibbonEndpointDirections
      presentation clauseIndex).Nodup := by
  unfold clauseRibbonEndpointDirections
  apply
    (activeClauseOccurrenceEntries_nodup
      source.erase clauseIndex).map_on
  intro first firstMember second secondMember directionsEqual
  by_contra different
  have firstClause :=
    (mem_activeClauseOccurrenceEntries_iff
      source.erase clauseIndex first).mp
        firstMember
  have secondClause :=
    (mem_activeClauseOccurrenceEntries_iff
      source.erase clauseIndex second).mp
        secondMember
  have directionsDifferent :=
    occurrenceSourceClauseDirections_ne_of_same_clause
      presentation different
      (by
        let planar :=
          presentation.toPlanarIncidencePresentation
        let firstData := occurrenceSpliceData planar first
        let secondData := occurrenceSpliceData planar second
        change
          firstData.indexed.1.clauseIndex =
            secondData.indexed.1.clauseIndex
        calc
          firstData.indexed.1.clauseIndex =
              occurrenceClauseIndex source.erase
                first.1.1 first.1.2 :=
            (occurrenceClauseIndex_eq_indexedClauseIndex
              planar first).symm
          _ = occurrenceClauseIndex source.erase
                second.1.1 second.1.2 :=
            firstClause.trans secondClause.symm
          _ = secondData.indexed.1.clauseIndex :=
            occurrenceClauseIndex_eq_indexedClauseIndex
              planar second)
  exact directionsDifferent directionsEqual

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
