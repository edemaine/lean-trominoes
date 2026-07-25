import LeanTrominoes.PeriodicOneInThreeToThreeDMMatchingSoundness

/-!
# Internal variable-gadget incidences

This file connects the symbolic six-cycle gadget to the actual incidence
enumerator of the typed periodic 3DM construction.  Each internal red or
green element sees exactly the two neighboring variable triples prescribed
by Figure 10(a), at zero offset.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- `filterMap` distributes through an outer `flatMap`. -/
theorem filterMap_flatMap {First Second Third : Type*}
    (values : List First) (blocks : First → List Second)
    (filter : Second → Option Third) :
    (values.flatMap blocks).filterMap filter =
      values.flatMap fun value => (blocks value).filterMap filter := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp [List.filterMap_append, induction]

/-- If a target is absent, mapping one fixed block only at that target
produces the empty list. -/
theorem flatMap_if_eq_eq_nil_of_not_mem {Element Output : Type*}
    [DecidableEq Element] (values : List Element) (target : Element)
    (output : List Output) (notMember : target ∉ values) :
    (values.flatMap fun value =>
      if value = target then output else []) = [] := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.mem_cons, not_or] at notMember
      have headNe : head ≠ target :=
        fun equal => notMember.1 equal.symm
      simp [headNe, induction notMember.2]

/-- A duplicate-free list containing a target contributes exactly the one
block selected at that target. -/
theorem flatMap_if_eq_of_nodup {Element Output : Type*}
    [DecidableEq Element] (values : List Element) (target : Element)
    (output : List Output) (nodup : values.Nodup)
    (member : target ∈ values) :
    (values.flatMap fun value =>
      if value = target then output else []) = output := by
  induction values with
  | nil => simp at member
  | cons head tail induction =>
      rw [List.nodup_cons] at nodup
      simp only [List.mem_cons] at member
      by_cases same : head = target
      · subst head
        simp [flatMap_if_eq_eq_nil_of_not_mem
          tail target output nodup.1]
      · have tailMember : target ∈ tail :=
          member.resolve_left fun equal => same equal.symm
        simp [same, induction nodup.2 tailMember]

/-- One six-triple block contributes precisely the two incidences of a chosen
internal red element when its atom matches, and contributes none otherwise. -/
theorem redVariableBlock_filterMap {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (current target : Variable) (red : PlanarThreeDM.VariableRed) :
    (allVariableTriples.map (Triple.variable current)).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).red
          if reference.atom = RedElement.variable target red then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) =
      if current = target then
        (PlanarThreeDM.VariableRed.neighbors red).map fun triple =>
          ⟨.variable target triple, (0, 0)⟩
      else
        [] := by
  by_cases same : current = target
  · subst current
    cases red <;>
      simp [allVariableTriples, tripleReferences,
        variableTripleReferences,
        PlanarThreeDM.VariableTriple.references,
        PlanarThreeDM.VariableRed.neighbors]
  · cases red <;>
      simp [tripleReferences,
        variableTripleReferences,
        PlanarThreeDM.VariableTriple.references, same]

/-- Clause-auxiliary triples never meet a variable-internal red element. -/
theorem redClauseAuxiliaries_filterMap_nil {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (target : Variable) (red : PlanarThreeDM.VariableRed) :
    (clauseAuxiliaryTriples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).red
          if reference.atom = RedElement.variable target red then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) = [] := by
  simp [clauseAuxiliaryTriples, tripleReferences,
    clauseAuxiliaryReferences]

/-- The constructed typed problem exposes exactly the symbolic red neighbors
of a listed variable gadget. -/
theorem problem_redIncidences_variable {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (red : PlanarThreeDM.VariableRed) :
    (problem source).redIncidences (.variable atom red) =
      (PlanarThreeDM.VariableRed.neighbors red).map fun triple =>
        ⟨.variable atom triple, (0, 0)⟩ := by
  rw [TypedPeriodicThreeDM.redIncidences]
  change
    (triples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).red
          if reference.atom = RedElement.variable atom red then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) = _
  rw [triples, List.filterMap_append,
    redClauseAuxiliaries_filterMap_nil, List.append_nil,
    variableTriples, filterMap_flatMap]
  simp_rw [redVariableBlock_filterMap]
  exact flatMap_if_eq_of_nodup
    (occurringVariables source) atom
    ((PlanarThreeDM.VariableRed.neighbors red).map fun triple =>
      (⟨.variable atom triple, (0, 0)⟩ : Incidence Variable))
    (occurringVariables_nodup source) atomMember

/-- One six-triple block contributes precisely the two incidences of a chosen
internal green element when its atom matches. -/
theorem greenVariableBlock_filterMap {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (current target : Variable)
    (green : PlanarThreeDM.VariableGreen) :
    (allVariableTriples.map (Triple.variable current)).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).green
          if reference.atom = GreenElement.variable target green then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) =
      if current = target then
        (PlanarThreeDM.VariableGreen.neighbors green).map fun triple =>
          ⟨.variable target triple, (0, 0)⟩
      else
        [] := by
  by_cases same : current = target
  · subst current
    cases green <;>
      simp [allVariableTriples, tripleReferences,
        variableTripleReferences,
        PlanarThreeDM.VariableTriple.references,
        PlanarThreeDM.VariableGreen.neighbors]
  · cases green <;>
      simp [tripleReferences,
        variableTripleReferences,
        PlanarThreeDM.VariableTriple.references, same]

/-- Clause-auxiliary triples never meet a variable-internal green element. -/
theorem greenClauseAuxiliaries_filterMap_nil {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (target : Variable) (green : PlanarThreeDM.VariableGreen) :
    (clauseAuxiliaryTriples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).green
          if reference.atom = GreenElement.variable target green then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) = [] := by
  simp [clauseAuxiliaryTriples, tripleReferences,
    clauseAuxiliaryReferences]

/-- The constructed typed problem exposes exactly the symbolic green
neighbors of a listed variable gadget. -/
theorem problem_greenIncidences_variable {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (green : PlanarThreeDM.VariableGreen) :
    (problem source).greenIncidences (.variable atom green) =
      (PlanarThreeDM.VariableGreen.neighbors green).map fun triple =>
        ⟨.variable atom triple, (0, 0)⟩ := by
  rw [TypedPeriodicThreeDM.greenIncidences]
  change
    (triples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).green
          if reference.atom = GreenElement.variable atom green then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) = _
  rw [triples, List.filterMap_append,
    greenClauseAuxiliaries_filterMap_nil, List.append_nil,
    variableTriples, filterMap_flatMap]
  simp_rw [greenVariableBlock_filterMap]
  exact flatMap_if_eq_of_nodup
    (occurringVariables source) atom
    ((PlanarThreeDM.VariableGreen.neighbors green).map fun triple =>
      (⟨.variable atom triple, (0, 0)⟩ : Incidence Variable))
    (occurringVariables_nodup source) atomMember

/-- Typed incident values at an internal red element are exactly the symbolic
variable-gadget neighbor selections. -/
theorem problem_redIncidentValues_variable {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (assignment : (problem source).MatchingAssignment)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (red : PlanarThreeDM.VariableRed) (cell : Cell) :
    (problem source).redIncidentValues assignment
        (.variable atom red) cell =
      (PlanarThreeDM.VariableRed.neighbors red).map fun triple =>
        assignment (.variable atom triple) cell := by
  rw [TypedPeriodicThreeDM.redIncidentValues,
    problem_redIncidences_variable source atom atomMember red]
  simp [TypedPeriodicThreeDM.incidenceValue, Cell.sub]

/-- Typed incident values at an internal green element are exactly the
symbolic variable-gadget neighbor selections. -/
theorem problem_greenIncidentValues_variable {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (assignment : (problem source).MatchingAssignment)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (green : PlanarThreeDM.VariableGreen) (cell : Cell) :
    (problem source).greenIncidentValues assignment
        (.variable atom green) cell =
      (PlanarThreeDM.VariableGreen.neighbors green).map fun triple =>
        assignment (.variable atom triple) cell := by
  rw [TypedPeriodicThreeDM.greenIncidentValues,
    problem_greenIncidences_variable source atom atomMember green]
  simp [TypedPeriodicThreeDM.incidenceValue, Cell.sub]

/-- Covering all internal red and green elements of a listed variable gadget
is exactly the previously verified six-cycle predicate. -/
theorem variableGadgetHolds_of_internal_covers {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (assignment : (problem source).MatchingAssignment)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (cell : Cell)
    (redCovers : ∀ red,
      PeriodicOneInThree.ExactlyOne
        ((problem source).redIncidentValues assignment
          (.variable atom red) cell))
    (greenCovers : ∀ green,
      PeriodicOneInThree.ExactlyOne
        ((problem source).greenIncidentValues assignment
          (.variable atom green) cell)) :
    PlanarThreeDM.VariableGadgetHolds fun triple =>
      assignment (.variable atom triple) cell := by
  constructor
  · intro red
    rw [← problem_redIncidentValues_variable
      source assignment atom atomMember red cell]
    exact redCovers red
  · intro green
    rw [← problem_greenIncidentValues_variable
      source assignment atom atomMember green cell]
    exact greenCovers green

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
