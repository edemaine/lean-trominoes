import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMNodup
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableSiteElements

/-!
# Distinct assembled planar 3DM vertex positions

The assembled drawing emits four typed vertex blocks.  We tag those four
families uniformly, use the injective source incidence drawing to separate
different owner macrocells, and use the exhaustively certified variable-site
and clause-core drawings inside a common owner macrocell.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- A uniformly tagged vertex of the typed planar 3DM presentation. -/
inductive AssembledTypedVertex (Variable : Type*)
  | triple (value : Triple Variable)
  | red (value : RedElement Variable)
  | green (value : GreenElement Variable)
  | blue (value : BlueElement Variable)
  deriving DecidableEq, Repr

/-- Typed vertices in the same four-block order as the encoded incidence
graph. -/
def assembledTypedVertices
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (AssembledTypedVertex Variable) :=
  (triples source).map .triple ++
    (redElements source).map .red ++
    (greenElements source).map .green ++
    (blueElements source).map .blue

/-- The typed vertex presentation itself has no duplicates. -/
theorem assembledTypedVertices_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (assembledTypedVertices source).Nodup := by
  have tripleNodup :
      ((triples source).map AssembledTypedVertex.triple).Nodup :=
    (triples_nodup source).map fun _ _ equal =>
      AssembledTypedVertex.triple.inj equal
  have redNodup :
      ((redElements source).map AssembledTypedVertex.red).Nodup :=
    (redElements_nodup source).map fun _ _ equal =>
      AssembledTypedVertex.red.inj equal
  have greenNodup :
      ((greenElements source).map AssembledTypedVertex.green).Nodup :=
    (greenElements_nodup source).map fun _ _ equal =>
      AssembledTypedVertex.green.inj equal
  have blueNodup :
      ((blueElements source).map AssembledTypedVertex.blue).Nodup :=
    (blueElements_nodup source).map fun _ _ equal =>
      AssembledTypedVertex.blue.inj equal
  rw [assembledTypedVertices, List.nodup_append]
  refine ⟨?_, blueNodup, ?_⟩
  · rw [List.nodup_append]
    refine ⟨?_, greenNodup, ?_⟩
    · rw [List.nodup_append]
      refine ⟨tripleNodup, redNodup, ?_⟩
      intro _ firstMember _ secondMember equal
      rcases List.mem_map.mp firstMember with ⟨_, _, rfl⟩
      rcases List.mem_map.mp secondMember with ⟨_, _, rfl⟩
      cases equal
    · intro first firstMember _ secondMember equal
      rw [List.mem_append] at firstMember
      rcases firstMember with firstMember | firstMember
      · rcases List.mem_map.mp firstMember with ⟨_, _, rfl⟩
        rcases List.mem_map.mp secondMember with ⟨_, _, rfl⟩
        cases equal
      · rcases List.mem_map.mp firstMember with ⟨_, _, rfl⟩
        rcases List.mem_map.mp secondMember with ⟨_, _, rfl⟩
        cases equal
  · intro first firstMember _ secondMember equal
    rw [List.mem_append] at firstMember
    rcases firstMember with firstMember | firstMember
    · rw [List.mem_append] at firstMember
      rcases firstMember with firstMember | firstMember
      · rcases List.mem_map.mp firstMember with ⟨_, _, rfl⟩
        rcases List.mem_map.mp secondMember with ⟨_, _, rfl⟩
        cases equal
      · rcases List.mem_map.mp firstMember with ⟨_, _, rfl⟩
        rcases List.mem_map.mp secondMember with ⟨_, _, rfl⟩
        cases equal
    · rcases List.mem_map.mp firstMember with ⟨_, _, rfl⟩
      rcases List.mem_map.mp secondMember with ⟨_, _, rfl⟩
      cases equal

/-- Owner macrocell of a uniformly tagged assembled vertex. -/
def assembledTypedVertexOwner {Variable : Type*} :
    AssembledTypedVertex Variable → AssemblyMacrocellOwner Variable
  | .triple value => tripleMacrocellOwner value
  | .red value => redElementMacrocellOwner value
  | .green value => greenElementMacrocellOwner value
  | .blue value => blueElementMacrocellOwner value

/-- Local refined-cell offset of a uniformly tagged assembled vertex. -/
def assembledTypedVertexOffset
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    AssembledTypedVertex Variable → Cell
  | .triple value => tripleMacrocellOffset source value
  | .red value => redElementMacrocellOffset source value
  | .green value => greenElementMacrocellOffset source value
  | .blue value => blueElementMacrocellOffset source value

/-- Physical position of a uniformly tagged assembled vertex. -/
def assembledTypedVertexPosition
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) :
    AssembledTypedVertex Variable → Cell
  | .triple value => assembledTriplePosition routing value
  | .red value => assembledRedElementPosition routing value
  | .green value => assembledGreenElementPosition routing value
  | .blue value => assembledBlueElementPosition routing value

/-- The original position list is exactly the image of the uniform typed
vertex presentation. -/
theorem assembledVertexPositions_eq_map_typed
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) :
    assembledVertexPositions routing =
      (assembledTypedVertices source).map
        (assembledTypedVertexPosition routing) := by
  simp [assembledVertexPositions, assembledTypedVertices,
    List.map_append, List.map_map, Function.comp_def,
    assembledTypedVertexPosition]

/-- Membership in the uniform presentation implies declaration of its
source macrocell owner. -/
theorem assembledTypedVertexOwner_declared
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (vertex : AssembledTypedVertex Variable)
    (member : vertex ∈ assembledTypedVertices source) :
    (assembledTypedVertexOwner vertex).IsDeclared source := by
  cases vertex with
  | triple value =>
      apply tripleMacrocellOwner_declared source value
      simpa [assembledTypedVertices] using member
  | red value =>
      apply redElementMacrocellOwner_declared source value
      simpa [assembledTypedVertices] using member
  | green value =>
      apply greenElementMacrocellOwner_declared source value
      simpa [assembledTypedVertices] using member
  | blue value =>
      apply blueElementMacrocellOwner_declared source value
      simpa [assembledTypedVertices] using member

/-- Every uniform typed vertex has an open-macrocell local offset. -/
theorem assembledTypedVertexOffset_inside
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (vertex : AssembledTypedVertex Variable) :
    Cell.PositionInOpenMacrocell
      standardThreeStrandLayout.factor
      (assembledTypedVertexOffset source vertex) := by
  cases vertex with
  | triple value =>
      exact tripleMacrocellOffset_inside source value
  | red value =>
      exact redElementMacrocellOffset_inside source value
  | green value =>
      exact greenElementMacrocellOffset_inside source value
  | blue value =>
      exact blueElementMacrocellOffset_inside source value

/-- Under the standard routing, every uniform typed vertex is its owner's
refined source position plus its local offset. -/
theorem assembledTypedVertexPosition_standard
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (vertex : AssembledTypedVertex Variable) :
    assembledTypedVertexPosition
        (constructedThreeStrandRouting
          presentation standardThreeStrandLayout)
        vertex =
      Cell.macrocellPosition standardThreeStrandLayout.factor
        (assemblyMacrocellOwnerPosition source placement
          (assembledTypedVertexOwner vertex))
        (assembledTypedVertexOffset source.erase vertex) := by
  cases vertex with
  | triple value =>
      exact assembledTriplePosition_standard presentation value
  | red value =>
      exact assembledRedElementPosition_standard presentation value
  | green value =>
      exact assembledGreenElementPosition_standard presentation value
  | blue value =>
      exact assembledBlueElementPosition_standard presentation value

/-- Incidence-graph vertex represented by a macrocell owner. -/
def AssemblyMacrocellOwner.toCNFVertex {Variable : Type*} :
    AssemblyMacrocellOwner Variable → CNFVertex Variable
  | .atom value => .variable value
  | .clause clauseIndex => .clause clauseIndex

/-- A declared macrocell owner represents a listed source incidence-graph
vertex. -/
theorem AssemblyMacrocellOwner.toCNFVertex_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (owner : AssemblyMacrocellOwner Variable)
    (declared : owner.IsDeclared source) :
    owner.toCNFVertex ∈ source.incidenceGraph.vertices := by
  cases owner with
  | atom value =>
      apply List.mem_append_left
      simp only [PeriodicCNF.incidenceVariableVertices, List.mem_map]
      exact ⟨value, declared, rfl⟩
  | clause clauseIndex =>
      apply List.mem_append_right
      simp only [PeriodicCNF.incidenceClauseVertices, List.mem_map]
      exact ⟨clauseIndex, List.mem_range.mpr declared, rfl⟩

/-- In the zero-anchor gauge, the declared owner's physical position is the
certified source drawing position of its represented incidence vertex. -/
theorem assemblyMacrocellOwnerPosition_eq_vertexPosition
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (owner : AssemblyMacrocellOwner Variable)
    (declared : owner.IsDeclared source.erase) :
    assemblyMacrocellOwnerPosition source placement owner =
      (PositionedPeriodicCNF.incidenceDrawing
        source placement presentation.routes).vertexPosition
          source.erase.incidenceGraph owner.toCNFVertex := by
  have member :=
    AssemblyMacrocellOwner.toCNFVertex_mem source.erase owner declared
  rw [PositionedPeriodicCNF.incidenceDrawing_vertexPosition_of_mem
    source placement presentation.routes member]
  cases owner with
  | atom value =>
      rfl
  | clause clauseIndex =>
      have indexLt : clauseIndex < source.clauses.length := by
        change clauseIndex < source.erase.clauses.length at declared
        simpa [PositionedPeriodicCNF.erase] using declared
      change
        positionedClausePositionAt source clauseIndex =
          PositionedPeriodicCNF.incidenceVertexPositionAt
            source placement (.clause clauseIndex)
      rw [PositionedPeriodicCNF.incidenceVertexPositionAt_clause
        source placement clauseIndex indexLt]
      have anchorZero :=
        anchorsZero source.clauses[clauseIndex]
          (List.getElem_mem indexLt)
      simp [positionedClausePositionAt,
        List.getElem?_eq_getElem indexLt,
        PositionedPeriodicCNF.canonicalClausePosition,
        PeriodicVariablePlacement.translation, anchorZero,
        Cell.scale, Cell.sub]

/-- Distinct declared source owners have distinct physical macrocell
positions. -/
theorem assemblyMacrocellOwnerPosition_injective_on
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (first second : AssemblyMacrocellOwner Variable)
    (firstDeclared : first.IsDeclared source.erase)
    (secondDeclared : second.IsDeclared source.erase)
    (equal :
      assemblyMacrocellOwnerPosition source placement first =
        assemblyMacrocellOwnerPosition source placement second) :
    first = second := by
  have firstMember :=
    AssemblyMacrocellOwner.toCNFVertex_mem
      source.erase first firstDeclared
  have secondMember :=
    AssemblyMacrocellOwner.toCNFVertex_mem
      source.erase second secondDeclared
  have vertexEqual :=
    presentation.vertexPosition_injective_on
      firstMember secondMember (by
        rw [← assemblyMacrocellOwnerPosition_eq_vertexPosition
          presentation anchorsZero first firstDeclared]
        rw [← assemblyMacrocellOwnerPosition_eq_vertexPosition
          presentation anchorsZero second secondDeclared]
        exact equal)
  cases first <;> cases second <;>
    simp_all [AssemblyMacrocellOwner.toCNFVertex]

/-- Forget global names while retaining the finite variable-site vertex
represented by a uniformly tagged typed vertex. -/
def variableSiteVertexOfTyped
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    AssembledTypedVertex Variable →
      Sum VariableSiteTriple VariableSiteElement
  | .triple value =>
      .inl (variableSiteTripleOfTyped value)
  | .red value =>
      .inr (variableSiteRedElementOfTyped value)
  | .green value =>
      .inr (variableSiteGreenElementOfTyped source value)
  | .blue value =>
      .inr (variableSiteBlueElementOfTyped source value)

/-- Forgetting global names is injective among vertices owned by one fixed
source variable. -/
theorem variableSiteVertexOfTyped_injective_of_owner
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable)
    (first second : AssembledTypedVertex Variable)
    (firstMember : first ∈ assembledTypedVertices source)
    (secondMember : second ∈ assembledTypedVertices source)
    (firstOwner :
      assembledTypedVertexOwner first =
        AssemblyMacrocellOwner.atom atom)
    (secondOwner :
      assembledTypedVertexOwner second =
        AssemblyMacrocellOwner.atom atom)
    (equal :
      variableSiteVertexOfTyped source first =
        variableSiteVertexOfTyped source second) :
    first = second := by
  cases first with
  | triple first =>
      cases second with
      | triple second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              tripleMacrocellOwner, variableSiteVertexOfTyped,
              variableSiteTripleOfTyped]
      | red second =>
          cases equal
      | green second =>
          cases equal
      | blue second =>
          cases equal
  | red first =>
      cases second with
      | triple second =>
          cases equal
      | red second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              redElementMacrocellOwner, variableSiteVertexOfTyped,
              variableSiteRedElementOfTyped]
      | green second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              redElementMacrocellOwner, greenElementMacrocellOwner,
              variableSiteVertexOfTyped,
              variableSiteRedElementOfTyped,
              variableSiteGreenElementOfTyped, ordinaryVariantAt]
      | blue second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              redElementMacrocellOwner, blueElementMacrocellOwner,
              variableSiteVertexOfTyped,
              variableSiteRedElementOfTyped,
              variableSiteBlueElementOfTyped, ordinaryVariantAt]
  | green first =>
      cases second with
      | triple second =>
          cases equal
      | red second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              greenElementMacrocellOwner, redElementMacrocellOwner,
              variableSiteVertexOfTyped,
              variableSiteGreenElementOfTyped,
              variableSiteRedElementOfTyped, ordinaryVariantAt]
      | green second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              greenElementMacrocellOwner, variableSiteVertexOfTyped,
              variableSiteGreenElementOfTyped, ordinaryVariantAt]
      | blue second =>
          have greenMember : first ∈ greenElements source := by
            simpa [assembledTypedVertices] using firstMember
          have blueMember : second ∈ blueElements source := by
            simpa [assembledTypedVertices] using secondMember
          rcases greenVariableElement_location
              source first greenMember atom firstOwner with
            ⟨_, greenSlot, _, greenBlockMember⟩
          rcases blueVariableElement_location
              source second blueMember atom secondOwner with
            ⟨_, blueSlot, _, blueBlockMember⟩
          exact
            (variableSiteGreenElement_ne_blueElement
              source atom greenSlot first greenBlockMember
              blueSlot second blueBlockMember
              (Sum.inr.inj equal)).elim
  | blue first =>
      cases second with
      | triple second =>
          cases equal
      | red second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              blueElementMacrocellOwner, redElementMacrocellOwner,
              variableSiteVertexOfTyped,
              variableSiteBlueElementOfTyped,
              variableSiteRedElementOfTyped, ordinaryVariantAt]
      | green second =>
          have blueMember : first ∈ blueElements source := by
            simpa [assembledTypedVertices] using firstMember
          have greenMember : second ∈ greenElements source := by
            simpa [assembledTypedVertices] using secondMember
          rcases blueVariableElement_location
              source first blueMember atom firstOwner with
            ⟨_, blueSlot, _, blueBlockMember⟩
          rcases greenVariableElement_location
              source second greenMember atom secondOwner with
            ⟨_, greenSlot, _, greenBlockMember⟩
          exact
            (variableSiteBlueElement_ne_greenElement
              source atom blueSlot first blueBlockMember
              greenSlot second greenBlockMember
              (Sum.inr.inj equal)).elim
      | blue second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              blueElementMacrocellOwner, variableSiteVertexOfTyped,
              variableSiteBlueElementOfTyped, ordinaryVariantAt]

/-- Active finite variable-site vertex corresponding to one listed global
typed vertex owned by `atom`. -/
def activeVariableSiteVertex
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable)
    (vertex : AssembledTypedVertex Variable)
    (member : vertex ∈ assembledTypedVertices source)
    (owner :
      assembledTypedVertexOwner vertex =
        AssemblyMacrocellOwner.atom atom) :
    Sum
      (ActiveVariableSiteTriple
        (sourceVariableSiteCount source atom)
        (sourceVariableSiteKind source atom))
      (ActiveVariableSiteElement
        (sourceVariableSiteCount source atom)
        (sourceVariableSiteKind source atom)) := by
  cases vertex with
  | triple value =>
      have tripleMember : value ∈ triples source := by
        simpa [assembledTypedVertices] using member
      cases value with
      | ordinary valueAtom slot variant localTriple =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          have location :=
            ordinaryTriple_location source valueAtom slot variant
              localTriple tripleMember
          exact .inl
            (activeVariableSiteTriple source valueAtom location.1
              slot location.2.1
              (.ordinary valueAtom slot variant localTriple)
              location.2.2)
      | fixedRed valueAtom slot localTriple =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          have location :=
            fixedRedTriple_location source valueAtom slot
              localTriple tripleMember
          exact .inl
            (activeVariableSiteTriple source valueAtom location.1
              slot location.2.1
              (.fixedRed valueAtom slot localTriple)
              location.2.2)
      | clause clauseIndex set =>
          cases owner
  | red value =>
      have typedMember : value ∈ redElements source := by
        simpa [assembledTypedVertices] using member
      cases value with
      | cycleLink valueAtom slot =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          have location :=
            redCycleLink_location source valueAtom slot typedMember
          exact .inr
            (activeVariableSiteRedElement source valueAtom location.1
              slot location.2.1 (.cycleLink valueAtom slot)
              location.2.2)
      | fixedRedInternal valueAtom slot element =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          have location :=
            redFixedRedInternal_location
              source valueAtom slot element typedMember
          exact .inr
            (activeVariableSiteRedElement source valueAtom location.1
              slot location.2.1
              (.fixedRedInternal valueAtom slot element)
              location.2.2)
      | clauseInternal clauseIndex =>
          cases owner
      | clauseTerminal clauseIndex group =>
          cases owner
  | green value =>
      have typedMember : value ∈ greenElements source := by
        simpa [assembledTypedVertices] using member
      cases value with
      | ordinaryInternal valueAtom slot element =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          have location :=
            greenOrdinaryInternal_location
              source valueAtom slot element typedMember
          exact .inr
            (activeVariableSiteGreenElement source valueAtom location.1
              slot location.2.1
              (.ordinaryInternal valueAtom slot element)
              location.2.2)
      | fixedRedInternal valueAtom slot element =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          have location :=
            greenFixedRedInternal_location
              source valueAtom slot element typedMember
          exact .inr
            (activeVariableSiteGreenElement source valueAtom location.1
              slot location.2.1
              (.fixedRedInternal valueAtom slot element)
              location.2.2)
      | clauseInternal clauseIndex =>
          cases owner
      | clauseTerminal clauseIndex group =>
          cases owner
  | blue value =>
      have typedMember : value ∈ blueElements source := by
        simpa [assembledTypedVertices] using member
      cases value with
      | ordinaryInternal valueAtom slot element =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          have location :=
            blueOrdinaryInternal_location
              source valueAtom slot element typedMember
          exact .inr
            (activeVariableSiteBlueElement source valueAtom location.1
              slot location.2.1
              (.ordinaryInternal valueAtom slot element)
              location.2.2)
      | fixedRedInternal valueAtom slot element =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          have location :=
            blueFixedRedInternal_location
              source valueAtom slot element typedMember
          exact .inr
            (activeVariableSiteBlueElement source valueAtom location.1
              slot location.2.1
              (.fixedRedInternal valueAtom slot element)
              location.2.2)
      | clauseInternal clauseIndex =>
          cases owner
      | clauseTerminal clauseIndex group =>
          cases owner

/-- Forget the activity proof on a finite variable-site vertex. -/
def activeVariableSiteVertexValue
    {count : Nat}
    {kind : VariableSiteSlot → VariableConnectorKind} :
    Sum
      (ActiveVariableSiteTriple count kind)
      (ActiveVariableSiteElement count kind) →
      Sum VariableSiteTriple VariableSiteElement
  | .inl triple => .inl triple.1
  | .inr element => .inr element.1

/-- Packaging a listed variable-owned vertex as active does not change its
underlying finite local name. -/
theorem activeVariableSiteVertex_value
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable)
    (vertex : AssembledTypedVertex Variable)
    (member : vertex ∈ assembledTypedVertices source)
    (owner :
      assembledTypedVertexOwner vertex =
        AssemblyMacrocellOwner.atom atom) :
    activeVariableSiteVertexValue
        (activeVariableSiteVertex source atom vertex member owner) =
      variableSiteVertexOfTyped source vertex := by
  cases vertex with
  | triple value =>
      cases value with
      | ordinary valueAtom slot variant localTriple =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          rfl
      | fixedRed valueAtom slot localTriple =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          rfl
      | clause clauseIndex set =>
          cases owner
  | red value =>
      cases value with
      | cycleLink valueAtom slot =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          rfl
      | fixedRedInternal valueAtom slot element =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          rfl
      | clauseInternal clauseIndex =>
          cases owner
      | clauseTerminal clauseIndex group =>
          cases owner
  | green value =>
      cases value with
      | ordinaryInternal valueAtom slot element =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          rfl
      | fixedRedInternal valueAtom slot element =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          rfl
      | clauseInternal clauseIndex =>
          cases owner
      | clauseTerminal clauseIndex group =>
          cases owner
  | blue value =>
      cases value with
      | ordinaryInternal valueAtom slot element =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          rfl
      | fixedRedInternal valueAtom slot element =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          rfl
      | clauseInternal clauseIndex =>
          cases owner
      | clauseTerminal clauseIndex group =>
          cases owner

/-- Position of a finite active vertex on either side of the variable-site
incidence graph. -/
def activeVariableSiteVertexPosition
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) :
    Sum
      (ActiveVariableSiteTriple
        (sourceVariableSiteCount source atom)
        (sourceVariableSiteKind source atom))
      (ActiveVariableSiteElement
        (sourceVariableSiteCount source atom)
        (sourceVariableSiteKind source atom)) →
      Cell
  | .inl triple =>
      (sourceVariableSiteDrawing source atom).triplePosition triple
  | .inr element =>
      (sourceVariableSiteDrawing source atom).elementPosition element

/-- The exhaustive variable-site planarity certificate makes the combined
triple/element position function injective. -/
theorem activeVariableSiteVertexPosition_injective
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source) :
    Function.Injective
      (activeVariableSiteVertexPosition source atom) := by
  have distinct :=
    (sourceVariableSiteDrawing_isValid
      source atom atomMember).2.2.2.2.2
  intro first second equal
  cases first with
  | inl first =>
      cases second with
      | inl second =>
          exact congrArg Sum.inl (distinct.1 equal)
      | inr second =>
          exact (distinct.2.2 first second equal).elim
  | inr first =>
      cases second with
      | inl second =>
          exact (distinct.2.2 second first equal.symm).elim
      | inr second =>
          exact congrArg Sum.inr (distinct.2.1 equal)

/-- A listed vertex in a variable-owned macrocell has exactly the translated
position of its packaged active finite variable-site vertex. -/
theorem assembledTypedVertexOffset_eq_activeVariableSite
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable)
    (vertex : AssembledTypedVertex Variable)
    (member : vertex ∈ assembledTypedVertices source)
    (owner :
      assembledTypedVertexOwner vertex =
        AssemblyMacrocellOwner.atom atom) :
    assembledTypedVertexOffset source vertex =
      Cell.add standardThreeStrandLayout.variableOffset
        (activeVariableSiteVertexPosition source atom
          (activeVariableSiteVertex source atom vertex member owner)) := by
  cases vertex with
  | triple value =>
      have typedMember : value ∈ triples source := by
        simpa [assembledTypedVertices] using member
      cases value with
      | ordinary valueAtom slot variant localTriple =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          have location :=
            ordinaryTriple_location source valueAtom slot variant
              localTriple typedMember
          have positionEq :=
            activeOrdinaryTriple_position source valueAtom location.1
              slot location.2.1 variant localTriple location.2.2
          simpa [assembledTypedVertexOffset,
            tripleMacrocellOffset,
            activeVariableSiteVertexPosition,
            activeVariableSiteVertex] using
            congrArg
              (Cell.add standardThreeStrandLayout.variableOffset)
              positionEq.symm
      | fixedRed valueAtom slot localTriple =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          have location :=
            fixedRedTriple_location source valueAtom slot
              localTriple typedMember
          have positionEq :=
            activeFixedRedTriple_position source valueAtom location.1
              slot location.2.1 localTriple location.2.2
          simpa [assembledTypedVertexOffset,
            tripleMacrocellOffset,
            activeVariableSiteVertexPosition,
            activeVariableSiteVertex] using
            congrArg
              (Cell.add standardThreeStrandLayout.variableOffset)
              positionEq.symm
      | clause clauseIndex set =>
          cases owner
  | red value =>
      have typedMember : value ∈ redElements source := by
        simpa [assembledTypedVertices] using member
      cases value with
      | cycleLink valueAtom slot =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          have location :=
            redCycleLink_location source valueAtom slot typedMember
          simpa [assembledTypedVertexOffset,
            activeVariableSiteVertexPosition,
            activeVariableSiteVertex] using
            redElementMacrocellOffset_eq_variableSite
              source valueAtom location.1 slot location.2.1
              (.cycleLink valueAtom slot) location.2.2
      | fixedRedInternal valueAtom slot element =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          have location :=
            redFixedRedInternal_location
              source valueAtom slot element typedMember
          simpa [assembledTypedVertexOffset,
            activeVariableSiteVertexPosition,
            activeVariableSiteVertex] using
            redElementMacrocellOffset_eq_variableSite
              source valueAtom location.1 slot location.2.1
              (.fixedRedInternal valueAtom slot element)
              location.2.2
      | clauseInternal clauseIndex =>
          cases owner
      | clauseTerminal clauseIndex group =>
          cases owner
  | green value =>
      have typedMember : value ∈ greenElements source := by
        simpa [assembledTypedVertices] using member
      cases value with
      | ordinaryInternal valueAtom slot element =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          have location :=
            greenOrdinaryInternal_location
              source valueAtom slot element typedMember
          simpa [assembledTypedVertexOffset,
            activeVariableSiteVertexPosition,
            activeVariableSiteVertex] using
            greenElementMacrocellOffset_eq_variableSite
              source valueAtom location.1 slot location.2.1
              (.ordinaryInternal valueAtom slot element)
              location.2.2
      | fixedRedInternal valueAtom slot element =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          have location :=
            greenFixedRedInternal_location
              source valueAtom slot element typedMember
          simpa [assembledTypedVertexOffset,
            activeVariableSiteVertexPosition,
            activeVariableSiteVertex] using
            greenElementMacrocellOffset_eq_variableSite
              source valueAtom location.1 slot location.2.1
              (.fixedRedInternal valueAtom slot element)
              location.2.2
      | clauseInternal clauseIndex =>
          cases owner
      | clauseTerminal clauseIndex group =>
          cases owner
  | blue value =>
      have typedMember : value ∈ blueElements source := by
        simpa [assembledTypedVertices] using member
      cases value with
      | ordinaryInternal valueAtom slot element =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          have location :=
            blueOrdinaryInternal_location
              source valueAtom slot element typedMember
          simpa [assembledTypedVertexOffset,
            activeVariableSiteVertexPosition,
            activeVariableSiteVertex] using
            blueElementMacrocellOffset_eq_variableSite
              source valueAtom location.1 slot location.2.1
              (.ordinaryInternal valueAtom slot element)
              location.2.2
      | fixedRedInternal valueAtom slot element =>
          have atomEq : valueAtom = atom :=
            AssemblyMacrocellOwner.atom.inj owner
          subst atom
          have location :=
            blueFixedRedInternal_location
              source valueAtom slot element typedMember
          simpa [assembledTypedVertexOffset,
            activeVariableSiteVertexPosition,
            activeVariableSiteVertex] using
            blueElementMacrocellOffset_eq_variableSite
              source valueAtom location.1 slot location.2.1
              (.fixedRedInternal valueAtom slot element)
              location.2.2
      | clauseInternal clauseIndex =>
          cases owner
      | clauseTerminal clauseIndex group =>
          cases owner

/-- Within one declared variable macrocell, equality of local offsets
recovers equality of the original tagged typed vertices. -/
theorem assembledTypedVertex_eq_of_variableOwner_offset_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable)
    (first second : AssembledTypedVertex Variable)
    (firstMember : first ∈ assembledTypedVertices source)
    (secondMember : second ∈ assembledTypedVertices source)
    (firstOwner :
      assembledTypedVertexOwner first =
        AssemblyMacrocellOwner.atom atom)
    (secondOwner :
      assembledTypedVertexOwner second =
        AssemblyMacrocellOwner.atom atom)
    (offsetEqual :
      assembledTypedVertexOffset source first =
        assembledTypedVertexOffset source second) :
    first = second := by
  have atomMember :
      atom ∈ occurringVariables source := by
    have declared :=
      assembledTypedVertexOwner_declared source first firstMember
    rw [firstOwner] at declared
    exact declared
  rw [assembledTypedVertexOffset_eq_activeVariableSite
      source atom first firstMember firstOwner,
    assembledTypedVertexOffset_eq_activeVariableSite
      source atom second secondMember secondOwner] at offsetEqual
  have localPositionEqual :=
    Cell.add_left_injective
      standardThreeStrandLayout.variableOffset offsetEqual
  have localVertexEqual :=
    activeVariableSiteVertexPosition_injective
      source atom atomMember localPositionEqual
  have rawEqual :=
    congrArg activeVariableSiteVertexValue localVertexEqual
  rw [activeVariableSiteVertex_value
      source atom first firstMember firstOwner,
    activeVariableSiteVertex_value
      source atom second secondMember secondOwner] at rawEqual
  exact
    variableSiteVertexOfTyped_injective_of_owner
      source atom first second firstMember secondMember
      firstOwner secondOwner rawEqual

/-- Color and terminal group are recovered from the clause terminal selected
by that pair. -/
@[simp]
theorem terminalElementForColor_eq_iff
    (firstColor secondColor : WireColor)
    (firstGroup secondGroup : X3CClauseTerminalGroup) :
    terminalElementForColor firstColor firstGroup =
        terminalElementForColor secondColor secondGroup ↔
      firstColor = secondColor ∧ firstGroup = secondGroup := by
  cases firstColor <;> cases secondColor <;>
    cases firstGroup <;> cases secondGroup <;>
    simp [terminalElementForColor]

/-- Forget global names while retaining the corresponding vertex of the
finite X3C clause-core drawing. -/
def clauseVertexOfTyped {Variable : Type*} :
    AssembledTypedVertex Variable →
      Sum X3CClauseSet X3CClauseElement
  | .triple (.clause _ set) =>
      .inl set
  | .triple _ =>
      .inl .topLeftOuter
  | .red (.clauseInternal _) =>
      .inr (.internal .left)
  | .red (.clauseTerminal _ group) =>
      .inr (.terminal (terminalElementForColor .red group))
  | .red _ =>
      .inr (.internal .left)
  | .green (.clauseInternal _) =>
      .inr (.internal .right)
  | .green (.clauseTerminal _ group) =>
      .inr (.terminal (terminalElementForColor .green group))
  | .green _ =>
      .inr (.internal .right)
  | .blue (.clauseInternal _) =>
      .inr (.internal .bottom)
  | .blue (.clauseTerminal _ group) =>
      .inr (.terminal (terminalElementForColor .blue group))
  | .blue _ =>
      .inr (.internal .bottom)

/-- Forgetting the common clause index is injective among tagged vertices
owned by that clause. -/
theorem clauseVertexOfTyped_injective_of_owner
    {Variable : Type*}
    (clauseIndex : Nat)
    (first second : AssembledTypedVertex Variable)
    (firstOwner :
      assembledTypedVertexOwner first =
        AssemblyMacrocellOwner.clause clauseIndex)
    (secondOwner :
      assembledTypedVertexOwner second =
        AssemblyMacrocellOwner.clause clauseIndex)
    (equal :
      clauseVertexOfTyped first = clauseVertexOfTyped second) :
    first = second := by
  cases first with
  | triple first =>
      cases second with
      | triple second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              tripleMacrocellOwner, clauseVertexOfTyped]
      | red second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              tripleMacrocellOwner, redElementMacrocellOwner,
              clauseVertexOfTyped]
      | green second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              tripleMacrocellOwner, greenElementMacrocellOwner,
              clauseVertexOfTyped]
      | blue second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              tripleMacrocellOwner, blueElementMacrocellOwner,
              clauseVertexOfTyped]
  | red first =>
      cases second with
      | triple second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              redElementMacrocellOwner, tripleMacrocellOwner,
              clauseVertexOfTyped]
      | red second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              redElementMacrocellOwner, clauseVertexOfTyped]
      | green second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              redElementMacrocellOwner, greenElementMacrocellOwner,
              clauseVertexOfTyped]
      | blue second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              redElementMacrocellOwner, blueElementMacrocellOwner,
              clauseVertexOfTyped]
  | green first =>
      cases second with
      | triple second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              greenElementMacrocellOwner, tripleMacrocellOwner,
              clauseVertexOfTyped]
      | red second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              greenElementMacrocellOwner, redElementMacrocellOwner,
              clauseVertexOfTyped]
      | green second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              greenElementMacrocellOwner, clauseVertexOfTyped]
      | blue second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              greenElementMacrocellOwner, blueElementMacrocellOwner,
              clauseVertexOfTyped]
  | blue first =>
      cases second with
      | triple second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              blueElementMacrocellOwner, tripleMacrocellOwner,
              clauseVertexOfTyped]
      | red second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              blueElementMacrocellOwner, redElementMacrocellOwner,
              clauseVertexOfTyped]
      | green second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              blueElementMacrocellOwner, greenElementMacrocellOwner,
              clauseVertexOfTyped]
      | blue second =>
          cases first <;> cases second <;>
            simp_all [assembledTypedVertexOwner,
              blueElementMacrocellOwner, clauseVertexOfTyped]

/-- Combined triple/element position function of the finite X3C clause
core. -/
def clauseVertexPosition :
    Sum X3CClauseSet X3CClauseElement → Cell
  | .inl set => X3CClauseOrthogonal.setPosition set
  | .inr element => X3CClauseOrthogonal.elementPosition element

/-- The exhaustive clause-core certificate makes its combined vertex
position function injective. -/
theorem clauseVertexPosition_injective :
    Function.Injective clauseVertexPosition := by
  have distinct :=
    X3CClauseOrthogonal.drawing_isValid.2.2.2.2.2
  intro first second equal
  cases first with
  | inl first =>
      cases second with
      | inl second =>
          exact congrArg Sum.inl (distinct.1 equal)
      | inr second =>
          exact (distinct.2.2 first second equal).elim
  | inr first =>
      cases second with
      | inl second =>
          exact (distinct.2.2 second first equal.symm).elim
      | inr second =>
          exact congrArg Sum.inr (distinct.2.1 equal)

/-- A typed vertex in a clause-owned macrocell has exactly the translated
position of its finite clause-core name. -/
theorem assembledTypedVertexOffset_eq_clause
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (vertex : AssembledTypedVertex Variable)
    (owner :
      assembledTypedVertexOwner vertex =
        AssemblyMacrocellOwner.clause clauseIndex) :
    assembledTypedVertexOffset source vertex =
      Cell.add standardThreeStrandLayout.clauseOffset
        (clauseVertexPosition (clauseVertexOfTyped vertex)) := by
  cases vertex with
  | triple value =>
      cases value <;>
        simp_all [assembledTypedVertexOwner, tripleMacrocellOwner,
          assembledTypedVertexOffset, tripleMacrocellOffset,
          clauseVertexOfTyped, clauseVertexPosition,
          orientedTripleLocalPosition]
  | red value =>
      cases value <;>
        simp_all [assembledTypedVertexOwner,
          redElementMacrocellOwner, assembledTypedVertexOffset,
          redElementMacrocellOffset, clauseVertexOfTyped,
          clauseVertexPosition, redClauseElementLocalPosition]
  | green value =>
      cases value <;>
        simp_all [assembledTypedVertexOwner,
          greenElementMacrocellOwner, assembledTypedVertexOffset,
          greenElementMacrocellOffset, clauseVertexOfTyped,
          clauseVertexPosition, greenClauseElementLocalPosition]
  | blue value =>
      cases value <;>
        simp_all [assembledTypedVertexOwner,
          blueElementMacrocellOwner, assembledTypedVertexOffset,
          blueElementMacrocellOffset, clauseVertexOfTyped,
          clauseVertexPosition, blueClauseElementLocalPosition]

/-- Within one clause macrocell, equality of local offsets recovers equality
of the original tagged typed vertices. -/
theorem assembledTypedVertex_eq_of_clauseOwner_offset_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (first second : AssembledTypedVertex Variable)
    (firstOwner :
      assembledTypedVertexOwner first =
        AssemblyMacrocellOwner.clause clauseIndex)
    (secondOwner :
      assembledTypedVertexOwner second =
        AssemblyMacrocellOwner.clause clauseIndex)
    (offsetEqual :
      assembledTypedVertexOffset source first =
        assembledTypedVertexOffset source second) :
    first = second := by
  rw [assembledTypedVertexOffset_eq_clause
      source clauseIndex first firstOwner,
    assembledTypedVertexOffset_eq_clause
      source clauseIndex second secondOwner] at offsetEqual
  have localPositionEqual :=
    Cell.add_left_injective
      standardThreeStrandLayout.clauseOffset offsetEqual
  have localVertexEqual :=
    clauseVertexPosition_injective localPositionEqual
  exact
    clauseVertexOfTyped_injective_of_owner
      clauseIndex first second firstOwner secondOwner localVertexEqual

/-- The standard assembled position map is injective on the listed tagged
typed vertices. -/
theorem standardAssembledTypedVertexPosition_injective_on
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (first second : AssembledTypedVertex Variable)
    (firstMember :
      first ∈ assembledTypedVertices source.erase)
    (secondMember :
      second ∈ assembledTypedVertices source.erase)
    (positionEqual :
      assembledTypedVertexPosition
          (constructedThreeStrandRouting
            presentation standardThreeStrandLayout)
          first =
        assembledTypedVertexPosition
          (constructedThreeStrandRouting
            presentation standardThreeStrandLayout)
          second) :
    first = second := by
  rw [assembledTypedVertexPosition_standard presentation first,
    assembledTypedVertexPosition_standard presentation second]
      at positionEqual
  have macrocellParts :=
    (Cell.macrocellPosition_eq_iff
      standardThreeStrandLayout.factorPositive
      (assembledTypedVertexOffset_inside source.erase first)
      (assembledTypedVertexOffset_inside source.erase second)).mp
        positionEqual
  have firstDeclared :=
    assembledTypedVertexOwner_declared
      source.erase first firstMember
  have secondDeclared :=
    assembledTypedVertexOwner_declared
      source.erase second secondMember
  have ownerEqual :=
    assemblyMacrocellOwnerPosition_injective_on
      presentation anchorsZero
      (assembledTypedVertexOwner first)
      (assembledTypedVertexOwner second)
      firstDeclared secondDeclared macrocellParts.1
  cases firstOwner :
      assembledTypedVertexOwner first with
  | atom atom =>
      have secondOwner :
          assembledTypedVertexOwner second =
            AssemblyMacrocellOwner.atom atom := by
        rw [← ownerEqual, firstOwner]
      exact
        assembledTypedVertex_eq_of_variableOwner_offset_eq
          source.erase atom first second firstMember secondMember
          firstOwner secondOwner macrocellParts.2
  | clause clauseIndex =>
      have secondOwner :
          assembledTypedVertexOwner second =
            AssemblyMacrocellOwner.clause clauseIndex := by
        rw [← ownerEqual, firstOwner]
      exact
        assembledTypedVertex_eq_of_clauseOwner_offset_eq
          source.erase clauseIndex first second
          firstOwner secondOwner macrocellParts.2

/-- All standard assembled vertex positions are pairwise distinct. -/
theorem standardAssembledVertexPositions_nodup
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source) :
    (assembledVertexPositions
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout)).Nodup := by
  rw [assembledVertexPositions_eq_map_typed]
  apply List.Nodup.map_on
  · intro first firstMember second secondMember equal
    exact standardAssembledTypedVertexPosition_injective_on
      presentation anchorsZero first second
      firstMember secondMember equal
  · exact assembledTypedVertices_nodup source.erase

/-- The normalized source used by the reduction satisfies assembled vertex
distinctness unconditionally. -/
theorem standardNormalizedAssembledVertexPositions_nodup
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement) :
    (assembledVertexPositions
      (constructedThreeStrandRouting
        (normalizedIncidencePresentation presentation)
        standardThreeStrandLayout)).Nodup := by
  exact standardAssembledVertexPositions_nodup
    (normalizedIncidencePresentation presentation)
    (normalizedPositionedSource_hasZeroClauseAnchors
      source placement)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
