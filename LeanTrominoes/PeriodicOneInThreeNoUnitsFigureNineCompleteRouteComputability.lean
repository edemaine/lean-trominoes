/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineSuffixComputability

/-!
# Computability of complete composed Figure 9 routes

The inherited-suffix dispatcher covers only original source atoms.  This
module supplies singleton suffixes for both auxiliary generations, joins the
result to the computed local route, and identifies the proof-free lookup with
the certified complete route family.
-/

noncomputable section

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

set_option maxHeartbeats 1000000
set_option linter.overlappingInstances false

private abbrev ComposedVariable (Variable : Type*) :=
  OneInThreeNoUnitVariable (OneInThreeVariable Variable)

/-- Recover an original source atom through the two auxiliary sums. -/
def originalSourceAtom?
    {Variable : Type*} : ComposedVariable Variable → Option Variable
  | .inl (.inl atom) => some atom
  | _ => none

theorem originalSourceAtom?_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (originalSourceAtom? (Variable := Variable)) := by
  have inner : Primrec fun atom : OneInThreeVariable Variable =>
      match atom with
      | .inl sourceAtom => some sourceAtom
      | .inr _ => none := by
    exact (Primrec.sumCasesOn Primrec.id
      (Primrec.option_some.comp Primrec.snd).to₂
      (Primrec.const none).to₂).of_eq fun atom => by
        cases atom <;> rfl
  exact (Primrec.sumCasesOn Primrec.id
    (inner.comp Primrec.snd).to₂
    (Primrec.const none).to₂).of_eq fun atom => by
      cases atom with
      | inl innerAtom => cases innerAtom <;> rfl
      | inr _ => rfl

/-- Presentation lookup of one literal in the twice-replaced formula. -/
def composedLiteral?
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    Option (PeriodicLiteral (ComposedVariable Variable)) :=
  (PeriodicOneInThreeNoUnitsPositioned.formula
    (PeriodicOneInThreePositioned.formula source)).clauses[clauseIndex]?.bind
      fun clause => clause.literals[literalIndex]?

private theorem composedLiteral?_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePrimrec : Primrec source) :
    Primrec fun input : (Input × Nat) × Nat =>
      composedLiteral? (source input.1.1) input.1.2 input.2 := by
  let Query := (Input × Nat) × Nat
  have target : Primrec fun input : Query =>
      PeriodicOneInThreeNoUnitsPositioned.formula
        (PeriodicOneInThreePositioned.formula
          (source input.1.1)) :=
    (PeriodicOneInThreeNoUnitsPositioned.formula_primrec.comp
      (PeriodicOneInThreePositioned.formula_primrec.comp
        sourcePrimrec)).comp (Primrec.fst.comp Primrec.fst)
  have clause : Primrec fun input : Query =>
      (PeriodicOneInThreeNoUnitsPositioned.formula
        (PeriodicOneInThreePositioned.formula
          (source input.1.1))).clauses[input.1.2]? :=
    Primrec.list_getElem?.comp
      (PositionedPeriodicCNF.clauses_primrec.comp target)
      (Primrec.snd.comp Primrec.fst)
  have literal : Primrec₂ fun (input : Query)
      (clause : PositionedPeriodicClause (ComposedVariable Variable)) =>
      clause.literals[input.2]? := by
    exact Primrec.list_getElem?.comp
      (PositionedPeriodicClause.literals_primrec.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst) |>.to₂
  exact (Primrec.option_bind clause literal).of_eq fun input => by
    unfold composedLiteral?
    cases (PeriodicOneInThreeNoUnitsPositioned.formula
      (PeriodicOneInThreePositioned.formula
        (source input.1.1))).clauses[input.1.2]? <;> rfl

/-- Executable local splice point, obtained as the last point of the already
computed normalized local route. -/
def normalizedLocalEndpointComputed
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (clauseIndex literalIndex : Nat) : Cell :=
  (normalizedLocalRoutes source sourcePlacement
    clauseIndex literalIndex).getLastD (0, 0)

private theorem polylineGetLastD_primrec :
    Primrec fun route : List Cell => route.getLastD (0, 0) := by
  have last : Primrec fun route : List Cell => route.reverse.head? :=
    Primrec.list_head?.comp (Primrec.list_reverse.comp Primrec.id)
  exact (Primrec.option_getD.comp last
    (Primrec.const ((0, 0) : Cell))).of_eq fun route => by simp

theorem normalizedLocalEndpointComputed_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period) :
    Primrec fun input : (Input × Nat) × Nat =>
      normalizedLocalEndpointComputed
        (source input.1.1) (sourcePlacement input.1.1)
        input.1.2 input.2 := by
  exact polylineGetLastD_primrec.comp
    (normalizedLocalRoutes_primrec
      source sourcePlacement sourcePrimrec periodPrimrec)

private theorem getLastD_eq_of_getLast?_eq_some
    {Alpha : Type*} (values : List Alpha) (default value : Alpha)
    (last : values.getLast? = some value) :
    values.getLastD default = value := by
  cases values with
  | nil => simp at last
  | cons first rest =>
      have nonempty : first :: rest ≠ [] := by simp
      rw [List.getLast?_eq_getLast_of_ne_nil nonempty] at last
      simpa [List.getLastD] using Option.some.inj last

/-- On every genuine incidence, the executable last-point selector is the
advertised local splice point. -/
theorem normalizedLocalEndpointComputed_eq_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause : PositionedPeriodicClause (ComposedVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal : PeriodicLiteral (ComposedVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    normalizedLocalEndpointComputed source sourcePlacement
        clauseIndex literalIndex =
      normalizedLocalEndpoint source sourcePlacement
        clauseIndex literalIndex := by
  apply getLastD_eq_of_getLast?_eq_some
  exact (normalizedLocalRoutes_endpoints_of_members
    source sourcePlacement sourceWidth sourceDistinct
    clauseMember literalMember).2

/-- Complete proof-free suffix lookup: inherited incidences use the computed
fan suffix, while both auxiliary generations stop at the local endpoint. -/
def completeRouteSuffixesComputed
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat) : List Cell :=
  match composedLiteral? source clauseIndex literalIndex with
  | none => []
  | some literal =>
      match originalSourceAtom? literal.atom with
      | some _ =>
          orderedInheritedRouteSuffixesComputed
            source sourcePlacement sourceRoutes
            clauseIndex literalIndex
      | none =>
          [normalizedLocalEndpointComputed
            source sourcePlacement clauseIndex literalIndex]

/-- Complete suffix lookup is primitive recursive from the positioned source,
its placement period, and its source-route lookup. -/
theorem completeRouteSuffixesComputed_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (sourceRoutes : Input → PositionedPeriodicCNF.IncidenceRoutes)
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period)
    (sourceRoutesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      sourceRoutes input.1.1 input.1.2 input.2) :
    Primrec fun input : (Input × Nat) × Nat =>
      completeRouteSuffixesComputed
        (source input.1.1) (sourcePlacement input.1.1)
        (sourceRoutes input.1.1) input.1.2 input.2 := by
  let Query := (Input × Nat) × Nat
  have selected : Primrec fun input : Query =>
      composedLiteral? (source input.1.1) input.1.2 input.2 :=
    composedLiteral?_primrec source sourcePrimrec
  have noLiteral : Primrec fun _input : Query => ([] : List Cell) :=
    Primrec.const []
  have someLiteral : Primrec₂ fun (input : Query)
      (literal : PeriodicLiteral (ComposedVariable Variable)) =>
      match originalSourceAtom? literal.atom with
      | some _ =>
          orderedInheritedRouteSuffixesComputed
            (source input.1.1) (sourcePlacement input.1.1)
            (sourceRoutes input.1.1) input.1.2 input.2
      | none =>
          [normalizedLocalEndpointComputed
            (source input.1.1) (sourcePlacement input.1.1)
            input.1.2 input.2] := by
    let Combined := Query ×
      PeriodicLiteral (ComposedVariable Variable)
    have sourceAtom : Primrec fun input : Combined =>
        originalSourceAtom? input.2.atom :=
      originalSourceAtom?_primrec.comp
        (PeriodicThreeCNF.literal_atom_primrec.comp Primrec.snd)
    have inherited : Primrec fun input : Combined =>
        orderedInheritedRouteSuffixesComputed
          (source input.1.1.1) (sourcePlacement input.1.1.1)
          (sourceRoutes input.1.1.1) input.1.1.2 input.1.2 :=
      (orderedInheritedRouteSuffixesComputed_primrec
        source sourcePlacement sourceRoutes sourcePrimrec
        periodPrimrec sourceRoutesPrimrec).comp Primrec.fst
    have auxiliary : Primrec fun input : Combined =>
        [normalizedLocalEndpointComputed
          (source input.1.1.1) (sourcePlacement input.1.1.1)
          input.1.1.2 input.1.2] :=
      Primrec.list_cons.comp
        ((normalizedLocalEndpointComputed_primrec
          source sourcePlacement sourcePrimrec periodPrimrec).comp
            Primrec.fst)
        (Primrec.const [])
    have sourceBranch : Primrec₂ fun (_input : Combined)
        (_atom : Variable) =>
        orderedInheritedRouteSuffixesComputed
          (source _input.1.1.1) (sourcePlacement _input.1.1.1)
          (sourceRoutes _input.1.1.1) _input.1.1.2 _input.1.2 :=
      inherited.comp Primrec.fst |>.to₂
    change Primrec fun input : Combined =>
      match originalSourceAtom? input.2.atom with
      | some _ =>
          orderedInheritedRouteSuffixesComputed
            (source input.1.1.1) (sourcePlacement input.1.1.1)
            (sourceRoutes input.1.1.1) input.1.1.2 input.1.2
      | none =>
          [normalizedLocalEndpointComputed
            (source input.1.1.1) (sourcePlacement input.1.1.1)
            input.1.1.2 input.1.2]
    exact (Primrec.option_casesOn sourceAtom auxiliary
      sourceBranch).of_eq fun input => by
        cases originalSourceAtom? input.2.atom <;> rfl
  exact (Primrec.option_casesOn selected noLiteral someLiteral).of_eq
    fun input => by
      unfold completeRouteSuffixesComputed
      cases composedLiteral? (source input.1.1)
          input.1.2 input.2 <;> rfl

/-- The proof-free complete suffix lookup agrees with any certified ordered
suffix family whose route field is the established ordered lookup. -/
theorem completeRouteSuffixesComputed_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (original :
      OriginalInheritedCanonicalIncidenceRouteSuffixes
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source))
        (composedPlacement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement))
    (originalRoutes :
      ∀ clauseIndex literalIndex,
        original.routes clauseIndex literalIndex =
          orderedInheritedRouteSuffixesRoutes
            source sourcePlacement sourceWidth sourceRoutes
            clauseIndex literalIndex)
    (clauseIndex literalIndex : Nat) :
    completeRouteSuffixesComputed
        source sourcePlacement sourceRoutes clauseIndex literalIndex =
      (completeRouteSuffixes source sourcePlacement
        sourceWidth sourceDistinct original).routes
        clauseIndex literalIndex := by
  let target := PeriodicOneInThreeNoUnitsPositioned.formula
    (PeriodicOneInThreePositioned.formula source)
  cases clauseLookup : target.clauses[clauseIndex]? with
  | none =>
      simp [completeRouteSuffixesComputed, composedLiteral?, target,
        clauseLookup, completeRouteSuffixes,
        PositionedPeriodicCNF.completeSumIncidenceRouteSuffixes,
        PositionedPeriodicCNF.completeSumIncidenceRouteSuffixesRoutes]
  | some clause =>
      cases literalLookup : clause.literals[literalIndex]? with
      | none =>
          simp [completeRouteSuffixesComputed, composedLiteral?, target,
            clauseLookup, literalLookup, completeRouteSuffixes,
            PositionedPeriodicCNF.completeSumIncidenceRouteSuffixes,
            PositionedPeriodicCNF.completeSumIncidenceRouteSuffixesRoutes]
      | some literal =>
          have clauseMember :
              (clause, clauseIndex) ∈ target.clauses.zipIdx :=
            (List.mem_zipIdx_iff_getElem?).mpr clauseLookup
          have literalMember :
              (literal, literalIndex) ∈ clause.literals.zipIdx :=
            (List.mem_zipIdx_iff_getElem?).mpr literalLookup
          rw [completeRouteSuffixes_routes_of_members
            source sourcePlacement sourceWidth sourceDistinct
            original clauseMember literalMember]
          have endpointEq :=
            normalizedLocalEndpointComputed_eq_of_members
              source sourcePlacement sourceWidth sourceDistinct
              clauseMember literalMember
          cases atomEq : literal.atom with
          | inr _ =>
              simp [completeRouteSuffixesComputed, composedLiteral?, target,
                clauseLookup, literalLookup, originalSourceAtom?, atomEq,
                endpointEq]
          | inl figureAtom =>
              cases figureEq : figureAtom with
              | inr _ =>
                  simp [completeRouteSuffixesComputed, composedLiteral?, target,
                    clauseLookup, literalLookup, originalSourceAtom?, atomEq,
                    figureEq, endpointEq]
              | inl _ =>
                  rw [originalRoutes clauseIndex literalIndex,
                    ← orderedInheritedRouteSuffixesComputed_eq
                      source sourcePlacement sourceWidth sourceDistinct
                      sourceRoutes clauseIndex literalIndex]
                  simp [completeRouteSuffixesComputed, composedLiteral?, target,
                    clauseLookup, literalLookup, originalSourceAtom?, atomEq,
                    figureEq]

/-- Fully spliced proof-free route lookup. -/
def splicedRoutesComputed
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat) : List Cell :=
  joinAtEndpoint
    (normalizedLocalRoutes source sourcePlacement
      clauseIndex literalIndex)
    (completeRouteSuffixesComputed
      source sourcePlacement sourceRoutes clauseIndex literalIndex)

theorem splicedRoutesComputed_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (sourceRoutes : Input → PositionedPeriodicCNF.IncidenceRoutes)
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period)
    (sourceRoutesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      sourceRoutes input.1.1 input.1.2 input.2) :
    Primrec fun input : (Input × Nat) × Nat =>
      splicedRoutesComputed
        (source input.1.1) (sourcePlacement input.1.1)
        (sourceRoutes input.1.1) input.1.2 input.2 := by
  exact joinAtEndpoint_primrec _ _
    (normalizedLocalRoutes_primrec
      source sourcePlacement sourcePrimrec periodPrimrec)
    (completeRouteSuffixesComputed_primrec
      source sourcePlacement sourceRoutes sourcePrimrec
      periodPrimrec sourceRoutesPrimrec)

theorem splicedRoutesComputed_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (original :
      OriginalInheritedCanonicalIncidenceRouteSuffixes
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source))
        (composedPlacement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement))
    (originalRoutes :
      ∀ clauseIndex literalIndex,
        original.routes clauseIndex literalIndex =
          orderedInheritedRouteSuffixesRoutes
            source sourcePlacement sourceWidth sourceRoutes
            clauseIndex literalIndex)
    (clauseIndex literalIndex : Nat) :
    splicedRoutesComputed
        source sourcePlacement sourceRoutes clauseIndex literalIndex =
      splicedRoutes source sourcePlacement sourceWidth sourceDistinct
        original clauseIndex literalIndex := by
  unfold splicedRoutesComputed splicedRoutes
    PositionedPeriodicCNF.spliceLocalIncidenceRoutes
  rw [completeRouteSuffixesComputed_eq
    source sourcePlacement sourceWidth sourceDistinct sourceRoutes
    original originalRoutes clauseIndex literalIndex]

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
