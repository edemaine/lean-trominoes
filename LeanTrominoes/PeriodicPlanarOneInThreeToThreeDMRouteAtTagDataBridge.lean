/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalRoutes

/-! # Generic proof-free tag lookup for typed incidence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget

/-- Select a proof-free typed route from an optional triple. -/
def typedRouteFromOptionData
    {Variable : Type*}
    (route : Triple Variable → WireColor → List Cell)
    (color : WireColor)
    (triple? : Option (Triple Variable)) : List Cell :=
  match triple? with
  | none => []
  | some triple => route triple color

/-- Total tag lookup in an explicit proof-free typed-triple list. -/
def typedRouteAtTagListData
    {Variable : Type*}
    (typedTriples : List (Triple Variable))
    (route : Triple Variable → WireColor → List Cell)
    (tag : PeriodicThreeDM.IncidenceTag) : List Cell :=
  typedRouteFromOptionData route tag.color
    typedTriples[tag.tripleIndex]?

/-- Total tag lookup driven by a proof-free typed route function. -/
def typedRouteAtTagData
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (route : Triple Variable → WireColor → List Cell)
    (tag : PeriodicThreeDM.IncidenceTag) : List Cell :=
  typedRouteAtTagListData (triples source) route tag

/-- If a proof-free typed route agrees on every listed triple, its total tag
lookup agrees with the dependent certified assembly lookup. -/
theorem typedRouteAtTagData_eq_assembled
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (route : Triple Variable → WireColor → List Cell)
    (agrees : ∀
      triple : {triple : Triple Variable // triple ∈ triples source},
      ∀ color,
        route triple.1 color =
          assembledTypedIncidenceRoute routing triple color)
    (tag : PeriodicThreeDM.IncidenceTag) :
    typedRouteAtTagData source route tag =
      assembledRouteAtTag routing tag := by
  unfold typedRouteAtTagData typedRouteAtTagListData
    typedRouteFromOptionData assembledRouteAtTag
  by_cases indexLt : tag.tripleIndex < (triples source).length
  · rw [dif_pos indexLt, List.getElem?_eq_getElem indexLt]
    exact agrees
      ⟨(triples source)[tag.tripleIndex]'indexLt,
        List.getElem_mem indexLt⟩
      tag.color
  · rw [dif_neg indexLt]
    have lookupNone : (triples source)[tag.tripleIndex]? = none :=
      List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt indexLt)
    rw [lookupNone]

/-- The list-level selector specializes the source-level selector without
unfolding the source's concrete triple construction. -/
theorem typedRouteAtTagListData_eq_assembled
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (route : Triple Variable → WireColor → List Cell)
    (agrees : ∀
      triple : {triple : Triple Variable // triple ∈ triples source},
      ∀ color,
        route triple.1 color =
          assembledTypedIncidenceRoute routing triple color)
    (tag : PeriodicThreeDM.IncidenceTag) :
    typedRouteAtTagListData (triples source) route tag =
      assembledRouteAtTag routing tag :=
  typedRouteAtTagData_eq_assembled routing route agrees tag

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
