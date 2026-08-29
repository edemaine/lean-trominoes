/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackKindData
import LeanTrominoes.RetainedAngularFanFallbackSuffixDirectionBatchSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTerminalColumnData

/-! # Aligned fallback-suffix queries for carrier and bend blocks -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace FallbackSuffixQueries

open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open FallbackSuffixDirectionCompiler.Batch

/-- Zip aligned policy, terminal-data, and occurrence-slot columns into
compact suffix queries.  As with `List.zip`, the shortest column wins. -/
def alignedQueries :
    List RetainedFallbackFanKind →
      List RetainedTerminalData →
        List RetainedTerminalSlot → List Query
  | kind :: kinds, terminal :: terminals, slot :: slots =>
      { kind := kind
        direction := terminal.1
        rawLength := terminal.2
        slot := slot } :: alignedQueries kinds terminals slots
  | _, _, _ => []

/-- Query selected directly from the public route-policy test. -/
def routeQuery
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : Query where
  kind := retainedFallbackFanKindOfRoute route
  direction := terminal.1
  rawLength := terminal.2
  slot := slot

def carrierQueries
    (horizontal : Bool) (span : Int)
    (slots : List RetainedTerminalSlot) : List Query :=
  alignedQueries carrierFallbackFanKindBlock
    (carrierLensRouteTerminalDataBlock horizontal span) slots

def bendQueries
    (firstPort secondPort : CornerPort)
    (slots : List RetainedTerminalSlot) : List Query :=
  alignedQueries bendFallbackFanKindBlock
    (bendRouteTerminalDataBlock firstPort secondPort) slots

/-- The canonical carrier query block uses exactly the public singleton-
prefix choice on each of its four local routes. -/
theorem carrierQueries_eq_routeQueries
    (horizontal : Bool) (span : Int)
    (first second third fourth : RetainedTerminalSlot) :
    carrierQueries horizontal span [first, second, third, fourth] =
      [routeQuery (horizontalEqualityLensRoutes span 0 0)
          (carrierLensRouteTerminalData horizontal span 0 0) first,
        routeQuery (horizontalEqualityLensRoutes span 0 1)
          (carrierLensRouteTerminalData horizontal span 0 1) second,
        routeQuery (horizontalEqualityLensRoutes span 1 0)
          (carrierLensRouteTerminalData horizontal span 1 0) third,
        routeQuery (horizontalEqualityLensRoutes span 1 1)
          (carrierLensRouteTerminalData horizontal span 1 1) fourth] := by
  rfl

/-- The canonical bend query block uses the public route-policy choice on
each finite corner-table route; all four choices are ordinary. -/
theorem bendQueries_eq_routeQueries
    (firstPort secondPort : CornerPort)
    (first second third fourth : RetainedTerminalSlot) :
    bendQueries firstPort secondPort [first, second, third, fourth] =
      [routeQuery (cornerEqualityRoutes firstPort secondPort 0 0)
          (bendRouteTerminalData firstPort secondPort 0 0) first,
        routeQuery (cornerEqualityRoutes firstPort secondPort 0 1)
          (bendRouteTerminalData firstPort secondPort 0 1) second,
        routeQuery (cornerEqualityRoutes firstPort secondPort 1 0)
          (bendRouteTerminalData firstPort secondPort 1 0) third,
        routeQuery (cornerEqualityRoutes firstPort secondPort 1 1)
          (bendRouteTerminalData firstPort secondPort 1 1) fourth] := by
  cases firstPort <;> cases secondPort <;> rfl

theorem alignedQueries_lengthPositive
    (kinds : List RetainedFallbackFanKind)
    (terminals : List RetainedTerminalData)
    (slots : List RetainedTerminalSlot)
    (terminalPositive : ∀ terminal ∈ terminals, 0 < terminal.2) :
    ∀ query ∈ alignedQueries kinds terminals slots,
      0 < query.rawLength := by
  induction kinds generalizing terminals slots with
  | nil => simp [alignedQueries]
  | cons kind kinds induction =>
      cases terminals with
      | nil => simp [alignedQueries]
      | cons terminal terminals =>
          cases slots with
          | nil => simp [alignedQueries]
          | cons slot slots =>
              intro query queryMember
              simp only [alignedQueries, List.mem_cons] at queryMember
              rcases queryMember with queryEq | queryMember
              · subst query
                exact terminalPositive terminal (by simp)
              · exact induction terminals slots
                  (fun rest restMember =>
                    terminalPositive rest (by simp [restMember]))
                  query queryMember

theorem carrierLensRouteTerminalDataBlock_lengthPositive
    (horizontal : Bool) (span : Int) (large : 6 < span) :
    ∀ terminal ∈ carrierLensRouteTerminalDataBlock horizontal span,
      0 < terminal.2 := by
  intro terminal terminalMember
  simp only [carrierLensRouteTerminalDataBlock, List.mem_cons,
    List.not_mem_nil, or_false] at terminalMember
  rcases terminalMember with terminalEq | terminalEq | terminalEq |
      terminalEq
  · subst terminal
    simp [carrierLensRouteTerminalData]
  · subst terminal
    simp [carrierLensRouteTerminalData]
  · subst terminal
    simp [carrierLensRouteTerminalData]
  · subst terminal
    simp [carrierLensRouteTerminalData]
    omega

theorem bendRouteTerminalDataBlock_lengthPositive
    (firstPort secondPort : CornerPort) :
    ∀ terminal ∈ bendRouteTerminalDataBlock firstPort secondPort,
      0 < terminal.2 := by
  cases firstPort <;> cases secondPort <;> native_decide

/-- Every query of a geometrically valid carrier block has positive raw
terminal length. -/
theorem carrierQueries_lengthPositive
    (horizontal : Bool) (span : Int) (large : 6 < span)
    (slots : List RetainedTerminalSlot) :
    ∀ query ∈ carrierQueries horizontal span slots,
      0 < query.rawLength :=
  alignedQueries_lengthPositive _ _ _
    (carrierLensRouteTerminalDataBlock_lengthPositive
      horizontal span large)

/-- Every query of a finite bend block has positive raw terminal length. -/
theorem bendQueries_lengthPositive
    (firstPort secondPort : CornerPort)
    (slots : List RetainedTerminalSlot) :
    ∀ query ∈ bendQueries firstPort secondPort slots,
      0 < query.rawLength :=
  alignedQueries_lengthPositive _ _ _
    (bendRouteTerminalDataBlock_lengthPositive firstPort secondPort)

end FallbackSuffixQueries
end PeriodicEightOccurrenceSplit
end LeanTrominoes
