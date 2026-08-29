/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackSuffixQueryColumnCompiler
import LeanTrominoes.RetainedAngularFanFallbackSuffixQueryData
import LeanTrominoes.RetainedAngularFanFallbackHeaderRoleCompiler

/-! # List semantics of fallback-suffix query columns -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace FallbackSuffixQueryColumns

open FallbackSuffixQueryFormatter

@[simp] theorem alignedQueries_length
    (roles : List HeaderRole)
    (radials : List Nat)
    (slots : List RetainedTerminalSlot) :
    (alignedQueries roles radials slots).length =
      min roles.length (min radials.length slots.length) := by
  induction roles generalizing radials slots with
  | nil => simp [alignedQueries]
  | cons role roles induction =>
      cases radials with
      | nil => simp [alignedQueries]
      | cons radial radials =>
          cases slots with
          | nil => simp [alignedQueries]
          | cons slot slots =>
              simp [alignedQueries, induction]

/-- Every aligned query inherits positivity from its radial column. -/
theorem alignedQueries_lengthPositive
    (roles : List HeaderRole)
    (radials : List Nat)
    (slots : List RetainedTerminalSlot)
    (radialPositive : ∀ radial ∈ radials, 0 < radial) :
    ∀ query ∈ alignedQueries roles radials slots,
      0 < query.rawLength := by
  induction roles generalizing radials slots with
  | nil => simp [alignedQueries]
  | cons role roles induction =>
      cases radials with
      | nil => simp [alignedQueries]
      | cons radial radials =>
          cases slots with
          | nil => simp [alignedQueries]
          | cons slot slots =>
              intro query queryMember
              simp only [alignedQueries, List.mem_cons] at queryMember
              rcases queryMember with queryEq | queryMember
              · subst query
                exact radialPositive radial (by simp)
              · exact induction radials slots
                  (fun rest restMember =>
                    radialPositive rest (by simp [restMember]))
                  query queryMember

/-- Ordinary bend roles and the two projections of a terminal-data list
reconstruct the semantic ordinary-query zipper. -/
theorem alignedQueries_bendRoles_terminalData
    (terminals : List RetainedTerminalData)
    (slots : List RetainedTerminalSlot) :
    alignedQueries
        (FallbackSuffixHeaderRoles.bendRoles
          (terminals.map Prod.fst))
        (terminals.map Prod.snd) slots =
      FallbackSuffixQueries.alignedQueries
        (List.replicate terminals.length .ordinary)
        terminals slots := by
  induction terminals generalizing slots with
  | nil => simp [alignedQueries,
      FallbackSuffixQueries.alignedQueries,
      FallbackSuffixHeaderRoles.bendRoles]
  | cons terminal terminals induction =>
      cases slots with
      | nil => simp [alignedQueries,
          FallbackSuffixQueries.alignedQueries,
          FallbackSuffixHeaderRoles.bendRoles]
      | cons slot slots =>
          simp only [List.map_cons, List.length_cons]
          rw [List.replicate_succ]
          change
            { kind := RetainedFallbackFanKind.ordinary
              direction := terminal.1
              rawLength := terminal.2
              slot := slot } ::
                alignedQueries
                  (FallbackSuffixHeaderRoles.bendRoles
                    (terminals.map Prod.fst))
                  (terminals.map Prod.snd) slots =
              { kind := RetainedFallbackFanKind.ordinary
                direction := terminal.1
                rawLength := terminal.2
                slot := slot } ::
                FallbackSuffixQueries.alignedQueries
                  (List.replicate terminals.length .ordinary)
                  terminals slots
          rw [induction slots]

end FallbackSuffixQueryColumns

namespace FallbackSuffixQueries

@[simp] theorem alignedQueries_length
    (kinds : List RetainedFallbackFanKind)
    (terminals : List RetainedTerminalData)
    (slots : List RetainedTerminalSlot) :
    (alignedQueries kinds terminals slots).length =
      min kinds.length (min terminals.length slots.length) := by
  induction kinds generalizing terminals slots with
  | nil => simp [alignedQueries]
  | cons kind kinds induction =>
      cases terminals with
      | nil => simp [alignedQueries]
      | cons terminal terminals =>
          cases slots with
          | nil => simp [alignedQueries]
          | cons slot slots =>
              simp [alignedQueries, induction]

end FallbackSuffixQueries
end PeriodicEightOccurrenceSplit
end LeanTrominoes
