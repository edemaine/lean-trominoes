/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinExecution

/-! # Linear clock bound for delimited-route joining -/

namespace LeanTrominoes.DelimitedRouteJoin

theorem resultAux_remainingPrefixes_length_le
    (phase : Phase) (prefixes suffixes : List Token) :
    (resultAux phase prefixes suffixes).remainingPrefixes.length ≤
      prefixes.length := by
  cases phase with
  | «prefix» =>
      cases prefixes with
      | nil => simp [resultAux]
      | cons token prefixes =>
          cases token with
          | direction direction =>
              have bound := resultAux_remainingPrefixes_length_le
                Phase.prefix prefixes suffixes
              simp [resultAux]
              omega
          | routeEnd =>
              have bound := resultAux_remainingPrefixes_length_le
                Phase.suffix prefixes suffixes
              simp [resultAux]
              omega
  | suffix =>
      cases suffixes with
      | nil => simp [resultAux]
      | cons token suffixes =>
          cases token with
          | direction direction =>
              simpa [resultAux] using
                (resultAux_remainingPrefixes_length_le
                  Phase.suffix prefixes suffixes)
          | routeEnd =>
              simpa [resultAux] using
                (resultAux_remainingPrefixes_length_le
                  Phase.prefix prefixes suffixes)
  termination_by prefixes.length + suffixes.length
  decreasing_by
    all_goals simp_wf

theorem resultAux_remainingSuffixes_length_le
    (phase : Phase) (prefixes suffixes : List Token) :
    (resultAux phase prefixes suffixes).remainingSuffixes.length ≤
      suffixes.length := by
  cases phase with
  | «prefix» =>
      cases prefixes with
      | nil => simp [resultAux]
      | cons token prefixes =>
          cases token with
          | direction direction =>
              simpa [resultAux] using
                (resultAux_remainingSuffixes_length_le
                  Phase.prefix prefixes suffixes)
          | routeEnd =>
              simpa [resultAux] using
                (resultAux_remainingSuffixes_length_le
                  Phase.suffix prefixes suffixes)
  | suffix =>
      cases suffixes with
      | nil => simp [resultAux]
      | cons token suffixes =>
          cases token with
          | direction direction =>
              have bound := resultAux_remainingSuffixes_length_le
                Phase.suffix prefixes suffixes
              simp [resultAux]
              omega
          | routeEnd =>
              have bound := resultAux_remainingSuffixes_length_le
                Phase.prefix prefixes suffixes
              simp [resultAux]
              omega
  termination_by prefixes.length + suffixes.length
  decreasing_by
    all_goals simp_wf

theorem resultAux_output_length_le
    (phase : Phase) (prefixes suffixes : List Token) :
    (resultAux phase prefixes suffixes).output.length ≤
      prefixes.length + suffixes.length := by
  cases phase with
  | «prefix» =>
      cases prefixes with
      | nil => simp [resultAux]
      | cons token prefixes =>
          cases token with
          | direction direction =>
              have bound := resultAux_output_length_le
                Phase.prefix prefixes suffixes
              simp [resultAux]
              omega
          | routeEnd =>
              have bound := resultAux_output_length_le
                Phase.suffix prefixes suffixes
              simp [resultAux]
              omega
  | suffix =>
      cases suffixes with
      | nil => simp [resultAux]
      | cons token suffixes =>
          cases token with
          | direction direction =>
              have bound := resultAux_output_length_le
                Phase.suffix prefixes suffixes
              simp [resultAux]
              omega
          | routeEnd =>
              have bound := resultAux_output_length_le
                Phase.prefix prefixes suffixes
              simp [resultAux]
              omega
  termination_by prefixes.length + suffixes.length
  decreasing_by
    all_goals simp_wf

theorem joinTime_le (phase : Phase) (prefixes suffixes : List Token) :
    joinTime phase prefixes suffixes ≤
      2 * (prefixes.length + suffixes.length) + 1 := by
  cases phase with
  | «prefix» =>
      cases prefixes with
      | nil => simp [joinTime]
      | cons token prefixes =>
          cases token with
          | direction direction =>
              have bound := joinTime_le Phase.prefix prefixes suffixes
              simp [joinTime]
              omega
          | routeEnd =>
              have bound := joinTime_le Phase.suffix prefixes suffixes
              simp [joinTime]
              omega
  | suffix =>
      cases suffixes with
      | nil => simp [joinTime]
      | cons token suffixes =>
          cases token with
          | direction direction =>
              have bound := joinTime_le Phase.suffix prefixes suffixes
              simp [joinTime]
              omega
          | routeEnd =>
              have bound := joinTime_le Phase.prefix prefixes suffixes
              simp [joinTime]
              omega
  termination_by prefixes.length + suffixes.length
  decreasing_by
    all_goals simp_wf

/-- The exact total clock is linear in the complete separated encoding. -/
theorem totalTime_le (prefixes suffixes : List Token) :
    totalTime prefixes suffixes ≤
      9 * (encode (prefixes, suffixes)).length := by
  have joinBound := joinTime_le Phase.prefix prefixes suffixes
  have prefixBound := resultAux_remainingPrefixes_length_le
    Phase.prefix prefixes suffixes
  have suffixBound := resultAux_remainingSuffixes_length_le
    Phase.prefix prefixes suffixes
  have outputBound := resultAux_output_length_le
    Phase.prefix prefixes suffixes
  simp only [totalTime, parseTime, encode,
    SeparatedProductEncoding.encode_length, id_eq]
  omega

end LeanTrominoes.DelimitedRouteJoin
