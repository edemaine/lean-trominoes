/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetOrientationBehavior

/-! # Kernel-checked supported port tables and type-specific configurations -/

namespace LeanTrominoes.Gadget

set_option maxRecDepth 10000

/-- The supported tables, materialized once for subsequent finite checks. -/
def cachedSupportedCellPortTable : Tromino → Finset (OrthogonalCellType × PortConfiguration)
  | .L => {(.blank, { north := ∅, east := ∅, south := ∅, west := ∅ }), (.wire
  (.horizontal)
  (.red), { north := ∅, east := {{(-1, 2), (-1, 3), (0, 2)}}, south := ∅, west := {{(-1, 2), (0, 2), (-1, 1)}} }), (.wire
  (.horizontal)
  (.red), { north := ∅, east := {{(-1, 2), (-1, 3), (0, 2)}}, south := ∅, west := {{(-1, 2), (-1, 3), (0, 2)}} }), (.wire
  (.horizontal)
  (.red), { north := ∅, east := ∅, south := ∅, west := ∅ }), (.wire
  (.horizontal)
  (.green), { north := ∅, east := ∅, south := ∅, west := ∅ }), (.wire
  (.horizontal)
  (.green), { north := ∅, east := {{(0, 2), (-1, 2), (0, 3)}}, south := ∅, west := {{(0, 2), (-1, 2), (0, 3)}} }), (.wire
  (.horizontal)
  (.green), { north := ∅, east := {{(0, 2), (0, 1), (-1, 2)}}, south := ∅, west := {{(0, 2), (-1, 2), (0, 3)}} }), (.wire
  (.horizontal)
  (.blue), { north := ∅, east := {{(-1, 3), (-1, 4), (0, 3)}}, south := ∅, west := {{(-1, 3), (0, 3), (-1, 2)}} }), (.wire
  (.horizontal)
  (.blue), { north := ∅, east := {{(-1, 3), (-1, 4), (0, 3)}}, south := ∅, west := {{(-1, 3), (-1, 4), (0, 3)}} }), (.wire
  (.horizontal)
  (.blue), { north := ∅, east := ∅, south := ∅, west := ∅ }), (.wire
  (.vertical)
  (.red), { north := {{(2, -1), (2, 0), (3, -1)}}, east := ∅, south := {{(2, -1), (2, 0), (3, -1)}}, west := ∅ }), (.wire
  (.vertical)
  (.red), { north := {{(2, -1), (1, -1), (2, 0)}}, east := ∅, south := {{(2, -1), (2, 0), (3, -1)}}, west := ∅ }), (.wire
  (.vertical)
  (.red), { north := ∅, east := ∅, south := ∅, west := ∅ }), (.wire
  (.vertical)
  (.green), { north := {{(3, -1), (3, 0), (4, -1)}}, east := ∅, south := {{(3, -1), (3, 0), (4, -1)}}, west := ∅ }), (.wire
  (.vertical)
  (.green), { north := {{(3, -1), (2, -1), (3, 0)}}, east := ∅, south := {{(3, -1), (3, 0), (4, -1)}}, west := ∅ }), (.wire
  (.vertical)
  (.green), { north := ∅, east := ∅, south := ∅, west := ∅ }), (.wire
  (.vertical)
  (.blue), { north := {{(2, 0), (3, 0), (2, -1)}}, east := ∅, south := {{(2, 0), (3, 0), (2, -1)}}, west := ∅ }), (.wire
  (.vertical)
  (.blue), { north := {{(2, 0), (3, 0), (2, -1)}}, east := ∅, south := {{(2, 0), (2, -1), (1, 0)}}, west := ∅ }), (.wire
  (.vertical)
  (.blue), { north := ∅, east := ∅, south := ∅, west := ∅ }), (.bend
  (.northeast)
  (.red), { north := ∅, east := ∅, south := ∅, west := ∅ }), (.bend
  (.northeast)
  (.red), { north := {{(2, -1), (2, 0), (3, -1)}}, east := {{(-1, 2), (-1, 3), (0, 2)}}, south := ∅, west := ∅ }), (.bend
  (.northeast)
  (.red), { north := {{(2, -1), (1, -1), (2, 0)}}, east := {{(-1, 2), (-1, 3), (0, 2)}}, south := ∅, west := ∅ }), (.bend
  (.northeast)
  (.green), { north := ∅, east := {{(0, 2), (-1, 2), (0, 3)}}, south := ∅, west := ∅ }), (.bend
  (.northeast)
  (.green), { north := ∅, east := {{(0, 2), (0, 1), (-1, 2)}}, south := ∅, west := ∅ }), (.bend
  (.northeast)
  (.green), { north := {{(3, -1), (3, 0), (4, -1)}}, east := ∅, south := ∅, west := ∅ }), (.bend
  (.northeast)
  (.green), { north := {{(3, -1), (2, -1), (3, 0)}}, east := ∅, south := ∅, west := ∅ }), (.bend
  (.northeast)
  (.blue), { north := {{(2, 0), (2, -1), (1, 0)}}, east := ∅, south := ∅, west := ∅ }), (.bend
  (.northeast)
  (.blue), { north := ∅, east := {{(-1, 3), (-1, 4), (0, 3)}}, south := ∅, west := ∅ }), (.bend
  (.northwest)
  (.red), { north := ∅, east := ∅, south := ∅, west := {{(-1, 2), (0, 2), (-1, 1)}} }), (.bend
  (.northwest)
  (.red), { north := ∅, east := ∅, south := ∅, west := {{(-1, 2), (-1, 3), (0, 2)}} }), (.bend
  (.northwest)
  (.red), { north := {{(2, -1), (2, 0), (3, -1)}}, east := ∅, south := ∅, west := ∅ }), (.bend
  (.northwest)
  (.red), { north := {{(2, -1), (1, -1), (2, 0)}}, east := ∅, south := ∅, west := ∅ }), (.bend
  (.northwest)
  (.green), { north := ∅, east := ∅, south := ∅, west := ∅ }), (.bend
  (.northwest)
  (.green), { north := {{(3, -1), (3, 0), (4, -1)}}, east := ∅, south := ∅, west := {{(0, 2), (-1, 2), (0, 3)}} }), (.bend
  (.northwest)
  (.green), { north := {{(3, -1), (2, -1), (3, 0)}}, east := ∅, south := ∅, west := {{(0, 2), (-1, 2), (0, 3)}} }), (.bend
  (.northwest)
  (.blue), { north := {{(2, 0), (3, 0), (2, -1)}}, east := ∅, south := ∅, west := {{(-1, 3), (0, 3), (-1, 2)}} }), (.bend
  (.northwest)
  (.blue), { north := {{(2, 0), (3, 0), (2, -1)}}, east := ∅, south := ∅, west := {{(-1, 3), (-1, 4), (0, 3)}} }), (.bend
  (.northwest)
  (.blue), { north := ∅, east := ∅, south := ∅, west := ∅ }), (.bend
  (.southeast)
  (.red), { north := ∅, east := ∅, south := {{(2, -1), (1, -1), (2, 0)}}, west := ∅ }), (.bend
  (.southeast)
  (.red), { north := ∅, east := {{(-1, 2), (0, 2), (-1, 1)}}, south := ∅, west := ∅ }), (.bend
  (.southeast)
  (.green), { north := ∅, east := ∅, south := ∅, west := ∅ }), (.bend
  (.southeast)
  (.green), { north := ∅, east := {{(0, 2), (-1, 2), (0, 3)}}, south := {{(3, -1), (2, -1), (3, 0)}}, west := ∅ }), (.bend
  (.southeast)
  (.green), { north := ∅, east := {{(0, 2), (0, 1), (-1, 2)}}, south := {{(3, -1), (2, -1), (3, 0)}}, west := ∅ }), (.bend
  (.southeast)
  (.blue), { north := ∅, east := ∅, south := ∅, west := ∅ }), (.bend
  (.southeast)
  (.blue), { north := ∅, east := {{(-1, 3), (0, 3), (-1, 2)}}, south := {{(2, 0), (3, 0), (2, -1)}}, west := ∅ }), (.bend
  (.southeast)
  (.blue), { north := ∅, east := {{(-1, 3), (0, 3), (-1, 2)}}, south := {{(2, 0), (2, -1), (1, 0)}}, west := ∅ }), (.bend
  (.southwest)
  (.red), { north := ∅, east := ∅, south := ∅, west := ∅ }), (.bend
  (.southwest)
  (.red), { north := ∅, east := ∅, south := {{(2, -1), (2, 0), (3, -1)}}, west := {{(-1, 2), (0, 2), (-1, 1)}} }), (.bend
  (.southwest)
  (.red), { north := ∅, east := ∅, south := {{(2, -1), (2, 0), (3, -1)}}, west := {{(-1, 2), (-1, 3), (0, 2)}} }), (.bend
  (.southwest)
  (.green), { north := ∅, east := ∅, south := ∅, west := {{(0, 2), (0, 1), (-1, 2)}} }), (.bend
  (.southwest)
  (.green), { north := ∅, east := ∅, south := {{(3, -1), (3, 0), (4, -1)}}, west := ∅ }), (.bend
  (.southwest)
  (.blue), { north := ∅, east := ∅, south := {{(2, 0), (3, 0), (2, -1)}}, west := ∅ }), (.bend
  (.southwest)
  (.blue), { north := ∅, east := ∅, south := {{(2, 0), (2, -1), (1, 0)}}, west := ∅ }), (.bend
  (.southwest)
  (.blue), { north := ∅, east := ∅, south := ∅, west := {{(-1, 3), (0, 3), (-1, 2)}} }), (.bend
  (.southwest)
  (.blue), { north := ∅, east := ∅, south := ∅, west := {{(-1, 3), (-1, 4), (0, 3)}} }), (.monochromaticVertex (.red), { north := ∅, east := {{(-1, 2), (-1, 3), (0, 2)}}, south := ∅, west := {{(-1, 2), (0, 2), (-1, 1)}} }), (.monochromaticVertex (.red), { north := ∅, east := {{(-1, 2), (-1, 3), (0, 2)}}, south := ∅, west := {{(-1, 2), (-1, 3), (0, 2)}} }), (.monochromaticVertex (.red), { north := {{(2, -1), (2, 0), (3, -1)}}, east := {{(-1, 2), (-1, 3), (0, 2)}}, south := ∅, west := ∅ }), (.monochromaticVertex (.red), { north := {{(2, -1), (1, -1), (2, 0)}}, east := {{(-1, 2), (-1, 3), (0, 2)}}, south := ∅, west := ∅ }), (.monochromaticVertex (.red), { north := ∅, east := ∅, south := ∅, west := ∅ }), (.monochromaticVertex (.green), { north := ∅, east := ∅, south := ∅, west := ∅ }), (.monochromaticVertex (.green), { north := {{(3, -1), (3, 0), (4, -1)}}, east := ∅, south := ∅, west := {{(0, 2), (-1, 2), (0, 3)}} }), (.monochromaticVertex (.green), { north := {{(3, -1), (2, -1), (3, 0)}}, east := ∅, south := ∅, west := {{(0, 2), (-1, 2), (0, 3)}} }), (.monochromaticVertex (.green), { north := ∅, east := {{(0, 2), (-1, 2), (0, 3)}}, south := ∅, west := {{(0, 2), (-1, 2), (0, 3)}} }), (.monochromaticVertex (.green), { north := ∅, east := {{(0, 2), (0, 1), (-1, 2)}}, south := ∅, west := {{(0, 2), (-1, 2), (0, 3)}} }), (.monochromaticVertex (.blue), { north := {{(2, 0), (3, 0), (2, -1)}}, east := {{(-1, 3), (-1, 4), (0, 3)}}, south := ∅, west := {{(-1, 3), (0, 3), (-1, 2)}} }), (.monochromaticVertex (.blue), { north := {{(2, 0), (3, 0), (2, -1)}}, east := {{(-1, 3), (-1, 4), (0, 3)}}, south := ∅, west := {{(-1, 3), (-1, 4), (0, 3)}} }), (.monochromaticVertex (.blue), { north := {{(2, 0), (3, 0), (2, -1)}}, east := ∅, south := ∅, west := ∅ }), (.monochromaticVertex (.blue), { north := ∅, east := {{(-1, 3), (-1, 4), (0, 3)}}, south := ∅, west := ∅ }), (.trichromaticVertex (.blueRedGreen), { north := ∅, east := ∅, south := ∅, west := ∅ }), (.trichromaticVertex (.blueRedGreen), { north := {{(2, -1), (2, 0), (3, -1)}}, east := {{(0, 2), (-1, 2), (0, 3)}}, south := ∅, west := {{(-1, 3), (0, 3), (-1, 2)}} }), (.trichromaticVertex (.blueRedGreen), { north := {{(2, -1), (2, 0), (3, -1)}}, east := {{(0, 2), (0, 1), (-1, 2)}}, south := ∅, west := {{(-1, 3), (0, 3), (-1, 2)}} }), (.trichromaticVertex (.blueRedGreen), { north := {{(2, -1), (2, 0), (3, -1)}}, east := {{(0, 2), (-1, 2), (0, 3)}}, south := ∅, west := {{(-1, 3), (-1, 4), (0, 3)}} }), (.trichromaticVertex (.blueRedGreen), { north := {{(2, -1), (2, 0), (3, -1)}}, east := {{(0, 2), (0, 1), (-1, 2)}}, south := ∅, west := {{(-1, 3), (-1, 4), (0, 3)}} }), (.trichromaticVertex (.blueRedGreen), { north := {{(2, -1), (1, -1), (2, 0)}}, east := {{(0, 2), (-1, 2), (0, 3)}}, south := ∅, west := {{(-1, 3), (0, 3), (-1, 2)}} }), (.trichromaticVertex (.blueRedGreen), { north := {{(2, -1), (1, -1), (2, 0)}}, east := {{(0, 2), (0, 1), (-1, 2)}}, south := ∅, west := {{(-1, 3), (0, 3), (-1, 2)}} }), (.trichromaticVertex (.blueRedGreen), { north := {{(2, -1), (1, -1), (2, 0)}}, east := {{(0, 2), (-1, 2), (0, 3)}}, south := ∅, west := {{(-1, 3), (-1, 4), (0, 3)}} }), (.trichromaticVertex (.blueRedGreen), { north := {{(2, -1), (1, -1), (2, 0)}}, east := {{(0, 2), (0, 1), (-1, 2)}}, south := ∅, west := {{(-1, 3), (-1, 4), (0, 3)}} }), (.trichromaticVertex (.greenRedBlue), { north := {{(2, -1), (2, 0), (3, -1)}}, east := ∅, south := ∅, west := ∅ }), (.trichromaticVertex (.greenRedBlue), { north := {{(2, -1), (1, -1), (2, 0)}}, east := ∅, south := ∅, west := ∅ }), (.trichromaticVertex (.greenRedBlue), { north := ∅, east := {{(-1, 3), (-1, 4), (0, 3)}}, south := ∅, west := {{(0, 2), (-1, 2), (0, 3)}} })}
  | .I => {(.blank, { north := ∅, east := ∅, south := ∅, west := ∅ }), (.wire
  (.horizontal)
  (.red), { north := ∅, east := ∅, south := ∅, west := ∅ }), (.wire
  (.horizontal)
  (.red), { north := ∅, east := {{(0, 4), (-1, 4), (-2, 4)}}, south := ∅, west := {{(0, 4), (-1, 4), (-2, 4)}} }), (.wire
  (.horizontal)
  (.green), { north := ∅, east := {{(1, 4), (0, 4), (-1, 4)}}, south := ∅, west := {{(1, 4), (0, 4), (-1, 4)}} }), (.wire
  (.horizontal)
  (.green), { north := ∅, east := ∅, south := ∅, west := ∅ }), (.wire
  (.horizontal)
  (.blue), { north := ∅, east := {{(0, 4), (-1, 4), (-2, 4)}}, south := ∅, west := {{(0, 4), (-1, 4), (-2, 4)}} }), (.wire
  (.horizontal)
  (.blue), { north := ∅, east := {{(1, 4), (0, 4), (-1, 4)}}, south := ∅, west := {{(1, 4), (0, 4), (-1, 4)}} }), (.wire
  (.vertical)
  (.red), { north := {{(3, 0), (3, -1), (3, -2)}}, east := ∅, south := {{(3, 0), (3, -1), (3, -2)}}, west := ∅ }), (.wire
  (.vertical)
  (.red), { north := {{(3, 1), (3, 0), (3, -1)}}, east := ∅, south := {{(3, 1), (3, 0), (3, -1)}}, west := ∅ }), (.wire
  (.vertical)
  (.red), { north := ∅, east := ∅, south := ∅, west := ∅ }), (.wire
  (.vertical)
  (.green), { north := {{(2, 0), (2, -1), (2, -2)}}, east := ∅, south := {{(2, 0), (2, -1), (2, -2)}}, west := ∅ }), (.wire
  (.vertical)
  (.green), { north := {{(2, 1), (2, 0), (2, -1)}}, east := ∅, south := {{(2, 1), (2, 0), (2, -1)}}, west := ∅ }), (.wire
  (.vertical)
  (.green), { north := ∅, east := ∅, south := ∅, west := ∅ }), (.wire
  (.vertical)
  (.blue), { north := {{(1, 0), (1, -1), (1, -2)}}, east := ∅, south := {{(1, 0), (1, -1), (1, -2)}}, west := ∅ }), (.wire
  (.vertical)
  (.blue), { north := {{(1, 1), (1, 0), (1, -1)}}, east := ∅, south := {{(1, 1), (1, 0), (1, -1)}}, west := ∅ }), (.wire
  (.vertical)
  (.blue), { north := ∅, east := ∅, south := ∅, west := ∅ }), (.bend
  (.northeast)
  (.red), { north := {{(3, 0), (3, -1), (3, -2)}}, east := ∅, south := ∅, west := ∅ }), (.bend
  (.northeast)
  (.red), { north := {{(3, 1), (3, 0), (3, -1)}}, east := {{(0, 4), (-1, 4), (-2, 4)}}, south := ∅, west := ∅ }), (.bend
  (.northeast)
  (.green), { north := {{(2, 0), (2, -1), (2, -2)}}, east := {{(1, 4), (0, 4), (-1, 4)}}, south := ∅, west := ∅ }), (.bend
  (.northeast)
  (.green), { north := {{(2, 1), (2, 0), (2, -1)}}, east := ∅, south := ∅, west := ∅ }), (.bend
  (.northeast)
  (.blue), { north := {{(1, 0), (1, -1), (1, -2)}}, east := {{(0, 4), (-1, 4), (-2, 4)}}, south := ∅, west := ∅ }), (.bend
  (.northeast)
  (.blue), { north := {{(1, 1), (1, 0), (1, -1)}}, east := {{(1, 4), (0, 4), (-1, 4)}}, south := ∅, west := ∅ }), (.bend
  (.northwest)
  (.red), { north := {{(3, 0), (3, -1), (3, -2)}}, east := ∅, south := ∅, west := {{(0, 4), (-1, 4), (-2, 4)}} }), (.bend
  (.northwest)
  (.red), { north := {{(3, 1), (3, 0), (3, -1)}}, east := ∅, south := ∅, west := ∅ }), (.bend
  (.northwest)
  (.green), { north := {{(2, 0), (2, -1), (2, -2)}}, east := ∅, south := ∅, west := ∅ }), (.bend
  (.northwest)
  (.green), { north := {{(2, 1), (2, 0), (2, -1)}}, east := ∅, south := ∅, west := {{(1, 4), (0, 4), (-1, 4)}} }), (.bend
  (.northwest)
  (.blue), { north := {{(1, 0), (1, -1), (1, -2)}}, east := ∅, south := ∅, west := {{(1, 4), (0, 4), (-1, 4)}} }), (.bend
  (.northwest)
  (.blue), { north := {{(1, 1), (1, 0), (1, -1)}}, east := ∅, south := ∅, west := {{(0, 4), (-1, 4), (-2, 4)}} }), (.bend
  (.southeast)
  (.red), { north := ∅, east := ∅, south := {{(3, 1), (3, 0), (3, -1)}}, west := ∅ }), (.bend
  (.southeast)
  (.red), { north := ∅, east := {{(0, 4), (-1, 4), (-2, 4)}}, south := {{(3, 0), (3, -1), (3, -2)}}, west := ∅ }), (.bend
  (.southeast)
  (.green), { north := ∅, east := {{(1, 4), (0, 4), (-1, 4)}}, south := {{(2, 1), (2, 0), (2, -1)}}, west := ∅ }), (.bend
  (.southeast)
  (.green), { north := ∅, east := ∅, south := {{(2, 0), (2, -1), (2, -2)}}, west := ∅ }), (.bend
  (.southeast)
  (.blue), { north := ∅, east := {{(0, 4), (-1, 4), (-2, 4)}}, south := {{(1, 1), (1, 0), (1, -1)}}, west := ∅ }), (.bend
  (.southeast)
  (.blue), { north := ∅, east := {{(1, 4), (0, 4), (-1, 4)}}, south := {{(1, 0), (1, -1), (1, -2)}}, west := ∅ }), (.bend
  (.southwest)
  (.red), { north := ∅, east := ∅, south := {{(3, 1), (3, 0), (3, -1)}}, west := {{(0, 4), (-1, 4), (-2, 4)}} }), (.bend
  (.southwest)
  (.red), { north := ∅, east := ∅, south := {{(3, 0), (3, -1), (3, -2)}}, west := ∅ }), (.bend
  (.southwest)
  (.green), { north := ∅, east := ∅, south := {{(2, 0), (2, -1), (2, -2)}}, west := {{(1, 4), (0, 4), (-1, 4)}} }), (.bend
  (.southwest)
  (.green), { north := ∅, east := ∅, south := {{(2, 1), (2, 0), (2, -1)}}, west := ∅ }), (.bend
  (.southwest)
  (.blue), { north := ∅, east := ∅, south := {{(1, 0), (1, -1), (1, -2)}}, west := {{(0, 4), (-1, 4), (-2, 4)}} }), (.bend
  (.southwest)
  (.blue), { north := ∅, east := ∅, south := {{(1, 1), (1, 0), (1, -1)}}, west := {{(1, 4), (0, 4), (-1, 4)}} }), (.monochromaticVertex (.red), { north := {{(3, 0), (3, -1), (3, -2)}}, east := {{(0, 4), (-1, 4), (-2, 4)}}, south := ∅, west := {{(0, 4), (-1, 4), (-2, 4)}} }), (.monochromaticVertex (.red), { north := {{(3, 0), (3, -1), (3, -2)}}, east := {{(1, 4), (0, 4), (-1, 4)}}, south := ∅, west := {{(1, 4), (0, 4), (-1, 4)}} }), (.monochromaticVertex (.red), { north := {{(3, 0), (3, -1), (3, -2)}}, east := ∅, south := ∅, west := ∅ }), (.monochromaticVertex (.red), { north := {{(3, 1), (3, 0), (3, -1)}}, east := {{(0, 4), (-1, 4), (-2, 4)}}, south := ∅, west := ∅ }), (.monochromaticVertex (.green), { north := {{(2, 0), (2, -1), (2, -2)}}, east := {{(0, 4), (-1, 4), (-2, 4)}}, south := ∅, west := {{(0, 4), (-1, 4), (-2, 4)}} }), (.monochromaticVertex (.green), { north := {{(2, 0), (2, -1), (2, -2)}}, east := {{(1, 4), (0, 4), (-1, 4)}}, south := ∅, west := {{(1, 4), (0, 4), (-1, 4)}} }), (.monochromaticVertex (.green), { north := {{(2, 0), (2, -1), (2, -2)}}, east := ∅, south := ∅, west := ∅ }), (.monochromaticVertex (.green), { north := {{(2, 1), (2, 0), (2, -1)}}, east := ∅, south := ∅, west := {{(1, 4), (0, 4), (-1, 4)}} }), (.monochromaticVertex (.blue), { north := {{(1, 0), (1, -1), (1, -2)}}, east := {{(0, 4), (-1, 4), (-2, 4)}}, south := ∅, west := {{(0, 4), (-1, 4), (-2, 4)}} }), (.monochromaticVertex (.blue), { north := {{(1, 0), (1, -1), (1, -2)}}, east := {{(1, 4), (0, 4), (-1, 4)}}, south := ∅, west := {{(1, 4), (0, 4), (-1, 4)}} }), (.monochromaticVertex (.blue), { north := {{(1, 0), (1, -1), (1, -2)}}, east := ∅, south := ∅, west := ∅ }), (.monochromaticVertex (.blue), { north := {{(1, 1), (1, 0), (1, -1)}}, east := {{(1, 4), (0, 4), (-1, 4)}}, south := ∅, west := {{(0, 4), (-1, 4), (-2, 4)}} }), (.trichromaticVertex (.blueRedGreen), { north := {{(3, 0), (3, -1), (3, -2)}}, east := ∅, south := ∅, west := {{(0, 4), (-1, 4), (-2, 4)}} }), (.trichromaticVertex (.blueRedGreen), { north := {{(3, 1), (3, 0), (3, -1)}}, east := {{(0, 4), (-1, 4), (-2, 4)}}, south := ∅, west := {{(0, 4), (-1, 4), (-2, 4)}} }), (.trichromaticVertex (.blueRedGreen), { north := {{(3, 1), (3, 0), (3, -1)}}, east := {{(1, 4), (0, 4), (-1, 4)}}, south := ∅, west := {{(1, 4), (0, 4), (-1, 4)}} }), (.trichromaticVertex (.blueRedGreen), { north := {{(3, 1), (3, 0), (3, -1)}}, east := ∅, south := ∅, west := ∅ }), (.trichromaticVertex (.greenRedBlue), { north := {{(3, 0), (3, -1), (3, -2)}}, east := {{(1, 4), (0, 4), (-1, 4)}}, south := ∅, west := {{(1, 4), (0, 4), (-1, 4)}} }), (.trichromaticVertex (.greenRedBlue), { north := {{(3, 1), (3, 0), (3, -1)}}, east := {{(0, 4), (-1, 4), (-2, 4)}}, south := ∅, west := ∅ })}

/-- The materialized tables are exactly the supported geometric tables. -/
theorem cachedSupportedCellPortTable_eq (tromino : Tromino) :
    cachedSupportedCellPortTable tromino = supportedCellPortTable tromino := by
  cases tromino <;> decide +kernel

/-- Configurations supported at one specified L-gadget cell type. -/
abbrev LSupportedConfiguration (cellType : OrthogonalCellType) :=
  { configuration : PortConfiguration //
    (cellType, configuration) ∈ supportedCellPortTable .L }

instance (cellType : OrthogonalCellType) : Fintype (LSupportedConfiguration cellType) :=
  Fintype.ofFinset
    (((cachedSupportedCellPortTable .L).filter
      (fun entry => entry.1 = cellType)).image Prod.snd) (by
    intro configuration
    rw [← cachedSupportedCellPortTable_eq .L]
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨entry, ⟨member, typeEq⟩, configurationEq⟩
      have entryEq : entry = (cellType, configuration) :=
        Prod.ext typeEq configurationEq
      rw [entryEq] at member
      exact member
    · intro member
      exact ⟨(cellType, configuration), ⟨member, rfl⟩, rfl⟩)

end LeanTrominoes.Gadget
