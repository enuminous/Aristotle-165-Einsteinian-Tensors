import Mathlib

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace FieldSpaceCheck

/-- The 11 sectors, in the source order `E, M, S, F, W, T, I, R, H, P, A`. -/
inductive Sector
  | E | M | S | F | W | T | I | R | H | P | A
  deriving DecidableEq, Fintype, Repr

open Sector

/-- Sector kinds: gravity `E`, gauge `M, S`, and eight scalar sectors. -/
def isGauge (s : Sector) : Bool := s = M || s = S
def isScalar (s : Sector) : Bool := !(s = E) && !isGauge s

/-- The atlas: every 3-element set of sectors. -/
def triplets : Finset (Finset Sector) := Finset.univ.powersetCard 3

end FieldSpaceCheck
