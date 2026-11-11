import Othello.HintParse
import Othello.Six.Hints

/-!
# 6 × 6 Othello: the initial position on bitboards
-/

namespace Othello

/-- One mask per square of the 6 × 6 board. -/
def masks6 : List UInt64 :=
  [0x1, 0x2, 0x4, 0x8, 0x10, 0x20,
   0x100, 0x200, 0x400, 0x800, 0x1000, 0x2000,
   0x10000, 0x20000, 0x40000, 0x80000, 0x100000, 0x200000,
   0x1000000, 0x2000000, 0x4000000, 0x8000000, 0x10000000, 0x20000000,
   0x100000000, 0x200000000, 0x400000000, 0x800000000, 0x1000000000, 0x2000000000,
   0x10000000000, 0x20000000000, 0x40000000000, 0x80000000000, 0x100000000000, 0x200000000000]

/-- All squares of the 6 × 6 board. -/
def mask6 : UInt64 := 0x3F3F3F3F3F3F

/-- The discs of Black / White in the initial position. -/
def black6 : UInt64 := 0x4080000
def white6 : UInt64 := 0x8040000

theorem masks6_eq : masks6 = sqMasks 6 := by decide +kernel

theorem mask6_eq : mask6 = boardMask 6 := by decide +kernel

theorem mem_mask6 (i : Int) : Mem mask6 i ↔ Valid 6 i := by
  rw [mask6_eq]; exact mem_boardMask (by decide) i

theorem repr_initial6 : Repr 6 black6 white6 (initial 3) .black :=
  repr_of_check (by decide) (by decide +kernel)

end Othello
