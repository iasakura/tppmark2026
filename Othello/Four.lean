import Othello.Search

/-!
# Problem 1: 4 × 4 Othello

From the standard initial position of 4 × 4 Othello, White (the second
player) wins under optimal play.  More precisely, the result under optimal
play is 3–11: White wins by 8.

All computations in this file are checked by the Lean kernel (`decide +kernel`);
no compiler is trusted.
-/

namespace Othello

/-- One mask per square of the 4 × 4 board. -/
def masks4 : List UInt64 :=
  [0x1, 0x2, 0x4, 0x8,
   0x100, 0x200, 0x400, 0x800,
   0x10000, 0x20000, 0x40000, 0x80000,
   0x1000000, 0x2000000, 0x4000000, 0x8000000]

/-- All squares of the 4 × 4 board. -/
def mask4 : UInt64 := 0x0F0F0F0F

/-- The discs of Black / White in the initial position. -/
def black4 : UInt64 := 0x20400
def white4 : UInt64 := 0x40200

theorem masks4_eq : masks4 = sqMasks 4 := by decide +kernel

theorem mask4_eq : mask4 = boardMask 4 := by decide +kernel

theorem mem_mask4 (i : Int) : Mem mask4 i ↔ Valid 4 i := by
  rw [mask4_eq]; exact mem_boardMask (by decide) i

theorem repr_initial4 : Repr 4 black4 white4 (initial 2) .black :=
  repr_of_check (by decide) (by decide +kernel)

/-- The search (run by the kernel) finds a strategy for White that wins by 8. -/
theorem search_white4 :
    BB.secOp false masks4 mask4 4 8 60 Hint.none black4 white4 = true := by
  set_option maxHeartbeats 0 in
  decide +kernel

/-- The search (run by the kernel) finds a strategy for Black that loses by
no more than 8. -/
theorem search_black4 :
    BB.secMe false masks4 mask4 4 (-8) 60 Hint.none black4 white4 = true := by
  set_option maxHeartbeats 0 in
  decide +kernel

/-- White can secure a win by 8 discs. -/
theorem white_secures_4x4 : Secures 4 .white 8 (initial 2) .black :=
  (sec_sound (n := 4) (by decide) masks4_eq mem_mask4 false nofun 4 8 60 Hint.none
    black4 white4 (initial 2) .black repr_initial4).2 search_white4

/-- Black can secure a loss by no more than 8 discs. -/
theorem black_secures_4x4 : Secures 4 .black (-8) (initial 2) .black :=
  (sec_sound (n := 4) (by decide) masks4_eq mem_mask4 false nofun 4 (-8) 60 Hint.none
    black4 white4 (initial 2) .black repr_initial4).1 search_black4

/-- **Problem 1.**  In 4 × 4 Othello, White (the second player) wins under
optimal play: White has a strategy which guarantees, whatever Black does,
that the game ends with more white discs than black discs. -/
theorem white_wins_4x4 : Secures 4 .white 1 (initial 2) .black :=
  white_secures_4x4.mono (by decide)

/-- The result of 4 × 4 Othello under optimal play: Black has 8 discs fewer
than White (the final score is 3–11). -/
theorem othello_4x4 : OptimalResult 4 (initial 2) .black (-8) :=
  ⟨black_secures_4x4, white_secures_4x4⟩

end Othello
