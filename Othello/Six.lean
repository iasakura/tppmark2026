import Othello.Six.Black
import Othello.Six.White

/-!
# Problem 2: 6 × 6 Othello

From the standard initial position of 6 × 6 Othello, White (the second
player) wins 20–16 under optimal play: White can secure a win by 4 discs, and
Black can make sure not to lose by more.

The two game-tree searches behind this theorem (`search_black6`,
`search_white6`) are far too large for the Lean kernel; they are run as
compiled code by `native_decide`.  Hence these theorems depend on the axiom
`Lean.ofReduceBool` (trust in the Lean compiler), in addition to the three
standard axioms.
-/

namespace Othello

/-- **Problem 2.**  The result of 6 × 6 Othello under optimal play: Black has
4 discs fewer than White (16–20). -/
theorem othello_6x6 : OptimalResult 6 (initial 3) .black (-4) :=
  ⟨black_secures_6x6, white_secures_6x6⟩

/-- In particular, White wins 6 × 6 Othello. -/
theorem white_wins_6x6 : Secures 6 .white 1 (initial 3) .black :=
  white_secures_6x6.mono (by decide)

end Othello
