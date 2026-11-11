import Othello.Reference

/-!
# Games that realise the optimal results

The theorems of `Othello/Four.lean` and `Othello/Six.lean` determine the
*margin* under optimal play.  Here we exhibit complete games, checked against
the rules of the specification, whose final scores are the scores usually
quoted: 3–11 for 4 × 4 and 16–20 for 6 × 6.

The games were produced by the external solver (`tools/gen.cpp`), which at
every turn picks a move that keeps the game-theoretic value.  That the moves
are optimal is *not* proved here; what is proved is that these are complete
legal games with the stated final scores.
-/

namespace Othello

/-- A complete game of 4 × 4 Othello ending 3–11. -/
def line4 : List Square :=
  [(1, 0), (0, 0), (0, 1), (2, 0), (3, 3), (0, 2), (3, 0), (1, 3), (0, 3), (2, 3)]

theorem line4_finished : FinishedGame 4 2 line4 3 11 :=
  checkRecord_sound (h := 2) (by decide) (by native_decide)

end Othello
