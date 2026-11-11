import Othello.Six.Defs

/-!
# 6 × 6 Othello: the search for Black

A computation of a few billion steps, run as compiled code (`native_decide`).
This file contains nothing else, so that it is recompiled only when the
search itself changes.
-/

namespace Othello

/-- The search finds a strategy for Black that loses by no more than 4. -/
theorem search_black6 :
    BB.secMe true masks6 mask6 5 (-4) 80 (parseHint hintBlack6) black6 white6 = true := by
  native_decide

end Othello
