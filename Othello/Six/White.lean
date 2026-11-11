import Othello.Six.Defs

/-!
# 6 × 6 Othello: the search for White

A computation of some twenty billion steps, run as compiled code
(`native_decide`).  This file contains nothing else, so that it is recompiled
only when the search itself changes.
-/

namespace Othello

/-- The search finds a strategy for White that wins by at least 4. -/
theorem search_white6 :
    BB.secOp true masks6 mask6 5 4 80 (parseHint hintWhite6) black6 white6 = true := by
  native_decide

end Othello
