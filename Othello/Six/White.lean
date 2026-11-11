import Othello.Six.Popcount

/-!
# 6 × 6 Othello: White can win by 4 discs
-/

namespace Othello

/-- The search finds a strategy for White that wins by at least 4.
This is a computation of several billion steps; it is run as compiled code
(`native_decide`). -/
theorem search_white6 :
    BB.secOp true masks6 mask6 5 4 80 (parseHint hintWhite6) black6 white6 = true := by
  native_decide

/-- White can secure a win by at least 4 discs. -/
theorem white_secures_6x6 : Secures 6 .white 4 (initial 3) .black :=
  (sec_sound (n := 6) (by decide) masks6_eq mem_mask6 true (fun _ => fast_margin6) 5 4 80
    (parseHint hintWhite6) black6 white6 (initial 3) .black repr_initial6).2 search_white6

end Othello
