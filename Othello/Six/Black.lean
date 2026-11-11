import Othello.Six.Popcount

/-!
# 6 × 6 Othello: Black can hold the loss to 4 discs
-/

namespace Othello

/-- The search finds a strategy for Black that loses by no more than 4.
This is a computation of a few billion steps; it is run as compiled code
(`native_decide`). -/
theorem search_black6 :
    BB.secMe true masks6 mask6 5 (-4) 80 (parseHint hintBlack6) black6 white6 = true := by
  native_decide

/-- Black can secure a loss by no more than 4 discs. -/
theorem black_secures_6x6 : Secures 6 .black (-4) (initial 3) .black :=
  (sec_sound (n := 6) (by decide) masks6_eq mem_mask6 true (fun _ => fast_margin6) 5 (-4) 80
    (parseHint hintBlack6) black6 white6 (initial 3) .black repr_initial6).1 search_black6

end Othello
