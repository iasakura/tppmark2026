import Othello.Refine

/-!
# A verified game-tree search

`BB.secMe` / `BB.secOp` search the game tree on bitboards.  They are the two
halves of an alpha-beta search with a null window: every node is either an
"or" node (one good move is enough) or an "and" node (all moves must be
answered), so no numeric bounds have to be passed around.

`sec_sound` proves that a successful search yields a strategy in the sense of
the specification (`Secures`).  The search also takes *hints* and uses a
move-ordering heuristic; both only influence the order in which moves are
tried, and the soundness theorem holds whatever they are.
-/

namespace Othello

/-- Hints for the search: a list of moves (bit numbers) to try first in the
current position, each with hints for the position after that move.
`par` is like `node` but additionally asks for the listed moves to be examined
in parallel (this is only done at "and" nodes). -/
inductive Hint where
  | node (children : List (UInt64 × Hint))
  | par (children : List (UInt64 × Hint))

namespace Hint

/-- No hints. -/
def none : Hint := .node []

end Hint

namespace BB

/-! ## Iterating over moves -/

/-- Does `k` hold for some bit of `mv`?  (`fuel` bounds the number of bits.) -/
@[specialize] def anyBit (k : UInt64 → Bool) : Nat → UInt64 → Bool
  | 0, _ => false
  | fuel + 1, mv =>
    if mv = 0 then false
    else
      let i := mv.log2
      let m := (1 : UInt64) <<< i
      if mv &&& m = 0 then false
      else k i || anyBit k fuel (mv ^^^ m)

/-- Does `k` hold for all bits of `mv`?  (`false` if `fuel` runs out.) -/
@[specialize] def allBit (k : UInt64 → Bool) : Nat → UInt64 → Bool
  | 0, _ => false
  | fuel + 1, mv =>
    if mv = 0 then true
    else
      let i := mv.log2
      let m := (1 : UInt64) <<< i
      if mv &&& m = 0 then false
      else k i && allBit k fuel (mv ^^^ m)

/-- Does `k` hold for some bit of `mv`?  The candidates `cs` are tried first,
in order, then the remaining bits. -/
@[specialize] def anyCand (k : UInt64 → Hint → Bool) : List (UInt64 × Hint) → UInt64 → Bool
  | [], mv => anyBit (fun i => k i Hint.none) 64 mv
  | (i, h) :: cs, mv =>
    let m := (1 : UInt64) <<< i
    if mv &&& m = 0 then anyCand k cs mv
    else k i h || anyCand k cs (mv ^^^ m)

/-- Does `k` hold for all bits of `mv`?  The candidates `cs` are tried first,
in order, then the remaining bits. -/
@[specialize] def allCand (k : UInt64 → Hint → Bool) : List (UInt64 × Hint) → UInt64 → Bool
  | [], mv => allBit (fun i => k i Hint.none) 64 mv
  | (i, h) :: cs, mv =>
    let m := (1 : UInt64) <<< i
    if mv &&& m = 0 then allCand k cs mv
    else k i h && allCand k cs (mv ^^^ m)

/-- Like `allCand`, but the candidates are examined in parallel tasks
(collected in `ts`), whose results are awaited at the end. -/
@[specialize] def allCandPar (k : UInt64 → Hint → Bool) :
    List (UInt64 × Hint) → UInt64 → List (Task Bool) → Bool
  | [], mv, ts => ts.all Task.get && allBit (fun i => k i Hint.none) 64 mv
  | (i, h) :: cs, mv, ts =>
    let m := (1 : UInt64) <<< i
    if mv &&& m = 0 then allCandPar k cs mv ts
    else allCandPar k cs (mv ^^^ m) (Task.spawn (fun _ => k i h) :: ts)

/-! ## Move ordering (not trusted: any order is sound) -/

/-- Number of set bits, by the usual bit-parallel method.  It is used by the
ordering heuristic and, when the search is run with `fast := true`, to count
the discs at the end of the game. -/
def popcount (x : UInt64) : UInt64 :=
  let m1 : UInt64 := 0x5555555555555555
  let m2 : UInt64 := 0x3333333333333333
  let m4 : UInt64 := 0x0f0f0f0f0f0f0f0f
  let h1 : UInt64 := 0x0101010101010101
  let a : UInt64 := x - ((x >>> 1) &&& m1)
  let b : UInt64 := (a &&& m2) + ((a >>> 2) &&& m2)
  let c : UInt64 := (b + (b >>> 4)) &&& m4
  (c * h1) >>> 56

/-- Insert a move into a list sorted by increasing key. -/
def insertKey (key i : UInt64) : List (UInt64 × UInt64) → List (UInt64 × UInt64)
  | [] => [(key, i)]
  | (k', i') :: l =>
    if key ≤ k' then (key, i) :: (k', i') :: l else (k', i') :: insertKey key i l

/-- The moves of `mv`, sorted by the number of replies they leave to the
opponent ("fastest first"). -/
def sortMoves (mask me opp : UInt64) : Nat → UInt64 → List (UInt64 × UInt64) →
    List (UInt64 × UInt64)
  | 0, _, acc => acc
  | fuel + 1, mv, acc =>
    if mv = 0 then acc
    else
      let i := mv.log2
      let m := (1 : UInt64) <<< i
      let f := flips me opp m
      let key := popcount (mobility mask (opp ^^^ f) (me ||| m ||| f))
      sortMoves mask me opp fuel (mv &&& ~~~m) (insertKey key i acc)

/-- The candidate moves to try first: the hinted ones if there are hints;
otherwise, when at least `ordMin` squares are empty, all moves sorted
"fastest first"; otherwise none (the moves are then tried in bit order). -/
def order (ordMin : UInt64) (h : Hint) (mask me opp mv : UInt64) : List (UInt64 × Hint) :=
  match h with
  | .node (c :: cs) => c :: cs
  | .par (c :: cs) => c :: cs
  | _ =>
    if ordMin ≤ popcount (mask ^^^ (me ||| opp)) then
      (sortMoves mask me opp 64 mv []).map fun p => (p.2, Hint.none)
    else []

/-- The margin of a finished game for the player to move: with `fast := false`
by `margin` (a loop over the squares, convenient for kernel evaluation), with
`fast := true` by `popcount`. -/
@[inline] def finalMargin (fast : Bool) (ms : List UInt64) (me opp : UInt64) : Int :=
  if fast then ((popcount me).toNat : Int) - ((popcount opp).toNat : Int)
  else margin ms me opp

/-! ## The search -/

mutual

/-- `secMe fast ms mask ordMin t fuel h me opp = true` only if the player to
move can secure a margin of at least `t`. -/
def secMe (fast : Bool) (ms : List UInt64) (mask ordMin : UInt64) (t : Int) :
    Nat → Hint → UInt64 → UInt64 → Bool
  | 0, _, _, _ => false
  | fuel + 1, h, me, opp =>
    let mv := mobility mask me opp
    if mv = 0 then
      if mobility mask opp me = 0 then decide (t ≤ finalMargin fast ms me opp)
      else secOp fast ms mask ordMin t fuel h opp me
    else
      anyCand (fun i h' =>
          let m := (1 : UInt64) <<< i
          let f := flips me opp m
          secOp fast ms mask ordMin t fuel h' (opp ^^^ f) (me ||| m ||| f))
        (order ordMin h mask me opp mv) mv

/-- `secOp fast ms mask ordMin t fuel h me opp = true` only if the player who
is *not* to move can secure a margin of at least `t`. -/
def secOp (fast : Bool) (ms : List UInt64) (mask ordMin : UInt64) (t : Int) :
    Nat → Hint → UInt64 → UInt64 → Bool
  | 0, _, _, _ => false
  | fuel + 1, h, me, opp =>
    let mv := mobility mask me opp
    if mv = 0 then
      if mobility mask opp me = 0 then decide (t ≤ finalMargin fast ms opp me)
      else secMe fast ms mask ordMin t fuel h opp me
    else
      match h with
      | .par cs =>
        allCandPar (fun i h' =>
            let m := (1 : UInt64) <<< i
            let f := flips me opp m
            secMe fast ms mask ordMin t fuel h' (opp ^^^ f) (me ||| m ||| f))
          cs mv []
      | _ =>
        allCand (fun i h' =>
            let m := (1 : UInt64) <<< i
            let f := flips me opp m
            secMe fast ms mask ordMin t fuel h' (opp ^^^ f) (me ||| m ||| f))
          (order ordMin h mask me opp mv) mv

end

end BB

/-! ## Soundness of the iteration over moves -/

/-- The bit number denoted by `i`. -/
def bitNo (i : UInt64) : Int := ((i.toNat % 64 : Nat) : Int)

theorem mem_bit {i : UInt64} {j : Int} : Mem ((1 : UInt64) <<< i) j ↔ j = bitNo i :=
  mem_one_shl

theorem mem_of_and_bit_ne_zero {mv i : UInt64} (h : ¬ mv &&& ((1 : UInt64) <<< i) = 0) :
    Mem mv (bitNo i) := by
  obtain ⟨j, hj⟩ := ne_zero_iff.1 h
  rw [mem_and, mem_bit] at hj
  rw [← hj.2]; exact hj.1

theorem mem_of_mem_xor_bit {mv i : UInt64} {j : Int}
    (h : ¬ mv &&& ((1 : UInt64) <<< i) = 0) (hj : Mem (mv ^^^ ((1 : UInt64) <<< i)) j) :
    Mem mv j := by
  rw [mem_xor] at hj
  rcases hj with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact h1
  · rw [mem_bit] at h2
    rw [h2] at h1
    exact absurd (mem_of_and_bit_ne_zero h) h1

theorem mem_xor_bit_of_ne {mv i : UInt64} {j : Int} (hj : Mem mv j) (hne : j ≠ bitNo i) :
    Mem (mv ^^^ ((1 : UInt64) <<< i)) j := by
  rw [mem_xor]
  exact Or.inl ⟨hj, fun h => hne (mem_bit.1 h)⟩

theorem anyBit_sound {k : UInt64 → Bool} :
    ∀ (fuel : Nat) (mv : UInt64), BB.anyBit k fuel mv = true →
      ∃ i : UInt64, Mem mv (bitNo i) ∧ k i = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro mv h
    simp [BB.anyBit] at h
  | succ fuel ih =>
    intro mv h
    simp only [BB.anyBit] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i hne
        rw [Bool.or_eq_true] at h
        rcases h with h | h
        · exact ⟨mv.log2, mem_of_and_bit_ne_zero hne, h⟩
        · obtain ⟨i, hi, hk⟩ := ih _ h
          exact ⟨i, mem_of_mem_xor_bit hne hi, hk⟩

theorem allBit_sound {k : UInt64 → Bool} :
    ∀ (fuel : Nat) (mv : UInt64), BB.allBit k fuel mv = true →
      ∀ j, Mem mv j → ∃ i : UInt64, j = bitNo i ∧ k i = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro mv h
    simp [BB.allBit] at h
  | succ fuel ih =>
    intro mv h j hj
    simp only [BB.allBit] at h
    split at h
    · rename_i hz
      rw [hz] at hj
      exact absurd hj (not_mem_zero j)
    · split at h
      · cases h
      · rw [Bool.and_eq_true] at h
        by_cases hji : j = bitNo mv.log2
        · exact ⟨mv.log2, hji, h.1⟩
        · exact ih _ h.2 j (mem_xor_bit_of_ne hj hji)

theorem anyCand_sound {k : UInt64 → Hint → Bool} :
    ∀ (cs : List (UInt64 × Hint)) (mv : UInt64), BB.anyCand k cs mv = true →
      ∃ (i : UInt64) (h : Hint), Mem mv (bitNo i) ∧ k i h = true := by
  intro cs
  induction cs with
  | nil =>
    intro mv h
    simp only [BB.anyCand] at h
    obtain ⟨i, hi, hk⟩ := anyBit_sound _ _ h
    exact ⟨i, Hint.none, hi, hk⟩
  | cons c cs ih =>
    intro mv h
    obtain ⟨i, hh⟩ := c
    simp only [BB.anyCand] at h
    split at h
    · exact ih _ h
    · rename_i hne
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · exact ⟨i, hh, mem_of_and_bit_ne_zero hne, h⟩
      · obtain ⟨i', h', hi', hk⟩ := ih _ h
        exact ⟨i', h', mem_of_mem_xor_bit hne hi', hk⟩

theorem allCand_sound {k : UInt64 → Hint → Bool} :
    ∀ (cs : List (UInt64 × Hint)) (mv : UInt64), BB.allCand k cs mv = true →
      ∀ j, Mem mv j → ∃ (i : UInt64) (h : Hint), j = bitNo i ∧ k i h = true := by
  intro cs
  induction cs with
  | nil =>
    intro mv h j hj
    simp only [BB.allCand] at h
    obtain ⟨i, hi, hk⟩ := allBit_sound _ _ h j hj
    exact ⟨i, Hint.none, hi, hk⟩
  | cons c cs ih =>
    intro mv h j hj
    obtain ⟨i, hh⟩ := c
    simp only [BB.allCand] at h
    split at h
    · exact ih _ h j hj
    · rw [Bool.and_eq_true] at h
      by_cases hji : j = bitNo i
      · exact ⟨i, hh, hji, h.1⟩
      · exact ih _ h.2 j (mem_xor_bit_of_ne hj hji)

theorem allCandPar_sound {k : UInt64 → Hint → Bool} :
    ∀ (cs : List (UInt64 × Hint)) (mv : UInt64) (ts : List (Task Bool)),
      BB.allCandPar k cs mv ts = true →
      ∀ j, Mem mv j → ∃ (i : UInt64) (h : Hint), j = bitNo i ∧ k i h = true := by
  have key : ∀ (cs : List (UInt64 × Hint)) (mv : UInt64) (ts : List (Task Bool)),
      BB.allCandPar k cs mv ts = true →
      ts.all Task.get = true ∧
        ∀ j, Mem mv j → ∃ (i : UInt64) (h : Hint), j = bitNo i ∧ k i h = true := by
    intro cs
    induction cs with
    | nil =>
      intro mv ts h
      simp only [BB.allCandPar, Bool.and_eq_true] at h
      refine ⟨h.1, fun j hj => ?_⟩
      obtain ⟨i, hi, hk⟩ := allBit_sound _ _ h.2 j hj
      exact ⟨i, Hint.none, hi, hk⟩
    | cons c cs ih =>
      intro mv ts h
      obtain ⟨i, hh⟩ := c
      simp only [BB.allCandPar] at h
      split at h
      · exact ih _ _ h
      · obtain ⟨h1, h2⟩ := ih _ _ h
        rw [List.all_cons, Bool.and_eq_true] at h1
        refine ⟨h1.2, fun j hj => ?_⟩
        by_cases hji : j = bitNo i
        · exact ⟨i, hh, hji, h1.1⟩
        · exact h2 j (mem_xor_bit_of_ne hj hji)
  intro cs mv ts h
  exact (key cs mv ts h).2

/-! ## Soundness of the search -/

variable {n : Nat}

/-- A successful search is a strategy.  If the words `me` / `opp` represent
the board `b` with `c` to move, then

* `secMe … me opp = true` implies that `c` can secure a margin of at least `t`;
* `secOp … me opp = true` implies that the opponent of `c` can secure a margin
  of at least `t`.

This holds for all hints and whatever the ordering heuristic does.  If the
search is run with `fast := true`, the disc count by `popcount` must be known
to be correct on this board size (hypothesis `hfast`). -/
theorem sec_sound (hn : n ≤ 6) {ms : List UInt64} (hms : ms = sqMasks n)
    {mask : UInt64} (hmask : ∀ i, Mem mask i ↔ Valid n i)
    (fast : Bool)
    (hfast : fast = true → ∀ (me opp : UInt64) (b : Board) (c : Color),
      Repr n me opp b c →
      ((BB.popcount me).toNat : Int) - ((BB.popcount opp).toNat : Int) = margin n b c)
    (ordMin : UInt64) (t : Int) :
    ∀ (fuel : Nat) (h : Hint) (me opp : UInt64) (b : Board) (c : Color),
      Repr n me opp b c →
      (BB.secMe fast ms mask ordMin t fuel h me opp = true → Secures n c t b c) ∧
      (BB.secOp fast ms mask ordMin t fuel h me opp = true →
        Secures n c.opponent t b c) := by
  subst hms
  have hfinal : ∀ (me opp : UInt64) (b : Board) (c : Color), Repr n me opp b c →
      BB.finalMargin fast (sqMasks n) me opp = margin n b c := by
    intro me opp b c hr
    unfold BB.finalMargin
    split
    · rename_i hf
      exact hfast hf me opp b c hr
    · exact hr.margin_eq hn
  intro fuel
  induction fuel with
  | zero =>
    intro h me opp b c _
    constructor <;> intro hs <;> simp [BB.secMe, BB.secOp] at hs
  | succ fuel ih =>
    intro h me opp b c hr
    have hmv := mobility_eq_zero_iff hn hmask hr
    have hmv' := mobility_eq_zero_iff hn hmask hr.swap
    constructor
    · intro hs
      simp only [BB.secMe] at hs
      split at hs
      · rename_i hz
        split at hs
        · rename_i hz'
          have hle : t ≤ BB.finalMargin fast (sqMasks n) me opp := of_decide_eq_true hs
          rw [hfinal me opp b c hr] at hle
          exact .over (hmv.1 hz) (hmv'.1 hz') hle
        · rename_i hz'
          have h1 := (ih h opp me b c.opponent hr.swap).2 hs
          rw [Color.opponent_opponent] at h1
          exact .pass (hmv.1 hz) (fun h0 => hz' (hmv'.2 h0)) h1
      · obtain ⟨i, h', hi, hk⟩ := anyCand_sound _ _ hs
        obtain ⟨s, hlegal, hidx⟩ := (mem_mobility_spec hn hmask hr _).1 hi
        have hm : ∀ j, Mem ((1 : UInt64) <<< i) j ↔ j = idx s := by
          intro j; rw [mem_bit, hidx]
        have hr' := hr.play hn hlegal.1 hlegal.2.1 hm
        have h1 := (ih h' _ _ _ _ hr').2 hk
        rw [Color.opponent_opponent] at h1
        exact .choose s rfl (mem_moves.2 hlegal) h1
    · intro hs
      simp only [BB.secOp] at hs
      split at hs
      · rename_i hz
        split at hs
        · rename_i hz'
          have hle : t ≤ BB.finalMargin fast (sqMasks n) opp me := of_decide_eq_true hs
          rw [hfinal opp me b c.opponent hr.swap] at hle
          exact .over (hmv.1 hz) (hmv'.1 hz') hle
        · rename_i hz'
          have h1 := (ih h opp me b c.opponent hr.swap).1 hs
          exact .pass (hmv.1 hz) (fun h0 => hz' (hmv'.2 h0)) h1
      · rename_i hnz
        have hall : ∀ j, Mem (BB.mobility mask me opp) j →
            ∃ (i : UInt64) (h' : Hint), j = bitNo i ∧
              BB.secMe fast (sqMasks n) mask ordMin t fuel h'
                (opp ^^^ BB.flips me opp ((1 : UInt64) <<< i))
                (me ||| (1 : UInt64) <<< i ||| BB.flips me opp ((1 : UInt64) <<< i)) = true := by
          split at hs
          · exact allCandPar_sound _ _ _ hs
          · exact allCand_sound _ _ hs
        refine .reply (Color.ne_opponent c) (fun h0 => hnz (hmv.2 h0)) ?_
        intro s hsm
        have hlegal := mem_moves.1 hsm
        have hi : Mem (BB.mobility mask me opp) (idx s) :=
          (mem_mobility_spec hn hmask hr _).2 ⟨s, hlegal, rfl⟩
        obtain ⟨i, h', hidx, hk⟩ := hall _ hi
        have hm : ∀ j, Mem ((1 : UInt64) <<< i) j ↔ j = idx s := by
          intro j; rw [mem_bit, hidx]
        have hr' := hr.play hn hlegal.1 hlegal.2.1 hm
        exact (ih h' _ _ _ _ hr').1 hk

end Othello
