import Othello.Bitboard

/-!
# The bitboard move generator computes what the rules say

`Repr n me opp b c` relates a pair of words to a board `b` seen by the player
`c` who is to move.  The theorems of this file show that the bitboard
operations of `Othello/Bitboard.lean` refine the specification:

* `mem_flips_spec`    : `BB.flips` is the set of flipped discs;
* `Repr.play`         : making a move on the bitboard is `play`;
* `mem_mobility_spec` : `BB.mobility` is the set of legal moves;
* `Repr.margin_eq`    : `BB.margin` is the margin.
-/

namespace Othello

variable {n : Nat}

/-- The words `me` / `opp` hold the discs of `c` / of `c`'s opponent on the
board `b` (and nothing else). -/
structure Repr (n : Nat) (me opp : UInt64) (b : Board) (c : Color) : Prop where
  me_valid : ∀ i, Mem me i → Valid n i
  opp_valid : ∀ i, Mem opp i → Valid n i
  disjoint : ∀ i, Mem me i → ¬ Mem opp i
  me_iff : ∀ s, OnBoard n s → (b s = some c ↔ Mem me (idx s))
  opp_iff : ∀ s, OnBoard n s → (b s = some c.opponent ↔ Mem opp (idx s))

/-- Passing: the same board seen by the other player. -/
theorem Repr.swap {me opp : UInt64} {b : Board} {c : Color}
    (h : Repr n me opp b c) : Repr n opp me b c.opponent where
  me_valid := h.opp_valid
  opp_valid := h.me_valid
  disjoint := fun i hi hi' => h.disjoint i hi' hi
  me_iff := h.opp_iff
  opp_iff := by
    intro s hs
    rw [Color.opponent_opponent]
    exact h.me_iff s hs

theorem Repr.cell_me {me opp : UInt64} {b : Board} {c : Color}
    (h : Repr n me opp b c) {q : Square} :
    cell n b q = some c ↔ OnBoard n q ∧ Mem me (idx q) := by
  unfold cell
  by_cases hq : OnBoard n q
  · simp only [hq, ↓reduceIte, true_and]
    exact h.me_iff q hq
  · simp [hq]

theorem Repr.cell_opp {me opp : UInt64} {b : Board} {c : Color}
    (h : Repr n me opp b c) {q : Square} :
    cell n b q = some c.opponent ↔ OnBoard n q ∧ Mem opp (idx q) := by
  unfold cell
  by_cases hq : OnBoard n q
  · simp only [hq, ↓reduceIte, true_and]
    exact h.opp_iff q hq
  · simp [hq]

/-- A square is empty iff neither word has its bit. -/
theorem Repr.none_iff {me opp : UInt64} {b : Board} {c : Color}
    (h : Repr n me opp b c) {s : Square} (hs : OnBoard n s) :
    b s = none ↔ ¬ Mem me (idx s) ∧ ¬ Mem opp (idx s) := by
  rw [← h.me_iff s hs, ← h.opp_iff s hs]
  cases hb : b s with
  | none => simp
  | some c' =>
    simp only [reduceCtorEq, Option.some.injEq, false_iff, not_and, Classical.not_not]
    intro hne
    exact Color.eq_opponent_of_ne hne

/-! ## Rays -/

/-- Following bits of `opp` from a square of the board, one stays on the board. -/
theorem ray_onBoard (hn : n ≤ 6) {me opp : UInt64} {b : Board} {c : Color}
    (hr : Repr n me opp b c) {s : Square} {d : Int × Int}
    (hd : d ∈ directions) (hs : OnBoard n s) :
    ∀ j : Nat, (∀ j' : Nat, 1 ≤ j' → j' ≤ j → Mem opp (idx s + j' * delta d)) →
      OnBoard n (far s d j) := by
  intro j
  induction j with
  | zero =>
    intro _
    have e : far s d ((0 : Nat) : Int) = s := far_zero s d
    rw [e]; exact hs
  | succ j ih =>
    intro h
    have hj := ih (fun j' h1 h2 => h j' h1 (by omega))
    have e : ((j + 1 : Nat) : Int) = (j : Int) + 1 := by omega
    rw [e, ← step_far]
    apply onBoard_step hn hd hj
    rw [idx_far]
    have h1 := h (j + 1) (by omega) (Nat.le_refl _)
    have e2 : idx s + ((j + 1 : Nat) : Int) * delta d
        = idx s + (j : Int) * delta d + delta d := by grind
    rw [e2] at h1
    exact hr.opp_valid _ h1

/-- An outflanking line of the specification is a run of bits of `opp`
followed by a bit of `me`. -/
theorem outflank_iff (hn : n ≤ 6) {me opp : UInt64} {b : Board} {c : Color}
    (hr : Repr n me opp b c) {s : Square} {d : Int × Int}
    (hd : d ∈ directions) (hs : OnBoard n s) (j : Nat) :
    Outflank n b c s d ((j : Int) + 1) ↔
      (∀ j' : Nat, 1 ≤ j' → j' ≤ j → Mem opp (idx s + j' * delta d)) ∧
      Mem me (idx s + ((j : Int) + 1) * delta d) := by
  constructor
  · rintro ⟨hop, hc⟩
    constructor
    · intro j' h1 h2
      have h3 := (hr.cell_opp.1 (hop j' (by omega) (by omega))).2
      rwa [idx_far] at h3
    · have h3 := (hr.cell_me.1 hc).2
      rwa [idx_far] at h3
  · rintro ⟨hrun, hme⟩
    constructor
    · intro i h1 h2
      obtain ⟨k, rfl⟩ : ∃ k : Nat, i = k := ⟨i.toNat, by omega⟩
      apply hr.cell_opp.2
      refine ⟨ray_onBoard hn hr hd hs k (fun j' a b => hrun j' a (by omega)), ?_⟩
      rw [idx_far]
      exact hrun k (by omega) (by omega)
    · apply hr.cell_me.2
      have hj := ray_onBoard hn hr hd hs j hrun
      refine ⟨?_, by rw [idx_far]; exact hme⟩
      rw [← step_far]
      apply onBoard_step hn hd hj
      rw [idx_far]
      have e : idx s + (j : Int) * delta d + delta d
          = idx s + ((j : Int) + 1) * delta d := by grind
      rw [e]
      exact hr.me_valid _ hme

/-! ## Flips -/

namespace BB

/-- The discs flipped in one direction by a move on the square with bit `m`. -/
@[inline] def flipDir (sh : UInt64 → UInt64) (me opp m : UInt64) : UInt64 :=
  let x := walk sh m opp
  if sh x &&& me = 0 then 0 else x

/-- The discs flipped by a move of the player to move on the square with bit `m`. -/
def flips (me opp m : UInt64) : UInt64 :=
  flipDir (fun x => x >>> 9) me opp m ||| flipDir (fun x => x >>> 8) me opp m |||
  flipDir (fun x => x >>> 7) me opp m ||| flipDir (fun x => x >>> 1) me opp m |||
  flipDir (fun x => x <<< 1) me opp m ||| flipDir (fun x => x <<< 7) me opp m |||
  flipDir (fun x => x <<< 8) me opp m ||| flipDir (fun x => x <<< 9) me opp m

end BB

theorem isShift_of_eq {sh : UInt64 → UInt64} {δ δ' : Int} (h : IsShift sh δ) (e : δ = δ') :
    IsShift sh δ' := e ▸ h

theorem isShift_r9 : IsShift (fun x => x >>> 9) (delta (-1, -1)) :=
  isShift_of_eq (isShift_shr 9 (by decide)) (by decide)
theorem isShift_r8 : IsShift (fun x => x >>> 8) (delta (0, -1)) :=
  isShift_of_eq (isShift_shr 8 (by decide)) (by decide)
theorem isShift_r7 : IsShift (fun x => x >>> 7) (delta (1, -1)) :=
  isShift_of_eq (isShift_shr 7 (by decide)) (by decide)
theorem isShift_r1 : IsShift (fun x => x >>> 1) (delta (-1, 0)) :=
  isShift_of_eq (isShift_shr 1 (by decide)) (by decide)
theorem isShift_l1 : IsShift (fun x => x <<< 1) (delta (1, 0)) :=
  isShift_of_eq (isShift_shl 1 (by decide)) (by decide)
theorem isShift_l7 : IsShift (fun x => x <<< 7) (delta (-1, 1)) :=
  isShift_of_eq (isShift_shl 7 (by decide)) (by decide)
theorem isShift_l8 : IsShift (fun x => x <<< 8) (delta (0, 1)) :=
  isShift_of_eq (isShift_shl 8 (by decide)) (by decide)
theorem isShift_l9 : IsShift (fun x => x <<< 9) (delta (1, 1)) :=
  isShift_of_eq (isShift_shl 9 (by decide)) (by decide)

theorem mem_flipDir {sh : UInt64 → UInt64} {δ : Int} (h : IsShift sh δ)
    (me opp m : UInt64) (i : Int) :
    Mem (BB.flipDir sh me opp m) i ↔
      Chain m opp δ 4 i ∧ ∃ i', Chain m opp δ 4 i' ∧ Mem me (i' + δ) := by
  by_cases hz : sh (BB.walk sh m opp) &&& me = 0
  · simp only [BB.flipDir, hz, ↓reduceIte]
    constructor
    · intro hm
      exact absurd hm (not_mem_zero i)
    · rintro ⟨_, i', hc, hme⟩
      have h1 : Mem (sh (BB.walk sh m opp) &&& me) (i' + δ) := by
        rw [mem_and, h, mem_walk h]
        refine ⟨⟨?_, hme.nonneg, hme.lt⟩, hme⟩
        have e : i' + δ - δ = i' := by omega
        rw [e]; exact hc
      rw [hz] at h1
      exact absurd h1 (not_mem_zero _)
  · simp only [BB.flipDir, hz, ↓reduceIte]
    rw [mem_walk h]
    constructor
    · intro hc
      refine ⟨hc, ?_⟩
      obtain ⟨i'', hi''⟩ := ne_zero_iff.1 hz
      rw [mem_and, h, mem_walk h] at hi''
      refine ⟨i'' - δ, hi''.1.1, ?_⟩
      have e : i'' - δ + δ = i'' := by omega
      rw [e]; exact hi''.2
    · rintro ⟨hc, _⟩
      exact hc

/-- In one direction, the bitboard flips are the flips of the specification. -/
theorem mem_flipDir_spec (hn : n ≤ 6) {me opp : UInt64} {b : Board} {c : Color}
    (hr : Repr n me opp b c) {s : Square} {d : Int × Int}
    (hd : d ∈ directions) (hs : OnBoard n s)
    {sh : UInt64 → UInt64} (hsh : IsShift sh (delta d))
    {m : UInt64} (hm : ∀ i, Mem m i ↔ i = idx s) (i : Int) :
    Mem (BB.flipDir sh me opp m) i ↔ ∃ q, q ∈ flipsDir n b c s d ∧ idx q = i := by
  rw [mem_flipDir hsh, chain_single hm]
  constructor
  · rintro ⟨⟨j, hj1, hj4, rfl, hrun⟩, i', hc', hme⟩
    rw [chain_single hm] at hc'
    obtain ⟨j2, hj21, hj24, rfl, hrun2⟩ := hc'
    have hme' : Mem me (idx s + ((j2 : Int) + 1) * delta d) := by
      have e : idx s + (j2 : Int) * delta d + delta d
          = idx s + ((j2 : Int) + 1) * delta d := by grind
      rw [← e]; exact hme
    have hout := (outflank_iff hn hr hd hs j2).2 ⟨hrun2, hme'⟩
    have hle : j ≤ j2 := by
      apply Classical.byContradiction
      intro hlt
      have h1 := hrun (j2 + 1) (by omega) (by omega)
      have e : idx s + ((j2 + 1 : Nat) : Int) * delta d
          = idx s + ((j2 : Int) + 1) * delta d := by grind
      rw [e] at h1
      exact hr.disjoint _ hme' h1
    refine ⟨far s d j, ?_, by rw [idx_far]⟩
    rw [mem_flipsDir_iff hd hs]
    exact ⟨(j2 : Int) + 1, hout, j, by omega, by omega, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    rw [mem_flipsDir_iff hd hs] at hq
    obtain ⟨m', hout, i0, h1, h2, rfl⟩ := hq
    have hfit : m' < n := line_fits hd hs (cell_eq_some hout.2).1 (by omega)
    obtain ⟨j2, rfl⟩ : ∃ j2 : Nat, m' = (j2 : Int) + 1 := ⟨(m' - 1).toNat, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j : Nat, i0 = (j : Int) := ⟨i0.toNat, by omega⟩
    obtain ⟨hrun2, hme⟩ := (outflank_iff hn hr hd hs j2).1 hout
    refine ⟨⟨j, by omega, by omega, by rw [idx_far],
      fun j' a b => hrun2 j' a (by omega)⟩, idx s + (j2 : Int) * delta d, ?_, ?_⟩
    · rw [chain_single hm]
      exact ⟨j2, by omega, by omega, rfl, hrun2⟩
    · have e : idx s + (j2 : Int) * delta d + delta d
          = idx s + ((j2 : Int) + 1) * delta d := by grind
      rw [e]; exact hme

/-- The bitboard flips are the flips of the specification. -/
theorem mem_flips_spec (hn : n ≤ 6) {me opp : UInt64} {b : Board} {c : Color}
    (hr : Repr n me opp b c) {s : Square} (hs : OnBoard n s)
    {m : UInt64} (hm : ∀ i, Mem m i ↔ i = idx s) (i : Int) :
    Mem (BB.flips me opp m) i ↔ ∃ q, q ∈ flips n b c s ∧ idx q = i := by
  have dir : ∀ d, d ∈ directions → ∀ sh, IsShift sh (delta d) →
      (Mem (BB.flipDir sh me opp m) i ↔ ∃ q, q ∈ flipsDir n b c s d ∧ idx q = i) :=
    fun d hd sh hsh => mem_flipDir_spec hn hr hd hs hsh hm i
  simp only [BB.flips, mem_or,
    dir (-1, -1) (by simp [directions]) _ isShift_r9,
    dir (0, -1) (by simp [directions]) _ isShift_r8,
    dir (1, -1) (by simp [directions]) _ isShift_r7,
    dir (-1, 0) (by simp [directions]) _ isShift_r1,
    dir (1, 0) (by simp [directions]) _ isShift_l1,
    dir (-1, 1) (by simp [directions]) _ isShift_l7,
    dir (0, 1) (by simp [directions]) _ isShift_l8,
    dir (1, 1) (by simp [directions]) _ isShift_l9]
  simp only [flips, List.mem_flatMap, directions, List.mem_cons, List.mem_nil_iff, or_false]
  constructor
  · rintro (((((((⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩) |
      ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩) <;>
      exact ⟨q, ⟨_, by simp, hq⟩, rfl⟩
  · rintro ⟨q, ⟨d, hd, hq⟩, rfl⟩
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨q, hq, rfl⟩))))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, rfl⟩))))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, rfl⟩)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, rfl⟩))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨q, hq, rfl⟩))
    · exact Or.inl (Or.inr ⟨q, hq, rfl⟩)
    · exact Or.inr ⟨q, hq, rfl⟩

/-! ## Making a move -/

/-- Flipped discs are discs of the opponent on the board. -/
theorem flips_onBoard_opp {b : Board} {c : Color} {s : Square} (hs : OnBoard n s)
    {q : Square} (hq : q ∈ flips n b c s) : OnBoard n q ∧ b q = some c.opponent := by
  rw [mem_flips_iff hs] at hq
  obtain ⟨d, _, m, ⟨hop, _⟩, i, h1, h2, rfl⟩ := hq
  exact cell_eq_some (hop i h1 h2)

/-- Playing on the bitboard is playing on the board: after the move on the
empty square `s` (whose bit is `m`), the words are exchanged, the flipped
discs change sides and the new disc is added. -/
theorem Repr.play (hn : n ≤ 6) {me opp : UInt64} {b : Board} {c : Color}
    (hr : Repr n me opp b c) {s : Square} (hs : OnBoard n s) (he : b s = none)
    {m : UInt64} (hm : ∀ i, Mem m i ↔ i = idx s) :
    Repr n (opp ^^^ BB.flips me opp m) (me ||| m ||| BB.flips me opp m)
      (play n b c s) c.opponent := by
  have hf := mem_flips_spec hn hr hs hm
  have hfopp : ∀ i, Mem (BB.flips me opp m) i → Mem opp i := by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := (hf i).1 hi
    have h1 := flips_onBoard_opp hs hq
    exact (hr.opp_iff q h1.1).1 h1.2
  have hfq : ∀ q, OnBoard n q → (Mem (BB.flips me opp m) (idx q) ↔ q ∈ flips n b c s) := by
    intro q hq
    rw [hf]
    constructor
    · rintro ⟨q', hq', e⟩
      have := idx_inj hn (flips_onBoard_opp hs hq').1 hq e
      rw [← this]; exact hq'
    · intro h
      exact ⟨q, h, rfl⟩
  have hsnone := (hr.none_iff hs).1 he
  constructor
  · -- me_valid
    intro i hi
    rw [mem_xor] at hi
    rcases hi with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact hr.opp_valid i h1
    · exact absurd (hfopp i h2) h1
  · -- opp_valid
    intro i hi
    rw [mem_or, mem_or] at hi
    rcases hi with (h1 | h1) | h1
    · exact hr.me_valid i h1
    · rw [hm] at h1; rw [h1]; exact valid_idx hn hs
    · exact hr.opp_valid i (hfopp i h1)
  · -- disjoint
    intro i hi hi'
    rw [mem_xor] at hi
    rw [mem_or, mem_or] at hi'
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hi' with (h3 | h3) | h3
      · exact hr.disjoint i h3 h1
      · rw [hm] at h3; rw [h3] at h1; exact hsnone.2 h1
      · exact h2 h3
    · exact h1 (hfopp i h2)
  · -- me_iff
    intro q hq
    unfold Othello.play
    rw [mem_xor, hfq q hq]
    by_cases hcond : q = s ∨ q ∈ flips n b c s
    · simp only [hcond, ↓reduceIte]
      constructor
      · intro h
        exact absurd (Option.some.inj h) (Color.ne_opponent c)
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · rcases hcond with rfl | h3
          · exact absurd h1 hsnone.2
          · exact absurd h3 h2
        · exact absurd (hfopp _ ((hfq q hq).2 h2)) h1
    · simp only [hcond, ↓reduceIte]
      rw [hr.opp_iff q hq]
      constructor
      · intro h
        exact Or.inl ⟨h, fun h' => hcond (Or.inr h')⟩
      · rintro (⟨h1, _⟩ | ⟨h1, h2⟩)
        · exact h1
        · exact absurd (Or.inr h2) hcond
  · -- opp_iff
    intro q hq
    unfold Othello.play
    rw [Color.opponent_opponent, mem_or, mem_or, hfq q hq, hm]
    by_cases hcond : q = s ∨ q ∈ flips n b c s
    · simp only [hcond, ↓reduceIte, true_iff]
      rcases hcond with rfl | h3
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr h3
    · simp only [hcond, ↓reduceIte]
      rw [hr.me_iff q hq]
      constructor
      · intro h
        exact Or.inl (Or.inl h)
      · rintro ((h1 | h1) | h1)
        · exact h1
        · exact absurd (Or.inl (idx_inj hn hq hs h1)) hcond
        · exact absurd (Or.inr h1) hcond

/-! ## Legal moves -/

namespace BB

/-- Empty-or-not, the squares from which a move would flip something in the
direction opposite to `sh`. -/
@[inline] def mobDir (sh : UInt64 → UInt64) (me opp : UInt64) : UInt64 :=
  sh (walk sh me opp)

/-- The legal moves of the player to move.  `mask` is the set of all squares
of the board. -/
def mobility (mask me opp : UInt64) : UInt64 :=
  (mobDir (fun x => x >>> 9) me opp ||| mobDir (fun x => x >>> 8) me opp |||
   mobDir (fun x => x >>> 7) me opp ||| mobDir (fun x => x >>> 1) me opp |||
   mobDir (fun x => x <<< 1) me opp ||| mobDir (fun x => x <<< 7) me opp |||
   mobDir (fun x => x <<< 8) me opp ||| mobDir (fun x => x <<< 9) me opp)
  &&& (mask ^^^ (me ||| opp))

end BB

theorem isShift_r9' : IsShift (fun x => x >>> 9) (-(delta (1, 1))) :=
  isShift_of_eq (isShift_shr 9 (by decide)) (by decide)
theorem isShift_r8' : IsShift (fun x => x >>> 8) (-(delta (0, 1))) :=
  isShift_of_eq (isShift_shr 8 (by decide)) (by decide)
theorem isShift_r7' : IsShift (fun x => x >>> 7) (-(delta (-1, 1))) :=
  isShift_of_eq (isShift_shr 7 (by decide)) (by decide)
theorem isShift_r1' : IsShift (fun x => x >>> 1) (-(delta (1, 0))) :=
  isShift_of_eq (isShift_shr 1 (by decide)) (by decide)
theorem isShift_l1' : IsShift (fun x => x <<< 1) (-(delta (-1, 0))) :=
  isShift_of_eq (isShift_shl 1 (by decide)) (by decide)
theorem isShift_l7' : IsShift (fun x => x <<< 7) (-(delta (1, -1))) :=
  isShift_of_eq (isShift_shl 7 (by decide)) (by decide)
theorem isShift_l8' : IsShift (fun x => x <<< 8) (-(delta (0, -1))) :=
  isShift_of_eq (isShift_shl 8 (by decide)) (by decide)
theorem isShift_l9' : IsShift (fun x => x <<< 9) (-(delta (-1, -1))) :=
  isShift_of_eq (isShift_shl 9 (by decide)) (by decide)

/-- Something is flipped in direction `d` iff some line outflanks at least one disc. -/
theorem flipsDir_ne_nil_iff {b : Board} {c : Color} {s : Square} {d : Int × Int}
    (hd : d ∈ directions) (hs : OnBoard n s) :
    flipsDir n b c s d ≠ [] ↔ ∃ j : Nat, 1 ≤ j ∧ Outflank n b c s d ((j : Int) + 1) := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ h
    rw [mem_flipsDir_iff hd hs] at hq
    obtain ⟨m, hout, i, h1, h2, _⟩ := hq
    refine ⟨(m - 1).toNat, by omega, ?_⟩
    have e : (((m - 1).toNat : Nat) : Int) + 1 = m := by omega
    rw [e]; exact hout
  · rintro ⟨j, hj, hout⟩
    apply List.ne_nil_of_mem (a := far s d 1)
    rw [mem_flipsDir_iff hd hs]
    exact ⟨(j : Int) + 1, hout, 1, by omega, by omega, rfl⟩

/-- In one direction: the bit of an on-board square `s` is produced by `mobDir`
iff a move on `s` would flip something in direction `d`. -/
theorem mem_mobDir_spec (hn : n ≤ 6) {me opp : UInt64} {b : Board} {c : Color}
    (hr : Repr n me opp b c) {s : Square} {d : Int × Int}
    (hd : d ∈ directions) (hs : OnBoard n s)
    {sh : UInt64 → UInt64} (hsh : IsShift sh (-(delta d))) :
    Mem (BB.mobDir sh me opp) (idx s) ↔ flipsDir n b c s d ≠ [] := by
  have hv := valid_idx hn hs
  have hrange : 0 ≤ idx s ∧ idx s < 64 := by unfold Valid at hv; omega
  unfold BB.mobDir
  rw [hsh, mem_walk hsh, chain_iff, flipsDir_ne_nil_iff hd hs]
  constructor
  · rintro ⟨⟨j, hj1, hj4, hme, hall⟩, _, _⟩
    refine ⟨j, hj1, (outflank_iff hn hr hd hs j).2 ⟨?_, ?_⟩⟩
    · intro j' h1 h2
      have h3 := hall (j' - 1) (by omega)
      have e : idx s - -(delta d) - ((j' - 1 : Nat) : Int) * -(delta d)
          = idx s + (j' : Int) * delta d := by grind
      rw [e] at h3; exact h3
    · have e : idx s - -(delta d) - (j : Int) * -(delta d)
          = idx s + ((j : Int) + 1) * delta d := by grind
      rw [e] at hme; exact hme
  · rintro ⟨j, hj1, hout⟩
    have hfit : (j : Int) + 1 < n := line_fits hd hs (cell_eq_some hout.2).1 (by omega)
    obtain ⟨hrun, hme⟩ := (outflank_iff hn hr hd hs j).1 hout
    refine ⟨⟨j, hj1, by omega, ?_, ?_⟩, hrange.1, hrange.2⟩
    · have e : idx s - -(delta d) - (j : Int) * -(delta d)
          = idx s + ((j : Int) + 1) * delta d := by grind
      rw [e]; exact hme
    · intro j' hj'
      have h3 := hrun (j' + 1) (by omega) (by omega)
      have e : idx s + ((j' + 1 : Nat) : Int) * delta d
          = idx s - -(delta d) - (j' : Int) * -(delta d) := by grind
      rw [e] at h3; exact h3

/-- The bitboard move generator finds exactly the legal moves. -/
theorem mem_mobility_spec (hn : n ≤ 6) {mask me opp : UInt64} {b : Board} {c : Color}
    (hmask : ∀ i, Mem mask i ↔ Valid n i) (hr : Repr n me opp b c) (i : Int) :
    Mem (BB.mobility mask me opp) i ↔ ∃ s, Legal n b c s ∧ idx s = i := by
  have dir : ∀ s, OnBoard n s → ∀ d, d ∈ directions → ∀ sh, IsShift sh (-(delta d)) →
      (Mem (BB.mobDir sh me opp) (idx s) ↔ flipsDir n b c s d ≠ []) :=
    fun s hs d hd sh hsh => mem_mobDir_spec hn hr hd hs hsh
  have key : ∀ s, OnBoard n s →
      ((Mem (BB.mobDir (fun x => x >>> 9) me opp) (idx s) ∨
        Mem (BB.mobDir (fun x => x >>> 8) me opp) (idx s) ∨
        Mem (BB.mobDir (fun x => x >>> 7) me opp) (idx s) ∨
        Mem (BB.mobDir (fun x => x >>> 1) me opp) (idx s) ∨
        Mem (BB.mobDir (fun x => x <<< 1) me opp) (idx s) ∨
        Mem (BB.mobDir (fun x => x <<< 7) me opp) (idx s) ∨
        Mem (BB.mobDir (fun x => x <<< 8) me opp) (idx s) ∨
        Mem (BB.mobDir (fun x => x <<< 9) me opp) (idx s)) ↔ flips n b c s ≠ []) := by
    intro s hs
    rw [dir s hs (1, 1) (by simp [directions]) _ isShift_r9',
      dir s hs (0, 1) (by simp [directions]) _ isShift_r8',
      dir s hs (-1, 1) (by simp [directions]) _ isShift_r7',
      dir s hs (1, 0) (by simp [directions]) _ isShift_r1',
      dir s hs (-1, 0) (by simp [directions]) _ isShift_l1',
      dir s hs (1, -1) (by simp [directions]) _ isShift_l7',
      dir s hs (0, -1) (by simp [directions]) _ isShift_l8',
      dir s hs (-1, -1) (by simp [directions]) _ isShift_l9']
    unfold flips
    simp only [ne_eq, List.flatMap_eq_nil_iff, directions, List.mem_cons, List.mem_nil_iff,
      or_false]
    constructor
    · intro h hall
      rcases h with h | h | h | h | h | h | h | h <;> exact h (hall _ (by simp))
    · intro h
      apply Classical.byContradiction
      intro hno
      apply h
      intro d hd
      apply Classical.byContradiction
      intro hne
      apply hno
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hne]
  unfold BB.mobility
  rw [mem_and, mem_xor, hmask]
  simp only [mem_or, or_assoc]
  constructor
  · rintro ⟨hdir, ⟨hv, hocc⟩ | ⟨hv, hocc⟩⟩
    · obtain ⟨s, hs, rfl⟩ := exists_square_of_valid hv
      refine ⟨s, ⟨hs, ?_, (key s hs).1 hdir⟩, rfl⟩
      rw [hr.none_iff hs]
      exact ⟨fun h => hocc (Or.inl h), fun h => hocc (Or.inr h)⟩
    · rcases hocc with h | h
      · exact absurd (hr.me_valid _ h) hv
      · exact absurd (hr.opp_valid _ h) hv
  · rintro ⟨s, ⟨hs, he, hfl⟩, rfl⟩
    refine ⟨(key s hs).2 hfl, Or.inl ⟨valid_idx hn hs, ?_⟩⟩
    have := (hr.none_iff hs).1 he
    rintro (h | h)
    · exact this.1 h
    · exact this.2 h

/-- No legal move iff the mobility word is zero. -/
theorem mobility_eq_zero_iff (hn : n ≤ 6) {mask me opp : UInt64} {b : Board} {c : Color}
    (hmask : ∀ i, Mem mask i ↔ Valid n i) (hr : Repr n me opp b c) :
    BB.mobility mask me opp = 0 ↔ moves n b c = [] := by
  rw [eq_zero_iff, List.eq_nil_iff_forall_not_mem]
  constructor
  · intro h s hs
    exact h (idx s) ((mem_mobility_spec hn hmask hr _).2 ⟨s, mem_moves.1 hs, rfl⟩)
  · intro h i hi
    obtain ⟨s, hs, _⟩ := (mem_mobility_spec hn hmask hr i).1 hi
    exact h s (mem_moves.2 hs)

/-! ## Counting discs -/

/-- The word with only the bit of square `s`. -/
def sqMask (s : Square) : UInt64 := (1 : UInt64) <<< (idx s).toNat.toUInt64

/-- One mask per square of the board. -/
def sqMasks (n : Nat) : List UInt64 := (squares n).map sqMask

/-- The set of all squares of the board. -/
def boardMask (n : Nat) : UInt64 := (sqMasks n).foldl (fun a m => a ||| m) 0

theorem mem_sqMask (hn : n ≤ 6) {s : Square} (hs : OnBoard n s) (i : Int) :
    Mem (sqMask s) i ↔ i = idx s := by
  unfold sqMask
  rw [mem_one_shl]
  have hv := valid_idx hn hs
  unfold Valid at hv
  have e : (idx s).toNat.toUInt64.toNat = (idx s).toNat := by
    show (UInt64.ofNat (idx s).toNat).toNat = (idx s).toNat
    apply UInt64.toNat_ofNat_of_lt'
    unfold UInt64.size
    omega
  rw [e]
  omega

theorem and_sqMask_ne_zero (hn : n ≤ 6) {s : Square} (hs : OnBoard n s) (x : UInt64) :
    x &&& sqMask s ≠ 0 ↔ Mem x (idx s) := by
  rw [ne_zero_iff]
  constructor
  · rintro ⟨i, hi⟩
    rw [mem_and, mem_sqMask hn hs] at hi
    rw [← hi.2]; exact hi.1
  · intro h
    exact ⟨idx s, mem_and.2 ⟨h, (mem_sqMask hn hs _).2 rfl⟩⟩

theorem mem_boardMask (hn : n ≤ 6) (i : Int) : Mem (boardMask n) i ↔ Valid n i := by
  have gen : ∀ (l : List Square), (∀ s, s ∈ l → OnBoard n s) → ∀ (a : UInt64),
      (Mem ((l.map sqMask).foldl (fun a m => a ||| m) a) i ↔ Mem a i ∨ ∃ s, s ∈ l ∧ i = idx s) := by
    intro l
    induction l with
    | nil =>
      intro _ a
      simp
    | cons s l ih =>
      intro hl a
      rw [List.map_cons, List.foldl_cons, ih (fun t ht => hl t (List.mem_cons_of_mem _ ht)),
        mem_or, mem_sqMask hn (hl s List.mem_cons_self)]
      constructor
      · rintro ((h | h) | ⟨t, ht, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨s, List.mem_cons_self, h⟩
        · exact Or.inr ⟨t, List.mem_cons_of_mem _ ht, h⟩
      · rintro (h | ⟨t, ht, h⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.1 ht with rfl | ht
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨t, ht, h⟩
  unfold boardMask sqMasks
  rw [gen (squares n) (fun s hs => mem_squares.1 hs) 0]
  constructor
  · rintro (h | ⟨s, hs, rfl⟩)
    · exact absurd h (not_mem_zero i)
    · exact valid_idx hn (mem_squares.1 hs)
  · intro h
    obtain ⟨s, hs, rfl⟩ := exists_square_of_valid h
    exact Or.inr ⟨s, mem_squares.2 hs, rfl⟩

namespace BB

/-- The number of discs of the player to move minus the number of discs of
the other player, counted over the squares whose masks are listed in `ms`. -/
def margin (ms : List UInt64) (me opp : UInt64) : Int :=
  ms.foldl (fun a m => if me &&& m ≠ 0 then a + 1 else if opp &&& m ≠ 0 then a - 1 else a) 0

end BB

theorem Repr.margin_eq (hn : n ≤ 6) {me opp : UInt64} {b : Board} {c : Color}
    (hr : Repr n me opp b c) : BB.margin (sqMasks n) me opp = margin n b c := by
  have gen : ∀ (l : List Square), (∀ s, s ∈ l → OnBoard n s) → ∀ a : Int,
      (l.map sqMask).foldl
          (fun a m => if me &&& m ≠ 0 then a + 1 else if opp &&& m ≠ 0 then a - 1 else a) a
        = a + ((l.filter fun s => b s = some c).length : Int)
            - ((l.filter fun s => b s = some c.opponent).length : Int) := by
    intro l
    induction l with
    | nil =>
      intro _ a
      simp
    | cons s l ih =>
      intro hl a
      have hs : OnBoard n s := hl s List.mem_cons_self
      rw [List.map_cons, List.foldl_cons, ih (fun t ht => hl t (List.mem_cons_of_mem _ ht))]
      by_cases h1 : b s = some c
      · have hm : me &&& sqMask s ≠ 0 :=
          (and_sqMask_ne_zero hn hs me).2 ((hr.me_iff s hs).1 h1)
        have h2 : ¬ b s = some c.opponent := by
          rw [h1]
          intro h
          exact Color.ne_opponent c (Option.some.inj h)
        rw [List.filter_cons_of_pos (by simpa using h1),
          List.filter_cons_of_neg (by simpa using h2)]
        simp only [hm, ne_eq, not_false_eq_true, ↓reduceIte, List.length_cons]
        omega
      · have hm : me &&& sqMask s = 0 := Classical.byContradiction fun h =>
          h1 ((hr.me_iff s hs).2 ((and_sqMask_ne_zero hn hs me).1 h))
        by_cases h2 : b s = some c.opponent
        · have ho : opp &&& sqMask s ≠ 0 :=
            (and_sqMask_ne_zero hn hs opp).2 ((hr.opp_iff s hs).1 h2)
          rw [List.filter_cons_of_neg (by simpa using h1),
            List.filter_cons_of_pos (by simpa using h2)]
          simp only [hm, ho, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte,
            List.length_cons]
          omega
        · have ho : opp &&& sqMask s = 0 := Classical.byContradiction fun h =>
            h2 ((hr.opp_iff s hs).2 ((and_sqMask_ne_zero hn hs opp).1 h))
          rw [List.filter_cons_of_neg (by simpa using h1),
            List.filter_cons_of_neg (by simpa using h2)]
          simp only [hm, ho, ne_eq, not_true_eq_false, ↓reduceIte]
  have h := gen (squares n) (fun s hs => mem_squares.1 hs) 0
  unfold BB.margin sqMasks Othello.margin count
  rw [h]
  omega

/-! ## A decidable test for `Repr` -/

/-- An executable check that `me` / `opp` represent the board `b` seen by `c`. -/
def reprCheck (n : Nat) (me opp : UInt64) (b : Board) (c : Color) : Bool :=
  (me &&& boardMask n == me) && (opp &&& boardMask n == opp) && (me &&& opp == 0) &&
  (squares n).all fun s =>
    (decide (b s = some c) == decide (me &&& sqMask s ≠ 0)) &&
    (decide (b s = some c.opponent) == decide (opp &&& sqMask s ≠ 0))

theorem repr_of_check (hn : n ≤ 6) {me opp : UInt64} {b : Board} {c : Color}
    (h : reprCheck n me opp b c = true) : Repr n me opp b c := by
  unfold reprCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_decide] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  constructor
  · intro i hi
    rw [← h1, mem_and] at hi
    exact (mem_boardMask hn i).1 hi.2
  · intro i hi
    rw [← h2, mem_and] at hi
    exact (mem_boardMask hn i).1 hi.2
  · intro i hi hi'
    have : Mem (me &&& opp) i := mem_and.2 ⟨hi, hi'⟩
    rw [h3] at this
    exact not_mem_zero i this
  · intro s hs
    rw [(h4 s (mem_squares.2 hs)).1]
    exact and_sqMask_ne_zero hn hs me
  · intro s hs
    rw [(h4 s (mem_squares.2 hs)).2]
    exact and_sqMask_ne_zero hn hs opp

end Othello
