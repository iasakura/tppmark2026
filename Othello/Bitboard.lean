import Othello.Lemmas
import Othello.Bits

/-!
# Bitboards

A position is stored as two 64-bit words `me` / `opp` (the discs of the player
to move and of the other player).  Square `(x, y)` is bit `8 * y + x`: rows of
eight bits, of which a board of width `n ≤ 6` uses the low `n`.  The unused
bits of each row act as a guard band, so that shifting a word by 1, 7, 8 or 9
positions moves every disc one step in one of the eight directions and discs
never wrap around from one row to another.

This file defines the move generator on this representation
(`BB.mobility`, `BB.flips`, `BB.margin`) and proves that it computes exactly what
the specification in `Othello/Spec.lean` says (`mem_mobility_iff`,
`Repr.play`, `Repr.margin_eq`).
-/

namespace Othello

/-! ## Layout -/

/-- Bit number of a square. -/
def idx (s : Square) : Int := 8 * s.2 + s.1

/-- Difference between the bit numbers of a square and of its neighbour in
direction `d`. -/
def delta (d : Int × Int) : Int := 8 * d.2 + d.1

/-- The bit numbers which stand for squares of the `n × n` board. -/
def Valid (n : Nat) (i : Int) : Prop := 0 ≤ i ∧ i % 8 < n ∧ i / 8 < n

variable {n : Nat}

theorem idx_step (d : Int × Int) (s : Square) : idx (step d s) = idx s + delta d := by
  simp only [idx, step, delta]; omega

theorem idx_far (s : Square) (d : Int × Int) (j : Int) :
    idx (far s d j) = idx s + j * delta d := by
  simp only [idx, far, delta]; grind

theorem valid_idx (hn : n ≤ 6) {s : Square} (hs : OnBoard n s) : Valid n (idx s) := by
  unfold OnBoard at hs; unfold Valid idx; omega

theorem idx_inj (hn : n ≤ 6) {s t : Square} (hs : OnBoard n s) (ht : OnBoard n t)
    (h : idx s = idx t) : s = t := by
  unfold OnBoard at hs ht; unfold idx at h
  apply Prod.ext <;> omega

theorem exists_square_of_valid {i : Int} (h : Valid n i) :
    ∃ s, OnBoard n s ∧ idx s = i := by
  refine ⟨(i % 8, i / 8), ?_, ?_⟩
  · unfold Valid at h; unfold OnBoard; simp only; omega
  · unfold idx; simp only; omega

/-- The geometric fact behind the representation: if the bit next to a square
of the board (in direction `d`) is the bit of a square of the board, then that
square is the neighbour in direction `d` — there is no wrap-around. -/
theorem onBoard_step (hn : n ≤ 6) {s : Square} {d : Int × Int} (hd : d ∈ directions)
    (hs : OnBoard n s) (hv : Valid n (idx s + delta d)) : OnBoard n (step d s) := by
  simp only [directions, List.mem_cons, List.mem_nil_iff, or_false] at hd
  unfold OnBoard at hs
  unfold Valid idx delta at hv
  unfold OnBoard step
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only at hv ⊢ <;> omega

/-! ## Shifts and walks -/

/-- `IsShift sh δ`: the operation `sh` moves every bit by `δ` positions (bits
which leave the word are lost). -/
def IsShift (sh : UInt64 → UInt64) (δ : Int) : Prop :=
  ∀ x i, Mem (sh x) i ↔ Mem x (i - δ) ∧ 0 ≤ i ∧ i < 64

theorem isShift_shl (s : UInt64) (hs : s.toNat < 64) :
    IsShift (fun x => x <<< s) (s.toNat : Int) := by
  intro x i
  rw [mem_shl hs]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, by have := h2.nonneg; omega, h1⟩
  · rintro ⟨h1, _, h3⟩
    exact ⟨h3, h1⟩

theorem isShift_shr (s : UInt64) (hs : s.toNat < 64) :
    IsShift (fun x => x >>> s) (-(s.toNat : Int)) := by
  intro x i
  rw [mem_shr hs]
  have e : i - -(s.toNat : Int) = i + s.toNat := by omega
  rw [e]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1, by have := h2.lt; omega⟩
  · rintro ⟨h1, h2, _⟩
    exact ⟨h2, h1⟩

namespace BB

/-- Starting from the bits of `src`, move by `sh` up to four times, each time
keeping only the bits that land on a bit of `opp`; collect everything reached.
(Four steps are enough on a board of width at most 6.) -/
@[inline] def walk (sh : UInt64 → UInt64) (src opp : UInt64) : UInt64 :=
  let x := sh src &&& opp
  let x := x ||| (sh x &&& opp)
  let x := x ||| (sh x &&& opp)
  x ||| (sh x &&& opp)

end BB

/-- `Chain src opp δ k i`: bit `i` is reached from a bit of `src` by at least
one and at most `k` steps of `δ`, all of which (including the last one, on
`i`) land on bits of `opp`. -/
def Chain (src opp : UInt64) (δ : Int) : Nat → Int → Prop
  | 0, _ => False
  | k + 1, i => Mem opp i ∧ (Mem src (i - δ) ∨ Chain src opp δ k (i - δ))

theorem Chain.mono {src opp : UInt64} {δ : Int} :
    ∀ {k : Nat} {i : Int}, Chain src opp δ k i → Chain src opp δ (k + 1) i := by
  intro k
  induction k with
  | zero => intro i h; exact h.elim
  | succ k ih =>
    intro i h
    obtain ⟨ho, h⟩ := h
    refine ⟨ho, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (ih h)

theorem mem_walk {sh : UInt64 → UInt64} {δ : Int} (h : IsShift sh δ)
    (src opp : UInt64) (i : Int) :
    Mem (BB.walk sh src opp) i ↔ Chain src opp δ 4 i := by
  have base : ∀ i, Mem (sh src &&& opp) i ↔ Chain src opp δ 1 i := by
    intro i
    rw [mem_and, h]
    simp only [Chain, or_false]
    constructor
    · rintro ⟨⟨h1, _, _⟩, h2⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨⟨h1, h2.nonneg, h2.lt⟩, h2⟩
  have stp : ∀ (x : UInt64) (k : Nat), (∀ i, Mem x i ↔ Chain src opp δ (k + 1) i) →
      ∀ i, Mem (x ||| (sh x &&& opp)) i ↔ Chain src opp δ (k + 2) i := by
    intro x k hx i
    rw [mem_or, mem_and, h, hx, hx]
    constructor
    · rintro (h1 | ⟨⟨h1, _, _⟩, h2⟩)
      · exact h1.mono
      · exact ⟨h2, Or.inr h1⟩
    · rintro ⟨h2, h1 | h1⟩
      · exact Or.inl ⟨h2, Or.inl h1⟩
      · exact Or.inr ⟨⟨h1, h2.nonneg, h2.lt⟩, h2⟩
  exact stp _ 2 (stp _ 1 (stp _ 0 base)) i

/-- `Chain`, with the number of steps made explicit. -/
theorem chain_iff {src opp : UInt64} {δ : Int} :
    ∀ {k : Nat} {i : Int}, Chain src opp δ k i ↔
      ∃ j : Nat, 1 ≤ j ∧ j ≤ k ∧ Mem src (i - j * δ) ∧
        ∀ j' : Nat, j' < j → Mem opp (i - j' * δ) := by
  intro k
  induction k with
  | zero =>
    intro i
    simp only [Chain, false_iff]
    rintro ⟨j, h1, h2, _⟩
    omega
  | succ k ih =>
    intro i
    simp only [Chain]
    rw [ih]
    constructor
    · rintro ⟨ho, hs | ⟨j, h1, h2, hs, hall⟩⟩
      · refine ⟨1, Nat.le_refl _, by omega, ?_, ?_⟩
        · have e : i - ((1 : Nat) : Int) * δ = i - δ := by grind
          rw [e]; exact hs
        · intro j' hj'
          have e : i - (j' : Int) * δ = i := by
            have : j' = 0 := by omega
            subst this; grind
          rw [e]; exact ho
      · refine ⟨j + 1, by omega, by omega, ?_, ?_⟩
        · have e : i - ((j + 1 : Nat) : Int) * δ = i - δ - (j : Int) * δ := by grind
          rw [e]; exact hs
        · intro j' hj'
          cases j' with
          | zero =>
            have e : i - ((0 : Nat) : Int) * δ = i := by grind
            rw [e]; exact ho
          | succ j' =>
            have e : i - ((j' + 1 : Nat) : Int) * δ = i - δ - (j' : Int) * δ := by grind
            rw [e]; exact hall j' (by omega)
    · rintro ⟨j, h1, h2, hs, hall⟩
      have ho : Mem opp i := by
        have := hall 0 (by omega)
        have e : i - ((0 : Nat) : Int) * δ = i := by grind
        rw [e] at this; exact this
      refine ⟨ho, ?_⟩
      cases j with
      | zero => omega
      | succ j =>
        cases j with
        | zero =>
          left
          have e : i - ((0 + 1 : Nat) : Int) * δ = i - δ := by grind
          rw [e] at hs; exact hs
        | succ j =>
          right
          refine ⟨j + 1, by omega, by omega, ?_, ?_⟩
          · have e : i - ((j + 1 + 1 : Nat) : Int) * δ
                = i - δ - ((j + 1 : Nat) : Int) * δ := by grind
            rw [e] at hs; exact hs
          · intro j' hj'
            have := hall (j' + 1) (by omega)
            have e : i - ((j' + 1 : Nat) : Int) * δ = i - δ - (j' : Int) * δ := by grind
            rw [e] at this; exact this

/-- `Chain` from a single bit `i0`. -/
theorem chain_single {m opp : UInt64} {δ i0 : Int} (hm : ∀ i, Mem m i ↔ i = i0)
    {k : Nat} {i : Int} :
    Chain m opp δ k i ↔
      ∃ j : Nat, 1 ≤ j ∧ j ≤ k ∧ i = i0 + j * δ ∧
        ∀ j' : Nat, 1 ≤ j' → j' ≤ j → Mem opp (i0 + j' * δ) := by
  rw [chain_iff]
  constructor
  · rintro ⟨j, h1, h2, hs, hall⟩
    rw [hm] at hs
    refine ⟨j, h1, h2, by omega, ?_⟩
    intro j' hj1 hj2
    have := hall (j - j') (by omega)
    have e : i - ((j - j' : Nat) : Int) * δ = i0 + (j' : Int) * δ := by grind
    rw [e] at this; exact this
  · rintro ⟨j, h1, h2, hi, hall⟩
    refine ⟨j, h1, h2, ?_, ?_⟩
    · rw [hm]; omega
    · intro j' hj'
      have := hall (j - j') (by omega) (by omega)
      have e : i0 + ((j - j' : Nat) : Int) * δ = i - (j' : Int) * δ := by grind
      rw [e] at this; exact this

end Othello
