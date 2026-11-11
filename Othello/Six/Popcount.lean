import Othello.Six.Defs
import Std.Tactic.BVDecide

/-!
# Counting discs with `popcount` on the 6 × 6 board

The search for the 6 × 6 board is run with `fast := true`: at the end of a
game the discs are counted with the bit-parallel `BB.popcount`.  This file
proves that this count agrees with the specification (`fast_margin6`).

The equality between `BB.popcount` and a naive bit-by-bit count is proved by
`bv_decide` (a SAT solver whose certificate is checked by a verified checker
run as compiled code).
-/

namespace Othello

/-- The number of set bits of `x` among the bit positions `is`, counted one
by one. -/
def cntBits (is : List UInt64) (x : UInt64) : UInt64 :=
  is.foldl (fun a i => a + ((x >>> i) &&& 1)) 0

/-- The bit number of a square, as a machine word. -/
def sqIdx (s : Square) : UInt64 := (idx s).toNat.toUInt64

/-- The bit numbers of the squares of the 6 × 6 board. -/
def idxs6 : List UInt64 :=
  [0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 16, 17, 18, 19, 20, 21,
   24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 36, 37, 40, 41, 42, 43, 44, 45]

theorem idxs6_eq : idxs6 = (squares 6).map sqIdx := by decide +kernel

/-- On words without bits outside the 6 × 6 board, `popcount` counts the bits
of the 36 squares. -/
theorem popcount_eq_cntBits6 (x : UInt64) (h : x &&& 0xFFFFC0C0C0C0C0C0 = 0) :
    BB.popcount x = cntBits idxs6 x := by
  simp only [BB.popcount, cntBits, idxs6, List.foldl_cons, List.foldl_nil]
  bv_decide

theorem mem_ext {a b : UInt64} (h : ∀ j, Mem a j ↔ Mem b j) : a = b := by
  apply UInt64.toNat.inj
  apply Nat.eq_of_testBit_eq
  intro k
  have hk := h (k : Int)
  unfold Mem at hk
  simp only [Int.toNat_natCast] at hk
  have h0 : (0 : Int) ≤ (k : Int) := by omega
  cases ha : a.toNat.testBit k <;> cases hb : b.toNat.testBit k <;> simp_all

theorem mem_one {j : Int} : Mem (1 : UInt64) j ↔ j = 0 := by
  have h := @mem_one_shl 0 j
  have e : (1 : UInt64) <<< (0 : UInt64) = 1 := by decide
  rw [e] at h
  rw [h]
  have e2 : (((0 : UInt64).toNat % 64 : Nat) : Int) = 0 := by decide
  rw [e2]

/-- Bit `i` of `x`, isolated: the word `1` if it is set and `0` otherwise. -/
theorem shr_and_one {x i : UInt64} (hi : i.toNat < 64) :
    (Mem x (i.toNat : Int) → (x >>> i) &&& 1 = 1) ∧
    (¬ Mem x (i.toNat : Int) → (x >>> i) &&& 1 = 0) := by
  have key : ∀ j, Mem ((x >>> i) &&& 1) j ↔ (j = 0 ∧ Mem x (i.toNat : Int)) := by
    intro j
    rw [mem_and, mem_shr hi, mem_one]
    constructor
    · rintro ⟨⟨_, h1⟩, rfl⟩
      refine ⟨rfl, ?_⟩
      have e : (0 : Int) + (i.toNat : Int) = (i.toNat : Int) := by omega
      rw [e] at h1; exact h1
    · rintro ⟨rfl, h1⟩
      refine ⟨⟨by omega, ?_⟩, rfl⟩
      have e : (0 : Int) + (i.toNat : Int) = (i.toNat : Int) := by omega
      rw [e]; exact h1
  constructor
  · intro hm
    apply mem_ext
    intro j
    rw [key, mem_one]
    exact ⟨fun h => h.1, fun h => ⟨h, hm⟩⟩
  · intro hm
    apply mem_ext
    intro j
    rw [key]
    exact ⟨fun h => absurd h.2 hm, fun h => absurd h (not_mem_zero j)⟩

theorem sqIdx_toNat {n : Nat} (hn : n ≤ 6) {s : Square} (hs : OnBoard n s) :
    ((sqIdx s).toNat : Int) = idx s ∧ (sqIdx s).toNat < 64 := by
  have hv := valid_idx hn hs
  unfold Valid at hv
  have e : (sqIdx s).toNat = (idx s).toNat := by
    show (UInt64.ofNat (idx s).toNat).toNat = (idx s).toNat
    apply UInt64.toNat_ofNat_of_lt'
    unfold UInt64.size
    omega
  rw [e]
  omega

/-- Counting bit by bit over a list of squares gives the number of squares
whose bit is set. -/
theorem cntBits_toNat {n : Nat} (hn : n ≤ 6) (x : UInt64) :
    ∀ (l : List Square), (∀ s, s ∈ l → OnBoard n s) → ∀ (a : UInt64),
      a.toNat + l.length < 2 ^ 64 →
      ((l.map sqIdx).foldl (fun a i => a + ((x >>> i) &&& 1)) a).toNat
        = a.toNat + (l.filter fun s => Mem x (idx s)).length := by
  intro l
  induction l with
  | nil =>
    intro _ a _
    simp
  | cons s l ih =>
    intro hl a ha
    have hs : OnBoard n s := hl s List.mem_cons_self
    obtain ⟨h1, h2⟩ := sqIdx_toNat hn hs
    simp only [List.length_cons] at ha
    rw [List.map_cons, List.foldl_cons]
    by_cases hm : Mem x (idx s)
    · have e : (x >>> sqIdx s) &&& 1 = 1 := (shr_and_one h2).1 (by rw [h1]; exact hm)
      rw [e, ih (fun t ht => hl t (List.mem_cons_of_mem _ ht)),
        List.filter_cons_of_pos (by simpa using hm)]
      · have e2 : (a + 1).toNat = a.toNat + 1 := by
          rw [UInt64.toNat_add]
          have : (1 : UInt64).toNat = 1 := rfl
          rw [this]
          apply Nat.mod_eq_of_lt
          omega
        rw [e2, List.length_cons]
        omega
      · have e2 : (a + 1).toNat = a.toNat + 1 := by
          rw [UInt64.toNat_add]
          have : (1 : UInt64).toNat = 1 := rfl
          rw [this]
          apply Nat.mod_eq_of_lt
          omega
        rw [e2]
        omega
    · have e : (x >>> sqIdx s) &&& 1 = 0 := (shr_and_one h2).2 (by rw [h1]; exact hm)
      rw [e, ih (fun t ht => hl t (List.mem_cons_of_mem _ ht)),
        List.filter_cons_of_neg (by simpa using hm)]
      · have e2 : (a + 0).toNat = a.toNat := by simp
        rw [e2]
      · have e2 : (a + 0).toNat = a.toNat := by simp
        rw [e2]
        omega

theorem length_squares6 : (squares 6).length = 36 := by decide +kernel

/-- `popcount` counts the squares of the 6 × 6 board whose bit is set, for
words which have no other bits. -/
theorem popcount6 {x : UInt64} (hx : ∀ i, Mem x i → Valid 6 i) :
    (BB.popcount x).toNat = ((squares 6).filter fun s => Mem x (idx s)).length := by
  have hzero : x &&& 0xFFFFC0C0C0C0C0C0 = 0 := by
    rw [eq_zero_iff]
    intro i hi
    rw [mem_and] at hi
    have h1 : Mem mask6 i := (mem_mask6 i).2 (hx i hi.1)
    have h2 : Mem (mask6 &&& 0xFFFFC0C0C0C0C0C0) i := mem_and.2 ⟨h1, hi.2⟩
    have e : mask6 &&& 0xFFFFC0C0C0C0C0C0 = 0 := by decide
    rw [e] at h2
    exact not_mem_zero i h2
  rw [popcount_eq_cntBits6 x hzero, idxs6_eq]
  unfold cntBits
  rw [cntBits_toNat (n := 6) (by decide) x (squares 6) (fun s hs => mem_squares.1 hs) 0
    (by rw [length_squares6]; decide)]
  simp

/-- On the 6 × 6 board, the margin computed with `popcount` is the margin of
the specification. -/
theorem fast_margin6 (me opp : UInt64) (b : Board) (c : Color) (hr : Repr 6 me opp b c) :
    ((BB.popcount me).toNat : Int) - ((BB.popcount opp).toNat : Int) = margin 6 b c := by
  rw [popcount6 hr.me_valid, popcount6 hr.opp_valid]
  unfold margin count
  have e1 : ((squares 6).filter fun s => Mem me (idx s))
      = ((squares 6).filter fun s => b s = some c) := by
    apply List.filter_congr
    intro s hs
    have := hr.me_iff s (mem_squares.1 hs)
    by_cases h : b s = some c <;> simp_all
  have e2 : ((squares 6).filter fun s => Mem opp (idx s))
      = ((squares 6).filter fun s => b s = some c.opponent) := by
    apply List.filter_congr
    intro s hs
    have := hr.opp_iff s (mem_squares.1 hs)
    by_cases h : b s = some c.opponent <;> simp_all
  rw [e1, e2]

end Othello
