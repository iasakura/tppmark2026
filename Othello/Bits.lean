/-!
# 64-bit words as sets of bit positions

`Mem x i` says that bit number `i` of the machine word `x` is set.  The index
is an integer so that positions "off the word" (negative, or `≥ 64`) can be
talked about uniformly: they are never members.
-/

namespace Othello

/-- Bit number `i` of `x` is set. -/
def Mem (x : UInt64) (i : Int) : Prop :=
  0 ≤ i ∧ x.toNat.testBit i.toNat = true

instance (x : UInt64) (i : Int) : Decidable (Mem x i) := by
  unfold Mem; infer_instance

theorem Mem.nonneg {x : UInt64} {i : Int} (h : Mem x i) : 0 ≤ i := h.1

theorem Mem.lt {x : UInt64} {i : Int} (h : Mem x i) : i < 64 := by
  apply Classical.byContradiction
  intro hge
  have h1 : x.toNat < 2 ^ 64 := x.toNat_lt
  have h2 : (2 : Nat) ^ 64 ≤ 2 ^ i.toNat :=
    Nat.pow_le_pow_right (by decide) (by have := h.1; omega)
  have h3 := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h1 h2)
  rw [h.2] at h3
  cases h3

theorem mem_and {x y : UInt64} {i : Int} : Mem (x &&& y) i ↔ Mem x i ∧ Mem y i := by
  unfold Mem
  rw [UInt64.toNat_and, Nat.testBit_and, Bool.and_eq_true]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨⟨h0, h1⟩, h0, h2⟩
  · rintro ⟨⟨h0, h1⟩, _, h2⟩
    exact ⟨h0, h1, h2⟩

theorem mem_or {x y : UInt64} {i : Int} : Mem (x ||| y) i ↔ Mem x i ∨ Mem y i := by
  unfold Mem
  rw [UInt64.toNat_or, Nat.testBit_or, Bool.or_eq_true]
  constructor
  · rintro ⟨h0, h1 | h2⟩
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h2⟩
  · rintro (⟨h0, h1⟩ | ⟨h0, h2⟩)
    · exact ⟨h0, Or.inl h1⟩
    · exact ⟨h0, Or.inr h2⟩

theorem mem_xor {x y : UInt64} {i : Int} :
    Mem (x ^^^ y) i ↔ (Mem x i ∧ ¬ Mem y i) ∨ (¬ Mem x i ∧ Mem y i) := by
  unfold Mem
  rw [UInt64.toNat_xor, Nat.testBit_xor]
  cases hx : x.toNat.testBit i.toNat <;> cases hy : y.toNat.testBit i.toNat <;>
    simp

/-- Shifting left by `s` moves bit `i - s` to bit `i`; bits leaving the word are lost. -/
theorem mem_shl {x s : UInt64} {i : Int} (hs : s.toNat < 64) :
    Mem (x <<< s) i ↔ i < 64 ∧ Mem x (i - s.toNat) := by
  unfold Mem
  rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hs, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    have e : (i - s.toNat).toNat = i.toNat - s.toNat := by omega
    rw [e]
    exact ⟨by omega, by omega, h3⟩
  · rintro ⟨h1, h0, h3⟩
    have e : (i - s.toNat).toNat = i.toNat - s.toNat := by omega
    rw [e] at h3
    exact ⟨by omega, by omega, by omega, h3⟩

/-- Shifting right by `s` moves bit `i + s` to bit `i`. -/
theorem mem_shr {x s : UInt64} {i : Int} (hs : s.toNat < 64) :
    Mem (x >>> s) i ↔ 0 ≤ i ∧ Mem x (i + s.toNat) := by
  unfold Mem
  rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hs, Nat.testBit_shiftRight]
  constructor
  · rintro ⟨h0, h1⟩
    have e : (i + s.toNat).toNat = s.toNat + i.toNat := by omega
    rw [e]
    exact ⟨h0, by omega, h1⟩
  · rintro ⟨h0, _, h1⟩
    have e : (i + s.toNat).toNat = s.toNat + i.toNat := by omega
    rw [e] at h1
    exact ⟨h0, h1⟩

theorem not_mem_zero (i : Int) : ¬ Mem 0 i := by
  unfold Mem
  simp

theorem eq_zero_iff {x : UInt64} : x = 0 ↔ ∀ i, ¬ Mem x i := by
  constructor
  · rintro rfl i
    exact not_mem_zero i
  · intro h
    apply UInt64.toNat.inj
    apply Nat.eq_of_testBit_eq
    intro k
    rw [UInt64.toNat_zero, Nat.zero_testBit]
    cases hk : x.toNat.testBit k
    · rfl
    · exact absurd (show Mem x (k : Int) from ⟨by omega, by simpa using hk⟩) (h k)

theorem ne_zero_iff {x : UInt64} : x ≠ 0 ↔ ∃ i, Mem x i := by
  rw [Ne, eq_zero_iff]
  constructor
  · intro h
    apply Classical.byContradiction
    intro h'
    exact h fun i hi => h' ⟨i, hi⟩
  · rintro ⟨i, hi⟩ h
    exact h i hi

/-- The word with the single bit `k % 64` set. -/
theorem mem_one_shl {k : UInt64} {i : Int} :
    Mem ((1 : UInt64) <<< k) i ↔ i = ((k.toNat % 64 : Nat) : Int) := by
  unfold Mem
  rw [UInt64.toNat_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  have h1 : (1 : UInt64).toNat = 1 := rfl
  rw [h1]
  have hk : k.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h0, _, h2, h3⟩
    have h4 : i.toNat - k.toNat % 64 = 0 := by
      apply Classical.byContradiction
      intro hne
      have : (1 : Nat).testBit (i.toNat - k.toNat % 64) = false := by
        apply Nat.testBit_lt_two_pow
        have : 1 < 2 ^ (i.toNat - k.toNat % 64) := Nat.one_lt_two_pow hne
        exact this
      rw [this] at h3
      cases h3
    omega
  · intro h
    refine ⟨by omega, by omega, by omega, ?_⟩
    have h4 : i.toNat - k.toNat % 64 = 0 := by omega
    rw [h4]
    rfl

end Othello
