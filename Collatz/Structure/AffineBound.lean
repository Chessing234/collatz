import Collatz.Structure.Density

/-!
# The affine identity, with the constant bounded

`Congruence.accOrbit_pow_two_mul_add` describes how `T^k` acts on a residue
class.  A second, complementary identity describes how `T^k` acts on a single
number:

`2 ^ j · T^j(n) = 3 ^ {a(n,j)} · n + b`

for an accumulated constant `b` depending on the parity pattern.  The existing
statement in `Collatz.Accelerated` asserts only that such a `b` exists.  For
cycle arguments that is not enough — everything depends on *how large* `b` can
be, since the minimum of a cycle is exactly `b / (2^L − 3^a)`.

This file proves the sharp bound

`b + 2 ^ j ≤ 3 ^ j`

which is exactly `b ≤ 3 ^ j − 2 ^ j`, written additively so that truncated
subtraction never appears.  The bound is sharp: the parity pattern of all odd
steps attains it.

The recursion behind it is one line.  An even step leaves `b` alone; an odd step
sends `b ↦ 3b + 2 ^ j`.  If `b + 2 ^ j ≤ 3 ^ j` then

`(3b + 2^j) + 2^{j+1} = 3(b + 2^j) ≤ 3 · 3^j = 3^{j+1}`,

so the invariant reproduces itself exactly, with no slack lost.
-/

namespace Collatz
namespace AffineBound

open Reach Congruence

/-- **The affine identity with a bounded constant.**  For every `n` and `j`
there is a `b` with `2^j · T^j(n) = 3^{a(n,j)} · n + b` and `b + 2^j ≤ 3^j`. -/
theorem exists_affine_bounded (n j : Nat) :
    ∃ b : Nat, 2 ^ j * acceleratedOrbit j n = 3 ^ oddCount n j * n + b ∧
      b + 2 ^ j ≤ 3 ^ j := by
  induction j with
  | zero =>
    refine ⟨0, ?_, ?_⟩
    · simp [acceleratedOrbit]
    · simp
  | succ j ih =>
    obtain ⟨b, heq, hb⟩ := ih
    have hstep : acceleratedOrbit (j + 1) n = acceleratedStep (acceleratedOrbit j n) :=
      acceleratedOrbit_succ_step j n
    have hlast : oddCount n (j + 1) = oddCount n j + acceleratedOrbit j n % 2 :=
      Density.oddCount_succ_last n j
    have h2 : (2:Nat) ^ (j + 1) = 2 * 2 ^ j := Arith.two_pow_succ j
    have h3 : (3:Nat) ^ (j + 1) = 3 * 3 ^ j := Arith.three_pow_succ j
    have hswap : ∀ x : Nat, 2 * (2 ^ j * x) = 2 ^ j * (2 * x) := by
      intro x
      rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ j)]
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j n) with he | ho
    · -- even step: the constant is unchanged
      refine ⟨b, ?_, ?_⟩
      · have hT : acceleratedStep (acceleratedOrbit j n) = acceleratedOrbit j n / 2 := by
          rw [acceleratedStep, if_pos he]
        have hhalf : 2 * (acceleratedOrbit j n / 2) = acceleratedOrbit j n := by omega
        rw [hstep, hT, hlast, he, Nat.add_zero, h2, Nat.mul_assoc, hswap, hhalf]
        exact heq
      · have hle : (2:Nat) ^ j ≤ 3 ^ j := Arith.two_pow_le_three_pow j
        omega
    · -- odd step: the constant triples and picks up `2 ^ j`
      refine ⟨3 * b + 2 ^ j, ?_, ?_⟩
      · have hT : acceleratedStep (acceleratedOrbit j n)
            = (3 * acceleratedOrbit j n + 1) / 2 := by
          rw [acceleratedStep, if_neg (by omega)]
        have hodd : 2 * ((3 * acceleratedOrbit j n + 1) / 2)
            = 3 * acceleratedOrbit j n + 1 := by omega
        have hexp : 3 ^ (oddCount n j + 1) = 3 * 3 ^ oddCount n j := Arith.three_pow_succ _
        rw [hstep, hT, hlast, ho, h2, Nat.mul_assoc, hswap, hodd, hexp]
        -- `2^j (3x + 1) = 3 (3^a n + b) + 2^j` after substituting the hypothesis
        have hexpand : 2 ^ j * (3 * acceleratedOrbit j n + 1)
            = 3 * (2 ^ j * acceleratedOrbit j n) + 2 ^ j := by
          rw [Nat.mul_add, Nat.mul_one]
          rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm (2 ^ j) 3]
        rw [hexpand, heq, Nat.mul_add, ← Nat.mul_assoc]
        omega
      · -- `(3b + 2^j) + 2^{j+1} = 3 (b + 2^j) ≤ 3 · 3^j`
        have hmul : 3 * (b + 2 ^ j) ≤ 3 * 3 ^ j := Nat.mul_le_mul_left 3 hb
        omega

/-- The bound in subtractive form. -/
theorem affine_const_le {n j b : Nat}
    (h : 2 ^ j * acceleratedOrbit j n = 3 ^ oddCount n j * n + b) :
    b + 2 ^ j ≤ 3 ^ j := by
  obtain ⟨b', heq, hb'⟩ := exists_affine_bounded n j
  have : b = b' := by omega
  omega

/-- The identity in the form used by cycle arguments: the constant is at most
`3 ^ j − 2 ^ j`, stated as `b + 2 ^ j ≤ 3 ^ j`. -/
theorem affine_of_cycle {n j : Nat} (h : acceleratedOrbit j n = n) :
    ∃ b : Nat, 2 ^ j * n = 3 ^ oddCount n j * n + b ∧ b + 2 ^ j ≤ 3 ^ j := by
  obtain ⟨b, heq, hb⟩ := exists_affine_bounded n j
  rw [h] at heq
  exact ⟨b, heq, hb⟩

end AffineBound
end Collatz
