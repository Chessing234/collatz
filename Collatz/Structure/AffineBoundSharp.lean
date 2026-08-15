import Collatz.Structure.AffineBound

/-!
# A second bound on the affine constant

`AffineBound.exists_affine_bounded` proves `b + 2^j ≤ 3^j` for the constant in

`2 ^ j · T^j(n) = 3 ^ {a(n,j)} · n + b`.

That bound is sharp when *every* step is odd, but wasteful otherwise: it charges
a factor of three to steps that only halve.  Tracking the odd-step count instead
gives the complementary bound

**`b + 2 ^ j ≤ 3 ^ {a(n,j)} · 2 ^ j`**

which is far better whenever `a` is small.  The recursion reproduces it exactly:
an even step doubles both sides, and an odd step sends `b + 2^j` to
`3(b + 2^j)` while multiplying the right-hand side by three.

The two bounds are genuinely complementary.  Near the critical ratio
`a/L ≈ log 2 / log 3` the first is stronger, because `3 ^ L < 4 ^ L ≈ 2^L·3^a`;
far from it the second is stronger.  A cycle must satisfy both, which is
recorded as `cycle_two_bounds`.
-/

namespace Collatz
namespace AffineBoundSharp

open Reach Congruence

/-- **The odd-step-weighted bound.**  The affine constant satisfies
`b + 2 ^ j ≤ 3 ^ {a(n,j)} · 2 ^ j`. -/
theorem exists_affine_bounded_odd (n j : Nat) :
    ∃ b : Nat, 2 ^ j * acceleratedOrbit j n = 3 ^ oddCount n j * n + b ∧
      b + 2 ^ j ≤ 3 ^ oddCount n j * 2 ^ j := by
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
    have hswap : ∀ x : Nat, 2 * (2 ^ j * x) = 2 ^ j * (2 * x) := by
      intro x
      rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ j)]
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j n) with he | ho
    · -- even step: the constant is unchanged, both sides double
      refine ⟨b, ?_, ?_⟩
      · have hT : acceleratedStep (acceleratedOrbit j n) = acceleratedOrbit j n / 2 := by
          rw [acceleratedStep, if_pos he]
        have hhalf : 2 * (acceleratedOrbit j n / 2) = acceleratedOrbit j n := by omega
        rw [hstep, hT, hlast, he, Nat.add_zero, h2, Nat.mul_assoc, hswap, hhalf]
        exact heq
      · rw [hlast, he, h2]
        simp only [Nat.add_zero]
        -- `b + 2·2^j ≤ 3^a·2^j + 2^j ≤ 3^a·(2·2^j)`
        have hone : (1:Nat) * 2 ^ j ≤ 3 ^ oddCount n j * 2 ^ j :=
          Nat.mul_le_mul_right _ (Arith.one_le_three_pow _)
        rw [Nat.one_mul] at hone
        have h2j : 2 * 2 ^ j = 2 ^ j + 2 ^ j := by omega
        have hdouble : 3 ^ oddCount n j * (2 * 2 ^ j)
            = 3 ^ oddCount n j * 2 ^ j + 3 ^ oddCount n j * 2 ^ j := by
          rw [h2j, Nat.mul_add]
        omega
    · -- odd step: both sides triple
      refine ⟨3 * b + 2 ^ j, ?_, ?_⟩
      · have hT : acceleratedStep (acceleratedOrbit j n)
            = (3 * acceleratedOrbit j n + 1) / 2 := by
          rw [acceleratedStep, if_neg (by omega)]
        have hodd : 2 * ((3 * acceleratedOrbit j n + 1) / 2)
            = 3 * acceleratedOrbit j n + 1 := by omega
        have hexp : 3 ^ (oddCount n j + 1) = 3 * 3 ^ oddCount n j := Arith.three_pow_succ _
        rw [hstep, hT, hlast, ho, h2, Nat.mul_assoc, hswap, hodd, hexp]
        have hexpand : 2 ^ j * (3 * acceleratedOrbit j n + 1)
            = 3 * (2 ^ j * acceleratedOrbit j n) + 2 ^ j := by
          rw [Nat.mul_add, Nat.mul_one]
          rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm (2 ^ j) 3]
        rw [hexpand, heq, Nat.mul_add, ← Nat.mul_assoc]
        omega
      · rw [hlast, ho, h2, Arith.three_pow_succ]
        -- `(3b + 2^j) + 2·2^j = 3(b + 2^j) ≤ 3·(3^a·2^j)`
        have hmul : 3 * (b + 2 ^ j) ≤ 3 * (3 ^ oddCount n j * 2 ^ j) :=
          Nat.mul_le_mul_left 3 hb
        have h2j : 2 * 2 ^ j = 2 ^ j + 2 ^ j := by omega
        have hassoc : 3 * 3 ^ oddCount n j * (2 * 2 ^ j)
            = 3 * (3 ^ oddCount n j * 2 ^ j) + 3 * (3 ^ oddCount n j * 2 ^ j) := by
          rw [h2j, Nat.mul_add, Nat.mul_assoc]
        omega

/-- The sharper bound specialised to a cycle. -/
theorem affine_of_cycle_odd {n j : Nat} (h : acceleratedOrbit j n = n) :
    ∃ b : Nat, 2 ^ j * n = 3 ^ oddCount n j * n + b ∧
      b + 2 ^ j ≤ 3 ^ oddCount n j * 2 ^ j := by
  obtain ⟨b, heq, hb⟩ := exists_affine_bounded_odd n j
  rw [h] at heq
  exact ⟨b, heq, hb⟩

/-- **Both bounds at once.**  A cycle point satisfies the two complementary
inequalities

`n · (2^L − 3^a) ≤ 3^L − 2^L`   and   `n · (2^L − 3^a) ≤ 2^L · (3^a − 1)`,

written here without truncated subtraction.  The first is stronger near the
critical ratio, the second far from it. -/
theorem cycle_two_bounds {n L : Nat} (h : acceleratedOrbit L n = n) :
    (2 ^ L * n + 2 ^ L ≤ 3 ^ oddCount n L * n + 3 ^ L) ∧
    (2 ^ L * n + 2 ^ L ≤ 3 ^ oddCount n L * n + 3 ^ oddCount n L * 2 ^ L) := by
  obtain ⟨b, heq, hb⟩ := AffineBound.affine_of_cycle h
  obtain ⟨b', heq', hb'⟩ := affine_of_cycle_odd h
  have hbb : b = b' := by omega
  subst hbb
  exact ⟨by omega, by omega⟩

/-- The odd-step count of a cycle cannot be tiny relative to the point: either
`3 ^ a` exceeds the point, or `2 ^ L` does not exceed its square. -/
theorem oddCount_or_length {n L : Nat} (_hn : 0 < n) (h : acceleratedOrbit L n = n) :
    2 ^ L * (n + 1) ≤ 3 ^ oddCount n L * (n + 2 ^ L) := by
  obtain ⟨_, hsharp⟩ := cycle_two_bounds h
  have hexp1 : 2 ^ L * (n + 1) = 2 ^ L * n + 2 ^ L := by
    rw [Nat.mul_add, Nat.mul_one]
  have hexp2 : 3 ^ oddCount n L * (n + 2 ^ L)
      = 3 ^ oddCount n L * n + 3 ^ oddCount n L * 2 ^ L := by
    rw [Nat.mul_add]
  omega

/-! ## Not having dropped forces odd steps

The sharper bound applies to any orbit, not only to cycles, and there it says
something concrete about the numbers that resist descent. -/

/-- **An orbit that has not dropped has taken many odd steps.**  If `T^k(n)` is
still at least `n`, and `k` is small enough that `2 ^ k ≤ n`, then

`2 ^ k < 2 · 3 ^ {a(n,k)}`.

So the odd-step count `a` is within one step of the critical density
`log 2 / log 3` — a number that has not yet dropped must have been taking odd
steps almost as fast as arithmetically possible. -/
theorem two_pow_lt_of_no_drop {n k : Nat} (_hn : 0 < n) (hk : 2 ^ k ≤ n)
    (hnodrop : n ≤ acceleratedOrbit k n) : 2 ^ k < 2 * 3 ^ oddCount n k := by
  obtain ⟨b, heq, hb⟩ := exists_affine_bounded_odd n k
  have hmul : 2 ^ k * n ≤ 2 ^ k * acceleratedOrbit k n :=
    Nat.mul_le_mul_left _ hnodrop
  have hle3 : 3 ^ oddCount n k * 2 ^ k ≤ 3 ^ oddCount n k * n :=
    Nat.mul_le_mul_left _ hk
  have hpos : 0 < 2 ^ k := Arith.two_pow_pos k
  -- `2^k n + 2^k ≤ 3^a n + 3^a 2^k ≤ 2 · (3^a n)`
  have hcomb : 2 ^ k * n + 2 ^ k
      ≤ 3 ^ oddCount n k * n + 3 ^ oddCount n k * n := by omega
  have h2X : 2 * 3 ^ oddCount n k = 3 ^ oddCount n k + 3 ^ oddCount n k := by omega
  have hstrict : 2 ^ k * n < (2 * 3 ^ oddCount n k) * n := by
    rw [h2X, Nat.add_mul]
    omega
  exact Nat.lt_of_mul_lt_mul_right hstrict

/-- Restated for a number that never drops: at every scale below `n` its
odd-step count is nearly critical. -/
theorem never_drops_odd_steps {n : Nat} (hn : 0 < n)
    (hnodrop : ∀ k : Nat, n ≤ acceleratedOrbit k n) (k : Nat) (hk : 2 ^ k ≤ n) :
    2 ^ k < 2 * 3 ^ oddCount n k :=
  two_pow_lt_of_no_drop hn hk (hnodrop k)

/-- The contrapositive, which is the form a descent argument wants: a
sufficiently light orbit must already have dropped. -/
theorem drops_of_light {n k : Nat} (hn : 0 < n) (hk : 2 ^ k ≤ n)
    (hlight : 2 * 3 ^ oddCount n k ≤ 2 ^ k) : acceleratedOrbit k n < n := by
  by_cases hdrop : acceleratedOrbit k n < n
  · exact hdrop
  · exact absurd (two_pow_lt_of_no_drop hn hk (by omega)) (by omega)

end AffineBoundSharp
end Collatz
