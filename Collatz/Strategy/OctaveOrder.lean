import Collatz.Structure.Predecessors

/-!
# Round XII, section XXIV — the octave coordinate and the ordered odd times

placeholder
-/

namespace Collatz
namespace OctaveOrder

open Reach

/-! ## 1.  The octave function -/

/-- `oct n = ⌊log₂ n⌋`, the dyadic **octave** of `n`. -/
abbrev oct (n : Nat) : Nat := Nat.log2 n

theorem le_oct_of_pow_le {k n : Nat} (h : 2 ^ k ≤ n) : k ≤ oct n := by
  have hlt : n < 2 ^ (oct n + 1) := Nat.lt_log2_self
  have : (2:Nat) ^ k < 2 ^ (oct n + 1) := Nat.lt_of_le_of_lt h hlt
  have := (Nat.pow_lt_pow_iff_right (a := 2) (by omega)).mp this
  omega

theorem oct_le_of_lt_pow {k n : Nat} (hn : 0 < n) (h : n < 2 ^ (k + 1)) : oct n ≤ k := by
  have hle : 2 ^ oct n ≤ n := Nat.log2_self_le (by omega)
  have : (2:Nat) ^ oct n < 2 ^ (k + 1) := Nat.lt_of_le_of_lt hle h
  have := (Nat.pow_lt_pow_iff_right (a := 2) (by omega)).mp this
  omega

/-- The octave is characterised by its two defining inequalities. -/
theorem oct_eq_of_bounds {k n : Nat} (h1 : 2 ^ k ≤ n) (h2 : n < 2 ^ (k + 1)) : oct n = k := by
  have hn : 0 < n := Nat.lt_of_lt_of_le (Nat.two_pow_pos k) h1
  have a1 := le_oct_of_pow_le h1
  have a2 := oct_le_of_lt_pow hn h2
  omega

theorem pow_oct_le {n : Nat} (hn : 0 < n) : 2 ^ oct n ≤ n := Nat.log2_self_le (by omega)

theorem lt_pow_oct_succ (n : Nat) : n < 2 ^ (oct n + 1) := Nat.lt_log2_self


/-! ## 2.  The octave step law -/

/-- **An even step drops the octave by exactly one.** -/
theorem oct_even_step {n : Nat} (hn : 2 ≤ n) (he : n % 2 = 0) : oct (n / 2) + 1 = oct n := by
  have hhalf : 0 < n / 2 := by omega
  have h1 : 2 ^ oct (n / 2) ≤ n / 2 := pow_oct_le hhalf
  have h2 : n / 2 < 2 ^ (oct (n / 2) + 1) := lt_pow_oct_succ _
  have hn2 : n = 2 * (n / 2) := by omega
  have g1 : 2 ^ (oct (n / 2) + 1) ≤ n := by
    rw [Nat.pow_succ, Nat.mul_comm]
    rw [hn2]
    exact Nat.mul_le_mul_left 2 h1
  have g2 : n < 2 ^ (oct (n / 2) + 1 + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm]
    rw [hn2]
    exact Nat.mul_lt_mul_left (by omega) h2
  have := oct_eq_of_bounds g1 g2
  omega

/-- **An odd step never drops the octave.** -/
theorem oct_le_oct_odd_step {n : Nat} (hn : 0 < n) (ho : n % 2 = 1) :
    oct n ≤ oct ((3 * n + 1) / 2) := by
  have h1 : 2 ^ oct n ≤ n := pow_oct_le hn
  have h2 : n ≤ (3 * n + 1) / 2 := by omega
  exact le_oct_of_pow_le (Nat.le_trans h1 h2)

/-- **An odd step raises the octave by at most one.** -/
theorem oct_odd_step_le {n : Nat} (hn : 0 < n) (ho : n % 2 = 1) :
    oct ((3 * n + 1) / 2) ≤ oct n + 1 := by
  have h2 : n < 2 ^ (oct n + 1) := lt_pow_oct_succ n
  have hpos : 0 < (3 * n + 1) / 2 := by omega
  refine oct_le_of_lt_pow hpos ?_
  have hp : (2:Nat) ^ (oct n + 1 + 1) = 2 * 2 ^ (oct n + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  omega

/-- The **raise indicator** of a single step: `1` exactly when the step is an odd
step that crosses into the next octave, `0` otherwise. -/
def raiseIdx (n : Nat) : Nat :=
  if n % 2 = 1 then (if 2 ^ (oct n + 2) ≤ 3 * n + 1 then 1 else 0) else 0

/-- The **even indicator** of a single step. -/
def evenIdx (n : Nat) : Nat := if n % 2 = 1 then 0 else 1

/-- The **odd indicator** of a single step. -/
def oddIdx (n : Nat) : Nat := if n % 2 = 1 then 1 else 0

theorem raiseIdx_le_oddIdx (n : Nat) : raiseIdx n ≤ oddIdx n := by
  unfold raiseIdx oddIdx
  split <;> split <;> omega

theorem oddIdx_add_evenIdx (n : Nat) : oddIdx n + evenIdx n = 1 := by
  unfold oddIdx evenIdx; split <;> omega

/-- **The exact octave increment of an odd step.** -/
theorem oct_odd_step {n : Nat} (hn : 0 < n) (ho : n % 2 = 1) :
    oct ((3 * n + 1) / 2) = oct n + raiseIdx n := by
  unfold raiseIdx
  rw [if_pos ho]
  have hlow : 2 ^ oct n ≤ n := pow_oct_le hn
  have hhigh : n < 2 ^ (oct n + 1) := lt_pow_oct_succ n
  have hp1 : (2:Nat) ^ (oct n + 1) = 2 * 2 ^ oct n := by rw [Nat.pow_succ, Nat.mul_comm]
  have hp2 : (2:Nat) ^ (oct n + 2) = 2 * 2 ^ (oct n + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  by_cases hcross : 2 ^ (oct n + 2) ≤ 3 * n + 1
  · rw [if_pos hcross]
    refine oct_eq_of_bounds ?_ ?_
    · omega
    · have hp3 : (2:Nat) ^ (oct n + 1 + 1) = 2 * 2 ^ (oct n + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      omega
  · rw [if_neg hcross]
    refine oct_eq_of_bounds ?_ ?_
    · omega
    · omega

/-- **The one-step octave balance.**  Every step, odd or even, satisfies
`oct (T x) + evenIdx x = oct x + raiseIdx x`. -/
theorem oct_step_balance {n : Nat} (hn : 0 < n) :
    oct (acceleratedStep n) + evenIdx n = oct n + raiseIdx n := by
  unfold evenIdx
  by_cases ho : n % 2 = 1
  · rw [if_pos ho]
    have hT : acceleratedStep n = (3 * n + 1) / 2 := by
      unfold acceleratedStep; rw [if_neg (by omega)]
    rw [hT, oct_odd_step hn ho]
  · rw [if_neg ho]
    have he : n % 2 = 0 := by omega
    have hT : acceleratedStep n = n / 2 := by
      unfold acceleratedStep; rw [if_pos he]
    have hn2 : 2 ≤ n := by omega
    have hr : raiseIdx n = 0 := by unfold raiseIdx; rw [if_neg ho]
    rw [hT, hr]
    have := oct_even_step hn2 he
    omega

/-- **Only an odd step can raise the octave.**  This is the word/magnitude
rigidity of Round X's `divergent_record_steps_odd`, at the level of a single step
and for every orbit. -/
theorem odd_of_oct_lt {n : Nat} (hn : 0 < n) (h : oct n < oct (acceleratedStep n)) :
    n % 2 = 1 := by
  by_cases ho : n % 2 = 1
  · exact ho
  · exfalso
    have he : n % 2 = 0 := by omega
    have hT : acceleratedStep n = n / 2 := by
      unfold acceleratedStep; rw [if_pos he]
    have hn2 : 2 ≤ n := by omega
    have := oct_even_step hn2 he
    rw [hT] at h
    omega

end OctaveOrder
end Collatz
