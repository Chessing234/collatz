import Collatz.Strategy.OrbitDescent

/-!
# Backward runs: the 3-adic mirror

`OddRuns.oddRun_iff` says a number takes `j` consecutive **odd steps** iff
`2 ^ j ∣ (x + 1)`, and then `2 ^ j (T^j(x) + 1) = 3 ^ j (x + 1)`.

The backward map has an exact mirror image of this, with the roles of `2` and
`3` exchanged.  The shrinking preimage `p(v) = (2v − 1)/3` satisfies

`3 · (p(v) + 1) = 2 · (v + 1)`,

which is the identity `3n + 1 = 2v` rewritten in the shifted coordinate — the
same shift `u = x + 1` that linearises the odd step.  Iterating:

**`j` consecutive backward steps are available at `v` iff `3 ^ j ∣ (v + 1)`,
and then `3 ^ j (p^j(v) + 1) = 2 ^ j (v + 1)`.**

So in the coordinate `u = x + 1`, an odd step multiplies by `3/2` and a backward
odd step multiplies by `2/3`; runs in either direction are governed by the
valuation of `u` at the *other* prime.  The two theorems are one theorem seen
from two sides.

## What it gives

Combining with `OrbitDescent.neverDrops_of_joins`: a backward run of length `j`
from any orbit point of the least never-dropper lands on a number that never
drops, so minimality forces it to be at least `m`.  That is

**for every orbit point `v` of the least never-dropper and every `j` with
`3 ^ j ∣ (v + 1)`:  `3 ^ j (m + 1) ≤ 2 ^ j (v + 1)`,  i.e.  `v + 1 ≥ (3/2)^j (m+1)`.**

This single statement subsumes the whole ladder of ad-hoc descents:

* `j = 1`, `v = m` gives `3(m+1) ≤ 2(m+1)`, impossible, so `3 ∤ (m+1)` — which is
  `Descent.minimal_not_two_mod_three`;
* `j = 1` at a general orbit point is `OrbitDescent.orbit_pred_ge`;
* every higher `j` is new.

Read contrapositively it is a **forbidden-valuation theorem**: no orbit point
below `(3/2)^j (m+1)` can be `−1` modulo `3 ^ j`.  Climbing backwards is rationed
exactly as climbing forwards is, and by the mirrored prime.
-/

namespace Collatz
namespace BackwardRun

open Reach Congruence NeverDrops Descent OrbitDescent

/-! ## The shifted coordinate -/

/-- The backward step in the shifted coordinate: `3(n+1) = 2(v+1)` is exactly
`3n + 1 = 2v`. -/
theorem backStep_shift (n v : Nat) : 3 * n + 1 = 2 * v ↔ 3 * (n + 1) = 2 * (v + 1) := by
  omega

/-- `2 ^ j ≤ 3 ^ j`. -/
theorem two_pow_le_three_pow (j : Nat) : (2:Nat) ^ j ≤ 3 ^ j :=
  Nat.pow_le_pow_left (by omega) j

/-! ## The orbit of one stays small -/

/-- Everything at or below `2` stays at or below `2`. -/
theorem accOrbit_small : ∀ (j x : Nat), 0 < x → x ≤ 2 → acceleratedOrbit j x ≤ 2 := by
  intro j
  induction j with
  | zero => intro x _ hx; rw [acceleratedOrbit]; exact hx
  | succ j ih =>
    intro x hx hx2
    have hstep : acceleratedStep x = 2 ∨ acceleratedStep x = 1 := by
      rcases (show x = 1 ∨ x = 2 by omega) with h | h <;> subst h <;> decide
    have hpos : 0 < acceleratedStep x := by rcases hstep with h | h <;> omega
    have hle : acceleratedStep x ≤ 2 := by rcases hstep with h | h <;> omega
    exact ih (acceleratedStep x) hpos hle

/-! ## Backward runs exist exactly on the `−1 mod 3 ^ j` classes -/

/-- **The backward run.**  If `3 ^ j ∣ (v + 1)` there is an `n` reaching `v` in
`j` steps with `3 ^ j (n + 1) = 2 ^ j (v + 1)`, and `n` is the least value of the
chain. -/
theorem exists_backChain : ∀ (j v : Nat), 0 < v → 3 ^ j ∣ (v + 1) →
    ∃ n : Nat, 0 < n ∧ 3 ^ j * (n + 1) = 2 ^ j * (v + 1) ∧
      acceleratedOrbit j n = v ∧ (∀ l : Nat, l < j → n ≤ acceleratedOrbit l n) := by
  intro j
  induction j with
  | zero =>
    intro v hv _
    refine ⟨v, hv, by simp, by rw [acceleratedOrbit], ?_⟩
    intro l hl
    omega
  | succ j ih =>
    intro v hv hdvd
    obtain ⟨c, hc⟩ := hdvd
    have hpow : (3:Nat) ^ (j + 1) = 3 * 3 ^ j := Arith.three_pow_succ j
    have h3pos : 0 < (3:Nat) ^ j := Arith.three_pow_pos j
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · subst h0; rw [Nat.mul_zero] at hc; omega
      · exact h0
    have h1 : 1 ≤ 3 ^ j * c := by
      calc (1:Nat) = 1 * 1 := by omega
        _ ≤ 3 ^ j * c := Nat.mul_le_mul h3pos hcpos
    have hA : v + 1 = 3 * (3 ^ j * c) := by rw [hc, hpow, Nat.mul_assoc]
    obtain ⟨n₁, hn₁def⟩ : ∃ n₁ : Nat, n₁ + 1 = 2 * (3 ^ j * c) :=
      ⟨2 * (3 ^ j * c) - 1, by omega⟩
    have hn₁pos : 0 < n₁ := by omega
    have hlink : 3 * (n₁ + 1) = 2 * (v + 1) := by rw [hn₁def, hA]; omega
    have hstepeq : 3 * n₁ + 1 = 2 * v := (backStep_shift n₁ v).mpr hlink
    have hdvd₁ : (3:Nat) ^ j ∣ (n₁ + 1) := ⟨2 * c, by rw [hn₁def, Nat.mul_left_comm]⟩
    obtain ⟨n, hnpos, hval, horb, hmid⟩ := ih n₁ hn₁pos hdvd₁
    have hstep : acceleratedStep n₁ = v := accStep_pred hn₁pos hstepeq
    have horb' : acceleratedOrbit (j + 1) n = v := by
      have hadd : acceleratedOrbit 1 (acceleratedOrbit j n) = acceleratedOrbit (1 + j) n :=
        acceleratedOrbit_add 1 j n
      rw [horb] at hadd
      have hone : acceleratedOrbit 1 n₁ = v := hstep
      rw [hone] at hadd
      rw [show j + 1 = 1 + j by omega, ← hadd]
    have hvalue : 3 ^ (j + 1) * (n + 1) = 2 ^ (j + 1) * (v + 1) := by
      have hA' : (3:Nat) ^ (j + 1) * (n + 1) = 3 * (3 ^ j * (n + 1)) := by
        rw [hpow, Nat.mul_assoc]
      have hB : (2:Nat) ^ (j + 1) * (v + 1) = 2 ^ j * (2 * (v + 1)) := by
        rw [Arith.two_pow_succ, Nat.mul_assoc, Nat.mul_left_comm]
      rw [hA', hval, hB, ← hlink, Nat.mul_left_comm]
    have hle₁ : n ≤ n₁ := by
      have h2 : (2:Nat) ^ j * (n₁ + 1) ≤ 3 ^ j * (n₁ + 1) :=
        Nat.mul_le_mul_right _ (two_pow_le_three_pow j)
      have hcancel : 3 ^ j * (n + 1) ≤ 3 ^ j * (n₁ + 1) := by omega
      have := Nat.le_of_mul_le_mul_left hcancel h3pos
      omega
    refine ⟨n, hnpos, hvalue, horb', ?_⟩
    intro l hl
    rcases Nat.lt_or_ge l j with hlt | hge
    · exact hmid l hlt
    · have hlj : l = j := by omega
      subst hlj
      rw [horb]
      exact hle₁

/-! ## The descent bound at every orbit point and every level -/

/-- **The master backward bound.**  For the least never-dropper `m`, every orbit
point `v` and every `j` with `3 ^ j ∣ (v + 1)` satisfies
`3 ^ j (m + 1) ≤ 2 ^ j (v + 1)`. -/
theorem orbit_backward_bound {m i j : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x))
    (hdvd : 3 ^ j ∣ (acceleratedOrbit i m + 1)) :
    3 ^ j * (m + 1) ≤ 2 ^ j * (acceleratedOrbit i m + 1) := by
  have hge : 307200 ≤ m := VerifiedSharp.neverDrops_ge_sharp hgt hnd
  have hv : m ≤ acceleratedOrbit i m := hnd i
  have hvpos : 0 < acceleratedOrbit i m := by omega
  obtain ⟨n, hnpos, hval, horb, hmid⟩ := exists_backChain j _ hvpos hdvd
  rcases Nat.lt_or_ge n m with hlt | hge'
  · exfalso
    have hnd' : NeverDrops n := neverDrops_of_joins hnd horb hmid (by omega)
    have hone : 1 < n := by
      rcases Nat.lt_or_ge n 2 with hsmall | hbig
      · exfalso
        have hn1 : n = 1 := by omega
        subst hn1
        have hb := accOrbit_small j 1 (by omega) (by omega)
        rw [horb] at hb
        omega
      · exact hbig
    exact hmin n hlt ⟨hone, hnd'⟩
  · have hmono : 3 ^ j * (m + 1) ≤ 3 ^ j * (n + 1) := Nat.mul_le_mul_left _ (by omega)
    omega

/-! ## Corollaries: what the master bound subsumes and what it adds -/

/-- **Recovering the level-one descent.**  At `i = 0`, `j = 1` the bound reads
`3(m+1) ≤ 2(m+1)`, which is false, so `3 ∤ (m + 1)`: the least never-dropper is
not `2 (mod 3)`.  This is `Descent.minimal_not_two_mod_three` as a special
case. -/
theorem not_two_mod_three_of_bound {m : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x)) : ¬ (3 ∣ (m + 1)) := by
  intro hdvd
  have hself : acceleratedOrbit 0 m = m := rfl
  have hb := orbit_backward_bound (i := 0) (j := 1) hgt hnd hmin
    (by rw [hself, Nat.pow_one]; exact hdvd)
  rw [hself, Nat.pow_one, Nat.pow_one] at hb
  omega

/-- **The forbidden-valuation form.**  No orbit point below `(3/2)^j (m+1)` can
be `−1` modulo `3 ^ j`.  Backward climbing is rationed exactly as forward
climbing is, with the primes exchanged. -/
theorem no_low_backward_run {m i j : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x))
    (hsmall : 2 ^ j * (acceleratedOrbit i m + 1) < 3 ^ j * (m + 1)) :
    ¬ (3 ^ j ∣ (acceleratedOrbit i m + 1)) := by
  intro hdvd
  have := orbit_backward_bound hgt hnd hmin hdvd
  omega

/-- **The mirror pair.**  Forward runs are governed by the `2`-adic valuation of
`x + 1` and backward runs by the `3`-adic valuation of the same quantity; each is
rationed by a power of the opposite prime.  Stated together at the least
never-dropper's own value. -/
theorem mirror_at_minimum {m : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x)) :
    (2:Nat) ^ 2 ∣ (m + 1) ∧ ¬ (3 ∣ (m + 1)) := by
  refine ⟨?_, not_two_mod_three_of_bound hgt hnd hmin⟩
  have h4 : m % 4 = 3 := mod_four_of_neverDrops hgt hnd
  have : (2:Nat) ^ 2 = 4 := by decide
  rw [this]
  omega

end BackwardRun
end Collatz
