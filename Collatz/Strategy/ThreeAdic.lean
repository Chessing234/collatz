import Collatz.Strategy.BackwardRun

/-!
# The exact 3-adic law of a forward step

`OddRuns` computes what a step does to the 2-adic valuation of `u = x + 1`.
This file computes what it does to the **3-adic** valuation, which is what the
master bound of `BackwardRun` is stated in terms of.

Two exact laws, in divisibility form so that no valuation function is needed:

* **odd step:** for odd `x`,  `3 ^ k ∣ (x + 1)  ↔  3 ^ (k+1) ∣ (T(x) + 1)`.
  The 3-adic valuation of `u` rises by *exactly one*, because `2(T(x)+1) = 3(x+1)`
  and `3` is coprime to `2`.
* **even step:** for even `x`,  `3 ^ j ∣ (T(x) + 1)  ↔  3 ^ j ∣ (x + 2)/2`;
  in particular `3 ∣ (T(x)+1)` exactly when `x ≡ 1 (mod 3)`.

A first guess — that `v₃(u)` simply counts the current run of odd steps — is
**false**: an even step can *inject* 3-divisibility from nothing.  Measured over
all orbits from odd starts below `20 000`, about `32%` of even steps do exactly
that.  So the even steps are where the master bound has content.

## The new constraint

Combining the even-step law with `BackwardRun.orbit_backward_bound` at the *next*
index gives, for the least never-dropper `m`:

**every even orbit point `x ≡ 1 (mod 3)` satisfies `x ≥ 3m + 1`.**

Equivalently, the window `[m, 3m+1)` contains no even orbit point congruent to
`1` modulo `3` — a forbidden region of width `2m`, in a residue class the earlier
results said nothing about.  Together with
`OrbitDescent.orbit_not_two_mod_three_below` (points `≡ 2 mod 3` are `≥ (3m+1)/2`)
both non-zero classes modulo three are now constrained, and by different amounts.
-/

namespace Collatz
namespace ThreeAdic

open Reach Congruence NeverDrops BackwardRun

/-! ## Coprimality -/

/-- A power of three dividing `2 y` divides `y`.  The mirror of
`OddRuns.dvd_of_three_mul`. -/
theorem dvd_of_two_mul : ∀ (k y : Nat), 3 ^ k ∣ 2 * y → 3 ^ k ∣ y := by
  intro k
  induction k with
  | zero => intro y _; simp
  | succ k ih =>
    intro y hdvd
    have hthree : y % 3 = 0 := by
      obtain ⟨c, hc⟩ := hdvd
      have h3 : (3:Nat) ^ (k + 1) = 3 * 3 ^ k := Arith.three_pow_succ k
      rw [h3, Nat.mul_assoc] at hc
      omega
    obtain ⟨y', hy'⟩ : ∃ y', y = 3 * y' := ⟨y / 3, by omega⟩
    subst hy'
    have hstrip : 3 ^ k ∣ 2 * y' := by
      obtain ⟨c, hc⟩ := hdvd
      refine ⟨c, ?_⟩
      have h3 : (3:Nat) ^ (k + 1) = 3 * 3 ^ k := Arith.three_pow_succ k
      rw [h3, Nat.mul_assoc] at hc
      omega
    obtain ⟨d, hd⟩ := ih y' hstrip
    refine ⟨d, ?_⟩
    have hA : (3:Nat) ^ (k + 1) * d = 3 * (3 ^ k * d) := by
      rw [Arith.three_pow_succ, Nat.mul_assoc]
    rw [hA, ← hd]

/-! ## The odd step raises the 3-adic valuation by exactly one -/

/-- **The odd-step law.**  For odd `x`, `3 ^ k` divides `x + 1` exactly when
`3 ^ (k+1)` divides `T(x) + 1`. -/
theorem three_pow_odd_step_iff {x : Nat} (hx : x % 2 = 1) (k : Nat) :
    3 ^ k ∣ (x + 1) ↔ 3 ^ (k + 1) ∣ (acceleratedStep x + 1) := by
  have hid : 2 * (acceleratedStep x + 1) = 3 * (x + 1) := OddRuns.two_mul_succ_step hx
  constructor
  · intro ⟨c, hc⟩
    refine dvd_of_two_mul (k + 1) _ ⟨c, ?_⟩
    have hA : (3:Nat) ^ (k + 1) * c = 3 * (3 ^ k * c) := by
      rw [Arith.three_pow_succ, Nat.mul_assoc]
    rw [hA, ← hc, ← hid]
  · intro ⟨c, hc⟩
    refine ⟨2 * c, ?_⟩
    have hA : (3:Nat) ^ (k + 1) * c = 3 * (3 ^ k * c) := by
      rw [Arith.three_pow_succ, Nat.mul_assoc]
    have hB : (3:Nat) ^ k * (2 * c) = 2 * (3 ^ k * c) := by
      rw [Nat.mul_left_comm]
    rw [hc, hA] at hid
    rw [hB]
    omega

/-! ## The even step can inject 3-divisibility -/

/-- **The even-step law at level one.**  For even `x`, the successor's shift is
divisible by three exactly when `x ≡ 1 (mod 3)`. -/
theorem three_dvd_even_step_iff {x : Nat} (hx : x % 2 = 0) :
    3 ∣ (acceleratedStep x + 1) ↔ x % 3 = 1 := by
  have hstep : acceleratedStep x = x / 2 := by
    rw [acceleratedStep, if_pos hx]
  rw [hstep]
  omega

/-! ## The new forbidden window -/

/-- **Even orbit points congruent to one modulo three are large.**  For the least
never-dropper, such a point is at least `3m + 1`.

The even step sends `x` to `x/2`, whose shift is divisible by three precisely on
this class; the master bound then applies at the next index with `j = 1`. -/
theorem even_orbit_one_mod_three_ge {m i : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x))
    (heven : acceleratedOrbit i m % 2 = 0)
    (hthree : acceleratedOrbit i m % 3 = 1) :
    3 * m + 1 ≤ acceleratedOrbit i m := by
  have hstep : acceleratedOrbit (i + 1) m = acceleratedOrbit i m / 2 := by
    rw [acceleratedOrbit_succ_step, acceleratedStep, if_pos heven]
  have hdvd : (3:Nat) ^ 1 ∣ (acceleratedOrbit (i + 1) m + 1) := by
    rw [Nat.pow_one, hstep]
    omega
  have hb := orbit_backward_bound (i := i + 1) (j := 1) hgt hnd hmin hdvd
  rw [Nat.pow_one, Nat.pow_one, hstep] at hb
  omega

/-- Restated as a forbidden window: no even orbit point below `3m + 1` is
`1 (mod 3)`. -/
theorem no_even_one_mod_three_below {m i : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x))
    (heven : acceleratedOrbit i m % 2 = 0)
    (hsmall : acceleratedOrbit i m < 3 * m + 1) :
    acceleratedOrbit i m % 3 ≠ 1 := by
  intro h
  have := even_orbit_one_mod_three_ge hgt hnd hmin heven h
  omega

/-- **Both non-zero classes modulo three are now constrained**, and by different
amounts: points `≡ 2 (mod 3)` are at least `(3m+1)/2`, and *even* points
`≡ 1 (mod 3)` are at least `3m + 1`. -/
theorem orbit_mod_three_windows {m i : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x)) :
    (2 * acceleratedOrbit i m < 3 * m + 1 → acceleratedOrbit i m % 3 ≠ 2) ∧
    (acceleratedOrbit i m % 2 = 0 → acceleratedOrbit i m < 3 * m + 1 →
      acceleratedOrbit i m % 3 ≠ 1) :=
  ⟨fun h => OrbitDescent.orbit_not_two_mod_three_below hgt hnd hmin h,
   fun he hs => no_even_one_mod_three_below hgt hnd hmin he hs⟩

/-! ## Odd starts never meet a multiple of three again

`ThreeObstruction.backward_of_three_dvd` says anything reaching a multiple of
three in `k` steps is exactly `2 ^ k` times it.  Applied to an odd start that is
immediately a contradiction, and it needs no never-dropping hypothesis at all. -/

/-- **An odd number's orbit avoids the multiples of three forever after.**  If
`3 ∣ T^k(x)` for `k ≥ 1` then `x = 2 ^ k · T^k(x)`, which is even. -/
theorem odd_orbit_not_three_dvd {x k : Nat} (hx : x % 2 = 1) (hk : 0 < k) :
    ¬ (3 ∣ acceleratedOrbit k x) := by
  intro h3
  have heq := ThreeObstruction.backward_of_three_dvd h3 k x rfl
  have hsplit : (2:Nat) ^ k = 2 * 2 ^ (k - 1) := by
    have hk1 : k = (k - 1) + 1 := by omega
    rw [show (2:Nat) ^ k = 2 ^ ((k - 1) + 1) from by rw [← hk1], Arith.two_pow_succ]
  rw [hsplit, Nat.mul_assoc] at heq
  omega

/-! ## No even orbit point low down

Composing the two forbidden windows with the previous theorem removes an entire
*parity* class from a whole interval, which neither window does alone. -/

/-- **The orbit of the least never-dropper has no even value below `(3m+1)/2`.**

An even orbit point `v` in that range cannot be `2 (mod 3)` (the first window),
cannot be `1 (mod 3)` (the second window, since `v < 3m+1`), and so would be
`0 (mod 3)` — impossible past time zero because `m` is odd.  Time zero is
excluded because `m` itself is odd. -/
theorem no_even_orbit_below {m i : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x))
    (heven : acceleratedOrbit i m % 2 = 0)
    (hsmall : 2 * acceleratedOrbit i m < 3 * m + 1) : False := by
  have hodd : m % 2 = 1 := odd_of_neverDrops hgt hnd
  -- time zero is odd, so `i ≥ 1`
  have hipos : 0 < i := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · exfalso
      subst h0
      rw [acceleratedOrbit] at heven
      omega
    · exact h0
  -- not `2 mod 3`
  have hne2 : acceleratedOrbit i m % 3 ≠ 2 :=
    OrbitDescent.orbit_not_two_mod_three_below hgt hnd hmin hsmall
  -- not `1 mod 3`
  have hne1 : acceleratedOrbit i m % 3 ≠ 1 :=
    no_even_one_mod_three_below hgt hnd hmin heven (by omega)
  -- so `0 mod 3`, impossible past time zero
  have h0 : 3 ∣ acceleratedOrbit i m := by omega
  exact odd_orbit_not_three_dvd hodd hipos h0

/-- Restated: every orbit value below `(3m+1)/2` is **odd**.  The orbit passes
through the window `[m, (3m+1)/2)` only at odd values, and each such value steps
up by exactly `3/2`, leaving the window at once. -/
theorem orbit_odd_below {m i : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x))
    (hsmall : 2 * acceleratedOrbit i m < 3 * m + 1) :
    acceleratedOrbit i m % 2 = 1 := by
  rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit i m) with he | ho
  · exact absurd (no_even_orbit_below hgt hnd hmin he hsmall) (fun h => h)
  · exact ho

/-- **The window is a single residue class modulo six.**  Past time zero the
orbit has no multiple of three at all, and in the window it has no even value and
nothing `2 (mod 3)`.  What is left is exactly `1 (mod 6)`. -/
theorem orbit_one_mod_six_below {m i : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x)) (hi : 0 < i)
    (hsmall : 2 * acceleratedOrbit i m < 3 * m + 1) :
    acceleratedOrbit i m % 6 = 1 := by
  have hodd : m % 2 = 1 := odd_of_neverDrops hgt hnd
  have hpodd : acceleratedOrbit i m % 2 = 1 := orbit_odd_below hgt hnd hmin hsmall
  have hne2 : acceleratedOrbit i m % 3 ≠ 2 :=
    OrbitDescent.orbit_not_two_mod_three_below hgt hnd hmin hsmall
  have hne0 : ¬ (3 ∣ acceleratedOrbit i m) := odd_orbit_not_three_dvd hodd hi
  omega

/-! ## The 3-adic dual of the run bound

`RunBounds.oddRun_le_cycleMax` says a bounded orbit caps the *2-adic* valuation
of `u = x + 1`: a run of `j` odd steps needs `2 ^ j ≤ M + 1`.  The master bound
gives the mirror statement for the *3-adic* valuation, and it is a two-sided
cap because it involves the minimum as well as the bound. -/

/-- **A bounded orbit caps the 3-adic valuation.**  If every point of the least
never-dropper's orbit is at most `B`, then `3 ^ j ∣ (T^i(m) + 1)` forces
`3 ^ j (m + 1) ≤ 2 ^ j (B + 1)`, i.e. `(3/2) ^ j ≤ (B+1)/(m+1)`. -/
theorem three_pow_le_of_bounded {m i j B : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x))
    (hB : ∀ k : Nat, acceleratedOrbit k m ≤ B)
    (hdvd : 3 ^ j ∣ (acceleratedOrbit i m + 1)) :
    3 ^ j * (m + 1) ≤ 2 ^ j * (B + 1) := by
  have hb := orbit_backward_bound hgt hnd hmin hdvd
  have hmono : 2 ^ j * (acceleratedOrbit i m + 1) ≤ 2 ^ j * (B + 1) :=
    Nat.mul_le_mul_left _ (by have := hB i; omega)
  omega

/-- Contrapositive: on a bounded orbit, no point is `−1` modulo `3 ^ j` once
`(3/2) ^ j` exceeds the spread `(B+1)/(m+1)`.  So the 3-adic valuation of `u` is
capped across the whole orbit, exactly as the 2-adic valuation is capped by the
run bound. -/
theorem no_high_three_valuation_of_bounded {m i j B : Nat} (hgt : 1 < m)
    (hnd : NeverDrops m) (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x))
    (hB : ∀ k : Nat, acceleratedOrbit k m ≤ B)
    (hspread : 2 ^ j * (B + 1) < 3 ^ j * (m + 1)) :
    ¬ (3 ^ j ∣ (acceleratedOrbit i m + 1)) := by
  intro hdvd
  have := three_pow_le_of_bounded hgt hnd hmin hB hdvd
  omega

/-- **The two caps together.**  On a bounded orbit both valuations of `u = x + 1`
are capped: the 2-adic one by the orbit bound alone (a run of `j` odd steps needs
`2 ^ j ≤ x + 1 ≤ B + 1`), the 3-adic one by the spread between the bound and the
minimum.  Divergent orbits escape both, which is precisely why the divergence
half is the harder one. -/
theorem both_caps {m i j B : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x))
    (hB : ∀ k : Nat, acceleratedOrbit k m ≤ B) :
    (2 ^ j ∣ (acceleratedOrbit i m + 1) → 2 ^ j ≤ B + 1) ∧
    (3 ^ j ∣ (acceleratedOrbit i m + 1) → 3 ^ j * (m + 1) ≤ 2 ^ j * (B + 1)) := by
  refine ⟨fun hdvd => ?_, fun hdvd => three_pow_le_of_bounded hgt hnd hmin hB hdvd⟩
  obtain ⟨c, hc⟩ := hdvd
  have hpos : 0 < acceleratedOrbit i m + 1 := by omega
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; rw [Nat.mul_zero] at hc; omega
    · exact h0
  have hle : 2 ^ j * 1 ≤ 2 ^ j * c := Nat.mul_le_mul_left _ hcpos
  have := hB i
  omega

end ThreeAdic
end Collatz
