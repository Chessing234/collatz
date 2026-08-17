import Collatz.Strategy.Descent

/-!
# Why backward descent cannot reach the multiples of three

`Descent` excludes the class `2 (mod 3)` outright and chips at `1 (mod 3)`.  The
class `0 (mod 3)` survives at every level of the search, and this file proves
that is not a limitation of the search: **no backward word of any length can
descend from a multiple of three.**

## The reason

A multiple of three has exactly one preimage under the accelerated map.

If `T(n) = v` with `n` even then `n = 2v`.  If `n` were odd then `3n + 1 = 2v`,
so `2v ≡ 1 (mod 3)`; but `3 ∣ v` forces `2v ≡ 0`.  So the odd preimage — the only
one that shrinks — does not exist (`pred_unique_of_three_dvd`).

Iterating, anything reaching a multiple of three in `k` steps is exactly `2 ^ k`
times it (`backward_of_three_dvd`).  The entire backward tree of a multiple of
three is a single doubling chain, so every element of it is *larger*
(`no_descent_of_three_dvd`).

**Consequently the descent programme cannot exclude `3 ∣ m`, by any word, at any
length, modulo any power of three.**  This is a genuine obstruction, not a gap
in the search, and it matches the computation exactly: at every modulus `3 ^ K`
tested, precisely the `3 ^ (K−1)` classes divisible by three survive.

## What it buys

The same fact runs forwards and is not purely negative.  If a never-dropping `m`
is divisible by three, no *later* point of its orbit is
(`orbit_not_three_dvd_of_neverDrops`): a later multiple of three would force the
whole preceding segment to be one, making `m` even, and a never-dropper above
`1` is odd.

On a cycle the orbit returns to `m`, so that is a contradiction, and
`neverDrops_cycle_not_three_dvd` re-proves `CycleModThree.not_three_dvd_of_accCycle`
in three lines from the predecessor count.  The divergent case has no return, so
it survives — which is precisely where the remaining difficulty sits.
-/

namespace Collatz
namespace ThreeObstruction

open Reach Congruence NeverDrops Descent

/-! ## A multiple of three has one preimage -/

/-- **Uniqueness of the preimage.**  The only accelerated preimage of a multiple
of three is its double; the shrinking odd preimage does not exist. -/
theorem pred_unique_of_three_dvd {n v : Nat} (h3 : 3 ∣ v) (h : acceleratedStep n = v) :
    n = 2 * v := by
  obtain ⟨w, hw⟩ := h3
  rcases Arith.mod_two_eq_zero_or_one n with he | ho
  · rw [acceleratedStep, if_pos he] at h
    omega
  · rw [acceleratedStep, if_neg (by omega)] at h
    omega

/-- **The backward tree is a doubling chain.**  Anything reaching a multiple of
three in `k` steps is exactly `2 ^ k` times it. -/
theorem backward_of_three_dvd {v : Nat} (h3 : 3 ∣ v) :
    ∀ (k n : Nat), acceleratedOrbit k n = v → n = 2 ^ k * v := by
  intro k
  induction k with
  | zero =>
    intro n h
    rw [acceleratedOrbit] at h
    simpa using h
  | succ k ih =>
    intro n h
    have hstep : acceleratedOrbit k (acceleratedStep n) = v := h
    have hk := ih (acceleratedStep n) hstep
    have hdvd : 3 ∣ 2 ^ k * v := Nat.dvd_trans h3 ⟨2 ^ k, Nat.mul_comm _ _⟩
    have := pred_unique_of_three_dvd hdvd (by rw [hk])
    rw [this, Arith.two_pow_succ, Nat.mul_assoc]

/-- **The obstruction.**  Nothing below a multiple of three ever reaches it, so
no backward word descends from `3 ∣ m`. -/
theorem no_descent_of_three_dvd {m n k : Nat} (h3 : 3 ∣ m) (_hm : 0 < m)
    (h : acceleratedOrbit k n = m) : m ≤ n := by
  have heq := backward_of_three_dvd h3 k n h
  have hpow : 0 < 2 ^ k := Arith.two_pow_pos k
  have hle : 1 * m ≤ 2 ^ k * m := Nat.mul_le_mul_right _ (by omega)
  omega

/-- Stated as the impossibility of the descent step used in `Descent`: there is
no strictly smaller predecessor at any depth. -/
theorem no_smaller_pred_of_three_dvd {m : Nat} (h3 : 3 ∣ m) (hm : 0 < m) :
    ¬ ∃ n k : Nat, n < m ∧ acceleratedOrbit k n = m := by
  intro ⟨n, k, hlt, h⟩
  have := no_descent_of_three_dvd h3 hm h
  omega

/-! ## The forward consequence -/

/-- **A never-dropping multiple of three leaves the multiples of three at once
and never returns.**  A later multiple of three would make the whole preceding
segment a doubling chain, forcing `m` to be even. -/
theorem orbit_not_three_dvd_of_neverDrops {m k : Nat} (hgt : 1 < m)
    (hnd : NeverDrops m) (hk : 0 < k) (h : 3 ∣ acceleratedOrbit k m) : False := by
  have hodd : m % 2 = 1 := odd_of_neverDrops hgt hnd
  have heq := backward_of_three_dvd h k m rfl
  have hpos : 0 < acceleratedOrbit k m := by
    have := hnd k
    omega
  have hsplit : (2:Nat) ^ k = 2 * 2 ^ (k - 1) := by
    have hk1 : k = (k - 1) + 1 := by omega
    rw [show (2:Nat) ^ k = 2 ^ ((k - 1) + 1) from by rw [← hk1], Arith.two_pow_succ]
  rw [hsplit, Nat.mul_assoc] at heq
  omega

/-- Hence no point of a never-dropping orbit past time zero is a multiple of
three. -/
theorem orbit_mod_three_of_neverDrops {m k : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hk : 0 < k) : acceleratedOrbit k m % 3 ≠ 0 := by
  intro h
  exact orbit_not_three_dvd_of_neverDrops hgt hnd hk (by omega)

/-- **A never-dropping point of a cycle is not a multiple of three.**  The orbit
returns to `m`, and by the previous result it cannot return to a multiple of
three.  This re-proves `CycleModThree.not_three_dvd_of_accCycle` from the
predecessor count alone. -/
theorem neverDrops_cycle_not_three_dvd {m L : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hL : 0 < L) (hcyc : acceleratedOrbit L m = m) : ¬ 3 ∣ m := by
  intro h3
  exact orbit_not_three_dvd_of_neverDrops hgt hnd hL (by rw [hcyc]; exact h3)

/-! ## Where this leaves the programme -/

/-- **The exact state of the descent programme.**  For the least never-dropper:

* `2 (mod 3)` is excluded (`Descent.minimal_not_two_mod_three`);
* `0 (mod 3)` can never be excluded by backward descent (`no_descent_of_three_dvd`),
  though it *is* excluded whenever the orbit is a cycle
  (`neverDrops_cycle_not_three_dvd`);
* `1 (mod 3)` is partially excluded — `4 (mod 9)` falls to
  `Descent.minimal_not_four_mod_nine`, and the search finds words for a further
  fraction of the classes.

So a divergent counterexample divisible by three is untouched by this method,
and that is the single case the programme provably cannot reach. -/
theorem programme_state {m : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x)) :
    m % 3 ≠ 2 ∧ m % 9 ≠ 4 ∧
    (∀ L : Nat, 0 < L → acceleratedOrbit L m = m → ¬ 3 ∣ m) ∧
    (3 ∣ m → ∀ n k : Nat, acceleratedOrbit k n = m → m ≤ n) :=
  ⟨minimal_not_two_mod_three hgt hnd hmin,
   minimal_not_four_mod_nine hgt hnd hmin,
   fun L hL hcyc => neverDrops_cycle_not_three_dvd hgt hnd hL hcyc,
   fun h3 n k h => no_descent_of_three_dvd h3 (by omega) h⟩

/-- **The reduction the programme achieves.**  Collatz follows from ruling out
never-droppers in the two surviving shapes: divisible by three, or `1 (mod 3)`
in a class with no descent word. -/
theorem collatz_of_no_surviving_class
    (h : ∀ m : Nat, 307200 ≤ m → m % 4 = 3 → (m % 3 = 0 ∨ m % 3 = 1) → ¬ NeverDrops m) :
    CollatzConjecture := by
  refine collatz_of_no_minimal_profile ?_
  intro m hge h4 h3 _
  exact h m hge h4 (by omega)

end ThreeObstruction
end Collatz
