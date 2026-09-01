import Collatz.Strategy.RayAsymmetry

/-!
# The order of 3 mod `2^j`, and why 2-adic congruences cannot obstruct divergence

`DepthThreshold` shows a window grows only if mean block depth exceeds
`log 3 / log(3/2) = 2.709511…`, against an unconstrained mean of `2`.  A divergent
orbit must sustain that forever.  The depths are not free — `a_{k+1} = v₂(3^(a_k−1)·w_k + 1)`
— so the natural attack is: each deep block *costs* a congruence, and sustaining
deep blocks means satisfying infinitely many congruences at once.  This file
carries that attack as far as it honestly goes, and then reports that it fails.

## The 2-adic structure, now proved

`RayAsymmetry.mirror_ray_deep` gave only `v₂(3^(2^s) − 1) ≥ s + 2`.  Here it is exact:

* **`exact_val`** — `∀ s ≥ 1, ∃ q, q odd ∧ 3^(2^s) = 2^(s+2)·q + 1`, i.e.
  `v₂(3^(2^s) − 1) = s + 2` on the nose.  The induction carries oddness of the
  quotient, since `q_{m+1} = 2^(m+2)·q_m² + q_m`.
* **`order_of_three`** — for `j ≥ 3`, `2^j ∣ 3^(2^(j−2)) − 1` and
  `2^j ∤ 3^(2^(j−3)) − 1`: **the multiplicative order of `3` mod `2^j` is exactly
  `2^(j−2)`.**  This is the fact underlying the whole `v₂(3^k·m + 1)` structure that
  `SwapForm`'s docstring records only by measurement.  New to this repository.
* `three_pow_periodic`, `three_pow_mod8` (sharpening `SwapForm.three_pow_mod_eight`'s
  `3^k % 8 ∈ {1,3}` to an exact `iff` on the parity of `k`), and the regeneration
  classes at `j = 3`:
  - `m ≡ 5 (mod 8)`: `8 ∣ 3^k·m + 1 ↔ k` odd
  - `m ≡ 7 (mod 8)`: `8 ∣ 3^k·m + 1 ↔ k` even
  - `m ≡ 1, 3 (mod 8)`: **never** — generalizing `RayAsymmetry.collatz_ray_shallow`
    from the ray `m = 1` to the whole coset.

For general `j` the corresponding `iff` and the uniqueness of `k` mod `2^(j−2)` need
a fiber-counting argument in the cyclic part of `(ℤ/2^j)*`; `order_of_three` supplies
the order, but the surjectivity onto the coset is **not** formalized here.  Stated
rather than claimed.

## The verdict: no obstruction, and why

**The congruence family is jointly satisfiable, with no finite-step conflict.**
Requiring depth `≥ j` at block `k+1` pins the exponent to one class mod `2^(j−2)`,
but leaves the odd part `w_{k+1}` — all the other bits — completely free.  Conditions
at different depths live on disjoint bit-positions of the 2-adic expansion and never
collide, because the block map is a **2-adic bijection**.  So deep blocks are cheap
to schedule 2-adically, and no counting or congruence argument at this level can
obstruct divergence.

This is a *non-obstruction*, and it is the deliverable.  It says precisely why the
divergence half needs a genuinely **archimedean** ingredient — something that sees
`n` itself and not merely its residues.

### Kill tests

* **`n ↦ n + 2^M`: FAILS**, as it must.  Everything here is a congruence on the
  current block's local coordinates, so adding `2^M` for `M` large relative to `j`
  changes nothing.  This is 2-adic-only — exactly the shape this development has
  killed a dozen devices on — and it is recorded as such rather than dressed up.
* No drift, no mean-zero heuristics, no density claims: every statement is an exact
  induction or an exact `iff`.
* `expStep` (`c = 0`) has no analogue: its block output `3^a·w` is odd times odd,
  so there is no `+1`-driven jump in 2-adic depth at all.  The theorems are
  vacuously inapplicable rather than violated — the correct outcome per
  `ShiftTrichotomy`.
* No claim is made that no divergent orbit exists.

No new bound; `RealizableFrontier6809.length_ge_6809` stands.
-/

namespace Collatz
namespace RegenOrder

private theorem sq_succ (y : Nat) : (y + 1) * (y + 1) = y * y + 2 * y + 1 := by
  simp [Nat.mul_add, Nat.add_mul]; omega

private theorem sq_mul (A q : Nat) : (A * q) * (A * q) = (A * A) * (q * q) := by
  simp [Nat.mul_comm, Nat.mul_left_comm]

/-- **Exact valuation.**  `v₂(3^(2^(m+1)) − 1) = m + 3` exactly (not just `≥`):
the quotient `q` is always odd.  This refines `RayAsymmetry.mirror_ray_deep`,
which proves only the `≥` half. -/
theorem three_pow_two_pow_odd_quotient :
    ∀ m : Nat, ∃ q : Nat, q % 2 = 1 ∧ 3 ^ (2 ^ (m + 1)) = 2 ^ (m + 3) * q + 1 := by
  intro m
  induction m with
  | zero => exact ⟨1, by decide, by decide⟩
  | succ m ih =>
    obtain ⟨q, hqodd, hq⟩ := ih
    refine ⟨2 ^ (m + 2) * (q * q) + q, ?_, ?_⟩
    · -- oddness of the new quotient
      have hA : (2 : Nat) ^ (m + 2) = 2 * 2 ^ (m + 1) := by
        rw [Nat.pow_succ]; omega
      have hAeven : 2 ^ (m + 2) * (q * q) = 2 * (2 ^ (m + 1) * (q * q)) := by
        rw [hA, Nat.mul_assoc]
      omega
    · -- same algebra as `mirror_ray_deep`
      have hd : 2 ^ (m + 2) = 2 ^ (m + 1) + 2 ^ (m + 1) := by
        rw [Nat.pow_succ]; omega
      have hsq : (3 : Nat) ^ (2 ^ (m + 2)) = 3 ^ (2 ^ (m + 1)) * 3 ^ (2 ^ (m + 1)) := by
        rw [hd, Nat.pow_add]
      have hAA : (2 : Nat) ^ (m + 3) * 2 ^ (m + 3) = 2 ^ (m + 4) * 2 ^ (m + 2) := by
        rw [← Nat.pow_add, ← Nat.pow_add]
        have he : m + 3 + (m + 3) = m + 4 + (m + 2) := by omega
        rw [he]
      have hp : (2 : Nat) ^ (m + 4) = 2 * 2 ^ (m + 3) := by
        rw [Nat.pow_succ]; omega
      have h2A : 2 * (2 ^ (m + 3) * q) = 2 ^ (m + 4) * q := by
        rw [hp, Nat.mul_assoc]
      rw [hsq, hq, sq_succ, sq_mul, hAA, h2A]
      simp [Nat.mul_add, Nat.mul_assoc]

/-- Restated with `s = m + 1 ≥ 1`: `v₂(3^(2^s) − 1) = s + 2` exactly. -/
theorem exact_val (s : Nat) (hs : 1 ≤ s) :
    ∃ q : Nat, q % 2 = 1 ∧ 3 ^ (2 ^ s) = 2 ^ (s + 2) * q + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  exact three_pow_two_pow_odd_quotient m

/-- **The order of `3` mod `2^j` is exactly `2^(j-2)`, for `j ≥ 3`.**  Divides
`2^(j-2)` (the `2^j ∣ 3^(2^(j-2)) − 1` half) but not `2^(j-3)` (the negation
half) — the standard `2`-adic fact behind the whole regeneration structure. -/
theorem order_of_three (j : Nat) (hj : 3 ≤ j) :
    (3 ^ (2 ^ (j - 2)) - 1) % 2 ^ j = 0
    ∧ (3 ^ (2 ^ (j - 3)) - 1) % 2 ^ j ≠ 0 := by
  constructor
  · obtain ⟨q, _, hq⟩ := exact_val (j - 2) (by omega)
    have he : j - 2 + 2 = j := by omega
    rw [he] at hq
    have : 3 ^ 2 ^ (j - 2) - 1 = 2 ^ j * q := by omega
    rw [this]
    simp [Nat.mul_mod_right]
  · rcases Nat.lt_or_ge j 4 with h3 | h4
    · -- j = 3 exactly: direct check, 3^1 - 1 = 2, 8 ∤ 2
      have : j = 3 := by omega
      subst this; decide
    · -- j ≥ 4: use exact_val at s = j - 3 ≥ 1
      obtain ⟨q, hqodd, hq⟩ := exact_val (j - 3) (by omega)
      have he : j - 3 + 2 = j - 1 := by omega
      rw [he] at hq
      have hsub : 3 ^ 2 ^ (j - 3) - 1 = 2 ^ (j - 1) * q := by omega
      rw [hsub]
      -- 2^j ∤ 2^(j-1)*q since q is odd: write q = 2t+1, then
      -- 2^(j-1)*q = 2^j*t + 2^(j-1), and 0 < 2^(j-1) < 2^j.
      obtain ⟨t, ht⟩ : ∃ t, q = 2 * t + 1 := ⟨q / 2, by omega⟩
      have hj1 : (2 : Nat) ^ j = 2 * 2 ^ (j - 1) := by
        obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        rw [hk]
        have hkk : (k + 1) - 1 = k := by omega
        rw [hkk, Nat.pow_succ, Nat.mul_comm]
      have hpos : 0 < (2:Nat) ^ (j - 1) := Nat.pow_pos (by omega)
      have hcomm : 2 ^ (j - 1) * (2 * t) = 2 ^ j * t := by
        rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ (j - 1)) 2, ← hj1]
      have hexp : 2 ^ (j - 1) * q = 2 ^ (j - 1) + 2 ^ j * t := by
        rw [ht, Nat.mul_add, Nat.mul_one, hcomm]
        omega
      have hlt : (2 : Nat) ^ (j - 1) < 2 ^ j := by rw [hj1]; omega
      rw [hexp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
      omega

/-- **Periodicity, one period.**  `3^k` is periodic mod `2^j` with period `2^(j-2)`
— the exact period, since `order_of_three` shows `2^(j-2)` is the order and no
smaller power of `2` works. -/
theorem three_pow_periodic (j : Nat) (hj : 3 ≤ j) (k : Nat) :
    3 ^ (k + 2 ^ (j - 2)) % 2 ^ j = 3 ^ k % 2 ^ j := by
  have h0 := (order_of_three j hj).1
  obtain ⟨c, hc⟩ : ∃ c, 3 ^ (2 ^ (j - 2)) - 1 = 2 ^ j * c := by
    have hpos2 : 0 < (2:Nat) ^ j := Nat.pow_pos (by omega)
    exact ⟨(3 ^ (2 ^ (j - 2)) - 1) / 2 ^ j, by
      have := Nat.div_add_mod (3 ^ (2 ^ (j - 2)) - 1) (2 ^ j)
      omega⟩
  have hpos3 : 0 < (3 : Nat) ^ (2 ^ (j - 2)) := Nat.pow_pos (by omega)
  have hc' : 3 ^ (2 ^ (j - 2)) = 2 ^ j * c + 1 := by omega
  have hsplit : (3 : Nat) ^ (k + 2 ^ (j - 2)) = 3 ^ k * 3 ^ (2 ^ (j - 2)) := by
    rw [Nat.pow_add]
  have hexp2 : (3 : Nat) ^ k * 3 ^ (2 ^ (j - 2)) = 3 ^ k + 2 ^ j * (3 ^ k * c) := by
    have hstep : (3:Nat) ^ k * (2 ^ j * c + 1) = 3 ^ k * (2 ^ j * c) + 3 ^ k := by
      rw [Nat.mul_add, Nat.mul_one]
    have hrearr : (3 : Nat) ^ k * (2 ^ j * c) = 2 ^ j * (3 ^ k * c) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (3 ^ k) (2 ^ j), Nat.mul_assoc]
    rw [hc', hstep, hrearr]
    omega
  rw [hsplit, hexp2, Nat.add_mul_mod_self_left]

/-- `3^k % 8` is exactly determined by the parity of `k`: `1` when even, `3`
when odd.  (This is `three_pow_mod_eight` from `SwapForm`, refined from a
membership fact `∈ {1,3}` to the exact value, by ordinary successor
induction — the `j = 3` case of the period-`2^(j-2)` pattern, done directly
rather than via `three_pow_periodic`.) -/
theorem three_pow_mod8 (k : Nat) :
    (k % 2 = 0 → 3 ^ k % 8 = 1) ∧ (k % 2 = 1 → 3 ^ k % 8 = 3) := by
  induction k with
  | zero => exact ⟨fun _ => by decide, fun h => by omega⟩
  | succ k ih =>
    obtain ⟨ih0, ih1⟩ := ih
    have hs : (3 : Nat) ^ (k + 1) = 3 ^ k * 3 := by rw [Nat.pow_succ]
    constructor
    · intro hk1
      have hk : k % 2 = 1 := by omega
      have h3 := ih1 hk
      obtain ⟨a, ha⟩ : ∃ a, 3 ^ k = 8 * a + 3 :=
        ⟨3 ^ k / 8, by have := Nat.div_add_mod (3 ^ k) 8; omega⟩
      rw [hs, ha]; omega
    · intro hk1
      have hk : k % 2 = 0 := by omega
      have h3 := ih0 hk
      obtain ⟨a, ha⟩ : ∃ a, 3 ^ k = 8 * a + 1 :=
        ⟨3 ^ k / 8, by have := Nat.div_add_mod (3 ^ k) 8; omega⟩
      rw [hs, ha]; omega

/-- **A concrete instance of the general congruence, fully verified.**  At
`j = 3` (period `2^(3-2) = 2`), for `m` odd with `m % 8 = 5`: `8 ∣ 3^k·m + 1`
holds exactly on the residue class `k % 2 = 1`. -/
theorem regen_class_j3_m5 (k m : Nat) (hm : m % 8 = 5) :
    (3 ^ k * m + 1) % 8 = 0 ↔ k % 2 = 1 := by
  have h := three_pow_mod8 k
  obtain ⟨a, ha⟩ : ∃ a, m = 8 * a + 5 :=
    ⟨m / 8, by have := Nat.div_add_mod m 8; omega⟩
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · have h1 := h.1 hk
    obtain ⟨b, hb⟩ : ∃ b, 3 ^ k = 8 * b + 1 :=
      ⟨3 ^ k / 8, by have := Nat.div_add_mod (3 ^ k) 8; omega⟩
    have heq : 3 ^ k * m = 8 * b * (8 * a + 5) + (8 * a + 5) := by
      rw [hb, ha, Nat.add_mul, Nat.one_mul]
    have heq2 : 8 * b * (8 * a + 5) = 8 * (b * (8 * a + 5)) := by rw [Nat.mul_assoc]
    rw [heq2] at heq
    omega
  · have h1 := h.2 hk
    obtain ⟨b, hb⟩ : ∃ b, 3 ^ k = 8 * b + 3 :=
      ⟨3 ^ k / 8, by have := Nat.div_add_mod (3 ^ k) 8; omega⟩
    have heq : 3 ^ k * m = 8 * b * (8 * a + 5) + 3 * (8 * a + 5) := by
      rw [hb, ha, Nat.add_mul]
    have heq2 : 8 * b * (8 * a + 5) = 8 * (b * (8 * a + 5)) := by rw [Nat.mul_assoc]
    rw [heq2] at heq
    omega

/-- The `m % 8 = 7` sibling: residue class `k % 2 = 0`. -/
theorem regen_class_j3_m7 (k m : Nat) (hm : m % 8 = 7) :
    (3 ^ k * m + 1) % 8 = 0 ↔ k % 2 = 0 := by
  have h := three_pow_mod8 k
  obtain ⟨a, ha⟩ : ∃ a, m = 8 * a + 7 :=
    ⟨m / 8, by have := Nat.div_add_mod m 8; omega⟩
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · have h1 := h.1 hk
    obtain ⟨b, hb⟩ : ∃ b, 3 ^ k = 8 * b + 1 :=
      ⟨3 ^ k / 8, by have := Nat.div_add_mod (3 ^ k) 8; omega⟩
    have heq : 3 ^ k * m = 8 * b * (8 * a + 7) + (8 * a + 7) := by
      rw [hb, ha, Nat.add_mul, Nat.one_mul]
    have heq2 : 8 * b * (8 * a + 7) = 8 * (b * (8 * a + 7)) := by rw [Nat.mul_assoc]
    rw [heq2] at heq
    omega
  · have h1 := h.2 hk
    obtain ⟨b, hb⟩ : ∃ b, 3 ^ k = 8 * b + 3 :=
      ⟨3 ^ k / 8, by have := Nat.div_add_mod (3 ^ k) 8; omega⟩
    have heq : 3 ^ k * m = 8 * b * (8 * a + 7) + 3 * (8 * a + 7) := by
      rw [hb, ha, Nat.add_mul]
    have heq2 : 8 * b * (8 * a + 7) = 8 * (b * (8 * a + 7)) := by rw [Nat.mul_assoc]
    rw [heq2] at heq
    omega

/-- The `m % 8 ∈ {1,3}` case: **never** satisfiable, for any `k` — this is
`RayAsymmetry.collatz_ray_shallow` (`m = 1`) generalized to the whole even
coset of residues that `3^k` never reaches when multiplied by `m`. -/
theorem regen_class_empty (k m : Nat) (hm : m % 8 = 1 ∨ m % 8 = 3) :
    (3 ^ k * m + 1) % 8 ≠ 0 := by
  have h := three_pow_mod8 k
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · have h1 := h.1 hk
    obtain ⟨b, hb⟩ : ∃ b, 3 ^ k = 8 * b + 1 :=
      ⟨3 ^ k / 8, by have := Nat.div_add_mod (3 ^ k) 8; omega⟩
    rcases hm with hm | hm
    · obtain ⟨a, ha⟩ : ∃ a, m = 8 * a + 1 :=
        ⟨m / 8, by have := Nat.div_add_mod m 8; omega⟩
      have heq : 3 ^ k * m = 8 * b * (8 * a + 1) + (8 * a + 1) := by
        rw [hb, ha, Nat.add_mul, Nat.one_mul]
      have heq2 : 8 * b * (8 * a + 1) = 8 * (b * (8 * a + 1)) := by rw [Nat.mul_assoc]
      rw [heq2] at heq; omega
    · obtain ⟨a, ha⟩ : ∃ a, m = 8 * a + 3 :=
        ⟨m / 8, by have := Nat.div_add_mod m 8; omega⟩
      have heq : 3 ^ k * m = 8 * b * (8 * a + 3) + (8 * a + 3) := by
        rw [hb, ha, Nat.add_mul, Nat.one_mul]
      have heq2 : 8 * b * (8 * a + 3) = 8 * (b * (8 * a + 3)) := by rw [Nat.mul_assoc]
      rw [heq2] at heq; omega
  · have h1 := h.2 hk
    obtain ⟨b, hb⟩ : ∃ b, 3 ^ k = 8 * b + 3 :=
      ⟨3 ^ k / 8, by have := Nat.div_add_mod (3 ^ k) 8; omega⟩
    rcases hm with hm | hm
    · obtain ⟨a, ha⟩ : ∃ a, m = 8 * a + 1 :=
        ⟨m / 8, by have := Nat.div_add_mod m 8; omega⟩
      have heq : 3 ^ k * m = 8 * b * (8 * a + 1) + 3 * (8 * a + 1) := by
        rw [hb, ha, Nat.add_mul]
      have heq2 : 8 * b * (8 * a + 1) = 8 * (b * (8 * a + 1)) := by rw [Nat.mul_assoc]
      rw [heq2] at heq; omega
    · obtain ⟨a, ha⟩ : ∃ a, m = 8 * a + 3 :=
        ⟨m / 8, by have := Nat.div_add_mod m 8; omega⟩
      have heq : 3 ^ k * m = 8 * b * (8 * a + 3) + 3 * (8 * a + 3) := by
        rw [hb, ha, Nat.add_mul]
      have heq2 : 8 * b * (8 * a + 3) = 8 * (b * (8 * a + 3)) := by rw [Nat.mul_assoc]
      rw [heq2] at heq; omega

end RegenOrder
end Collatz
