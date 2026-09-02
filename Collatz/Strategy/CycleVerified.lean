import Collatz.Strategy.GapBarriers
import Collatz.Search.VerifiedRange
import Collatz.Strategy.NeverDrops

/-!
# A cycle's least element exceeds the verified range

`Collatz.Strategy.GapBarriers.cycle_length_ge_12_of_verified` takes
`1086464 < n 0` as a hypothesis.  This file discharges it from the repository's
own kernel-proved range, so nothing is assumed.

The argument avoids bounding every Terras iterate from below.  Instead:

* the Terras orbit of a cycle is **periodic** with period `K = Ksum k L`
  (`cycle_accOrbit_period`), because `traj_acceleratedOrbit` returns it to `n 0`;
* the Terras orbit of `1` stays inside `{1, 2}` (`accOrbit_one`);
* so if any iterate were `1`, then sliding forward to the next multiple of `K`
  would put `n 0` itself inside `{1, 2}`, contradicting `n 0 ≥ 3`.

That gives `¬ AccReachesOne (n 0)`, and `NeverDrops.accReachesOne_iff` together
with `VerifiedRange.verified_1086464` then forces `n 0 ≥ 1086464`.

Lean 4.33.0-rc1.  No Mathlib, no `sorry`, no `axiom`.
-/

namespace Collatz
namespace CycleVerified

open GapBarriers Reach

/-- The Terras orbit of `1` never leaves `{1, 2}`. -/
theorem accOrbit_one : ∀ s : Nat, acceleratedOrbit s 1 = 1 ∨ acceleratedOrbit s 1 = 2 := by
  intro s
  induction s with
  | zero => exact Or.inl rfl
  | succ s ih =>
    rw [acceleratedOrbit_succ_step]
    rcases ih with h | h <;> rw [h]
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- The Terras orbit of a cycle is periodic with period `K = Ksum k L`. -/
theorem cycle_accOrbit_period {n k : Nat → Nat} {L : Nat} (htraj : Traj n k L)
    (hodd : n 0 % 2 = 1) (hcyc : n L = n 0) :
    ∀ m : Nat, acceleratedOrbit (m * Ksum k L) (n 0) = n 0 := by
  have hone : acceleratedOrbit (Ksum k L) (n 0) = n 0 := by
    rw [traj_acceleratedOrbit L htraj hodd, hcyc]
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show (m + 1) * Ksum k L = Ksum k L + m * Ksum k L by
      rw [Nat.succ_mul]; omega, ← acceleratedOrbit_add, ih, hone]

/-- **A cycle above `2` never reaches `1`.** -/
theorem not_accReachesOne_of_cycle {n k : Nat → Nat} {L : Nat} (hL : 0 < L)
    (htraj : Traj n k L) (hodd : n 0 % 2 = 1) (hcyc : n L = n 0) (hN : 3 ≤ n 0) :
    ∀ t : Nat, acceleratedOrbit t (n 0) ≠ 1 := by
  intro t hcontra
  have hK : 1 ≤ Ksum k L := by
    have := Ksum_ge (k := k) L htraj.one_le
    omega
  have hge : t ≤ t * Ksum k L := Nat.le_mul_of_pos_right t (by omega)
  have hper := cycle_accOrbit_period htraj hodd hcyc t
  have hsplit : acceleratedOrbit (t * Ksum k L) (n 0)
      = acceleratedOrbit (t * Ksum k L - t) (acceleratedOrbit t (n 0)) := by
    rw [acceleratedOrbit_add]
    congr 1
    omega
  rw [hsplit, hcontra] at hper
  rcases accOrbit_one (t * Ksum k L - t) with h | h <;> rw [h] at hper <;> omega

/-- **The least element of a nontrivial cycle exceeds the verified range.**
Discharged from `VerifiedRange.verified_1086464`, which the repository proves in
the kernel — no citation and no external hypothesis. -/
theorem cycle_min_ge_verified {n k : Nat → Nat} {L : Nat} (hL : 0 < L)
    (htraj : Traj n k L) (hodd : n 0 % 2 = 1) (hcyc : n L = n 0) (hN : 3 ≤ n 0) :
    1086464 ≤ n 0 := by
  rcases Nat.lt_or_ge (n 0) 1086464 with hlt | hge
  · exfalso
    have hreach : ReachesOne (n 0) := VerifiedRange.verified_1086464 (n 0) (by omega) hlt
    obtain ⟨t, ht⟩ := (NeverDrops.accReachesOne_iff (by omega)).mp hreach
    exact not_accReachesOne_of_cycle hL htraj hodd hcyc hN t ht
  · exact hge

/-- **A nontrivial cycle has at least 12 odd steps — unconditionally.**

`GapBarriers.cycle_length_ge_12_of_verified` with its hypothesis discharged.
Nothing is cited: the `1086464` comes from this repository's own kernel-proved
`verified_1086464`, not from Barina's range. -/
theorem cycle_length_ge_12 {n k : Nat → Nat} {L : Nat}
    (htraj : Traj n k (L + 1)) (hodd : n 0 % 2 = 1) (hcyc : n (L + 1) = n 0)
    (hN : 3 ≤ n 0) (hmin : ∀ i : Nat, i < L + 1 → n 0 ≤ n i) : 12 ≤ L + 1 := by
  have hge := cycle_min_ge_verified (by omega) htraj hodd hcyc hN
  exact cycle_length_ge_12_of_verified htraj hcyc hmin (by omega)

/-! ## The valuation-count bound, at the verified scale

`GapBarriers.bigCount_bound` gives `2^E·(2N)^L ≤ (3N+1)^L` where `E` counts the
valuations `≥ 2` and `N` bounds the elements below.  Its strength depends
entirely on `N`: at `N = 3` it only forces a `0.2630` fraction of valuation-one
steps, and the `0.415037…` figure — `2 − log₂3` — is the `N → ∞` limit.

For a *cycle* that limit is essentially attained, because `cycle_min_ge_verified`
proves `N ≥ 1 086 464` outright.  At that `N`,

  `E ≤ 0.584963·L`,  so the valuation-one fraction is `≥ 0.415037`,

agreeing with the asymptotic value to six decimal places.  Nothing is assumed. -/

/-- **The count bound for a cycle, at the verified scale.** -/
theorem cycle_bigCount_bound {n k : Nat → Nat} {L : Nat} (hL : 0 < L)
    (htraj : Traj n k L) (hodd : n 0 % 2 = 1) (hcyc : n L = n 0) (hN : 3 ≤ n 0)
    (hmin : ∀ i : Nat, i < L → n 0 ≤ n i) :
    2 ^ bigCount k L * 2172928 ^ L ≤ 3259393 ^ L := by
  have hge := cycle_min_ge_verified hL htraj hodd hcyc hN
  have hposL : 0 < n L := by rw [hcyc]; omega
  have h := bigCount_bound (N := 1086464) htraj (by omega) hposL (by omega)
    (fun i hi => Nat.le_trans hge (hmin i hi))
  have e1 : 2 * 1086464 = 2172928 := rfl
  have e2 : 3 * 1086464 + 1 = 3259393 := rfl
  rw [e1, e2] at h
  exact h

set_option maxRecDepth 100000 in
/-- **At least five of the twelve valuations of a shortest possible cycle are
exactly `1`.**  `cycle_length_ge_12` says a nontrivial cycle has at least twelve
odd steps; at twelve, the count bound forces `E ≤ 7`. -/
theorem cycle_twelve_bigCount {n k : Nat → Nat}
    (htraj : Traj n k 12) (hodd : n 0 % 2 = 1) (hcyc : n 12 = n 0) (hN : 3 ≤ n 0)
    (hmin : ∀ i : Nat, i < 12 → n 0 ≤ n i) : bigCount k 12 ≤ 7 := by
  have h := cycle_bigCount_bound (by omega) htraj hodd hcyc hN hmin
  rcases Nat.lt_or_ge (bigCount k 12) 8 with hlt | hge
  · omega
  · exfalso
    have hpow : (2 : Nat) ^ 8 ≤ 2 ^ bigCount k 12 := Nat.pow_le_pow_right (by omega) hge
    have hmul : 2 ^ 8 * 2172928 ^ 12 ≤ 2 ^ bigCount k 12 * 2172928 ^ 12 :=
      Nat.mul_le_mul_right _ hpow
    have hnum : 3259393 ^ 12 < 2 ^ 8 * 2172928 ^ 12 := by decide
    omega

/-! ## The admissible-exponent window, at the verified scale

`cycle_three_pow_lt` and `cycle_min_bound` pin the cycle's halving total `K`
between two powers:
`3 ^ L < 2 ^ K` and `2 ^ K * N ^ L <= (3N+1) ^ L`, i.e. `3 ^ L < 2 ^ K <= (3 + 1/N) ^ L`.
The multiplicative width of that window is `(1 + 1/(3N)) ^ L`, so at the verified
scale `N >= 1086464` it is astronomically narrow: a power of two lands in it only
for very particular `L`.  This is the exact `Nat` form of the classical
Diophantine condition `0 < K*log 2 - L*log 3 <= L/(3N)`; nothing here is
asymptotic or heuristic.

Since `2 ^ K` only grows with `K`, the window is nonempty exactly when its
*smallest* candidate already fits.  That makes the test one comparison per `L`
rather than a search over `K`. -/

/-- The least exponent whose power of two exceeds `3 ^ L`. -/
def minPow2Above (L : Nat) : Nat := Nat.log2 (3 ^ L) + 1

theorem lt_two_pow_minPow2Above (L : Nat) : 3 ^ L < 2 ^ minPow2Above L :=
  Nat.lt_log2_self

/-- Minimality: any exponent clearing `3 ^ L` is at least `minPow2Above L`. -/
theorem minPow2Above_le {L K : Nat} (h : 3 ^ L < 2 ^ K) : minPow2Above L ≤ K := by
  rcases Nat.lt_or_ge K (minPow2Above L) with hlt | hge
  · exfalso
    have hKle : K ≤ Nat.log2 (3 ^ L) := by
      simp only [minPow2Above] at hlt; omega
    have hmono : (2 : Nat) ^ K ≤ 2 ^ Nat.log2 (3 ^ L) :=
      Nat.pow_le_pow_right (by omega) hKle
    have hpos : 0 < (3 : Nat) ^ L := Nat.pow_pos (by omega)
    have hself : (2 : Nat) ^ Nat.log2 (3 ^ L) ≤ 3 ^ L := Nat.log2_self_le (by omega)
    omega
  · exact hge

/-! ### An incremental scanner

Testing each length independently recomputes `3^L`, `V^L` and `(3V+1)^L` from
scratch, so a scan to `B` costs `O(B^2)` big multiplications.  Carrying the three
powers along — together with the running power of two — makes it `O(B)`.

The carried power of two is the only delicate part.  Writing `a` for the least
power of two above `3^L`, the least one above `3^(L+1)` is `2a` or `4a`, decided
by a single comparison; `minPow2Above_step` proves exactly that.

(As a scanning device this is also superseded: `CycleLength1539.excludedFast`
replaces the scan by two comparisons per length using `topIndex`, an integer
`⌊L·log₃2⌋`.  The `O(B)` carry below is still an improvement on recomputing the
powers, but it is not the best available shape.) -/

/-- A half-open band `(p, 2p]` contains at most one power of two. -/
theorem pow2_unique_in_band {e f p : Nat} (h1 : p < 2 ^ e) (h2 : 2 ^ e ≤ 2 * p)
    (h3 : p < 2 ^ f) (h4 : 2 ^ f ≤ 2 * p) : e = f := by
  have key : ∀ a b : Nat, p < 2 ^ b → 2 ^ a ≤ 2 * p → a ≤ b := by
    intro a b hb ha
    have hsucc : (2 : Nat) ^ (b + 1) = 2 ^ b * 2 := Nat.pow_succ _ _
    have hlt : (2 : Nat) ^ a < 2 ^ (b + 1) := by omega
    have := (Nat.pow_lt_pow_iff_right (by omega)).mp hlt
    omega
  have := key e f h3 h2
  have := key f e h1 h4
  omega

/-- The upper half of the band: `2 ^ minPow2Above L ≤ 2 * 3 ^ L`. -/
theorem two_pow_minPow2Above_le (L : Nat) : 2 ^ minPow2Above L ≤ 2 * 3 ^ L := by
  have hpos : 0 < (3 : Nat) ^ L := Nat.pow_pos (by omega)
  have hself : (2 : Nat) ^ Nat.log2 (3 ^ L) ≤ 3 ^ L := Nat.log2_self_le (by omega)
  have hsucc : (2 : Nat) ^ minPow2Above L = 2 ^ Nat.log2 (3 ^ L) * 2 := Nat.pow_succ _ _
  omega

/-- The recurrence driving the incremental scan. -/
theorem minPow2Above_step (L : Nat) :
    2 ^ minPow2Above (L + 1)
      = if 3 ^ (L + 1) < 2 * 2 ^ minPow2Above L then 2 * 2 ^ minPow2Above L
        else 4 * 2 ^ minPow2Above L := by
  have hpos : 0 < (3 : Nat) ^ L := Nat.pow_pos (by omega)
  have hlo : 3 ^ L < 2 ^ minPow2Above L := lt_two_pow_minPow2Above L
  have hhi : 2 ^ minPow2Above L ≤ 2 * 3 ^ L := two_pow_minPow2Above_le L
  have hlo' : 3 ^ (L + 1) < 2 ^ minPow2Above (L + 1) := lt_two_pow_minPow2Above (L + 1)
  have hhi' : 2 ^ minPow2Above (L + 1) ≤ 2 * 3 ^ (L + 1) := two_pow_minPow2Above_le (L + 1)
  have hp : (3 : Nat) ^ (L + 1) = 3 ^ L * 3 := Nat.pow_succ _ _
  have e1 : (2 : Nat) ^ (minPow2Above L + 1) = 2 ^ minPow2Above L * 2 := Nat.pow_succ _ _
  have e2 : (2 : Nat) ^ (minPow2Above L + 2) = 2 ^ (minPow2Above L + 1) * 2 := Nat.pow_succ _ _
  by_cases h : 3 ^ (L + 1) < 2 * 2 ^ minPow2Above L
  · rw [if_pos h]
    have := pow2_unique_in_band (p := 3 ^ (L + 1)) hlo' hhi'
      (f := minPow2Above L + 1) (by omega) (by omega)
    rw [this]; omega
  · rw [if_neg h]
    have := pow2_unique_in_band (p := 3 ^ (L + 1)) hlo' hhi'
      (f := minPow2Above L + 2) (by omega) (by omega)
    rw [this]; omega

/-- One comparison per length, carrying `p3 = 3^L`, `pV = V^L`, `pM = (3V+1)^L`
and `q = 2 ^ minPow2Above L`. -/
def windowScanFast (V : Nat) : Nat → Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _, _ => true
  | m + 1, p3, pV, pM, q =>
      decide (pM < q * pV) &&
        windowScanFast V m (p3 * 3) (pV * V) (pM * (3 * V + 1))
          (if p3 * 3 < 2 * q then 2 * q else 4 * q)

theorem windowScanFast_spec (V : Nat) : ∀ (m L : Nat),
    windowScanFast V m (3 ^ L) (V ^ L) ((3 * V + 1) ^ L) (2 ^ minPow2Above L) = true →
    ∀ j, j < m → (3 * V + 1) ^ (L + j) < 2 ^ minPow2Above (L + j) * V ^ (L + j) := by
  intro m
  induction m with
  | zero => intro L _ j hj; omega
  | succ m ih =>
    intro L hscan j hj
    simp only [windowScanFast, Bool.and_eq_true, decide_eq_true_eq] at hscan
    obtain ⟨h1, h2⟩ := hscan
    rw [← Nat.pow_succ, ← Nat.pow_succ, ← Nat.pow_succ, ← minPow2Above_step] at h2
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simpa using h1
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have := ih (L + 1) h2 j' (by omega)
      have hrw : L + 1 + j' = L + (j' + 1) := by omega
      rwa [hrw] at this

set_option maxRecDepth 40000 in
theorem windowScanFast_verified :
    windowScanFast 1086464 2966 1 1 1 2 = true := by decide

/-- `minPow2Above 0 = 1`, proved from the band rather than by reducing `Nat.log2`. -/
theorem minPow2Above_zero : minPow2Above 0 = 1 :=
  pow2_unique_in_band (p := 3 ^ 0) (lt_two_pow_minPow2Above 0)
    (two_pow_minPow2Above_le 0) (by decide) (by decide)

/-- A nontrivial cycle has at least 2966 odd steps.  Unconditional: the only
external input is the repository's kernel-checked verified range, via
`cycle_min_ge_verified`.

**This is superseded, and is kept only as an independent cross-check.**
`Strategy.RealizableFrontier6809.length_ge_6809` proves the stronger statement at
the same verified range: an odd-step budget of `4296`, frontier `L ≥ 6809` on the
accelerated clock, against `2966` and `4701` here.  The reason is that the
product bound `2 ^ K * N ^ L ≤ (3N+1) ^ L` used here is weaker than that file's
Beatty ceiling `Bcap`; by its own staircase table, the bound proved here at
`N = 1086464` is what the certificate already achieves at `c = 620859`.

What this does add is corroboration.  The window scan reaches the riser indices
`2966` and `3631` from a completely different inequality — no `Bcap`, no
certificate, just `cycle_three_pow_lt` against `cycle_min_bound` — and lands on
exactly the indices that table records.  Two independent routes to the same
staircase of convergents of `log₂ 3`. -/
theorem cycle_length_ge_2966 {n k : Nat → Nat} {L : Nat} (hL : 0 < L)
    (htraj : Traj n k L) (hodd : n 0 % 2 = 1) (hcyc : n L = n 0) (hN : 3 ≤ n 0)
    (hmin : ∀ i : Nat, i < L → n 0 ≤ n i) : 2966 ≤ L := by
  rcases Nat.lt_or_ge L 2966 with h | h
  · exfalso
    have hge := cycle_min_ge_verified hL htraj hodd hcyc hN
    have hmin' : ∀ i : Nat, i < L → 1086464 ≤ n i := fun i hi => Nat.le_trans hge (hmin i hi)
    have hK3 := cycle_three_pow_lt hL htraj hcyc (by omega)
    have hb := cycle_min_bound htraj hcyc (by omega) hmin'
    have hle : 2 ^ minPow2Above L * 1086464 ^ L ≤ 2 ^ Ksum k L * 1086464 ^ L :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (minPow2Above_le hK3))
    have hstart : windowScanFast 1086464 2966 (3 ^ 0) (1086464 ^ 0)
        ((3 * 1086464 + 1) ^ 0) (2 ^ minPow2Above 0) = true := by
      rw [minPow2Above_zero]; exact windowScanFast_verified
    have hspec := windowScanFast_spec 1086464 2966 0 hstart L h
    simp only [Nat.zero_add] at hspec
    omega
  · exact h

end CycleVerified
end Collatz
