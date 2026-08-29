import Collatz.Strategy.DeviceSwap

/-!
# Hercher's merging lemma, and the repository's Device 17 repaired

Hercher, *There are no Collatz m-cycles with m ≤ 91*, J. Integer Seq. 26 (2023),
Article 23.3.5 (arXiv:2201.00406).  His Lemma 9 is a **merging** lemma, and it is
exactly the map this repository already tried and discarded.

`CounterexampleDescent.Psi n = (n − 1) / 2` is Device 17, recorded there as
*"neither intertwines `T`"* — `not_psi_preserves_firstGrows`.  Hercher's Lemma 9
says the map does not have to intertwine: under one hypothesis the two orbits
**merge**, which is all a descent argument needs.

## The statement

Let `n` be odd with exactly `k` consecutive odd steps following it — equivalently
`n + 1 = 2 ^ k · u` with `u` odd — and let `ℓ` be the number of even steps after
those.  If `ℓ ≥ 2` then

`T^(k+2)(n) = T^(k+1)((n−1)/2)`.

The two trajectories are the same from then on (`merge_transfer`), so any
behaviour of `n`'s orbit — unboundedness in particular — is inherited by the
strictly smaller `(n−1)/2`.

## The derivation

Write `A = 3^(k−1) · u`, odd.  `run_climb` gives `T^k(n) = 3A − 1` and, since
`(n−1)/2 + 1 = 2^(k−1) · u`, also `T^(k−1)((n−1)/2) = A − 1`.

The hypothesis `4 ∣ 3A − 1` forces `A ≡ 3 (mod 4)` — because `A` is odd and
`3 · 3 ≡ 1 (mod 4)` — and therefore `A − 1 ≡ 2 (mod 4)`, so `(A−1)/2` is **odd**.
That is the whole content: the smaller trajectory arrives at an odd number exactly
when the larger one has a second halving to spend, and the two land together:

* larger: `3A − 1 → (3A−1)/2 → (3A−1)/4`, two even steps;
* smaller: `A − 1 → (A−1)/2` even step, then an **odd** step to
  `(3(A−1)/2 + 1)/2 = (3A−1)/4`.

## Why the repository's version failed

`CounterexampleDescent` asks `Ψ` to commute with `T` — `Φ(T(n)) = T(Φ(n))` — and
finds it does not.  Merging is weaker and sufficient: the orbits need not agree
step for step, only from some point on, and the number of steps differs by one on
each side.  The condition `ℓ ≥ 2` is what the repository's device was missing.

## Consequence for the divergence half (Hercher, Remark 10)

If a smallest divergent start exists, it has `ℓ = 1`: otherwise `(n−1)/2` is
smaller and inherits the divergence.  `merge_transfer` is the transfer step of that
argument, stated here without a divergence predicate so it applies to any
tail-property of the orbit.

## Testing

`merge` was checked on every odd `n < 400 000` satisfying its hypothesis —
100 002 cases, zero failures — before formalising.
-/

namespace Collatz
namespace HercherMerge

open Reach DeviceSwap

/-! ## The merging lemma -/

/-- Powers of three are odd. -/
theorem three_pow_odd' (j : Nat) : (3:Nat) ^ j % 2 = 1 := DeviceSwap.three_pow_odd j

/-- **Hercher's Lemma 9.**  With `n + 1 = 2^(j+1)·u` (`u` odd) — so `n` has exactly
`j+1` odd steps ahead of it — and at least two even steps after them, the orbit of
`n` and that of `(n−1)/2` meet:

`T^(j+3)(n) = T^(j+2)((n−1)/2)`. -/
theorem merge {n u j : Nat} (hu : u % 2 = 1)
    (hfac : n + 1 = 2 ^ (j + 1) * u)
    (hell : (3 ^ (j + 1) * u) % 4 = 1) :
    acceleratedOrbit (j + 3) n = acceleratedOrbit (j + 2) ((n - 1) / 2) := by
  have hupos : 0 < u := by omega
  -- `A = 3^j · u` is odd, and `3^(j+1)·u = 3A`
  have hA3 : (3:Nat) ^ (j + 1) * u = 3 * (3 ^ j * u) := by
    rw [Nat.pow_succ, Nat.mul_comm ((3:Nat) ^ j) 3, Nat.mul_assoc]
  have hAodd : (3 ^ j * u) % 2 = 1 := by
    rw [Nat.mul_mod, three_pow_odd' j, hu]
  -- the hypothesis pins `A` modulo four
  have hAmod : (3 ^ j * u) % 4 = 3 := by
    rw [hA3] at hell
    omega
  -- the larger trajectory: `T^(j+1)(n) = 3A − 1`
  have hbig := run_climb (j + 1) u n hupos hfac
  have hbigval : acceleratedOrbit (j + 1) n = 3 * (3 ^ j * u) - 1 := by
    rw [hA3] at hbig; omega
  -- the smaller start: `(n−1)/2 + 1 = 2^j · u`
  have hnval : n = 2 ^ (j + 1) * u - 1 := by omega
  have hhalf : (n - 1) / 2 + 1 = 2 ^ j * u := by
    have h2 : (2:Nat) ^ (j + 1) * u = 2 * (2 ^ j * u) := by
      rw [Arith.two_pow_succ, Nat.mul_assoc]
    have hpos : 0 < (2:Nat) ^ j * u := Nat.mul_pos (Arith.two_pow_pos j) hupos
    omega
  have hsmall := run_climb j u ((n - 1) / 2) hupos hhalf
  have hsmallval : acceleratedOrbit j ((n - 1) / 2) = 3 ^ j * u - 1 := by omega
  -- one even step on the small side, landing on an odd number
  have hev1 : acceleratedOrbit (j + 1) ((n - 1) / 2) = (3 ^ j * u - 1) / 2 := by
    rw [acceleratedOrbit_succ_step, hsmallval, acceleratedStep, if_pos (by omega)]
  have hoddmid : ((3 ^ j * u - 1) / 2) % 2 = 1 := by omega
  have hsm2 : acceleratedOrbit (j + 2) ((n - 1) / 2)
      = (3 * ((3 ^ j * u - 1) / 2) + 1) / 2 := by
    have hidx : j + 2 = (j + 1) + 1 := by omega
    rw [hidx, acceleratedOrbit_succ_step, hev1, acceleratedStep, if_neg (by omega)]
  -- two even steps on the large side
  have hbig1 : acceleratedOrbit (j + 2) n = (3 * (3 ^ j * u) - 1) / 2 := by
    have hidx : j + 2 = (j + 1) + 1 := by omega
    rw [hidx, acceleratedOrbit_succ_step, hbigval, acceleratedStep, if_pos (by omega)]
  have hbig2 : acceleratedOrbit (j + 3) n = ((3 * (3 ^ j * u) - 1) / 2) / 2 := by
    have hidx : j + 3 = (j + 2) + 1 := by omega
    rw [hidx, acceleratedOrbit_succ_step, hbig1, acceleratedStep, if_pos (by omega)]
  rw [hbig2, hsm2]
  omega

/-- **The transfer.**  Once the two orbits meet they agree for ever, so every
tail-property of `n`'s orbit is inherited by the strictly smaller `(n−1)/2`. -/
theorem merge_transfer {n u j : Nat} (hu : u % 2 = 1)
    (hfac : n + 1 = 2 ^ (j + 1) * u)
    (hell : (3 ^ (j + 1) * u) % 4 = 1) :
    ∀ t : Nat, acceleratedOrbit (j + 3 + t) n = acceleratedOrbit (j + 2 + t) ((n - 1) / 2) := by
  intro t
  have hm := merge hu hfac hell
  have hL : acceleratedOrbit (j + 3 + t) n
      = acceleratedOrbit t (acceleratedOrbit (j + 3) n) := by
    rw [acceleratedOrbit_add]
    congr 1
    omega
  have hR : acceleratedOrbit (j + 2 + t) ((n - 1) / 2)
      = acceleratedOrbit t (acceleratedOrbit (j + 2) ((n - 1) / 2)) := by
    rw [acceleratedOrbit_add]
    congr 1
    omega
  rw [hL, hR, hm]

/-- The descent is strict: the merging partner is smaller. -/
theorem merge_lt {n : Nat} (hn : 1 < n) : (n - 1) / 2 < n := by omega

/-- The largest orbit value over a prefix. -/
def orbitMax (n : Nat) : Nat → Nat
  | 0 => n
  | k + 1 => Nat.max (orbitMax n k) (acceleratedOrbit (k + 1) n)

theorem le_orbitMax (n : Nat) : ∀ K i : Nat, i ≤ K → acceleratedOrbit i n ≤ orbitMax n K := by
  intro K
  induction K with
  | zero =>
    intro i hi
    have hi0 : i = 0 := by omega
    rw [hi0]
    exact Nat.le_refl _
  | succ K ih =>
    intro i hi
    rcases Nat.lt_or_ge i (K + 1) with hlt | hge
    · exact Nat.le_trans (ih i (by omega)) (Nat.le_max_left _ _)
    · have hiK : i = K + 1 := by omega
      rw [hiK]
      exact Nat.le_max_right _ _

/-- **Hercher's Remark 10, transfer half.**  If the orbit of `n` is unbounded then
so is the orbit of the strictly smaller `(n−1)/2`.  Hence a smallest divergent
start cannot have two even steps after its opening odd run: it must have `ℓ = 1`.

The only bookkeeping is that an unbounded orbit has witnesses arbitrarily late,
since any prefix is bounded by `orbitMax`. -/
theorem unbounded_descends {n u j : Nat} (hu : u % 2 = 1)
    (hfac : n + 1 = 2 ^ (j + 1) * u)
    (hell : (3 ^ (j + 1) * u) % 4 = 1)
    (hub : ∀ B : Nat, ∃ t : Nat, B < acceleratedOrbit t n) :
    ∀ B : Nat, ∃ t : Nat, B < acceleratedOrbit t ((n - 1) / 2) := by
  intro B
  obtain ⟨s, hs⟩ := hub (B + orbitMax n (j + 2))
  rcases Nat.lt_or_ge s (j + 3) with hlt | hge
  · exfalso
    have hle := le_orbitMax n (j + 2) s (by omega)
    omega
  · refine ⟨j + 2 + (s - (j + 3)), ?_⟩
    have htr := merge_transfer hu hfac hell (s - (j + 3))
    have hidx : j + 3 + (s - (j + 3)) = s := by omega
    rw [hidx] at htr
    omega

end HercherMerge
end Collatz
