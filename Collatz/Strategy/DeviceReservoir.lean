import Collatz.Strategy.ExcursionLTE
import Collatz.Strategy.ExcursionCofactor

/-!
# The divisibility reservoir

`v₂(n)` is present supply: factors of two sitting in `n`, spent by even
steps.  The **reservoir** `R(n)` is future halving capacity stored in the
odd kernel, on the side of the cofactor that does *not* feed the current
peak `3^v u − 1`.

Write `n = 2^r κ` with `κ` odd, and `κ + 1 = 2^α μ` with `μ` odd.  Then

  `R(n) = v₂(μ + 1)`.

LTE reads the current extra halvings `W` off `v₂(μ − 1)` and `v₂(3^v − 1)`.
The unused neighbor `μ + 1` feeds `3^v μ + 1`.  After a light landing
`W = 1` that quantity is exactly `2(e + 1)`, so `R` predicts the *next*
odd-run length `v'` — a letter the current parity word `(v, W)` does not
contain.

This is not a rename of `W`, of `v₂(n)`, of plus-five, of 11-fuel, or of
`drop_iff` slack.  It is not a proof of Collatz.  The even branch of
`expStep` is `3x/2`, so the identity `3^v u + 1 = 2(e + 1)` never starts;
`3x + 5` and `3x + 7` use a different shift and break the same identity.
-/

namespace Collatz
namespace DeviceReservoir

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap
open Collatz.ExcursionLTE Collatz.ExcursionCofactor


/-! ## 1.  Definition -/

/-- The divisibility reservoir of `n` is `ρ` when the odd kernel `κ` of `n`
has successor cofactor `μ` (so `κ + 1 = 2^α μ` with `μ` odd) and
`v₂(μ + 1) = ρ`. -/
def Reservoir (n ρ : Nat) : Prop :=
  ∃ r κ α μ : Nat,
    Val2 n r ∧
    κ % 2 = 1 ∧ n = 2 ^ r * κ ∧
    μ % 2 = 1 ∧ κ + 1 = 2 ^ α * μ ∧
    Val2 (μ + 1) ρ


/-! ## 2.  Existence, uniqueness, even conservation -/

/-- Every positive integer has a reservoir. -/
theorem exists_reservoir {n : Nat} (hn : 0 < n) : ∃ ρ, Reservoir n ρ := by
  obtain ⟨r, hr⟩ := Val2.exists_of_pos hn
  obtain ⟨κ, hκ, hnκ⟩ := hr
  have hκp : 0 < κ + 1 := Nat.succ_pos κ
  obtain ⟨α, hα⟩ := Val2.exists_of_pos hκp
  obtain ⟨μ, hμ, hκα⟩ := hα
  have hμp : 0 < μ + 1 := Nat.succ_pos μ
  obtain ⟨ρ, hρ⟩ := Val2.exists_of_pos hμp
  exact ⟨ρ, r, κ, α, μ, ⟨κ, hκ, hnκ⟩, hκ, hnκ, hμ, hκα, hρ⟩

/-- The odd kernel is unique. -/
theorem kernel_unique {n r r' κ κ' : Nat}
    (hr : Val2 n r) (hr' : Val2 n r')
    (hκ : κ % 2 = 1) (hκ' : κ' % 2 = 1)
    (hn : n = 2 ^ r * κ) (hn' : n = 2 ^ r' * κ') : κ = κ' := by
  have heq : r = r' := Val2.unique hr hr'
  subst heq
  exact Val2.cofactor_unique hκ hκ' hn hn'

/-- The reservoir value is unique. -/
theorem reservoir_unique {n ρ ρ' : Nat}
    (h : Reservoir n ρ) (h' : Reservoir n ρ') : ρ = ρ' := by
  obtain ⟨r, κ, α, μ, hr, hκ, hnκ, hμ, hκα, hρ⟩ := h
  obtain ⟨r', κ', α', μ', hr', hκ', hnκ', hμ', hκα', hρ'⟩ := h'
  have hκeq : κ = κ' := kernel_unique hr hr' hκ hκ' hnκ hnκ'
  subst hκeq
  have hαeq : α = α' :=
    Val2.unique ⟨μ, hμ, hκα⟩ ⟨μ', hμ', hκα'⟩
  subst hαeq
  have hμeq : μ = μ' := Val2.cofactor_unique hμ hμ' hκα hκα'
  subst hμeq
  exact Val2.unique hρ hρ'

/-- **Even Collatz steps conserve the reservoir.**  Present supply is spent;
the odd kernel, and with it `R`, is unchanged.  False of `expStep`, whose
even branch multiplies the kernel by `3`. -/
theorem reservoir_even {n ρ : Nat} (_hn : 0 < n) :
    Reservoir (2 * n) ρ ↔ Reservoir n ρ := by
  constructor
  · intro h
    obtain ⟨r, κ, α, μ, hr, hκ, hnκ, hμ, hκα, hρ⟩ := h
    have hrpos : 0 < r := by
      rcases Nat.eq_zero_or_pos r with rfl | hp
      · have : (2 * n) % 2 = 1 := Val2.odd_of_zero hr
        omega
      · exact hp
    obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by omega⟩
    have hn' : Val2 n t := Val2.of_two_mul hr
    have hneq : n = 2 ^ t * κ := by
      have h2 : 2 * n = 2 ^ (t + 1) * κ := hnκ
      rw [two_pow_succ t, Nat.mul_assoc] at h2
      exact Nat.eq_of_mul_eq_mul_left (by omega : (0 : Nat) < 2) h2
    exact ⟨t, κ, α, μ, hn', hκ, hneq, hμ, hκα, hρ⟩
  · intro h
    obtain ⟨r, κ, α, μ, hr, hκ, hnκ, hμ, hκα, hρ⟩ := h
    refine ⟨r + 1, κ, α, μ, Val2.two_mul hr, hκ, ?_, hμ, hκα, hρ⟩
    rw [two_pow_succ r, Nat.mul_assoc, hnκ]


/-! ## 3.  Bridge to the excursion cofactor -/

/-- For an odd start the kernel is the start itself. -/
theorem reservoir_of_odd {n ρ : Nat} (hodd : n % 2 = 1) :
    Reservoir n ρ ↔
      ∃ α μ : Nat, μ % 2 = 1 ∧ n + 1 = 2 ^ α * μ ∧ Val2 (μ + 1) ρ := by
  constructor
  · intro h
    obtain ⟨r, κ, α, μ, hr, hκ, hnκ, hμ, hκα, hρ⟩ := h
    have hr0 : r = 0 := by
      have : Val2 n 0 := Val2.of_odd hodd
      exact Val2.unique hr this
    subst hr0
    rw [Nat.pow_zero, Nat.one_mul] at hnκ
    subst hnκ
    exact ⟨α, μ, hμ, hκα, hρ⟩
  · intro h
    obtain ⟨α, μ, hμ, hκα, hρ⟩ := h
    exact ⟨0, n, α, μ, Val2.of_odd hodd, hodd, by rw [Nat.pow_zero, Nat.one_mul],
      hμ, hκα, hρ⟩

/-- On an excursion, `R(n)` is exactly `v₂(u + 1)`. -/
theorem reservoir_of_excursion {n v u W e ρ : Nat}
    (h : IsExcursion n v u W e) :
    Reservoir n ρ ↔ Val2 (u + 1) ρ := by
  have hodd : n % 2 = 1 := h.1
  have hu : u % 2 = 1 := h.2.1
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  rw [reservoir_of_odd hodd]
  constructor
  · intro hR
    obtain ⟨α, μ, hμ, hκα, hρ⟩ := hR
    have hαv : α = v :=
      Val2.unique ⟨μ, hμ, hκα⟩ ⟨u, hu, hnu⟩
    subst hαv
    have hμu : μ = u := Val2.cofactor_unique hμ hu hκα hnu
    subst hμu
    exact hρ
  · intro hρ
    exact ⟨v, u, hu, hnu, hρ⟩


/-! ## 4.  Arithmetic of the unused neighbor `3^v u + 1` -/

/-- Peak-plus identity: `3^v (u + 1) − (3^v − 1) = 3^v u + 1`. -/
theorem plus_one_split {v u : Nat} (_hu : 1 ≤ u) :
    3 ^ v * (u + 1) - (3 ^ v - 1) = 3 ^ v * u + 1 := by
  rw [Nat.mul_add]
  have hb : 1 ≤ 3 ^ v := one_le_three_pow v
  omega

/-- Scaling `u + 1` by `3^v` does not change its valuation. -/
theorem val2_scaled_u_succ {v u ρ : Nat} (h : Val2 (u + 1) ρ) :
    Val2 (3 ^ v * (u + 1)) ρ := by
  have := Val2.mul (val2_three_pow v) h
  simpa using this

/-- If `y ≤ x` and `v₂(y) < v₂(x)`, the difference takes the smaller
valuation. -/
theorem val2_sub_of_lt {x y r s : Nat}
    (hyx : y ≤ x) (hy : Val2 y r) (hx : Val2 x s) (hrs : r < s) :
    Val2 (x - y) r := by
  have hne : x ≠ y := by
    intro heq
    subst heq
    exact Nat.lt_irrefl r (Val2.unique hy hx ▸ hrs)
  have hlt : y < x := Nat.lt_of_le_of_ne hyx hne.symm
  have hdpos : 0 < x - y := Nat.sub_pos_of_lt hlt
  obtain ⟨t, ht⟩ := Val2.exists_of_pos hdpos
  have hx' : Val2 (x - y + y) s := by
    rw [Nat.sub_add_cancel hyx]
    exact hx
  rcases Nat.lt_trichotomy t r with htr | heq | hrt
  · have hadd := Val2.add_of_lt ht hy htr
    have : t = s := Val2.unique hadd hx'
    omega
  · exact heq ▸ ht
  · have hadd := Val2.add_of_lt hy ht hrt
    have hcomm : y + (x - y) = x - y + y := Nat.add_comm _ _
    have : r = s := Val2.unique (hcomm ▸ hadd) hx'
    omega

/-- If `y ≤ x` and `v₂(x) < v₂(y)`, the difference takes `v₂(x)`. -/
theorem val2_sub_of_gt {x y r s : Nat}
    (hyx : y ≤ x) (hy : Val2 y s) (hx : Val2 x r) (hrs : r < s) :
    Val2 (x - y) r := by
  have hne : x ≠ y := by
    intro heq
    subst heq
    exact Nat.lt_irrefl r (Val2.unique hx hy ▸ hrs)
  have hlt : y < x := Nat.lt_of_le_of_ne hyx hne.symm
  have hdpos : 0 < x - y := Nat.sub_pos_of_lt hlt
  obtain ⟨t, ht⟩ := Val2.exists_of_pos hdpos
  have hx' : Val2 (x - y + y) r := by
    rw [Nat.sub_add_cancel hyx]
    exact hx
  rcases Nat.lt_trichotomy t s with hts | heq | hst
  · have hadd := Val2.add_of_lt ht hy hts
    exact Val2.unique hadd hx' ▸ ht
  · subst heq
    have hge := val2_add_succ_le ht hy hx'
    omega
  · have hadd := Val2.add_of_lt hy ht hst
    have hcomm : y + (x - y) = x - y + y := Nat.add_comm _ _
    have : s = r := Val2.unique (hcomm ▸ hadd) hx'
    omega

/-- Equal valuations: the difference is strictly more divisible by two. -/
theorem val2_sub_of_eq_ge {x y r t : Nat}
    (hyx : y < x) (hy : Val2 y r) (hx : Val2 x r) (ht : Val2 (x - y) t) :
    r + 1 ≤ t := by
  obtain ⟨m, hm, hex⟩ := hx
  obtain ⟨m', hm', hey⟩ := hy
  have hdiv : 2 ^ (r + 1) ∣ x - y := by
    have hmgt : m' < m := by
      have : 2 ^ r * m' < 2 ^ r * m := by
        rw [← hey, ← hex]
        exact hyx
      exact Nat.lt_of_mul_lt_mul_left this
    have hhalf : 2 * ((m - m') / 2) = m - m' := by omega
    refine ⟨(m - m') / 2, ?_⟩
    rw [hex, hey, ← Nat.mul_sub_left_distrib, ← hhalf, two_pow_succ r]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact (Val2.dvd_iff_le ht).mp hdiv

/-- `3^v − 1 ≤ 3^v (u + 1)` for `u ≥ 1`. -/
private theorem lte_le_scaled {v u : Nat} (hu : 1 ≤ u) :
    3 ^ v - 1 ≤ 3 ^ v * (u + 1) := by
  have h3 : 1 ≤ 3 ^ v := one_le_three_pow v
  have : 3 ^ v ≤ 3 ^ v * (u + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega


/-! ## 5.  Light landings: `R` predicts the next odd run -/

/-- After a light excursion, `3^v u + 1 = 2(e + 1)`.  This is the extra
Collatz halving `W = 1`; `expStep` does `3x/2` on the peak and misses it. -/
theorem light_peak_plus {n v u e : Nat} (h : IsExcursion n v u 1 e) :
    3 ^ v * u + 1 = 2 * (e + 1) := by
  have heq := peak_plus_eq h
  have h2 : (2 : Nat) ^ 1 = 2 := rfl
  rw [h2] at heq
  omega

/-- Light landing: `v₂(3^v u + 1) = v' + 1`. -/
theorem val2_light_peak_plus {n v u e v' u' : Nat}
    (h : IsExcursion n v u 1 e) (hu' : u' % 2 = 1)
    (hnext : e + 1 = 2 ^ v' * u') :
    Val2 (3 ^ v * u + 1) (v' + 1) := by
  have hV := val2_peak_plus h hu' hnext
  have h2 : (2 : Nat) ^ 1 = 2 := rfl
  have hid : 3 ^ v * u + 2 ^ 1 - 1 = 3 ^ v * u + 1 := by
    rw [h2]
    omega
  have hW : 1 + v' = v' + 1 := Nat.add_comm _ _
  exact hW ▸ (hid ▸ hV)

/-- `u ≥ 1` on an excursion. -/
private theorem u_ge_one {n v u W e : Nat} (h : IsExcursion n v u W e) : 1 ≤ u := by
  have : u % 2 = 1 := h.2.1
  omega

/-- **Main theorem, smaller-reservoir side.**  On a light excursion, if
`R(n) < v₂(3^v − 1)` then the next odd-run length is exactly `R(n) − 1`.

The current parity word is `(v, 1)`.  It does not determine `v'`.  The
unused cofactor neighbor does. -/
theorem next_v_of_reservoir_lt {n v u e ρ L v' u' : Nat}
    (h : IsExcursion n v u 1 e)
    (hρ : Val2 (u + 1) ρ)
    (hL : Val2 (3 ^ v - 1) L)
    (hu' : u' % 2 = 1)
    (hnext : e + 1 = 2 ^ v' * u')
    (hlt : ρ < L) :
    v' + 1 = ρ := by
  have hu : 1 ≤ u := u_ge_one h
  have hx : Val2 (3 ^ v * (u + 1)) ρ := val2_scaled_u_succ (v := v) hρ
  have hle : 3 ^ v - 1 ≤ 3 ^ v * (u + 1) := lte_le_scaled hu
  have hdiff := val2_sub_of_gt hle hL hx hlt
  have hsplit : 3 ^ v * (u + 1) - (3 ^ v - 1) = 3 ^ v * u + 1 := plus_one_split hu
  have hplus : Val2 (3 ^ v * u + 1) ρ := hsplit ▸ hdiff
  have hland := val2_light_peak_plus h hu' hnext
  exact Val2.unique hland hplus

/-- **Main theorem, LTE-dominated side.**  If `v₂(3^v − 1) < R(n)` on a
light excursion, the next run is `v₂(3^v − 1) − 1`. -/
theorem next_v_of_lte_lt {n v u e ρ L v' u' : Nat}
    (h : IsExcursion n v u 1 e)
    (hρ : Val2 (u + 1) ρ)
    (hL : Val2 (3 ^ v - 1) L)
    (hu' : u' % 2 = 1)
    (hnext : e + 1 = 2 ^ v' * u')
    (hlt : L < ρ) :
    v' + 1 = L := by
  have hu : 1 ≤ u := u_ge_one h
  have hx : Val2 (3 ^ v * (u + 1)) ρ := val2_scaled_u_succ (v := v) hρ
  have hle : 3 ^ v - 1 ≤ 3 ^ v * (u + 1) := lte_le_scaled hu
  have hdiff := val2_sub_of_lt hle hL hx hlt
  have hsplit : 3 ^ v * (u + 1) - (3 ^ v - 1) = 3 ^ v * u + 1 := plus_one_split hu
  have hplus : Val2 (3 ^ v * u + 1) L := hsplit ▸ hdiff
  have hland := val2_light_peak_plus h hu' hnext
  exact Val2.unique hland hplus

/-- **Collision.**  If `R(n) = v₂(3^v − 1)` on a light excursion, the next
run is at least `R(n)`. -/
theorem next_v_ge_of_collision {n v u e ρ v' u' : Nat}
    (h : IsExcursion n v u 1 e)
    (hρ : Val2 (u + 1) ρ)
    (hL : Val2 (3 ^ v - 1) ρ)
    (hu' : u' % 2 = 1)
    (hnext : e + 1 = 2 ^ v' * u') :
    ρ ≤ v' := by
  have hu : 1 ≤ u := u_ge_one h
  have hx : Val2 (3 ^ v * (u + 1)) ρ := val2_scaled_u_succ (v := v) hρ
  have hle : 3 ^ v - 1 ≤ 3 ^ v * (u + 1) := lte_le_scaled hu
  have hne : 3 ^ v - 1 ≠ 3 ^ v * (u + 1) := by
    intro heq
    have hsplit := plus_one_split (v := v) hu
    rw [heq] at hsplit
    have : 3 ^ v * u + 1 = 0 := by
      have : 3 ^ v * (u + 1) - (3 ^ v * (u + 1)) = 3 ^ v * u + 1 := hsplit
      omega
    omega
  have hlt : 3 ^ v - 1 < 3 ^ v * (u + 1) := Nat.lt_of_le_of_ne hle hne
  have hsplit : 3 ^ v * (u + 1) - (3 ^ v - 1) = 3 ^ v * u + 1 := plus_one_split hu
  have hland := val2_light_peak_plus h hu' hnext
  have hdiff : Val2 (3 ^ v * (u + 1) - (3 ^ v - 1)) (v' + 1) := hsplit ▸ hland
  have hge := val2_sub_of_eq_ge hlt hL hx hdiff
  omega


/-! ## 6.  Recursive meaning on a continuing odd run -/

/-- One accelerated odd step, while the run continues (`n ≡ 3 (mod 4)`),
replaces the cofactor `μ` by `3μ`.  The reservoir becomes `v₂(3μ + 1)`. -/
theorem reservoir_odd_continue {n v u W e ρ' : Nat}
    (h : IsExcursion n v u W e) (h3 : n % 4 = 3)
    (hρ' : Val2 (3 * u + 1) ρ') :
    Reservoir ((3 * n + 1) / 2) ρ' := by
  have hvne : v ≠ 1 := by
    intro hv
    have := (v_eq_one_iff h).mp hv
    omega
  have hv : 2 ≤ v := by
    have hvp : 0 < v := h.2.2.2.1
    omega
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  have hu : u % 2 = 1 := h.2.1
  have hT : (3 * n + 1) / 2 + 1 = 3 * (n + 1) / 2 := by omega
  have hpow : 2 ^ v = 2 * 2 ^ (v - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, v = k + 1 := ⟨v - 1, by omega⟩
    subst hk
    exact two_pow_succ k
  have hTeq : (3 * n + 1) / 2 + 1 = 2 ^ (v - 1) * (3 * u) := by
    rw [hT, hnu, hpow]
    have hx : 3 * (2 * 2 ^ (v - 1) * u) = 2 * (3 * 2 ^ (v - 1) * u) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [hx, Nat.mul_div_cancel_left _ (by omega : (0 : Nat) < 2)]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h3u : (3 * u) % 2 = 1 := by
    have h3odd : (3 : Nat) % 2 = 1 := rfl
    rw [Nat.mul_mod, h3odd, hu]
  have hTodd : ((3 * n + 1) / 2) % 2 = 1 := by
    have hTp : ((3 * n + 1) / 2 + 1) % 2 = 0 := by
      rw [hTeq, Nat.mul_mod]
      have : (2 : Nat) ^ (v - 1) % 2 = 0 :=
        two_pow_even (by omega : 0 < v - 1)
      rw [this]
      simp
    omega
  refine (reservoir_of_odd hTodd).mpr ?_
  exact ⟨v - 1, 3 * u, h3u, hTeq, hρ'⟩


/-! ## 7.  Witnesses: not `W`, not plus-five, not 11-fuel; next-run checks -/

theorem eleven_ex : IsExcursion 11 2 3 1 13 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

theorem twentyseven_ex : IsExcursion 27 2 7 1 31 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

theorem fiftynine_ex : IsExcursion 59 2 15 1 67 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

theorem eleven_reservoir : Reservoir 11 2 :=
  (reservoir_of_excursion eleven_ex).mpr ⟨1, rfl, rfl⟩

theorem twentyseven_reservoir : Reservoir 27 3 :=
  (reservoir_of_excursion twentyseven_ex).mpr ⟨1, rfl, rfl⟩

theorem fiftynine_reservoir : Reservoir 59 4 :=
  (reservoir_of_excursion fiftynine_ex).mpr ⟨1, rfl, rfl⟩

/-- Same first-excursion parity word `(v, W) = (2, 1)`, different reservoirs. -/
theorem same_word_different_reservoir :
    IsExcursion 11 2 3 1 13 ∧ IsExcursion 27 2 7 1 31 ∧
      Reservoir 11 2 ∧ Reservoir 27 3 ∧ 2 ≠ 3 :=
  ⟨eleven_ex, twentyseven_ex, eleven_reservoir, twentyseven_reservoir, by omega⟩

/-- `R` is not `W`. -/
theorem reservoir_ne_W :
    IsExcursion 11 2 3 1 13 ∧ Reservoir 11 2 :=
  ⟨eleven_ex, eleven_reservoir⟩

/-- `R` is not plus-five: `v₂(11 + 5) = 4`. -/
theorem reservoir_ne_plus_five : Val2 (11 + 5) 4 ∧ Reservoir 11 2 :=
  ⟨⟨1, rfl, rfl⟩, eleven_reservoir⟩

/-- `R` is not 11-fuel: `v₂(11 · 27 + 19) = 2`, while `R(27) = 3`. -/
theorem reservoir_ne_eleven_fuel : Val2 (11 * 27 + 19) 2 ∧ Reservoir 27 3 :=
  ⟨⟨79, rfl, rfl⟩, twentyseven_reservoir⟩

/-- Witness, `ρ < L`: `11` has `R = 2 < 3 = v₂(8)`, next run `v' = 1`. -/
theorem eleven_next_v : (1 : Nat) + 1 = 2 :=
  next_v_of_reservoir_lt eleven_ex ⟨1, rfl, rfl⟩ ⟨1, rfl, rfl⟩
    (by decide : (7 : Nat) % 2 = 1) (by decide : 13 + 1 = 2 ^ 1 * 7)
    (by omega : (2 : Nat) < 3)

theorem eleven_next_run : 13 % 4 = 1 := by decide

/-- Witness, `L < ρ`: `59` has `R = 4 > 3`, next run `v' = 2`. -/
theorem fiftynine_next_v : (2 : Nat) + 1 = 3 :=
  next_v_of_lte_lt fiftynine_ex ⟨1, rfl, rfl⟩ ⟨1, rfl, rfl⟩
    (by decide : (17 : Nat) % 2 = 1) (by decide : 67 + 1 = 2 ^ 2 * 17)
    (by omega : (3 : Nat) < 4)

theorem fiftynine_next_run : 67 % 8 = 3 := by decide

/-- Witness, collision: `27` has `R = 3 = L`, next run `v' = 5 ≥ 3`. -/
theorem twentyseven_next_v : (3 : Nat) ≤ 5 :=
  next_v_ge_of_collision twentyseven_ex ⟨1, rfl, rfl⟩ ⟨1, rfl, rfl⟩
    (by decide : (1 : Nat) % 2 = 1) (by decide : 31 + 1 = 2 ^ 5 * 1)

theorem twentyseven_next_run : 31 + 1 = 2 ^ 5 * 1 := by decide

/-- Even conservation on `10 → 5`.  `expStep 10 = 15` changes the reservoir. -/
theorem ten_conserves : Reservoir 10 2 ∧ Reservoir 5 2 := by
  have h5 : Reservoir 5 2 := by
    refine ⟨0, 5, 1, 3, Val2.of_odd (by decide), by decide, by decide,
      by decide, by decide, ⟨1, rfl, rfl⟩⟩
  have h10 : Reservoir 10 2 := (reservoir_even (by omega : (0 : Nat) < 5)).mpr h5
  exact ⟨h10, h5⟩

theorem fifteen_reservoir : Reservoir 15 1 :=
  ⟨0, 15, 4, 1, Val2.of_odd (by decide), by decide, by decide,
    by decide, by decide, ⟨1, rfl, rfl⟩⟩

/-- **`expStep` test.**  Collatz even step `10 → 5` conserves `R = 2`.
`expStep` sends `10` to `15`, whose reservoir is `1`. -/
theorem expStep_breaks_reservoir : Reservoir 10 2 ∧ Reservoir 15 1 ∧ 2 ≠ 1 :=
  ⟨ten_conserves.1, fifteen_reservoir, by omega⟩

/-- On the peak of `11`, Collatz extracts `W = 1` and lands at `13`.
`expStep` does `3 · 26 / 2 = 39`. -/
theorem expStep_misses_light_landing :
    3 * (3 ^ 2 * 3 - 1) / 2 = 39 ∧ 39 ≠ 13 := by
  decide

/-- **`3x + 5` test.**  The `3n + 1` odd run of `11` has length `2` and
passes through `17`.  The `3x + 5` odd step is already a different odd
number. -/
theorem three_x_five_breaks_run :
    (3 * 11 + 5) / 2 = 19 ∧ 19 ≠ 17 ∧ 19 ≠ 13 := by
  decide

/-- **`3x + 7` test.**  `59` is light of type `(2, 1)` for `3n + 1`, with
predicted next run `v' = 2` (landing `67`).  The first `3x + 7` odd step
already leaves the run. -/
theorem three_x_seven_breaks_run :
    (3 * 59 + 7) / 2 = 92 ∧ 92 % 2 = 0 ∧ 67 % 2 = 1 := by
  decide

end DeviceReservoir
end Collatz

section AxiomAudit
open Collatz.DeviceReservoir
#print axioms exists_reservoir
#print axioms reservoir_even
#print axioms reservoir_of_excursion
#print axioms next_v_of_reservoir_lt
#print axioms next_v_of_lte_lt
#print axioms next_v_ge_of_collision
#print axioms reservoir_odd_continue
#print axioms same_word_different_reservoir
#print axioms expStep_breaks_reservoir
end AxiomAudit
