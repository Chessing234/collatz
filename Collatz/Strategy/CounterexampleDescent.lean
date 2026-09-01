import Collatz.Strategy.ExcursionMap

/-!
# Counterexample-space descent — Devices 16 and 17

Assume a number `m > 1` never drops.  A descent *in the space of
counterexamples* would be an explicit map sending `m` to another
never-dropper with a strictly smaller value.  `T(m)` is not a candidate:
`m` odd forces `T(m) = (3m+1)/2 > m`.

Device 16 is the odd cofactor of `m+1`.  Device 17 is the adjacent
sibling obtained by stripping one factor of two from `m+1`.  Both are
strictly smaller.  Neither intertwines `T`, and neither preserves the
one-step growth property that `NeverDrops` requires of an odd start.
On a least non-Mersenne never-dropper the cofactor map produces a
dropper, by minimality in `Nat` — not by an unproved self-similarity.

No statement here is Collatz.
-/

namespace Collatz
namespace CounterexampleDescent

open Collatz.Arith Collatz.LiftExponent Collatz.OddRuns
open Collatz.ExcursionMap Collatz.NeverDrops


/-! ## The two maps -/

/-- Strip factors of two, using `fuel` to stay structurally recursive. -/
def oddPartAux : Nat → Nat → Nat
  | 0, n => n
  | fuel + 1, n => if n % 2 = 0 then oddPartAux fuel (n / 2) else n

/-- The odd part of a natural number. -/
def oddPart (n : Nat) : Nat := oddPartAux n n

/-- **Device 16.**  `Φ(n)` is the odd cofactor of `n+1`: `n+1 = 2^v · Φ(n)`
with `Φ(n)` odd. -/
def Phi (n : Nat) : Nat := oddPart (n + 1)

/-- **Device 17.**  `Ψ(n) = (n−1)/2`.  On odd `n` this peels one factor of
two from the shift: `Ψ(n)+1 = (n+1)/2`. -/
def Psi (n : Nat) : Nat := (n - 1) / 2

/-- The first excursion of an odd start does not land below the start. -/
def FirstGrows (n : Nat) : Prop :=
  ∃ v u W e : Nat, IsExcursion n v u W e ∧ n ≤ e


/-! ## 1.  Odd-part arithmetic -/

/-- Enough fuel recovers the factorisation `n = 2^v · odd`. -/
theorem oddPartAux_spec : ∀ (fuel n : Nat), 0 < n → n ≤ fuel →
    ∃ v : Nat, n = 2 ^ v * oddPartAux fuel n ∧ oddPartAux fuel n % 2 = 1 := by
  intro fuel
  induction fuel with
  | zero => intro n hn hle; omega
  | succ fuel ih =>
    intro n hn hle
    rw [oddPartAux]
    by_cases he : n % 2 = 0
    · rw [if_pos he]
      have hn2 : 0 < n / 2 := by omega
      have hle2 : n / 2 ≤ fuel := by omega
      obtain ⟨v, hv, hodd⟩ := ih (n / 2) hn2 hle2
      refine ⟨v + 1, ?_, hodd⟩
      rw [two_pow_succ, Nat.mul_assoc, ← hv]
      omega
    · rw [if_neg he]
      exact ⟨0, by simp, by omega⟩

/-- The odd part is a power-of-two divisor away from the number itself. -/
theorem oddPart_spec {n : Nat} (hn : 0 < n) :
    ∃ v : Nat, n = 2 ^ v * oddPart n ∧ oddPart n % 2 = 1 :=
  oddPartAux_spec n n hn (Nat.le_refl n)

/-- Stripping `2^k` from an odd cofactor recovers that cofactor. -/
theorem oddPart_two_pow_mul {m k : Nat} (hm : m % 2 = 1) :
    oddPart (2 ^ k * m) = m := by
  have hm0 : 0 < m := by omega
  have hn : 0 < 2 ^ k * m := Nat.mul_pos (two_pow_pos k) hm0
  obtain ⟨v, hv, hodd⟩ := oddPart_spec hn
  have hval : Val2 (2 ^ k * m) k := Val2.two_pow_mul (Val2.of_odd hm) k
  have hval' : Val2 (2 ^ k * m) v := ⟨oddPart (2 ^ k * m), hodd, hv⟩
  have heq : k = v := Val2.unique hval hval'
  subst heq
  exact (Val2.cofactor_unique hm hodd rfl hv).symm

/-- On an excursion, `Φ` is the cofactor `u`. -/
theorem phi_eq_u {n v u W e : Nat} (h : IsExcursion n v u W e) : Phi n = u := by
  have hn1 : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  have hu : u % 2 = 1 := h.2.1
  rw [Phi, hn1]
  exact oddPart_two_pow_mul hu


/-! ## 2.  Device 16 is a strict decrease, and does not intertwine `T` -/

/-- For odd `n > 1`, the cofactor of `n+1` is strictly smaller. -/
theorem phi_lt {n : Nat} (hodd : n % 2 = 1) (hgt : 1 < n) : Phi n < n := by
  have hn1 : 0 < n + 1 := by omega
  obtain ⟨v, hv, hodd'⟩ := oddPart_spec hn1
  have hvpos : 0 < v := by
    rcases Nat.eq_zero_or_pos v with rfl | hp
    · rw [Nat.pow_zero, Nat.one_mul] at hv
      omega
    · exact hp
  have hge : 2 * oddPart (n + 1) ≤ n + 1 := by
    have htwo : (2 : Nat) ^ 1 ≤ 2 ^ v := two_pow_le_two_pow hvpos
    have : (2 : Nat) ^ 1 * oddPart (n + 1) ≤ 2 ^ v * oddPart (n + 1) :=
      Nat.mul_le_mul_right _ htwo
    rw [Nat.pow_one] at this
    rwa [← hv] at this
  have hpos : 0 < oddPart (n + 1) := by omega
  have : oddPart (n + 1) < n := by omega
  simpa [Phi] using this

/-- `1` is a fixed point, not a descent. -/
theorem phi_one : Phi 1 = 1 := by decide

/-- Mersenne numbers collapse to `1`. -/
theorem phi_mersenne (k : Nat) : Phi (2 ^ k - 1) = 1 := by
  cases k with
  | zero =>
    simp [Phi, oddPart, oddPartAux]
  | succ k =>
    have hpos : 0 < 2 ^ (k + 1) := two_pow_pos (k + 1)
    have : (2 ^ (k + 1) - 1) + 1 = 2 ^ (k + 1) := by omega
    rw [Phi, this, show (2 : Nat) ^ (k + 1) = 2 ^ (k + 1) * 1 by rw [Nat.mul_one]]
    exact oddPart_two_pow_mul rfl

/-- The opening-run identity: `T^j(n)+1 = 2^{v−j} 3^j u` along the odd
run, which is *not* a function of the orbit of `u`. -/
theorem run_shift {n v u W e : Nat} (h : IsExcursion n v u W e) :
    acceleratedOrbit v n + 1 = 3 ^ v * u := by
  have hrun : OddRun n v := (oddRun_iff v n).mpr ⟨u, h.2.2.2.2.2.1⟩
  exact RunValue.oddRun_value_quot hrun h.2.2.2.2.2.1

/-- **Self-similarity obstruction.**  `Φ ∘ T ≠ T ∘ Φ` at every odd start.
The first odd step multiplies the shift `n+1` by `3/2`, so `Φ(T(n)) = 3u`,
while `T(Φ(n)) = (3u+1)/2`. -/
theorem not_intertwine {n v u W e : Nat} (h : IsExcursion n v u W e) :
    oddPart (acceleratedStep n + 1) ≠ acceleratedStep u := by
  have hn : n % 2 = 1 := h.1
  have hu : u % 2 = 1 := h.2.1
  have hv : 0 < v := h.2.2.2.1
  have hid : 2 * (acceleratedStep n + 1) = 3 * (n + 1) := two_mul_succ_step hn
  have hn1 : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  have h3u : (3 * u) % 2 = 1 := by
    have : (3 : Nat) % 2 = 1 := by decide
    rw [Nat.mul_mod, this, hu]
  have hpow : (2 : Nat) ^ v = 2 * 2 ^ (v - 1) := by
    cases v with
    | zero => omega
    | succ t =>
      rw [two_pow_succ, Nat.add_sub_cancel]
  have hshift : acceleratedStep n + 1 = 2 ^ (v - 1) * (3 * u) := by
    have hrhs : 3 * (n + 1) = 2 * (2 ^ (v - 1) * (3 * u)) := by
      rw [hn1, hpow]
      simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    have : 2 * (acceleratedStep n + 1) = 2 * (2 ^ (v - 1) * (3 * u)) := by
      rw [hid, hrhs]
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  have hphi : oddPart (acceleratedStep n + 1) = 3 * u := by
    rw [hshift]
    exact oddPart_two_pow_mul h3u
  have hTu : acceleratedStep u = (3 * u + 1) / 2 := by
    rw [acceleratedStep, if_neg (by omega)]
  intro heq
  rw [hphi, hTu] at heq
  have hcancel : 2 * ((3 * u + 1) / 2) = 3 * u + 1 := by omega
  omega

/-- Concrete witness of the obstruction at `27`.  `Φ(T(27)) = 21 ≠ 11 = T(Φ(27))`. -/
theorem not_intertwine_twenty_seven :
    oddPart (acceleratedStep 27 + 1) = 21 ∧ acceleratedStep 7 = 11 := by
  decide


/-! ## 3.  Device 16 cannot descend through a least non-Mersenne never-dropper -/

/-- If `m > 1` is a least never-dropper and is not Mersenne, then `Φ(m)`
drops.  The space of counterexamples is well-founded in `Nat`, so a
strictly smaller image of the least element cannot itself be a
never-dropper. -/
theorem phi_kills_least_non_mersenne {m : Nat}
    (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ y : Nat, 1 < y → y < m → ¬ NeverDrops y)
    (hnonmer : 1 < Phi m) :
    ¬ NeverDrops (Phi m) := by
  have hodd : m % 2 = 1 := odd_of_neverDrops hgt hnd
  have hlt : Phi m < m := phi_lt hodd hgt
  exact hmin (Phi m) hnonmer hlt

/-- `NeverDrops` on an odd start forces the first excursion to grow. -/
theorem firstGrows_of_neverDrops {n : Nat}
    (hodd : n % 2 = 1) (h : NeverDrops n) : FirstGrows n := by
  obtain ⟨v, u, W, e, hex⟩ := exists_excursion hodd
  refine ⟨v, u, W, e, hex, ?_⟩
  have hland := landing_eq hex
  have := h (v + W)
  rwa [← hland]


/-! ## 4.  First-excursion growth: the 27/7 pair, and the refutation -/

/-- `7` first-grows: landing `13`.  Light, since `2^{3+1} = 16 ≤ 27 = 3^3`. -/
theorem firstGrows_seven : FirstGrows 7 :=
  ⟨3, 1, 1, 13, seven_first_excursion, by omega⟩

/-- `27` first-grows: landing `31`.  Cofactor `Φ(27) = 7`. -/
theorem twenty_seven_is_excursion : IsExcursion 27 2 7 1 31 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

theorem phi_twenty_seven : Phi 27 = 7 := by decide

theorem firstGrows_twenty_seven : FirstGrows 27 :=
  ⟨2, 7, 1, 31, twenty_seven_is_excursion, by omega⟩

/-- The pair `27 ↦ 7` does *not* refute transfer of `FirstGrows` along `Φ`:
both first-grow.  It is recorded so that the obstruction is not mistaken
for this famous hailstone. -/
theorem phi_preserves_firstGrows_at_twenty_seven :
    Phi 27 = 7 ∧ FirstGrows 27 ∧ FirstGrows 7 :=
  ⟨phi_twenty_seven, firstGrows_twenty_seven, firstGrows_seven⟩

/-- `5` drops in one excursion, landing at `1`. -/
theorem not_firstGrows_five : ¬ FirstGrows 5 := by
  intro ⟨v, u, W, e, h, hle⟩
  have h5 : IsExcursion 5 1 3 3 1 := five_drops.1
  have he : e = 1 := next_odd_unique h h5
  omega

/-- `39 = 2^3 · 5 − 1` first-grows (landing `67`), and `Φ(39) = 5` drops. -/
theorem thirty_nine_is_excursion : IsExcursion 39 3 5 1 67 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

theorem phi_thirty_nine : Phi 39 = 5 := by decide

theorem firstGrows_thirty_nine : FirstGrows 39 :=
  ⟨3, 5, 1, 67, thirty_nine_is_excursion, by omega⟩

/-- **`FirstGrows` does not transfer along `Φ`.**  Witness `39 ↦ 5`. -/
theorem not_phi_preserves_firstGrows :
    FirstGrows 39 ∧ Phi 39 = 5 ∧ ¬ FirstGrows 5 :=
  ⟨firstGrows_thirty_nine, phi_thirty_nine, not_firstGrows_five⟩

/-- The whole family: `u ≡ 1 (mod 4)`, `u > 1`, forces `n = 8u−1` to
first-grow (the excursion is light: `16 ≤ 27`) while `u` itself drops
(`v = 1`). -/
theorem eight_u_is_excursion {u : Nat} (hu : u % 4 = 1) (_hgt : 1 < u) :
    IsExcursion (8 * u - 1) 3 u 1 ((27 * u - 1) / 2) := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, u = 4 * k + 1 := ⟨u / 4, by omega⟩
  subst hk
  have hodd_n : (8 * (4 * k + 1) - 1) % 2 = 1 := by omega
  have hu2 : (4 * k + 1) % 2 = 1 := by omega
  have hsimp : 27 * (4 * k + 1) - 1 = 108 * k + 26 := by omega
  have hdiv : (108 * k + 26) / 2 = 54 * k + 13 := by omega
  have he : ((27 * (4 * k + 1) - 1) / 2) % 2 = 1 := by
    rw [hsimp, hdiv]
    omega
  have h8 : (2 : Nat) ^ 3 = 8 := by decide
  have h27 : (3 : Nat) ^ 3 = 27 := by decide
  have h2 : (2 : Nat) ^ 1 = 2 := by decide
  refine ⟨hodd_n, hu2, he, by omega, by omega, ?_, ?_⟩
  · rw [h8]
    omega
  · rw [h27, h2, hsimp, hdiv]
    omega

theorem firstGrows_eight_u {u : Nat} (hu : u % 4 = 1) (hgt : 1 < u) :
    FirstGrows (8 * u - 1) := by
  refine ⟨3, u, 1, (27 * u - 1) / 2, eight_u_is_excursion hu hgt, ?_⟩
  exact no_drop_of_light (eight_u_is_excursion hu hgt) (by decide)

theorem not_firstGrows_of_one_mod_four {u : Nat}
    (hu : u % 4 = 1) (hgt : 1 < u) : ¬ FirstGrows u := by
  intro ⟨v, w, W, e, h, hle⟩
  have hv : v = 1 := (v_eq_one_iff h).mpr hu
  have hdrop : e < u := drop_of_v_one h hv hgt
  omega

/-- **Family form of the Device-16 obstruction on `FirstGrows`.** -/
theorem phi_firstGrows_obstruction {u : Nat}
    (hu : u % 4 = 1) (hgt : 1 < u) :
    FirstGrows (8 * u - 1) ∧ Phi (8 * u - 1) = u ∧ ¬ FirstGrows u := by
  refine ⟨firstGrows_eight_u hu hgt, ?_, not_firstGrows_of_one_mod_four hu hgt⟩
  have hex := eight_u_is_excursion hu hgt
  exact phi_eq_u hex


/-! ## 5.  Device 17 — adjacent sibling -/

/-- On odd `n`, `Ψ` peels one two from the shift. -/
theorem psi_shift {n : Nat} (hodd : n % 2 = 1) :
    Psi n + 1 = (n + 1) / 2 := by
  unfold Psi
  omega

/-- For `v ≥ 2`, the sibling keeps the same odd cofactor. -/
theorem psi_preserves_cofactor {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hv : 2 ≤ v) :
    Psi n + 1 = 2 ^ (v - 1) * u := by
  have hn : n % 2 = 1 := h.1
  have hn1 : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  have hpsi := psi_shift hn
  have hsplit : (2 : Nat) ^ v = 2 * 2 ^ (v - 1) := by
    match v, hv with
    | t + 2, _ =>
      rw [show t + 2 - 1 = t + 1 by omega, two_pow_succ]
  have hhalf : (n + 1) / 2 = 2 ^ (v - 1) * u := by
    rw [hn1, hsplit, Nat.mul_assoc]
    exact Nat.mul_div_cancel_left (2 ^ (v - 1) * u) (by omega)
  rwa [hhalf] at hpsi

/-- `Ψ` is strictly smaller for `n > 1`. -/
theorem psi_lt {n : Nat} (hgt : 1 < n) : Psi n < n := by
  unfold Psi
  omega

/-- `13` drops in one excursion (`v = 1`). -/
theorem thirteen_is_excursion : IsExcursion 13 1 7 2 5 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

theorem not_firstGrows_thirteen : ¬ FirstGrows 13 := by
  intro ⟨v, u, W, e, h, hle⟩
  have h13 := thirteen_is_excursion
  have he : e = 5 := next_odd_unique h h13
  omega

theorem psi_twenty_seven : Psi 27 = 13 := by decide

/-- **`FirstGrows` does not transfer along `Ψ`.**  Witness `27 ↦ 13`.
This is the pair complementary to `27 ↦ 7`: the cofactor first-grows,
the adjacent sibling drops. -/
theorem not_psi_preserves_firstGrows :
    FirstGrows 27 ∧ Psi 27 = 13 ∧ ¬ FirstGrows 13 :=
  ⟨firstGrows_twenty_seven, psi_twenty_seven, not_firstGrows_thirteen⟩

/-- A never-dropper is `3 (mod 4)`, so `Ψ` lands on an odd number. -/
theorem psi_odd_of_neverDrops {m : Nat} (hgt : 1 < m) (h : NeverDrops m) :
    Psi m % 2 = 1 := by
  have h4 : m % 4 = 3 := mod_four_of_neverDrops hgt h
  unfold Psi
  omega


/-! ## 6.  What transfer of `NeverDrops` along `Φ` would actually buy -/

/-- If `NeverDrops` passed to the odd cofactor, every never-dropper `> 1`
would produce a never-dropping Mersenne number.  The implication is a
reduction, not a proof of Collatz: the profile is already satisfied by
`2^k − 1` for large `k`. -/
theorem transfer_reaches_mersenne
    (htrans : ∀ x : Nat, 1 < x → NeverDrops x → NeverDrops (Phi x))
    {x : Nat} (hgt : 1 < x) (h : NeverDrops x) :
    ∃ k : Nat, 0 < k ∧ NeverDrops (2 ^ k - 1) := by
  induction x using Nat.strongRecOn with
  | _ x ih =>
    have hodd : x % 2 = 1 := odd_of_neverDrops hgt h
    have hlt : Phi x < x := phi_lt hodd hgt
    have hndu : NeverDrops (Phi x) := htrans x hgt h
    rcases Nat.lt_or_ge (Phi x) 2 with hsmall | hbig
    · have h1 : Phi x = 1 := by
        have hpos : 0 < Phi x := by
          obtain ⟨v, hv, hodd'⟩ := oddPart_spec (n := x + 1) (by omega)
          have : 0 < oddPart (x + 1) := by omega
          simpa [Phi] using this
        omega
      obtain ⟨v, hv, _⟩ := oddPart_spec (n := x + 1) (by omega)
      have hvpos : 0 < v := by
        rcases Nat.eq_zero_or_pos v with rfl | hp
        · rw [Nat.pow_zero, Nat.one_mul] at hv
          omega
        · exact hp
      have hx : x + 1 = 2 ^ v := by
        have : oddPart (x + 1) = 1 := by simpa [Phi] using h1
        rw [this, Nat.mul_one] at hv
        exact hv
      refine ⟨v, hvpos, ?_⟩
      have : x = 2 ^ v - 1 := by omega
      rwa [← this]
    · exact ih (Phi x) hlt hbig hndu

end CounterexampleDescent
end Collatz
