import Collatz.Strategy.ExcursionMap
import Collatz.Strategy.ScaleRecord
import Collatz.Strategy.AffineExact

/-!
# The successor pair, and the landing collision

The canonical partner of `n` is `n + 1`, not an arithmetic progression of
difference `2 ^ k`.  Consecutive integers have opposite parity, so the first
step is always mixed: the `+1` in `3n + 1` survives in the difference, instead
of cancelling as it does when both sides are odd.

The exact one-step laws are

* `n` odd  ⇒  `T(n) = T(n+1) + n`
* `n` even ⇒  `T(n+1) = T(n) + n + 2`

`expStep` replaces the even branch by `3x/2`.  On an odd start that gives
`expStep(n+1) = expStep n + 1`, not `+ n`.  The identity that uses the `+1`
fails because `expStep` treats the even side as if the inhomogeneous term were
`0`.

Along an excursion `n + 1 = 2 ^ v u`, the partner is a pure-halving orbit:
`T^v(n+1) = u`, the odd cofactor.  That is the pair evolution; it is not a
ranking on `u` (already refuted in `ExcursionCofactor`).  At the same time the
odd run of `n` is at the peak `3 ^ v u − 1`.  After the extra halvings, a
same-time meeting `T^{v+W}(n) = T^{v+W}(n+1)` would force

    2 ^ W · T^W(u) + 1  =  3 ^ v · u

with `W < v` on every light excursion, which is impossible.

No statement about the existence of never-droppers is made.
-/

namespace Collatz
namespace DeviceCollision

open Collatz.Arith Collatz.LiftExponent Collatz.OddRuns Collatz.RunValue
open Collatz.RunDescent Collatz.ExcursionMap Collatz.ScaleRecord
open Collatz.AffineExact


/-! ## 1.  One-step pair laws (the `+1` is the content) -/

/-- **Odd start.**  `T(n) − T(n+1) = n`.  The `+1` does not cancel, because
the partner is even. -/
theorem odd_succ_step {n : Nat} (h : n % 2 = 1) :
    acceleratedStep n = acceleratedStep (n + 1) + n := by
  have he : (n + 1) % 2 = 0 := by omega
  rw [acceleratedStep, acceleratedStep, if_neg (by omega), if_pos he]
  omega

/-- **Even start.**  `T(n+1) − T(n) = n + 2`. -/
theorem even_succ_step {n : Nat} (h : n % 2 = 0) :
    acceleratedStep (n + 1) = acceleratedStep n + n + 2 := by
  have ho : (n + 1) % 2 = 1 := by omega
  rw [acceleratedStep, acceleratedStep, if_pos h, if_neg (by omega)]
  omega

/-- **`expStep` fails the odd-start identity.**  The even partner is multiplied
by `3/2` rather than halved, and the difference collapses to `1`. -/
theorem expStep_succ_of_odd {n : Nat} (h : n % 2 = 1) :
    expStep (n + 1) = expStep n + 1 := by
  have he : (n + 1) % 2 = 0 := by omega
  have hL : expStep (n + 1) = 3 * (n + 1) / 2 := by
    unfold expStep
    rw [if_pos he]
  have hR : expStep n = (3 * n + 1) / 2 := by
    unfold expStep
    rw [if_neg (by omega)]
  rw [hL, hR]
  omega

/-- The Collatz odd-start law and the `expStep` law disagree on every odd start. -/
theorem expStep_ne_odd_succ_step {n : Nat} (h : n % 2 = 1) :
    expStep (n + 1) ≠ acceleratedStep (n + 1) + n := by
  have hC := odd_succ_step h
  have hE := expStep_succ_of_odd h
  have hodd : expStep n = acceleratedStep n := expStep_odd_eq h
  intro heq
  have : expStep n + 1 = acceleratedStep n := by
    rw [← hE, heq, ← hC]
  omega


/-! ## 2.  Two-step laws, split by the class of `n` -/

/-- `n ≡ 1 (mod 4)`: after two steps the pair is again consecutive, swapped.
This is the `v = 1` family, which drops in one excursion. -/
theorem two_step_one_mod_four {n : Nat} (h : n % 4 = 1) :
    acceleratedOrbit 2 (n + 1) = acceleratedOrbit 2 n + 1 := by
  have hn : n % 2 = 1 := by omega
  have he : (n + 1) % 2 = 0 := by omega
  have hT : acceleratedStep n = (3 * n + 1) / 2 := by
    rw [acceleratedStep, if_neg (by omega)]
  have hS : acceleratedStep (n + 1) = (n + 1) / 2 := by
    rw [acceleratedStep, if_pos he]
  have hTe : ((3 * n + 1) / 2) % 2 = 0 := by omega
  have hSo : ((n + 1) / 2) % 2 = 1 := by omega
  have hT2 : acceleratedOrbit 2 n = (3 * n + 1) / 4 := by
    change acceleratedStep (acceleratedStep n) = _
    rw [hT, acceleratedStep, if_pos hTe]
    omega
  have hS2 : acceleratedOrbit 2 (n + 1) = (3 * n + 5) / 4 := by
    change acceleratedStep (acceleratedStep (n + 1)) = _
    rw [hS, acceleratedStep, if_neg (by omega)]
    omega
  omega

/-- `n ≡ 3 (mod 4)`: the difference after two steps is exactly `2n + 1`. -/
theorem two_step_three_mod_four {n : Nat} (h : n % 4 = 3) :
    acceleratedOrbit 2 n = acceleratedOrbit 2 (n + 1) + 2 * n + 1 := by
  have hn : n % 2 = 1 := by omega
  have he : (n + 1) % 2 = 0 := by omega
  have hT : acceleratedStep n = (3 * n + 1) / 2 := by
    rw [acceleratedStep, if_neg (by omega)]
  have hS : acceleratedStep (n + 1) = (n + 1) / 2 := by
    rw [acceleratedStep, if_pos he]
  have hTo : ((3 * n + 1) / 2) % 2 = 1 := by omega
  have hSe : ((n + 1) / 2) % 2 = 0 := by omega
  have hT2 : acceleratedOrbit 2 n = (9 * n + 5) / 4 := by
    change acceleratedStep (acceleratedStep n) = _
    rw [hT, acceleratedStep, if_neg (by omega)]
    omega
  have hS2 : acceleratedOrbit 2 (n + 1) = (n + 1) / 4 := by
    change acceleratedStep (acceleratedStep (n + 1)) = _
    rw [hS, acceleratedStep, if_pos hSe]
    omega
  omega


/-! ## 3.  Affine pair evolution -/

/-- **Exact pair law, any two starts.**  Subtracting the affine identities
is this sum, written so both sides stay in `Nat`.  The `+1` lives entirely
in the two accumulators. -/
theorem affine_pair (n m k : Nat) :
    2 ^ k * acceleratedOrbit k n + 3 ^ oddCount m k * m + affineC k m =
      2 ^ k * acceleratedOrbit k m + 3 ^ oddCount n k * n + affineC k n := by
  have hn := affine_exact n k
  have hm := affine_exact m k
  omega

/-- **Homogeneous difference.**  When the first `k` parities agree, the
accumulators and odd-counts match, and the `+1` cancels.  The successor pair
never meets this hypothesis at `k ≥ 1`, because consecutive integers have
opposite parity. -/
theorem same_parity_pair {n m k : Nat}
    (hc : oddCount n k = oddCount m k) (hC : affineC k n = affineC k m) :
    2 ^ k * acceleratedOrbit k n + 3 ^ oddCount n k * m =
      2 ^ k * acceleratedOrbit k m + 3 ^ oddCount n k * n := by
  have hn := affine_exact n k
  have hm := affine_exact m k
  rw [hc.symm, hC.symm] at hm
  omega


/-! ## 4.  The partner along an excursion is the cofactor -/

private theorem two_pow_mul_sub {j v : Nat} (h : j ≤ v) :
    2 ^ j * 2 ^ (v - j) = 2 ^ v := by
  have : j + (v - j) = v := by omega
  rw [← Arith.two_pow_add, this]

/-- A prefix of a pure-halving orbit remains even. -/
theorem even_orbit_le {m r y j : Nat}
    (hm : m % 2 = 1) (hy : y = 2 ^ r * m) (hj : j ≤ r) :
    ∀ i : Nat, i < j → acceleratedOrbit i y % 2 = 0 :=
  fun i hi => even_orbit_of_val2 hm hy i (by omega)

/-- **Partner orbit.**  `T^j(n+1) = 2^{v−j} u` for every `j ≤ v`. -/
theorem partner_orbit {n v u W e j : Nat}
    (h : IsExcursion n v u W e) (hj : j ≤ v) :
    acceleratedOrbit j (n + 1) = 2 ^ (v - j) * u := by
  have hy : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  have heven := even_orbit_le h.2.1 hy hj
  have hchain := halving_chain j (n + 1) heven
  have hpow := two_pow_mul_sub hj
  have : 2 ^ j * acceleratedOrbit j (n + 1) = 2 ^ j * (2 ^ (v - j) * u) := by
    rw [hchain, hy, ← Nat.mul_assoc, hpow]
  exact Nat.eq_of_mul_eq_mul_left (two_pow_pos j) this

/-- **The cofactor is the successor orbit at time `v`.**  This is the pair
evolution of `n` against `n + 1`, not a ranking on `u`. -/
theorem partner_is_cofactor {n v u W e : Nat} (h : IsExcursion n v u W e) :
    acceleratedOrbit v (n + 1) = u := by
  have := partner_orbit h (Nat.le_refl v)
  simpa using this

/-- At the end of the odd run the pair is `(3^v u − 1, u)`. -/
theorem peak_vs_partner {n v u W e : Nat} (h : IsExcursion n v u W e) :
    acceleratedOrbit v n + 1 = 3 ^ v * acceleratedOrbit v (n + 1) := by
  have hpeak := peak_eq h
  have hu := partner_is_cofactor h
  have hu1 : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  have hge : 1 ≤ 3 ^ v * u := Nat.mul_le_mul (one_le_three_pow v) hu1
  rw [hpeak, hu]
  omega


/-! ## 5.  `expStep` keeps the shift pair; Collatz does not -/

private theorem mul_two_pow_succ (a m c : Nat) :
    a * 2 ^ (m + 1) * c = 2 * (a * 2 ^ m * c) := by
  rw [Arith.two_pow_succ]
  calc
    a * (2 * 2 ^ m) * c
        = (a * 2) * (2 ^ m * c) := by
          rw [← Nat.mul_assoc a 2, Nat.mul_assoc (a * 2)]
    _ = (2 * a) * (2 ^ m * c) := by rw [Nat.mul_comm a 2]
    _ = 2 * (a * (2 ^ m * c)) := by rw [Nat.mul_assoc]
    _ = 2 * (a * 2 ^ m * c) := by rw [Nat.mul_assoc]

/-- Pure even `expStep` orbit of a power of two. -/
theorem exp_even_pow {k u : Nat} :
    ∀ j : Nat, j ≤ k →
      expOrbit j (2 ^ k * u) = 3 ^ j * 2 ^ (k - j) * u := by
  intro j
  induction j with
  | zero =>
    intro _
    simp [expOrbit]
  | succ j ih =>
    intro hj
    have hj0 : j ≤ k := by omega
    have hsplit : k - j = (k - (j + 1)) + 1 := by omega
    have ih' := ih hj0
    rw [expOrbit_succ_step, ih']
    have hval :
        3 ^ j * 2 ^ (k - j) * u = 2 * (3 ^ j * 2 ^ (k - (j + 1)) * u) := by
      rw [hsplit, mul_two_pow_succ]
    have heven : (3 ^ j * 2 ^ (k - j) * u) % 2 = 0 := by
      rw [hval]; omega
    have hstep : expStep (3 ^ j * 2 ^ (k - j) * u) =
        3 * (3 ^ j * 2 ^ (k - j) * u) / 2 := by
      unfold expStep
      rw [if_pos heven]
    rw [hstep, hval]
    have hcancel :
        3 * (2 * (3 ^ j * 2 ^ (k - (j + 1)) * u)) / 2 =
          3 * (3 ^ j * 2 ^ (k - (j + 1)) * u) := by
      have hswap : 3 * (2 * (3 ^ j * 2 ^ (k - (j + 1)) * u)) =
          2 * (3 * (3 ^ j * 2 ^ (k - (j + 1)) * u)) := by
        rw [← Nat.mul_assoc, Nat.mul_comm 3 2, Nat.mul_assoc]
      rw [hswap, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
    rw [hcancel]
    have hpow : 3 * 3 ^ j = 3 ^ (j + 1) := by
      rw [Nat.mul_comm, Nat.pow_succ]
    rw [Nat.mul_assoc (3 ^ j), ← Nat.mul_assoc 3, hpow, ← Nat.mul_assoc]

/-- `expStep` sends the partner `n+1` to the peak-plus-one, not to the cofactor. -/
theorem exp_partner_is_peak {n v u W e : Nat} (h : IsExcursion n v u W e) :
    expOrbit v (n + 1) = 3 ^ v * u := by
  have hy : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  have := exp_even_pow (k := v) (u := u) v (Nat.le_refl v)
  simpa [hy] using this

/-- Along an odd run, `expStep` agrees with Collatz. -/
theorem expOrbit_eq_of_oddRun {x : Nat} :
    ∀ j : Nat, OddRun x j → expOrbit j x = acceleratedOrbit j x := by
  intro j
  induction j generalizing x with
  | zero =>
    intro _
    rfl
  | succ j ih =>
    intro hrun
    have hx : x % 2 = 1 := by
      have := hrun 0 (by omega)
      simpa [acceleratedOrbit] using this
    have htail : OddRun (acceleratedStep x) j := by
      intro i hi
      have := hrun (i + 1) (by omega)
      simpa [acceleratedOrbit] using this
    rw [expOrbit_succ, acceleratedOrbit_succ, expStep_odd_eq hx]
    exact ih htail

/-- **`expStep` pair identity.**  After `v` steps the successor pair remains a
shift pair: `E^v(n) + 1 = E^v(n+1)`.  Collatz has `T^v(n) + 1 = 3^v T^v(n+1)`
instead (`peak_vs_partner`). -/
theorem exp_pair_stays_shift {n v u W e : Nat} (h : IsExcursion n v u W e) :
    expOrbit v n + 1 = expOrbit v (n + 1) := by
  have hrun : OddRun n v := (oddRun_iff v n).mpr ⟨u, h.2.2.2.2.2.1⟩
  have hEq := expOrbit_eq_of_oddRun v hrun
  have hpeak := peak_eq h
  have hE := exp_partner_is_peak h
  have hu1 : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  have hge : 1 ≤ 3 ^ v * u := Nat.mul_le_mul (one_le_three_pow v) hu1
  omega


/-! ## 6.  Shift bound, used by the collision -/

/-- **Crude shift bound.**  Equality on odd runs; slack on even steps.
`2 ^ k (T^k(x) + 1) ≤ 3 ^ k (x + 1)`. -/
theorem orbit_succ_le : ∀ (k x : Nat),
    2 ^ k * (acceleratedOrbit k x + 1) ≤ 3 ^ k * (x + 1) := by
  intro k
  induction k with
  | zero =>
    intro x
    simp [acceleratedOrbit]
  | succ k ih =>
    intro x
    have hstep : acceleratedOrbit (k + 1) x =
        acceleratedStep (acceleratedOrbit k x) :=
      acceleratedOrbit_succ_step k x
    have ihx := ih x
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k x) with he | ho
    · have hval : acceleratedStep (acceleratedOrbit k x) =
          acceleratedOrbit k x / 2 := by
        rw [acceleratedStep, if_pos he]
      have hrew :
          2 ^ (k + 1) * (acceleratedOrbit k x / 2 + 1) =
            2 ^ k * (acceleratedOrbit k x + 1) + 2 ^ k := by
        rw [Arith.two_pow_succ, Nat.mul_assoc, Nat.mul_left_comm 2]
        have h2 : 2 * (acceleratedOrbit k x / 2 + 1) =
            acceleratedOrbit k x + 2 := by omega
        rw [h2]
        have : acceleratedOrbit k x + 2 = (acceleratedOrbit k x + 1) + 1 := by
          omega
        rw [this, Nat.mul_add, Nat.mul_one]
      have h2le : (2:Nat) ^ k ≤ 2 * 3 ^ k :=
        Nat.le_trans (two_pow_le_three_pow k)
          (Nat.le_mul_of_pos_left (3 ^ k) (by omega : 0 < 2))
      have hslack : 2 ^ k ≤ 2 * 3 ^ k * (x + 1) := by
        have hone : 2 * 3 ^ k * 1 = 2 * 3 ^ k := by omega
        have h2le' : 2 ^ k ≤ 2 * 3 ^ k * 1 := by rwa [hone]
        exact Nat.le_trans h2le'
          (Nat.mul_le_mul_left (2 * 3 ^ k) (by omega : 1 ≤ x + 1))
      rw [hstep, hval, hrew, Arith.three_pow_succ]
      have hadd : 2 ^ k * (acceleratedOrbit k x + 1) + 2 ^ k
          ≤ 3 ^ k * (x + 1) + 2 * 3 ^ k * (x + 1) :=
        Nat.add_le_add ihx hslack
      have hR : 3 ^ k * (x + 1) + 2 * 3 ^ k * (x + 1) = 3 * 3 ^ k * (x + 1) := by
        have h2 : 2 * 3 ^ k * (x + 1) = 2 * (3 ^ k * (x + 1)) := by
          rw [Nat.mul_assoc]
        have h3 : 3 * 3 ^ k * (x + 1) = 3 * (3 ^ k * (x + 1)) := by
          rw [Nat.mul_assoc]
        rw [h2, h3]
        omega
      rwa [← hR]
    · have hval : acceleratedStep (acceleratedOrbit k x) =
          (3 * acceleratedOrbit k x + 1) / 2 := by
        rw [acceleratedStep, if_neg (by omega)]
      have hrew :
          2 ^ (k + 1) * ((3 * acceleratedOrbit k x + 1) / 2 + 1) =
            3 * (2 ^ k * (acceleratedOrbit k x + 1)) := by
        rw [Arith.two_pow_succ, Nat.mul_assoc, Nat.mul_left_comm 2]
        have h2 : 2 * ((3 * acceleratedOrbit k x + 1) / 2 + 1) =
            3 * (acceleratedOrbit k x + 1) := by omega
        rw [h2, Nat.mul_left_comm]
      rw [hstep, hval, hrew, Arith.three_pow_succ]
      have hR : 3 * 3 ^ k * (x + 1) = 3 * (3 ^ k * (x + 1)) := by
        rw [Nat.mul_assoc]
      rw [hR]
      exact Nat.mul_le_mul_left 3 ihx


/-! ## 7.  Collision theorem -/

/-- A light total exponent forces strictly more odd steps than extra halvings. -/
theorem light_W_lt_v {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hlight : 2 ^ (v + W) ≤ 3 ^ v) : W < v := by
  rcases Nat.lt_or_ge W v with hlt | hge
  · exact hlt
  · have hv : 0 < v := h.2.2.2.1
    have h2v : v + v ≤ v + W := by omega
    have hpow : (2:Nat) ^ (v + v) ≤ 2 ^ (v + W) := two_pow_le_two_pow h2v
    have h4 : (2:Nat) ^ (v + v) = 2 ^ (2 * v) := by
      rw [Nat.two_mul]
    have hlt : (3:Nat) ^ v < 2 ^ (2 * v) := three_pow_lt_four_pow hv
    omega

/-- **Landing collision is impossible when `W < v`.**  Same-time meeting
`T^{v+W}(n) = T^{v+W}(n+1)` would mean `e = T^W(u)`, hence
`2^W T^W(u) + 1 = 3^v u`, which overruns the shift bound. -/
theorem no_landing_collision_of_v_gt_W {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hW : W < v) :
    acceleratedOrbit (v + W) n ≠ acceleratedOrbit (v + W) (n + 1) := by
  intro heq
  have hland := landing_eq h
  have hu := partner_is_cofactor h
  have hshift :
      acceleratedOrbit (v + W) (n + 1) = acceleratedOrbit W u := by
    have hcomm : v + W = W + v := Nat.add_comm _ _
    rw [hcomm, ← acceleratedOrbit_add, hu]
  have heu : e = acceleratedOrbit W u := by
    rw [← hland, heq, hshift]
  have hpeak : 2 ^ W * e + 1 = 3 ^ v * u := (h.2.2.2.2.2.2).symm
  have hbound := orbit_succ_le W u
  have hu0 : 0 < u := by
    have : u % 2 = 1 := h.2.1
    omega
  have hvW : v ≥ W + 1 := by omega
  have h3le : (3:Nat) ^ (W + 1) ≤ 3 ^ v := three_pow_le_three_pow hvW
  have h3u : 3 * (3 ^ W * u) ≤ 3 ^ v * u := by
    have : 3 * 3 ^ W = 3 ^ (W + 1) := by
      rw [Nat.mul_comm, Nat.pow_succ]
    have hmul : 3 * (3 ^ W * u) = 3 * 3 ^ W * u := by
      rw [Nat.mul_assoc]
    rw [hmul, this]
    exact Nat.mul_le_mul_right u h3le
  have hpeakT : 2 ^ W * acceleratedOrbit W u + 1 = 3 ^ v * u := by
    rw [← heu, hpeak]
  have hbound' : 2 ^ W * acceleratedOrbit W u + 2 ^ W ≤ 3 ^ W * u + 3 ^ W := by
    have hmulR : 2 ^ W * (acceleratedOrbit W u + 1) =
        2 ^ W * acceleratedOrbit W u + 2 ^ W := by
      rw [Nat.mul_add, Nat.mul_one]
    have hmulL : 3 ^ W * (u + 1) = 3 ^ W * u + 3 ^ W := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [← hmulR, ← hmulL]
    exact hbound
  have hTu : 2 * (3 ^ W * u) ≤ 2 ^ W * acceleratedOrbit W u := by
    have hA : 3 * (3 ^ W * u) ≤ 2 ^ W * acceleratedOrbit W u + 1 := by
      rw [hpeakT]
      exact h3u
    have hB : 2 * (3 ^ W * u) + 1 ≤ 3 * (3 ^ W * u) := by
      have hp : 1 ≤ 3 ^ W * u :=
        Nat.mul_le_mul (one_le_three_pow W) (Nat.succ_le_of_lt hu0)
      have hadd : 2 * (3 ^ W * u) + 1 ≤ 2 * (3 ^ W * u) + 3 ^ W * u :=
        Nat.add_le_add_left hp _
      have h3 : 2 * (3 ^ W * u) + 3 ^ W * u = 3 * (3 ^ W * u) :=
        (Nat.succ_mul 2 _).symm
      rwa [h3] at hadd
    exact Nat.le_of_add_le_add_right (Nat.le_trans hB hA)
  have hlow : 2 * (3 ^ W * u) + 2 ^ W ≤ 2 ^ W * acceleratedOrbit W u + 2 ^ W :=
    Nat.add_le_add_right hTu _
  have hchain : 2 * (3 ^ W * u) + 2 ^ W ≤ 3 ^ W * u + 3 ^ W :=
    Nat.le_trans hlow hbound'
  have hstrict : 3 ^ W * u + 3 ^ W < 2 * (3 ^ W * u) + 2 ^ W := by
    have hlt : 3 ^ W < 3 ^ W * u + 2 ^ W :=
      Nat.lt_of_le_of_lt
        (by simpa using Nat.mul_le_mul_left (3 ^ W) (Nat.succ_le_of_lt hu0))
        (Nat.lt_add_of_pos_right (two_pow_pos W))
    have hstep : 3 ^ W * u + 3 ^ W < 3 ^ W * u + (3 ^ W * u + 2 ^ W) :=
      Nat.add_lt_add_left hlt _
    have hR : 3 ^ W * u + (3 ^ W * u + 2 ^ W) = 2 * (3 ^ W * u) + 2 ^ W := by
      rw [← Nat.add_assoc, Nat.two_mul]
    rwa [hR] at hstep
  exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hchain hstrict)

/-- **Light excursions cannot collide with the successor orbit at landing.**
Never-dropping on a light first excursion is a special case: the landing stays
at or above the start (`no_drop_of_light`), so a same-time meeting with the
partner would be an impossible equality. -/
theorem no_landing_collision_of_light {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hlight : 2 ^ (v + W) ≤ 3 ^ v) :
    acceleratedOrbit (v + W) n ≠ acceleratedOrbit (v + W) (n + 1) :=
  no_landing_collision_of_v_gt_W h (light_W_lt_v h hlight)


/-! ## 8.  Worked values, not a ranking -/

/-- `7` against `8`: after `v = 3` the partner is the cofactor `1`. -/
theorem seven_partner_is_cofactor :
    IsExcursion 7 3 1 1 13 ∧ acceleratedOrbit 3 8 = 1 :=
  ⟨⟨rfl, rfl, rfl, by decide, by decide, rfl, rfl⟩, by decide⟩

/-- The landing `13` is not the partner orbit at time `v + W = 4`. -/
theorem seven_no_landing_collision :
    acceleratedOrbit 4 7 ≠ acceleratedOrbit 4 8 := by
  decide

/-- `expStep` on the same pair: `E^3(7) + 1 = E^3(8)`, the shift identity
Collatz does not keep. -/
theorem seven_exp_stays_shift :
    expOrbit 3 7 + 1 = expOrbit 3 8 :=
  exp_pair_stays_shift seven_partner_is_cofactor.1

end DeviceCollision
end Collatz

section AxiomAudit
open Collatz.DeviceCollision
#print axioms odd_succ_step
#print axioms expStep_succ_of_odd
#print axioms expStep_ne_odd_succ_step
#print axioms two_step_one_mod_four
#print axioms two_step_three_mod_four
#print axioms affine_pair
#print axioms partner_is_cofactor
#print axioms peak_vs_partner
#print axioms exp_pair_stays_shift
#print axioms no_landing_collision_of_light
end AxiomAudit
