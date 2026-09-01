import Collatz.Strategy.ExcursionCofactor

/-!
# Telescoping drop criteria for a chain of two or three excursions

`drop_iff` is one step: `e < n` iff `3^v u + 2^W ≤ 2^{v+W} u`.  The
cofactor identity `3^v u + 2^W − 1 = 2^{W+v'} u'` pushes the next odd
state into `(v, W, u)` of the start.  Composing once or twice gives
exact `Nat` landing formulae, and the comparison with the *original*
`n` (not merely with the previous landing) as an inequality in the
letters of the chain.

This is not Collatz.  A light word can grow at every finite length
(`71 → 121 → 91 → 103`); the criterion says when a mixed word does
not.

Specialisations:

* `(3, 1)` then `(1, W' ≥ 2)` recovers LandOne heavy;
* `(2, 1)` then `(4, W' ≥ 3)` recovers RemTwo;
* `(3, 1)` then `(1, 1)` always grows (two-step negative law);
* `(3, 1)` then `(1, 1)` then `v'' = 1` drops (three-step, any `W''`);
* `(2, 1)` then leftover `v' = 6`, `W' ≥ 4` is a drop RemTwo missed;
* `(4, 1)` then `(1, 1)` always grows; `(4, 1)` then `(1, W' ≥ 2)` drops.
-/

namespace Collatz
namespace ExcursionTelescope

open Collatz.Arith Collatz.ExcursionMap Collatz.ExcursionCofactor


/-! ## 1.  Two-step landing, and `drop_iff_two` -/

/-- **Exact two-step landing.**  After excursions `(v, W)` and
`(v', W')`,

  `3^{v'} (3^v u + 2^W − 1) = 2^{W+v'+W'} e' + 2^{W+v'}`. -/
theorem two_step_landing {n v u W e v' u' W' e' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e') :
    3 ^ v' * (3 ^ v * u + 2 ^ W - 1) =
      2 ^ (W + v' + W') * e' + 2 ^ (W + v') := by
  have hid := next_cofactor_of_excursions h h'
  have hpeak : 3 ^ v' * u' = 2 ^ W' * e' + 1 := h'.2.2.2.2.2.2
  have hcomm : 3 ^ v' * (2 ^ (W + v') * u') =
      2 ^ (W + v') * (3 ^ v' * u') := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hid, hcomm, hpeak, Nat.mul_add, Nat.mul_one]
  have hL : 2 ^ (W + v') * (2 ^ W' * e') = 2 ^ (W + v' + W') * e' := by
    rw [← Nat.mul_assoc, ← Nat.pow_add]
  rw [hL]

/-- **Two-step drop against the original start**, in the next cofactor.

  `e' < n` iff `3^{v'} u' + 2^{W'} ≤ 2^{v+W'} u`. -/
theorem drop_iff_two {n v u W e v' u' W' e' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e') :
    e' < n ↔ 3 ^ v' * u' + 2 ^ W' ≤ 2 ^ (v + W') * u := by
  have hWpos : 0 < 2 ^ W' := two_pow_pos W'
  have hn' : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  have hpeak : 2 ^ W' * e' + 1 = 3 ^ v' * u' := h'.2.2.2.2.2.2.symm
  have hpow : (2 : Nat) ^ (v + W') * u = 2 ^ W' * (n + 1) := by
    rw [Nat.pow_add, hn']
    simp [Nat.mul_assoc, Nat.mul_comm]
  constructor
  · intro hlt
    have hmul : 2 ^ W' * e' < 2 ^ W' * n := Nat.mul_lt_mul_of_pos_left hlt hWpos
    have h1 : 2 ^ W' * e' + 1 ≤ 2 ^ W' * n := Nat.succ_le_of_lt hmul
    have h2 : 3 ^ v' * u' ≤ 2 ^ W' * n := by rw [← hpeak]; exact h1
    have h3 : 3 ^ v' * u' + 2 ^ W' ≤ 2 ^ W' * n + 2 ^ W' :=
      Nat.add_le_add_right h2 _
    have h4 : 2 ^ W' * n + 2 ^ W' = 2 ^ W' * (n + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [h4, ← hpow] at h3
    exact h3
  · intro hle
    have h3 : 3 ^ v' * u' + 2 ^ W' ≤ 2 ^ W' * (n + 1) := by
      rw [← hpow]; exact hle
    have h4 : 2 ^ W' * (n + 1) = 2 ^ W' * n + 2 ^ W' := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [h4] at h3
    have h2 : 3 ^ v' * u' ≤ 2 ^ W' * n := Nat.le_of_add_le_add_right h3
    have h1 : 2 ^ W' * e' + 1 ≤ 2 ^ W' * n := by rw [hpeak]; exact h2
    have hmul : 2 ^ W' * e' < 2 ^ W' * n := Nat.lt_of_succ_le h1
    exact Nat.lt_of_mul_lt_mul_left hmul

/-- Scaling an inequality by a positive factor is an iff. -/
private theorem mul_le_iff {a b c : Nat} (ha : 0 < a) : b ≤ c ↔ a * b ≤ a * c :=
  ⟨fun h => Nat.mul_le_mul_left a h, fun h => Nat.le_of_mul_le_mul_left h ha⟩

/-- Left-hand side of the expanded two-step criterion. -/
private theorem two_scale_left {W v' u' W' : Nat} :
    2 ^ (W + v') * (3 ^ v' * u' + 2 ^ W') =
      3 ^ v' * (2 ^ (W + v') * u') + 2 ^ (W + v' + W') := by
  rw [Nat.mul_add]
  have h1 : 2 ^ (W + v') * (3 ^ v' * u') = 3 ^ v' * (2 ^ (W + v') * u') := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h2 : 2 ^ (W + v') * 2 ^ W' = 2 ^ (W + v' + W') := by
    rw [← Nat.pow_add]
  rw [h1, h2]

/-- Right-hand side of the expanded two-step criterion. -/
private theorem two_scale_right (v u W v' W' : Nat) :
    2 ^ (W + v') * (2 ^ (v + W') * u) = 2 ^ (v + W + v' + W') * u := by
  have hexp : W + v' + (v + W') = v + W + v' + W' := by omega
  rw [← Nat.mul_assoc, ← Nat.pow_add, hexp]

/-- **Two-step drop**, expanded in `(v, W, u)` of each step.

  `e' < n` iff
  `3^{v'} (3^v u + 2^W − 1) + 2^{W+v'+W'} ≤ 2^{v+W+v'+W'} u`. -/
theorem drop_iff_two_expanded {n v u W e v' u' W' e' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e') :
    e' < n ↔
      3 ^ v' * (3 ^ v * u + 2 ^ W - 1) + 2 ^ (W + v' + W') ≤
        2 ^ (v + W + v' + W') * u := by
  have hid := next_cofactor_of_excursions h h'
  rw [drop_iff_two h h', mul_le_iff (two_pow_pos (W + v')),
      two_scale_left, two_scale_right, ← hid]


/-! ## 2.  Three-step landing, and `drop_iff_three` -/

/-- Rewrite `x + 2^k − 1` as `x + (2^k − 1)`. -/
private theorem add_two_pow_pred (x k : Nat) :
    x + 2 ^ k - 1 = x + (2 ^ k - 1) :=
  Nat.add_sub_assoc (one_le_two_pow k) x

/-- **Exact three-step landing.**  After `(v, W)`, `(v', W')`, `(v'', W'')`,

  `3^{v''} ( 3^{v'} (3^v u + 2^W − 1) + (2^{W'} − 1) 2^{W+v'} )`

  `= 2^{W+v'+W'+v''+W''} e'' + 2^{W+v'+W'+v''}`. -/
theorem three_step_landing {n v u W e v' u' W' e' v'' u'' W'' e'' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e')
    (h'' : IsExcursion e' v'' u'' W'' e'') :
    3 ^ v'' *
        (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
          (2 ^ W' - 1) * 2 ^ (W + v')) =
      2 ^ (W + v' + W' + v'' + W'') * e'' +
        2 ^ (W + v' + W' + v'') := by
  have hid1 := next_cofactor_of_excursions h h'
  have hid2 := next_cofactor_of_excursions h' h''
  have hpeak : 3 ^ v'' * u'' = 2 ^ W'' * e'' + 1 := h''.2.2.2.2.2.2
  have hmid :
      3 ^ v' * (3 ^ v * u + 2 ^ W - 1) + (2 ^ W' - 1) * 2 ^ (W + v') =
        2 ^ (W + v') * (3 ^ v' * u' + 2 ^ W' - 1) := by
    rw [hid1]
    have hdist :
        3 ^ v' * (2 ^ (W + v') * u') + (2 ^ W' - 1) * 2 ^ (W + v') =
          2 ^ (W + v') * (3 ^ v' * u' + (2 ^ W' - 1)) := by
      simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have hrew := add_two_pow_pred (3 ^ v' * u') W'
    rw [hdist, hrew]
  rw [hmid]
  have hcomm : 3 ^ v'' * (2 ^ (W + v') * (3 ^ v' * u' + 2 ^ W' - 1)) =
      2 ^ (W + v') * (3 ^ v'' * (3 ^ v' * u' + 2 ^ W' - 1)) := by
    simp [Nat.mul_comm, Nat.mul_left_comm]
  rw [hcomm, hid2]
  have hcomm2 : 3 ^ v'' * (2 ^ (W' + v'') * u'') =
      2 ^ (W' + v'') * (3 ^ v'' * u'') := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hcomm2, hpeak]
  have hinner : 2 ^ (W' + v'') * (2 ^ W'' * e'' + 1) =
      2 ^ (W' + v'' + W'') * e'' + 2 ^ (W' + v'') := by
    rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, ← Nat.pow_add]
  rw [hinner, Nat.mul_add]
  have hL : 2 ^ (W + v') * (2 ^ (W' + v'' + W'') * e'') =
      2 ^ (W + v' + W' + v'' + W'') * e'' := by
    have hexp : W + v' + (W' + v'' + W'') = W + v' + W' + v'' + W'' := by omega
    rw [← Nat.mul_assoc, ← Nat.pow_add, hexp]
  have hR : 2 ^ (W + v') * 2 ^ (W' + v'') = 2 ^ (W + v' + W' + v'') := by
    have hexp : W + v' + (W' + v'') = W + v' + W' + v'' := by omega
    rw [← Nat.pow_add, hexp]
  rw [hL, hR]

/-- **Three-step drop against the original start**, in the last cofactor.

  `e'' < n` iff `3^{v''} u'' + 2^{W''} ≤ 2^{v+W''} u`. -/
theorem drop_iff_three {n v u W e v' u' W' e' v'' u'' W'' e'' : Nat}
    (h : IsExcursion n v u W e) (_h' : IsExcursion e v' u' W' e')
    (h'' : IsExcursion e' v'' u'' W'' e'') :
    e'' < n ↔ 3 ^ v'' * u'' + 2 ^ W'' ≤ 2 ^ (v + W'') * u := by
  have hWpos : 0 < 2 ^ W'' := two_pow_pos W''
  have hn' : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  have hpeak : 2 ^ W'' * e'' + 1 = 3 ^ v'' * u'' := h''.2.2.2.2.2.2.symm
  have hpow : (2 : Nat) ^ (v + W'') * u = 2 ^ W'' * (n + 1) := by
    rw [Nat.pow_add, hn']
    simp [Nat.mul_assoc, Nat.mul_comm]
  constructor
  · intro hlt
    have hmul : 2 ^ W'' * e'' < 2 ^ W'' * n :=
      Nat.mul_lt_mul_of_pos_left hlt hWpos
    have h1 : 2 ^ W'' * e'' + 1 ≤ 2 ^ W'' * n := Nat.succ_le_of_lt hmul
    have h2 : 3 ^ v'' * u'' ≤ 2 ^ W'' * n := by rw [← hpeak]; exact h1
    have h3 : 3 ^ v'' * u'' + 2 ^ W'' ≤ 2 ^ W'' * n + 2 ^ W'' :=
      Nat.add_le_add_right h2 _
    have h4 : 2 ^ W'' * n + 2 ^ W'' = 2 ^ W'' * (n + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [h4, ← hpow] at h3
    exact h3
  · intro hle
    have h3 : 3 ^ v'' * u'' + 2 ^ W'' ≤ 2 ^ W'' * (n + 1) := by
      rw [← hpow]; exact hle
    have h4 : 2 ^ W'' * (n + 1) = 2 ^ W'' * n + 2 ^ W'' := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [h4] at h3
    have h2 : 3 ^ v'' * u'' ≤ 2 ^ W'' * n := Nat.le_of_add_le_add_right h3
    have h1 : 2 ^ W'' * e'' + 1 ≤ 2 ^ W'' * n := by rw [hpeak]; exact h2
    have hmul : 2 ^ W'' * e'' < 2 ^ W'' * n := Nat.lt_of_succ_le h1
    exact Nat.lt_of_mul_lt_mul_left hmul

/-- Left-hand side of the expanded three-step criterion, after one
cofactor substitution. -/
private theorem three_scale_left {W' v'' u'' W'' : Nat} :
    2 ^ (W' + v'') * (3 ^ v'' * u'' + 2 ^ W'') =
      3 ^ v'' * (2 ^ (W' + v'') * u'') + 2 ^ (W' + v'' + W'') := by
  rw [Nat.mul_add]
  have h1 : 2 ^ (W' + v'') * (3 ^ v'' * u'') =
      3 ^ v'' * (2 ^ (W' + v'') * u'') := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h2 : 2 ^ (W' + v'') * 2 ^ W'' = 2 ^ (W' + v'' + W'') := by
    rw [← Nat.pow_add]
  rw [h1, h2]

private theorem three_scale_mid {W v' u' W' v'' W'' : Nat} :
    2 ^ (W + v') *
        (3 ^ v'' * (3 ^ v' * u' + (2 ^ W' - 1)) + 2 ^ (W' + v'' + W'')) =
      3 ^ v'' * (3 ^ v' * (2 ^ (W + v') * u') +
          (2 ^ W' - 1) * 2 ^ (W + v')) +
        2 ^ (W + v' + W' + v'' + W'') := by
  rw [Nat.mul_add]
  have hc1 : 2 ^ (W + v') * (3 ^ v'' * (3 ^ v' * u' + (2 ^ W' - 1))) =
      3 ^ v'' * (2 ^ (W + v') * (3 ^ v' * u' + (2 ^ W' - 1))) := by
    simp [Nat.mul_assoc, Nat.mul_comm]
  have hd : 2 ^ (W + v') * (3 ^ v' * u' + (2 ^ W' - 1)) =
      3 ^ v' * (2 ^ (W + v') * u') + (2 ^ W' - 1) * 2 ^ (W + v') := by
    simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hc2 : 2 ^ (W + v') * 2 ^ (W' + v'' + W'') =
      2 ^ (W + v' + W' + v'' + W'') := by
    have hexp : W + v' + (W' + v'' + W'') = W + v' + W' + v'' + W'' := by omega
    rw [← Nat.pow_add, hexp]
  rw [hc1, hd, hc2]

/-- **Three-step drop**, expanded in `(v, W, u)` of each step. -/
theorem drop_iff_three_expanded {n v u W e v' u' W' e' v'' u'' W'' e'' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e')
    (h'' : IsExcursion e' v'' u'' W'' e'') :
    e'' < n ↔
      3 ^ v'' *
          (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
            (2 ^ W' - 1) * 2 ^ (W + v')) +
        2 ^ (W + v' + W' + v'' + W'') ≤
        2 ^ (v + W + v' + W' + v'' + W'') * u := by
  have hid1 := next_cofactor_of_excursions h h'
  have hid2 := next_cofactor_of_excursions h' h''
  have hR1 : 2 ^ (W' + v'') * (2 ^ (v + W'') * u) =
      2 ^ (v + W' + v'' + W'') * u := by
    have hexp : W' + v'' + (v + W'') = v + W' + v'' + W'' := by omega
    rw [← Nat.mul_assoc, ← Nat.pow_add, hexp]
  have hR0 : 2 ^ (W + v') * (2 ^ (v + W' + v'' + W'') * u) =
      2 ^ (v + W + v' + W' + v'' + W'') * u := by
    have hexp : W + v' + (v + W' + v'' + W'') =
        v + W + v' + W' + v'' + W'' := by omega
    rw [← Nat.mul_assoc, ← Nat.pow_add, hexp]
  rw [drop_iff_three h h' h'', mul_le_iff (two_pow_pos (W' + v'')),
      three_scale_left, hR1, ← hid2, add_two_pow_pred (3 ^ v' * u') W',
      mul_le_iff (two_pow_pos (W + v')), three_scale_mid, hR0, ← hid1]


/-! ## 3.  The two-step criterion as a peak comparison -/

/-- `a * (b * u) = b * (a * u)`. -/
private theorem mul_swap (a b u : Nat) : a * (b * u) = b * (a * u) := by
  rw [← Nat.mul_assoc, Nat.mul_comm a b, Nat.mul_assoc]

/-- `a + 2^W ≤ 2^{v+W} u` iff `a ≤ 2^W (2^v u − 1)`. -/
private theorem add_pow_le_iff {a v u W : Nat} (hu : 1 ≤ u) :
    a + 2 ^ W ≤ 2 ^ (v + W) * u ↔ a ≤ 2 ^ W * (2 ^ v * u - 1) := by
  have hpow : (2 : Nat) ^ (v + W) * u = 2 ^ W * (2 ^ v * u) := by
    rw [Nat.pow_add, Nat.mul_comm (2 ^ v), Nat.mul_assoc]
  have hpos : 1 ≤ 2 ^ v * u :=
    Nat.le_trans hu (Nat.le_mul_of_pos_left u (two_pow_pos v))
  have hsplit : 2 ^ W * (2 ^ v * u - 1) + 2 ^ W = 2 ^ W * (2 ^ v * u) := by
    have h : 2 ^ W * (2 ^ v * u - 1) + 2 ^ W * 1 =
        2 ^ W * (2 ^ v * u - 1 + 1) := by rw [← Nat.mul_add]
    rw [Nat.mul_one] at h
    rw [h, Nat.sub_add_cancel hpos]
  rw [hpow, ← hsplit]
  constructor
  · exact Nat.le_of_add_le_add_right
  · intro h; exact Nat.add_le_add_right h _

/-- If the comparison holds at the minimum extra-halving count `K`, it
holds for every larger power of two. -/
private theorem le_of_min_pow {a K b W : Nat}
    (hcore : a ≤ K * b) (hk : K ≤ 2 ^ W) : a ≤ 2 ^ W * b :=
  Nat.le_trans hcore (Nat.mul_le_mul_right b hk)

private theorem four_le_two_pow {W : Nat} (h : 2 ≤ W) : 4 ≤ 2 ^ W := by
  have : (2 : Nat) ^ 2 ≤ 2 ^ W := two_pow_le_two_pow h
  simpa using this

private theorem eight_le_two_pow {W : Nat} (h : 3 ≤ W) : 8 ≤ 2 ^ W := by
  have : (2 : Nat) ^ 3 ≤ 2 ^ W := two_pow_le_two_pow h
  simpa using this

private theorem sixteen_le_two_pow {W : Nat} (h : 4 ≤ W) : 16 ≤ 2 ^ W := by
  have : (2 : Nat) ^ 4 ≤ 2 ^ W := two_pow_le_two_pow h
  simpa using this


/-! ## 4.  Mixed light words: `(3, 1)` then `(1, ·)` -/

private theorem eqs_three_one {n u e : Nat} (h : IsExcursion n 3 u 1 e) :
    n + 1 = 8 * u ∧ 27 * u = 2 * e + 1 := by
  have hnu := h.2.2.2.2.2.1
  have hpeak := h.2.2.2.2.2.2
  rw [show (2 : Nat) ^ 3 = 8 by decide] at hnu
  rw [show (3 : Nat) ^ 3 = 27 by decide, Nat.pow_one] at hpeak
  exact ⟨hnu, hpeak⟩

private theorem one_le_u_of {n v u W e : Nat} (h : IsExcursion n v u W e) :
    1 ≤ u := by
  have : u % 2 = 1 := h.2.1
  omega

private theorem eight_e'_add {u u' e' k : Nat}
    (hrel : 4 * u' = k * u + 1) (hpeak : 2 * e' + 1 = 3 * u') :
    8 * e' + 4 = 3 * (k * u + 1) := by
  have h12u : 8 * e' + 4 = 12 * u' := by omega
  have h12 : 12 * u' = 3 * (4 * u') := by
    have : (12 : Nat) = 3 * 4 := by decide
    rw [this, Nat.mul_assoc]
  rw [h12u, h12, hrel]

private theorem eight_e'_eq {u e' k : Nat}
    (_hu : 1 ≤ u) (h : 8 * e' + 4 = 3 * (k * u + 1)) :
    8 * e' = 3 * k * u - 1 := by
  have : 3 * (k * u + 1) = 3 * k * u + 3 := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
  have h' : 8 * e' + 4 = 3 * k * u + 3 := by rwa [this] at h
  omega

private theorem four_u'_of_three_one {n u e u' W' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' W' e') :
    4 * u' = 27 * u + 1 := by
  have ⟨_, hpeak⟩ := eqs_three_one h
  have hnu' : e + 1 = 2 * u' := by
    have := h'.2.2.2.2.2.1
    rw [Nat.pow_one] at this
    exact this
  omega

/-- Core of LandOne heavy: the `W' = 2` comparison `3 u' ≤ 4 (8u − 1)`. -/
private theorem three_one_v_one_core {u u' : Nat}
    (hu : 1 ≤ u) (hrel : 4 * u' = 27 * u + 1) :
    3 * u' ≤ 4 * (8 * u - 1) := by
  have h12 : 12 * u' = 81 * u + 3 := by
    have h : 12 * u' = 3 * (4 * u') := by
      have : (12 : Nat) = 3 * 4 := by decide
      rw [this, Nat.mul_assoc]
    rw [h, hrel, Nat.mul_add, Nat.mul_one]
    have : (3 : Nat) * 27 = 81 := by decide
    rw [← Nat.mul_assoc, this]
  have hL : 4 * (3 * u') = 12 * u' := by
    have : (4 : Nat) * 3 = 12 := by decide
    rw [← Nat.mul_assoc, this]
  have hR : 4 * (4 * (8 * u - 1)) = 16 * (8 * u - 1) := by
    have : (4 : Nat) * 4 = 16 := by decide
    rw [← Nat.mul_assoc, this]
  have hR' : 16 * (8 * u - 1) = 128 * u - 16 := by
    rw [Nat.mul_sub, Nat.mul_one]
    have : (16 : Nat) * 8 = 128 := by decide
    rw [← Nat.mul_assoc, this]
  have hcmp : 81 * u + 3 ≤ 128 * u - 16 := by
    have : 19 ≤ 47 * u := by omega
    exact Nat.le_sub_of_add_le (by omega : 81 * u + 3 + 16 ≤ 128 * u)
  have : 4 * (3 * u') ≤ 4 * (4 * (8 * u - 1)) := by
    rw [hL, h12, hR, hR']
    exact hcmp
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- **Sanity: LandOne heavy.**  `(3, 1)` then `(1, W' ≥ 2)` drops below
the original start.  The two-step criterion at `W' = 2` is
`3 u' ≤ 4 (8u − 1)`, i.e. `81u + 19 ≤ 128u`. -/
theorem drop_of_three_one_then_v_one_heavy {n u e u' W' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' W' e')
    (hW : 2 ≤ W') : e' < n := by
  have hu := one_le_u_of h
  have hrel := four_u'_of_three_one h h'
  have hcore := three_one_v_one_core hu hrel
  refine (drop_iff_two h h').mpr ?_
  have h3 : (3 : Nat) ^ 1 = 3 := Nat.pow_one 3
  rw [h3, add_pow_le_iff hu]
  rw [show (2 : Nat) ^ 3 = 8 by decide]
  exact le_of_min_pow hcore (four_le_two_pow hW)

/-- **Negative law.**  `(3, 1)` then `(1, 1)` always grows:
`8 e' = 81u − 1 > 64u − 8 = 8 n`. -/
theorem grows_of_three_one_then_one_one {n u e u' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e') : n < e' := by
  have hu := one_le_u_of h
  have ⟨hnu, _⟩ := eqs_three_one h
  have hrel := four_u'_of_three_one h h'
  have hpeak : 2 * e' + 1 = 3 * u' := by
    have := h'.2.2.2.2.2.2
    rw [Nat.pow_one, Nat.pow_one] at this
    exact this.symm
  have h8e : 8 * e' = 81 * u - 1 := by
    have := eight_e'_eq hu (eight_e'_add hrel hpeak)
    have hk : (3 : Nat) * 27 = 81 := by decide
    rwa [hk] at this
  clear h h' hrel hpeak
  have hn8 : 8 * n = 64 * u - 8 := by omega
  have hcmp : 64 * u - 8 < 81 * u - 1 := by
    have : 7 < 17 * u := by omega
    omega
  have : 8 * n < 8 * e' := by
    rw [hn8, h8e]
    exact hcmp
  exact Nat.lt_of_mul_lt_mul_left this

/-- After `(3, 1)` then `(1, 1)` the cofactor satisfies `u ≥ 9`. -/
private theorem nine_le_u_of_one_one {n u e u' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e') : 9 ≤ u := by
  have hu : u % 2 = 1 := h.2.1
  have hu' : u' % 2 = 1 := h'.2.1
  have he' : e' % 2 = 1 := h'.2.2.1
  have hrel := four_u'_of_three_one h h'
  have hpeak : 3 * u' = 2 * e' + 1 := by
    have := h'.2.2.2.2.2.2
    rw [Nat.pow_one, Nat.pow_one] at this
    exact this
  omega

private theorem sixteen_u''_of_three_light {n u e u' e' u'' W'' e'' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e')
    (h'' : IsExcursion e' 1 u'' W'' e'') :
    16 * u'' = 81 * u + 7 := by
  have hrel := four_u'_of_three_one h h'
  have hpeak' : 3 * u' = 2 * e' + 1 := by
    have := h'.2.2.2.2.2.2
    rw [Nat.pow_one, Nat.pow_one] at this
    exact this
  have hnu'' : e' + 1 = 2 * u'' := by
    have := h''.2.2.2.2.2.1
    rw [Nat.pow_one] at this
    exact this
  have h4 : 4 * u'' = 3 * u' + 1 := by
    have : 2 * (e' + 1) = 3 * u' + 1 := by omega
    rw [hnu''] at this
    have : 2 * 2 * u'' = 3 * u' + 1 := by
      rwa [← Nat.mul_assoc] at this
    simpa using this
  have h16 : 16 * u'' = 4 * (4 * u'') := by
    have : (16 : Nat) = 4 * 4 := by decide
    rw [this, Nat.mul_assoc]
  rw [h16, h4]
  have : 4 * (3 * u' + 1) = 12 * u' + 4 := by omega
  rw [this]
  have h12 : 12 * u' = 3 * (4 * u') := by
    have : (12 : Nat) = 3 * 4 := by decide
    rw [this, Nat.mul_assoc]
  rw [h12, hrel]
  have : 3 * (27 * u + 1) + 4 = 81 * u + 7 := by
    have : (3 : Nat) * 27 = 81 := by decide
    rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, this]
  omega

/-- Core of the three-step drop: `3 u'' ≤ 2 (8u − 1)` once `u ≥ 9`. -/
private theorem three_one_one_one_core {u u'' : Nat}
    (hu : 9 ≤ u) (hrel : 16 * u'' = 81 * u + 7) :
    3 * u'' ≤ 2 * (8 * u - 1) := by
  have hL : 16 * (3 * u'') = 243 * u + 21 := by
    have : 16 * (3 * u'') = 3 * (16 * u'') := mul_swap 16 3 u''
    rw [this, hrel, Nat.mul_add]
    have h243 : (3 : Nat) * 81 = 243 := by decide
    have h21 : (3 : Nat) * 7 = 21 := by decide
    rw [← Nat.mul_assoc, h243, h21]
  have hR : 16 * (2 * (8 * u - 1)) = 32 * (8 * u - 1) := by
    have : (16 : Nat) * 2 = 32 := by decide
    rw [← Nat.mul_assoc, this]
  have hR' : 32 * (8 * u - 1) = 256 * u - 32 := by
    rw [Nat.mul_sub, Nat.mul_one]
    have : (32 : Nat) * 8 = 256 := by decide
    rw [← Nat.mul_assoc, this]
  have hcmp : 243 * u + 21 ≤ 256 * u - 32 := by
    have : 53 ≤ 13 * u := by omega
    exact Nat.le_sub_of_add_le (by omega : 243 * u + 21 + 32 ≤ 256 * u)
  have : 16 * (3 * u'') ≤ 16 * (2 * (8 * u - 1)) := by
    rw [hL, hR, hR']
    exact hcmp
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- **`(3, 1)` then `(1, 1)` then `v'' = 1`.**  The third excursion
drops below the original start for every `W'' ≥ 1`.  The criterion at
`W'' = 1` is `3 u'' ≤ 2 (8u − 1)`, and the two-light family has `u ≥ 9`. -/
theorem drop_of_three_one_one_one_then_v_one {n u e u' e' u'' W'' e'' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e')
    (h'' : IsExcursion e' 1 u'' W'' e'') : e'' < n := by
  have hu := nine_le_u_of_one_one h h'
  have hrel := sixteen_u''_of_three_light h h' h''
  have hcore := three_one_one_one_core hu hrel
  refine (drop_iff_three h h' h'').mpr ?_
  have h3 : (3 : Nat) ^ 1 = 3 := Nat.pow_one 3
  have hu1 : 1 ≤ u := Nat.le_trans (by omega : (1 : Nat) ≤ 9) hu
  rw [h3, add_pow_le_iff hu1]
  rw [show (2 : Nat) ^ 3 = 8 by decide]
  exact le_of_min_pow hcore (two_le_two_pow (IsExcursion.one_le_W h''))


/-! ## 5.  Mixed light words: `(2, 1)` then leftover `v' ≥ 3` -/

private theorem eqs_two_one {n u e : Nat} (h : IsExcursion n 2 u 1 e) :
    n + 1 = 4 * u ∧ 9 * u = 2 * e + 1 := by
  have hnu := h.2.2.2.2.2.1
  have hpeak := h.2.2.2.2.2.2
  rw [show (2 : Nat) ^ 2 = 4 by decide] at hnu
  rw [show (3 : Nat) ^ 2 = 9 by decide, Nat.pow_one] at hpeak
  exact ⟨hnu, hpeak⟩

/-- A genuine `(2, 1)` start has `u ≥ 3` (`u = 1` forces an even landing). -/
private theorem three_le_u_of_two_one {n u e : Nat}
    (h : IsExcursion n 2 u 1 e) : 3 ≤ u := by
  have hu : u % 2 = 1 := h.2.1
  have he : e % 2 = 1 := h.2.2.1
  have ⟨_, hpeak⟩ := eqs_two_one h
  omega

/-- Specialised two-step criterion after a `(2, 1)` step:

  `e' < n` iff `3^{v'} (9u + 1) + 2^{v'+W'+1} ≤ 2^{v'+W'+3} u`. -/
theorem drop_iff_two_one {n u e v' u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (h' : IsExcursion e v' u' W' e') :
    e' < n ↔
      3 ^ v' * (9 * u + 1) + 2 ^ (v' + W' + 1) ≤ 2 ^ (v' + W' + 3) * u := by
  have h9 : (3 : Nat) ^ 2 = 9 := by decide
  have h2 : (2 : Nat) ^ 1 = 2 := Nat.pow_one 2
  have hpeak_plus : 9 * u + 2 - 1 = 9 * u + 1 := by omega
  have hexL : 1 + v' + W' = v' + W' + 1 := by omega
  have hexR : 2 + 1 + v' + W' = v' + W' + 3 := by omega
  rw [drop_iff_two_expanded h h', h9, h2, hpeak_plus, hexL, hexR]

/-- Core of RemTwo: `81 u' ≤ 8 (4u − 1)` once `u ≥ 3`. -/
private theorem remtwo_core {u u' : Nat}
    (hu : 3 ≤ u) (hrel : 32 * u' = 9 * u + 1) :
    81 * u' ≤ 8 * (4 * u - 1) := by
  have hL : 32 * (81 * u') = 729 * u + 81 := by
    have : 32 * (81 * u') = 81 * (32 * u') := mul_swap 32 81 u'
    rw [this, hrel, Nat.mul_add, Nat.mul_one]
    have : (81 : Nat) * 9 = 729 := by decide
    rw [← Nat.mul_assoc, this]
  have hR : 32 * (8 * (4 * u - 1)) = 256 * (4 * u - 1) := by
    have : (32 : Nat) * 8 = 256 := by decide
    rw [← Nat.mul_assoc, this]
  have hR' : 256 * (4 * u - 1) = 1024 * u - 256 := by
    rw [Nat.mul_sub, Nat.mul_one]
    have : (256 : Nat) * 4 = 1024 := by decide
    rw [← Nat.mul_assoc, this]
  have hcmp : 729 * u + 81 ≤ 1024 * u - 256 := by
    have : 337 ≤ 295 * u := by
      have hmin : 295 * 3 ≤ 295 * u := Nat.mul_le_mul_left 295 hu
      have : (337 : Nat) ≤ 295 * 3 := by decide
      omega
    exact Nat.le_sub_of_add_le (by omega : 729 * u + 81 + 256 ≤ 1024 * u)
  have : 32 * (81 * u') ≤ 32 * (8 * (4 * u - 1)) := by
    rw [hL, hR, hR']
    exact hcmp
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- **Sanity: RemTwo.**  `(2, 1)` then `(4, W' ≥ 3)` drops below the
original start.  The criterion at `W' = 3` is `81 u' ≤ 8 (4u − 1)`,
i.e. `295u ≥ 337`. -/
theorem drop_of_two_one_then_v_four {n u e u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (h' : IsExcursion e 4 u' W' e')
    (hW : 3 ≤ W') : e' < n := by
  have hu := three_le_u_of_two_one h
  have hnu' : e + 1 = 16 * u' := by
    have := h'.2.2.2.2.2.1
    rw [show (2 : Nat) ^ 4 = 16 by decide] at this
    exact this
  have ⟨_, hpeak⟩ := eqs_two_one h
  have hrel : 32 * u' = 9 * u + 1 := by omega
  have hcore := remtwo_core hu hrel
  refine (drop_iff_two h h').mpr ?_
  have hu1 : 1 ≤ u := Nat.le_trans (by omega : (1 : Nat) ≤ 3) hu
  rw [show (3 : Nat) ^ 4 = 81 by decide, add_pow_le_iff hu1]
  rw [show (2 : Nat) ^ 2 = 4 by decide]
  exact le_of_min_pow hcore (eight_le_two_pow hW)

/-- Core of the new `v' = 6` drop: `729 u' ≤ 16 (4u − 1)` once `u ≥ 3`. -/
private theorem v_six_core {u u' : Nat}
    (hu : 3 ≤ u) (hrel : 128 * u' = 9 * u + 1) :
    729 * u' ≤ 16 * (4 * u - 1) := by
  have hL : 128 * (729 * u') = 6561 * u + 729 := by
    have : 128 * (729 * u') = 729 * (128 * u') := mul_swap 128 729 u'
    rw [this, hrel, Nat.mul_add, Nat.mul_one]
    have : (729 : Nat) * 9 = 6561 := by decide
    rw [← Nat.mul_assoc, this]
  have hR : 128 * (16 * (4 * u - 1)) = 2048 * (4 * u - 1) := by
    have : (128 : Nat) * 16 = 2048 := by decide
    rw [← Nat.mul_assoc, this]
  have hR' : 2048 * (4 * u - 1) = 8192 * u - 2048 := by
    rw [Nat.mul_sub, Nat.mul_one]
    have : (2048 : Nat) * 4 = 8192 := by decide
    rw [← Nat.mul_assoc, this]
  have hcmp : 6561 * u + 729 ≤ 8192 * u - 2048 := by
    have : 2777 ≤ 1631 * u := by
      have hmin : 1631 * 3 ≤ 1631 * u := Nat.mul_le_mul_left 1631 hu
      have : (2777 : Nat) ≤ 1631 * 3 := by decide
      omega
    exact Nat.le_sub_of_add_le
      (by omega : 6561 * u + 729 + 2048 ≤ 8192 * u)
  have : 128 * (729 * u') ≤ 128 * (16 * (4 * u - 1)) := by
    rw [hL, hR, hR']
    exact hcmp
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- **New drop.**  `(2, 1)` then leftover `(6, W' ≥ 4)` lands below the
original start.  RemTwo closed `v' = 4`; RemTwoLeft closed `v' = 3, 5`.
The criterion at `W' = 4` is `729 u' ≤ 16 (4u − 1)`, i.e. `1631u ≥ 2777`. -/
theorem lemmaX_of_two_one_then_v_six {n u e u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (h' : IsExcursion e 6 u' W' e')
    (hW : 4 ≤ W') : e' < n := by
  have hu := three_le_u_of_two_one h
  have hnu' : e + 1 = 64 * u' := by
    have := h'.2.2.2.2.2.1
    rw [show (2 : Nat) ^ 6 = 64 by decide] at this
    exact this
  have ⟨_, hpeak⟩ := eqs_two_one h
  have hrel : 128 * u' = 9 * u + 1 := by omega
  have hcore := v_six_core hu hrel
  refine (drop_iff_two h h').mpr ?_
  have hu1 : 1 ≤ u := Nat.le_trans (by omega : (1 : Nat) ≤ 3) hu
  rw [show (3 : Nat) ^ 6 = 729 by decide, add_pow_le_iff hu1]
  rw [show (2 : Nat) ^ 2 = 4 by decide]
  exact le_of_min_pow hcore (sixteen_le_two_pow hW)

/-- Packaged Lemma X witness. -/
theorem lemmaX_chain_of_two_one_then_v_six {n u e u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (h' : IsExcursion e 6 u' W' e')
    (hW : 4 ≤ W') : ExChain n e' ∧ e' < n :=
  ⟨ExChain.cons ⟨2, u, 1, h⟩ (ExChain.one ⟨6, u', W', h'⟩),
    lemmaX_of_two_one_then_v_six h h' hW⟩


/-! ## 6.  Mixed light words: `(4, 1)` then `(1, ·)` -/

private theorem eqs_four_one {n u e : Nat} (h : IsExcursion n 4 u 1 e) :
    n + 1 = 16 * u ∧ 81 * u = 2 * e + 1 := by
  have hnu := h.2.2.2.2.2.1
  have hpeak := h.2.2.2.2.2.2
  rw [show (2 : Nat) ^ 4 = 16 by decide] at hnu
  rw [show (3 : Nat) ^ 4 = 81 by decide, Nat.pow_one] at hpeak
  exact ⟨hnu, hpeak⟩

/-- A genuine `(4, 1)` start has `u ≥ 3`. -/
private theorem three_le_u_of_four_one {n u e : Nat}
    (h : IsExcursion n 4 u 1 e) : 3 ≤ u := by
  have hu : u % 2 = 1 := h.2.1
  have he : e % 2 = 1 := h.2.2.1
  have ⟨_, hpeak⟩ := eqs_four_one h
  omega

private theorem four_u'_of_four_one {n u e u' W' e' : Nat}
    (h : IsExcursion n 4 u 1 e) (h' : IsExcursion e 1 u' W' e') :
    4 * u' = 81 * u + 1 := by
  have ⟨_, hpeak⟩ := eqs_four_one h
  have hnu' : e + 1 = 2 * u' := by
    have := h'.2.2.2.2.2.1
    rw [Nat.pow_one] at this
    exact this
  omega

/-- Core: `3 u' ≤ 4 (16u − 1)` once `u ≥ 3`. -/
private theorem four_one_v_one_core {u u' : Nat}
    (hu : 3 ≤ u) (hrel : 4 * u' = 81 * u + 1) :
    3 * u' ≤ 4 * (16 * u - 1) := by
  have hL : 4 * (3 * u') = 243 * u + 3 := by
    have : 4 * (3 * u') = 3 * (4 * u') := mul_swap 4 3 u'
    rw [this, hrel, Nat.mul_add, Nat.mul_one]
    have : (3 : Nat) * 81 = 243 := by decide
    rw [← Nat.mul_assoc, this]
  have hR : 4 * (4 * (16 * u - 1)) = 16 * (16 * u - 1) := by
    have : (4 : Nat) * 4 = 16 := by decide
    rw [← Nat.mul_assoc, this]
  have hR' : 16 * (16 * u - 1) = 256 * u - 16 := by
    rw [Nat.mul_sub, Nat.mul_one]
    have : (16 : Nat) * 16 = 256 := by decide
    rw [← Nat.mul_assoc, this]
  have hcmp : 243 * u + 3 ≤ 256 * u - 16 := by
    have : 19 ≤ 13 * u := by
      have hmin : 13 * 3 ≤ 13 * u := Nat.mul_le_mul_left 13 hu
      have : (19 : Nat) ≤ 13 * 3 := by decide
      omega
    exact Nat.le_sub_of_add_le (by omega : 243 * u + 3 + 16 ≤ 256 * u)
  have : 4 * (3 * u') ≤ 4 * (4 * (16 * u - 1)) := by
    rw [hL, hR, hR']
    exact hcmp
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- **`(4, 1)` then `(1, W' ≥ 2)` drops** below the original start.  The
criterion at `W' = 2` is `3 u' ≤ 4 (16u − 1)`, i.e. `13u ≥ 19`. -/
theorem drop_of_four_one_then_v_one_heavy {n u e u' W' e' : Nat}
    (h : IsExcursion n 4 u 1 e) (h' : IsExcursion e 1 u' W' e')
    (hW : 2 ≤ W') : e' < n := by
  have hu := three_le_u_of_four_one h
  have hrel := four_u'_of_four_one h h'
  have hcore := four_one_v_one_core hu hrel
  refine (drop_iff_two h h').mpr ?_
  have hu1 : 1 ≤ u := Nat.le_trans (by omega : (1 : Nat) ≤ 3) hu
  have h3 : (3 : Nat) ^ 1 = 3 := Nat.pow_one 3
  rw [h3, add_pow_le_iff hu1]
  rw [show (2 : Nat) ^ 4 = 16 by decide]
  exact le_of_min_pow hcore (four_le_two_pow hW)

/-- **Negative law.**  `(4, 1)` then `(1, 1)` always grows:
`8 e' = 243u − 1 > 128u − 8 = 8 n`. -/
theorem grows_of_four_one_then_one_one {n u e u' e' : Nat}
    (h : IsExcursion n 4 u 1 e) (h' : IsExcursion e 1 u' 1 e') : n < e' := by
  have hu := three_le_u_of_four_one h
  have ⟨hnu, _⟩ := eqs_four_one h
  have hrel := four_u'_of_four_one h h'
  have hpeak : 2 * e' + 1 = 3 * u' := by
    have := h'.2.2.2.2.2.2
    rw [Nat.pow_one, Nat.pow_one] at this
    exact this.symm
  have hu1 : 1 ≤ u := Nat.le_trans (by omega : (1 : Nat) ≤ 3) hu
  have h8e : 8 * e' = 243 * u - 1 := by
    have := eight_e'_eq hu1 (eight_e'_add hrel hpeak)
    have hk : (3 : Nat) * 81 = 243 := by decide
    rwa [hk] at this
  clear h h' hrel hpeak
  have hn8 : 8 * n = 128 * u - 8 := by omega
  have hcmp : 128 * u - 8 < 243 * u - 1 := by
    have : 7 < 115 * u := by omega
    omega
  have : 8 * n < 8 * e' := by
    rw [hn8, h8e]
    exact hcmp
  exact Nat.lt_of_mul_lt_mul_left this

/-! ## 7.  Witnesses -/

/-- LandOne heavy, recovered: `7 → 13 → 5`. -/
theorem seven_two_step_drops :
    IsExcursion 7 3 1 1 13 ∧ IsExcursion 13 1 7 2 5 ∧ 5 < 7 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- RemTwo, recovered: `1947 → 2191 → 1387`. -/
theorem nineteen_forty_seven_two_step_drops :
    IsExcursion 1947 2 487 1 2191 ∧
    IsExcursion 2191 4 137 3 1387 ∧ 1387 < 1947 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- Two-step `(3, 1)` then `(1, 1)` grows: `71 → 121 → 91`. -/
theorem seventy_one_two_step_grows :
    IsExcursion 71 3 9 1 121 ∧ IsExcursion 121 1 61 1 91 ∧ 71 < 91 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- Three-step `(3, 1)` then `(1, 1)` then `v'' = 1` drops:
`455 → 769 → 577 → 433`. -/
theorem four_fifty_five_three_step_drops :
    IsExcursion 455 3 57 1 769 ∧
    IsExcursion 769 1 385 1 577 ∧
    IsExcursion 577 1 289 1 433 ∧ 433 < 455 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- **New witness.**  The `W' = 4` bound after leftover `v' = 6` is
attained and still drops: `10523 → 11839 → 8429`. -/
theorem ten_five_twenty_three_v_six :
    IsExcursion 10523 2 2631 1 11839 ∧
    IsExcursion 11839 6 185 4 8429 ∧ 8429 < 10523 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- `(4, 1)` then `(1, W' ≥ 2)` drops: `175 → 445 → 167`. -/
theorem one_seventy_five_two_step_drops :
    IsExcursion 175 4 11 1 445 ∧
    IsExcursion 445 1 223 2 167 ∧ 167 < 175 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- `(4, 1)` then `(1, 1)` grows: `47 → 121 → 91`. -/
theorem forty_seven_two_step_grows :
    IsExcursion 47 4 3 1 121 ∧ IsExcursion 121 1 61 1 91 ∧ 47 < 91 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

end ExcursionTelescope
end Collatz

section AxiomAudit
open Collatz.ExcursionTelescope
#print axioms two_step_landing
#print axioms drop_iff_two
#print axioms drop_iff_two_expanded
#print axioms three_step_landing
#print axioms drop_iff_three
#print axioms drop_iff_three_expanded
#print axioms drop_of_three_one_then_v_one_heavy
#print axioms grows_of_three_one_then_one_one
#print axioms drop_of_three_one_one_one_then_v_one
#print axioms drop_iff_two_one
#print axioms drop_of_two_one_then_v_four
#print axioms lemmaX_of_two_one_then_v_six
#print axioms drop_of_four_one_then_v_one_heavy
#print axioms grows_of_four_one_then_one_one
end AxiomAudit
