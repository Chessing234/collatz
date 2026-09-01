import Collatz.Accelerated
import Collatz.Core.Arith
import Collatz.Strategy.LiftExponent
import Collatz.Strategy.ExcursionMap

/-!
# The orbital ideal — Fitting content of the excursion lattice

An orbit prefix does not naturally produce a strictly descending chain of
ideals in a Noetherian ring: Noetherian is ACC, not DCC, and the vanishing
ideal of the first `k` orbit points in `ℚ[x]` is a strictly descending chain
on any infinite distinct orbit, with no contradiction.  The usable polarity
is the opposite one.  Extending the prefix must *enlarge* an ideal of `ℤ`
(equivalently, shrink a gcd).

Three objects are recorded.

1. **The difference ideal** `orbitalDiff n k`, the gcd of consecutive
   `|T^{i+1}(n) − T^i(n)|`.  Nested, and **equal to `1` as soon as the prefix
   contains one odd step and one even step** (`mixed_steps_unit`).  Secretly
   `(1)` on every mixed-parity prefix the rest of the development uses.
   Negative theorem.

2. **Type Fitting** `typeFit`.  Columns `(3^v, 2^W)` of the excursion types
   along a prefix; content is the gcd of `2×2` minors.  Zero if and only if
   every type is the same (`typeFit_eq_zero_iff`).  Not constantly `0` or
   `1`: two `(2,1)` give `0`, `(2,1)` then `(3,1)` give `36`, `(2,1)` then
   `(4,3)` give `90`.  The leftover rigid light word is exactly the kernel.

3. **Cofactor Fitting** `coFit`.  Columns `(3^v · u, 2^W)`.  On a repeated
   type this is `3^v · 2^W · |u − u'|`, so a pure `(2,1)`-word with changing
   cofactor has content `18 |u − u'|`, never `0` and never `1`.  The repair
   that still moves where `typeFit` vanishes.

No statement about Collatz is made.  Stabilisation of either Fitting gcd is
a theorem about a lattice of types (or cofactors), not a bound on an orbit.
-/

namespace Collatz
namespace DeviceIdeal

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap


/-! ## Absolute difference, as a gcd generator -/

/-- `|a − b|` in `Nat`, branch-free so that `omega` can see it. -/
def absNat (a b : Nat) : Nat := (a - b) + (b - a)

theorem absNat_of_le {a b : Nat} (h : a ≤ b) : absNat a b = b - a := by
  simp [absNat]; omega

theorem absNat_of_ge {a b : Nat} (h : b ≤ a) : absNat a b = a - b := by
  simp [absNat]; omega

theorem absNat_comm (a b : Nat) : absNat a b = absNat b a := by
  rcases Nat.le_total a b with h | h
  · rw [absNat_of_le h, absNat_of_ge h]
  · rw [absNat_of_ge h, absNat_of_le h]

theorem absNat_self (a : Nat) : absNat a a = 0 := by
  rw [absNat_of_le (Nat.le_refl a), Nat.sub_self]

theorem absNat_eq_zero (a b : Nat) : absNat a b = 0 ↔ a = b := by
  constructor
  · intro h
    rcases Nat.le_total a b with hab | hba
    · have := absNat_of_le hab; omega
    · have := absNat_of_ge hba; omega
  · intro h; subst h; exact absNat_self a

/-- Congruence modulo `d > 0` is divisibility of the absolute difference. -/
theorem mod_eq_iff_dvd_sub {d a b : Nat} (_hd : 0 < d) (hab : a ≤ b) :
    a % d = b % d ↔ d ∣ b - a := by
  constructor
  · intro h
    have ha := Nat.div_add_mod a d
    have hb := Nat.div_add_mod b d
    refine ⟨b / d - a / d, ?_⟩
    have hdiv : a / d ≤ b / d := Nat.div_le_div_right hab
    calc
      b - a
          = (d * (b / d) + b % d) - (d * (a / d) + a % d) := by rw [ha, hb]
      _ = (d * (b / d) + a % d) - (d * (a / d) + a % d) := by rw [h]
      _ = d * (b / d) - d * (a / d) := by omega
      _ = d * (b / d - a / d) := (Nat.mul_sub_left_distrib _ _ _).symm
  · intro ⟨k, hk⟩
    have : b = a + (b - a) := by omega
    rw [this, hk, Nat.add_mul_mod_self_left]

theorem mod_eq_iff_dvd_abs {d a b : Nat} (hd : 0 < d) :
    a % d = b % d ↔ d ∣ absNat a b := by
  rcases Nat.le_total a b with hab | hba
  · rw [absNat_of_le hab]
    exact mod_eq_iff_dvd_sub hd hab
  · rw [absNat_of_ge hba]
    have := mod_eq_iff_dvd_sub hd hba
    exact ⟨this.mp ∘ Eq.symm, Eq.symm ∘ this.mpr⟩

/-- `gcd(|a−b|, |b−c|)` divides `|a−c|`. -/
theorem gcd_abs_triangle (a b c : Nat) :
    Nat.gcd (absNat a b) (absNat b c) ∣ absNat a c := by
  have hd1 := Nat.gcd_dvd_left (absNat a b) (absNat b c)
  have hd2 := Nat.gcd_dvd_right (absNat a b) (absNat b c)
  cases Nat.eq_zero_or_pos (Nat.gcd (absNat a b) (absNat b c)) with
  | inl h0 =>
    rw [h0]
    have hab : absNat a b = 0 := (Nat.gcd_eq_zero_iff.mp h0).1
    have hbc : absNat b c = 0 := (Nat.gcd_eq_zero_iff.mp h0).2
    have ea : a = b := (absNat_eq_zero a b).mp hab
    have eb : b = c := (absNat_eq_zero b c).mp hbc
    subst ea; subst eb
    simp [absNat_self]
  | inr hdpos =>
    have h1 : a % _ = b % _ := (mod_eq_iff_dvd_abs hdpos).mpr hd1
    have h2 : b % _ = c % _ := (mod_eq_iff_dvd_abs hdpos).mpr hd2
    exact (mod_eq_iff_dvd_abs hdpos).mp (h1.trans h2)

theorem dvd_of_dvd_absNat {d x y : Nat} (habs : d ∣ absNat x y) (hy : d ∣ y) :
    d ∣ x := by
  cases Nat.eq_zero_or_pos d with
  | inl h0 =>
    subst h0
    have hy0 : y = 0 := Nat.zero_dvd.mp hy
    have hx0 : absNat x y = 0 := Nat.zero_dvd.mp habs
    have : x = y := (absNat_eq_zero x y).mp hx0
    subst this; subst hy0
    exact ⟨0, rfl⟩
  | inr hdpos =>
    rcases Nat.le_total x y with hxy | hyx
    · have : absNat x y = y - x := absNat_of_le hxy
      rw [this] at habs
      obtain ⟨k, hk⟩ := habs
      obtain ⟨m, hm⟩ := hy
      have hsum : x + d * k = d * m := by
        have : x + (y - x) = y := by omega
        rw [hk, hm] at this
        exact this
      refine ⟨m - k, ?_⟩
      have : d * (m - k) = d * m - d * k := Nat.mul_sub_left_distrib _ _ _
      omega
    · have : absNat x y = x - y := absNat_of_ge hyx
      rw [this] at habs
      obtain ⟨k, hk⟩ := habs
      obtain ⟨m, hm⟩ := hy
      refine ⟨k + m, ?_⟩
      have : x = (x - y) + y := by omega
      rw [this, hk, hm, Nat.mul_add]

theorem eq_one_of_dvd_one {d : Nat} (h : d ∣ 1) : d = 1 := by
  obtain ⟨t, ht⟩ := h
  have hpos : 0 < t := by
    cases t with
    | zero => omega
    | succ t => exact Nat.succ_pos t
  have hle : d ≤ 1 := by
    have : d ≤ d * t := Nat.le_mul_of_pos_right d hpos
    omega
  cases d with
  | zero => omega
  | succ d =>
    cases d with
    | zero => rfl
    | succ _ => omega


/-! ## Unique factorisation for the primes `2` and `3` -/

theorem three_pow_inj {a b : Nat} (h : 3 ^ a = 3 ^ b) : a = b := by
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · have := three_pow_lt_three_pow hlt; omega
  · exact heq
  · have := three_pow_lt_three_pow hgt; omega

/-- `3^v · 2^{W'} = 3^{v'} · 2^W` forces `v = v'` and `W = W'`. -/
theorem two_three_unique {v W v' W' : Nat}
    (h : 3 ^ v * 2 ^ W' = 3 ^ v' * 2 ^ W) : v = v' ∧ W = W' := by
  have hv : Val2 (3 ^ v * 2 ^ W') W' := by
    have hmul := Val2.mul (Val2.of_odd (three_pow_odd v)) (Val2.two_pow W')
    simpa using hmul
  have hv' : Val2 (3 ^ v' * 2 ^ W) W := by
    have hmul := Val2.mul (Val2.of_odd (three_pow_odd v')) (Val2.two_pow W)
    simpa using hmul
  have hW : W' = W := Val2.unique (h ▸ hv) hv'
  have hcancel : 3 ^ v * 2 ^ W' = 3 ^ v' * 2 ^ W' := by
    rw [h, hW]
  have : 3 ^ v = 3 ^ v' := Nat.eq_of_mul_eq_mul_right (two_pow_pos W') hcancel
  exact ⟨three_pow_inj this, hW.symm⟩


/-! ## Candidate C — the difference ideal, secretly `(1)` -/

/-- Consecutive step size at time `i`. -/
def stepDiff (n i : Nat) : Nat :=
  absNat (acceleratedOrbit i n) (acceleratedOrbit (i + 1) n)

/-- Gcd of the first `k` consecutive orbit differences.  The generator of the
principal difference ideal of the prefix `(n, T n, …, T^k n)`.  Empty prefix
(`k = 0`) is the zero ideal. -/
def orbitalDiff (n k : Nat) : Nat :=
  match k with
  | 0 => 0
  | k + 1 => Nat.gcd (stepDiff n k) (orbitalDiff n k)

theorem orbitalDiff_zero (n : Nat) : orbitalDiff n 0 = 0 := rfl

theorem orbitalDiff_succ (n k : Nat) :
    orbitalDiff n (k + 1) = Nat.gcd (stepDiff n k) (orbitalDiff n k) := rfl

/-- Extending the prefix shrinks the gcd (grows the ideal). -/
theorem orbitalDiff_succ_dvd (n k : Nat) :
    orbitalDiff n (k + 1) ∣ orbitalDiff n k :=
  Nat.gcd_dvd_right _ _

theorem orbitalDiff_dvd_step : ∀ {n k i : Nat}, i < k →
    orbitalDiff n k ∣ stepDiff n i
  | n, k + 1, i, hi => by
    rw [orbitalDiff_succ]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | heq
    · exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) (orbitalDiff_dvd_step hlt)
    · subst heq
      exact Nat.gcd_dvd_left _ _

/-- Every prefix value is congruent to the start, modulo `orbitalDiff n k`. -/
theorem orbitalDiff_dvd_from_start : ∀ {n k i : Nat}, i ≤ k →
    orbitalDiff n k ∣ absNat (acceleratedOrbit i n) n
  | n, 0, i, hi => by
    have : i = 0 := by omega
    subst this
    simp [orbitalDiff_zero, absNat_self, acceleratedOrbit_zero]
  | n, k + 1, i, hi => by
    rw [orbitalDiff_succ]
    rcases Nat.lt_or_eq_of_le hi with hlt | heq
    · have hle : i ≤ k := Nat.lt_succ_iff.mp hlt
      exact Nat.dvd_trans (Nat.gcd_dvd_right _ _)
        (orbitalDiff_dvd_from_start hle)
    · subst heq
      have hswap : stepDiff n k =
          absNat (acceleratedOrbit (k + 1) n) (acceleratedOrbit k n) := by
        simp [stepDiff, absNat_comm]
      have hstep : Nat.gcd (stepDiff n k) (orbitalDiff n k) ∣
          absNat (acceleratedOrbit (k + 1) n) (acceleratedOrbit k n) := by
        rw [hswap]
        exact Nat.gcd_dvd_left _ _
      have hstart : Nat.gcd (stepDiff n k) (orbitalDiff n k) ∣
          absNat (acceleratedOrbit k n) n :=
        Nat.dvd_trans (Nat.gcd_dvd_right _ _)
          (orbitalDiff_dvd_from_start (Nat.le_refl k))
      have hg : Nat.gcd (stepDiff n k) (orbitalDiff n k) ∣
          Nat.gcd (absNat (acceleratedOrbit (k + 1) n) (acceleratedOrbit k n))
            (absNat (acceleratedOrbit k n) n) :=
        Nat.dvd_gcd hstep hstart
      exact Nat.dvd_trans hg
        (gcd_abs_triangle (acceleratedOrbit (k + 1) n) (acceleratedOrbit k n) n)

theorem even_step_eq {v : Nat} (h : v % 2 = 0) :
    acceleratedStep v = v / 2 := by
  rw [acceleratedStep, if_pos h]

theorem odd_step_eq {v : Nat} (h : v % 2 = 1) :
    acceleratedStep v = (3 * v + 1) / 2 := by
  rw [acceleratedStep, if_neg (by omega)]

theorem two_mul_odd_step {v : Nat} (h : v % 2 = 1) :
    2 * acceleratedStep v = 3 * v + 1 := by
  rw [odd_step_eq h]
  omega

theorem absNat_half {v : Nat} (h : v % 2 = 0) : absNat v (v / 2) = v / 2 := by
  have : v / 2 ≤ v := by omega
  rw [absNat_of_ge this]
  have hv : 2 * (v / 2) = v := two_mul_div_two_of_even h
  omega

/-- **Negative theorem.**  One odd step and one even step in the prefix force
the difference ideal to be `(1)`. -/
theorem mixed_steps_unit {n k i j : Nat}
    (hn : 0 < n) (hi : i < k) (hj : j < k)
    (hodd : acceleratedOrbit i n % 2 = 1)
    (heven : acceleratedOrbit j n % 2 = 0) :
    orbitalDiff n k = 1 := by
  let d := orbitalDiff n k
  have hd_step_j : d ∣ stepDiff n j := orbitalDiff_dvd_step hj
  have hstepj : acceleratedStep (acceleratedOrbit j n) =
      acceleratedOrbit j n / 2 := even_step_eq heven
  have hsd : stepDiff n j = acceleratedOrbit j n / 2 := by
    unfold stepDiff
    rw [acceleratedOrbit_succ_step, hstepj, absNat_half heven]
  have hd_half : d ∣ acceleratedOrbit j n / 2 := by rwa [hsd] at hd_step_j
  have hd_even : d ∣ acceleratedOrbit j n := by
    have hv : 2 * (acceleratedOrbit j n / 2) = acceleratedOrbit j n :=
      two_mul_div_two_of_even heven
    obtain ⟨t, ht⟩ := hd_half
    refine ⟨2 * t, ?_⟩
    rw [← hv, ht, Nat.mul_left_comm]
  have hd_start : d ∣ absNat (acceleratedOrbit j n) n :=
    orbitalDiff_dvd_from_start (Nat.le_of_lt hj)
  have hd_n : d ∣ n := dvd_of_dvd_absNat (absNat_comm _ _ ▸ hd_start) hd_even
  have hd_i : d ∣ acceleratedOrbit i n :=
    dvd_of_dvd_absNat (orbitalDiff_dvd_from_start (Nat.le_of_lt hi)) hd_n
  have hi1 : i + 1 ≤ k := Nat.succ_le_of_lt hi
  have hd_i1 : d ∣ acceleratedOrbit (i + 1) n :=
    dvd_of_dvd_absNat (orbitalDiff_dvd_from_start hi1) hd_n
  have hival := acceleratedOrbit_succ_step i n
  have h2 : 2 * acceleratedOrbit (i + 1) n = 3 * acceleratedOrbit i n + 1 := by
    rw [hival, two_mul_odd_step hodd]
  have hd_3m1 : d ∣ 3 * acceleratedOrbit i n + 1 := by
    obtain ⟨t, ht⟩ := hd_i1
    refine ⟨2 * t, ?_⟩
    rw [← h2, ht, Nat.mul_left_comm]
  have hd_3m : d ∣ 3 * acceleratedOrbit i n := by
    obtain ⟨t, ht⟩ := hd_i
    refine ⟨3 * t, ?_⟩
    rw [ht, Nat.mul_left_comm]
  have hd1 : d ∣ 1 := by
    have hsub : 3 * acceleratedOrbit i n + 1 - 3 * acceleratedOrbit i n = 1 := by
      omega
    have := Nat.dvd_sub hd_3m1 hd_3m
    rwa [hsub] at this
  have hdpos : 0 < d := by
    cases Nat.eq_zero_or_pos d with
    | inr h => exact h
    | inl h0 =>
      have hsn : d ∣ n := hd_n
      rw [h0] at hsn
      have : n = 0 := Nat.zero_dvd.mp hsn
      omega
  exact eq_one_of_dvd_one hd1


/-! ## The trivial generator is the zero ideal -/

/-- The excursion identity, as an integer: the generator
`3^v u − 2^W e − 1` is zero.  Candidate A. -/
theorem excursion_relation_zero {n v u W e : Nat}
    (h : IsExcursion n v u W e) : 3 ^ v * u = 2 ^ W * e + 1 :=
  h.2.2.2.2.2.2


/-! ## Type Fitting — columns `(3^v, 2^W)` -/

/-- Absolute `2×2` minor of columns `(3^v, 2^W)` and `(3^{v'}, 2^{W'})`. -/
def minor (v W v' W' : Nat) : Nat :=
  absNat (3 ^ v * 2 ^ W') (3 ^ v' * 2 ^ W)

theorem minor_self (v W : Nat) : minor v W v W = 0 := by
  simp [minor, absNat_self]

theorem minor_comm (v W v' W' : Nat) : minor v W v' W' = minor v' W' v W := by
  simp [minor, absNat_comm]

theorem minor_eq_zero_iff {v W v' W' : Nat} :
    minor v W v' W' = 0 ↔ v = v' ∧ W = W' := by
  constructor
  · intro h
    have heq : 3 ^ v * 2 ^ W' = 3 ^ v' * 2 ^ W :=
      (absNat_eq_zero _ _).mp (by simpa [minor] using h)
    exact two_three_unique heq
  · intro ⟨hv, hW⟩
    subst hv; subst hW
    exact minor_self v W

/-- Gcd of minors between a fixed column and each column of a list. -/
def minorsAgainst (v W : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (v', W') :: rest => Nat.gcd (minor v W v' W') (minorsAgainst v W rest)

/-- Fitting content of the type matrix: gcd of all `2×2` minors. -/
def typeFit : List (Nat × Nat) → Nat
  | [] => 0
  | (v, W) :: rest => Nat.gcd (minorsAgainst v W rest) (typeFit rest)

theorem typeFit_nil : typeFit [] = 0 := rfl

theorem typeFit_singleton (p : Nat × Nat) : typeFit [p] = 0 := by
  cases p with
  | mk v W => simp [typeFit, minorsAgainst]

theorem typeFit_pair (v W v' W' : Nat) :
    typeFit [(v, W), (v', W')] = minor v W v' W' := by
  simp [typeFit, minorsAgainst]

theorem minorsAgainst_nil (v W : Nat) : minorsAgainst v W [] = 0 := rfl

theorem minorsAgainst_append (v W : Nat) :
    ∀ xs ys : List (Nat × Nat),
      minorsAgainst v W (xs ++ ys) =
        Nat.gcd (minorsAgainst v W xs) (minorsAgainst v W ys)
  | [], ys => by
    simp [minorsAgainst, Nat.gcd_zero_left]
  | (v', W') :: rest, ys => by
    simp [minorsAgainst, minorsAgainst_append v W rest ys, Nat.gcd_assoc]

theorem minorsAgainst_eq_zero (v W : Nat) :
    ∀ ps : List (Nat × Nat),
      minorsAgainst v W ps = 0 ↔ ∀ q ∈ ps, q = (v, W)
  | [] => by
    constructor
    · intro _ q hq; cases hq
    · intro _; rfl
  | (v', W') :: rest => by
    constructor
    · intro h q hq
      have h' : Nat.gcd (minor v W v' W') (minorsAgainst v W rest) = 0 := by
        simpa [minorsAgainst] using h
      have hg : minor v W v' W' = 0 ∧ minorsAgainst v W rest = 0 :=
        Nat.gcd_eq_zero_iff.mp h'
      have hp : v = v' ∧ W = W' := minor_eq_zero_iff.mp hg.1
      cases hq with
      | head =>
        obtain ⟨hv, hW⟩ := hp
        subst hv; subst hW; rfl
      | tail _ hq' =>
        exact (minorsAgainst_eq_zero v W rest).mp hg.2 q hq'
    · intro hall
      simp [minorsAgainst, Nat.gcd_eq_zero_iff]
      constructor
      · have hq : (v', W') = (v, W) := hall (v', W') (List.mem_cons_self)
        injection hq with hv hW
        exact minor_eq_zero_iff.mpr ⟨hv.symm, hW.symm⟩
      · exact (minorsAgainst_eq_zero v W rest).mpr fun q hq =>
          hall q (List.mem_cons_of_mem (v', W') hq)

theorem typeFit_eq_zero_iff :
    ∀ ps : List (Nat × Nat),
      typeFit ps = 0 ↔ ∀ p ∈ ps, ∀ q ∈ ps, p = q
  | [] => by
    constructor
    · intro _ p hp; cases hp
    · intro _; rfl
  | (v, W) :: rest => by
    constructor
    · intro h p hp q hq
      have h' : Nat.gcd (minorsAgainst v W rest) (typeFit rest) = 0 := by
        simpa [typeFit] using h
      have hg : minorsAgainst v W rest = 0 ∧ typeFit rest = 0 :=
        Nat.gcd_eq_zero_iff.mp h'
      have hrest := (typeFit_eq_zero_iff rest).mp hg.2
      have hcol := (minorsAgainst_eq_zero v W rest).mp hg.1
      have hp' : p = (v, W) ∨ p ∈ rest := List.mem_cons.mp hp
      have hq' : q = (v, W) ∨ q ∈ rest := List.mem_cons.mp hq
      rcases hp' with hp | hp <;> rcases hq' with hq | hq
      · subst hp; subst hq; rfl
      · subst hp; exact (hcol q hq).symm
      · subst hq; exact hcol p hp
      · exact hrest p hp q hq
    · intro hall
      simp [typeFit, Nat.gcd_eq_zero_iff]
      constructor
      · exact (minorsAgainst_eq_zero v W rest).mpr fun q hq =>
          (hall (v, W) List.mem_cons_self q (List.mem_cons_of_mem (v, W) hq)).symm
      · exact (typeFit_eq_zero_iff rest).mpr fun p hp q hq =>
          hall p (List.mem_cons_of_mem (v, W) hp) q (List.mem_cons_of_mem (v, W) hq)

/-- If `a ∣ c` and `b ∣ d` then `gcd a b ∣ gcd c d`. -/
private theorem gcd_dvd_gcd_of_dvd {a b c d : Nat}
    (hac : a ∣ c) (hbd : b ∣ d) : Nat.gcd a b ∣ Nat.gcd c d :=
  Nat.dvd_trans (Nat.gcd_dvd_gcd_of_dvd_left b hac)
    (Nat.gcd_dvd_gcd_of_dvd_right c hbd)

/-- Extending the list on the left shrinks the gcd. -/
theorem typeFit_cons_dvd (p : Nat × Nat) (ps : List (Nat × Nat)) :
    typeFit (p :: ps) ∣ typeFit ps := by
  cases p with
  | mk v W =>
    simp [typeFit]
    exact Nat.gcd_dvd_right _ _

theorem typeFit_append_dvd :
    ∀ ps qs : List (Nat × Nat), typeFit (ps ++ qs) ∣ typeFit ps
  | [], qs => Nat.dvd_zero _
  | (v, W) :: rest, qs => by
    have ih : typeFit (rest ++ qs) ∣ typeFit rest := typeFit_append_dvd rest qs
    have hm : minorsAgainst v W (rest ++ qs) ∣ minorsAgainst v W rest := by
      rw [minorsAgainst_append]
      exact Nat.gcd_dvd_left _ _
    simpa [typeFit] using gcd_dvd_gcd_of_dvd hm ih

theorem minorsAgainst_replicate (v W : Nat) :
    ∀ n : Nat, minorsAgainst v W (List.replicate n (v, W)) = 0
  | 0 => rfl
  | n + 1 => by
    simp [minorsAgainst, List.replicate_succ, minor_self,
      minorsAgainst_replicate v W n]

/-- A rigid type word has vanishing Fitting content. -/
theorem typeFit_replicate (p : Nat × Nat) :
    ∀ n : Nat, typeFit (List.replicate n p) = 0
  | 0 => rfl
  | n + 1 => by
    cases p with
    | mk v W =>
      simp [typeFit, List.replicate_succ, minorsAgainst_replicate,
        typeFit_replicate (v, W) n]


/-! ## Kernel-checked contents, not constantly `0` or `1` -/

theorem typeFit_two_light : typeFit [(2, 1), (2, 1)] = 0 := rfl

theorem typeFit_light_then_one : typeFit [(2, 1), (1, 1)] = 12 := rfl

theorem typeFit_light_then_two_two : typeFit [(2, 1), (2, 2)] = 18 := rfl

theorem typeFit_light_then_three : typeFit [(2, 1), (3, 1)] = 36 := rfl

theorem typeFit_light_then_four : typeFit [(2, 1), (4, 3)] = 90 := rfl

theorem typeFit_three_then_four : typeFit [(3, 1), (4, 1)] = 108 := rfl

theorem typeFit_three_types : typeFit [(2, 1), (3, 1), (4, 1)] = 36 := rfl

theorem typeFit_three_types_drop : typeFit [(2, 1), (3, 1), (4, 3)] = 18 := rfl

theorem typeFit_light_chain (n : Nat) :
    typeFit (List.replicate n (2, 1)) = 0 :=
  typeFit_replicate (2, 1) n

/-- Two consecutive excursions contribute their type-minor as Fitting content. -/
theorem typeFit_of_two_excursions
    {n v u W e v' u' W' e' : Nat}
    (_h : IsExcursion n v u W e) (_h' : IsExcursion e v' u' W' e') :
    typeFit [(v, W), (v', W')] = minor v W v' W' :=
  typeFit_pair v W v' W'


/-! ## Cofactor Fitting — the repair that moves on a rigid type -/

/-- Absolute `2×2` minor of columns `(3^v · u, 2^W)` and `(3^{v'} · u', 2^{W'})`. -/
def coMinor (v u W v' u' W' : Nat) : Nat :=
  absNat (3 ^ v * u * 2 ^ W') (3 ^ v' * u' * 2 ^ W)

theorem absNat_mul_left (c a b : Nat) :
    absNat (c * a) (c * b) = c * absNat a b := by
  cases c with
  | zero => simp [absNat]
  | succ c =>
    have hc : 0 < c + 1 := Nat.succ_pos c
    rcases Nat.le_total a b with hab | hba
    · have : (c + 1) * a ≤ (c + 1) * b := Nat.mul_le_mul_left _ hab
      rw [absNat_of_le hab, absNat_of_le this, Nat.mul_sub_left_distrib]
    · have : (c + 1) * b ≤ (c + 1) * a := Nat.mul_le_mul_left _ hba
      rw [absNat_of_ge hba, absNat_of_ge this, Nat.mul_sub_left_distrib]

/-- On a repeated type, cofactor Fitting is scaled cofactor drift. -/
theorem coMinor_same_type (v u W u' : Nat) :
    coMinor v u W v u' W = 3 ^ v * 2 ^ W * absNat u u' := by
  have h1 : 3 ^ v * u * 2 ^ W = (3 ^ v * 2 ^ W) * u := by
    rw [Nat.mul_assoc, Nat.mul_comm u, ← Nat.mul_assoc]
  have h2 : 3 ^ v * u' * 2 ^ W = (3 ^ v * 2 ^ W) * u' := by
    rw [Nat.mul_assoc, Nat.mul_comm u', ← Nat.mul_assoc]
  simp [coMinor, h1, h2, absNat_mul_left]

def coMinorsAgainst (v u W : Nat) : List (Nat × Nat × Nat) → Nat
  | [] => 0
  | (v', u', W') :: rest =>
      Nat.gcd (coMinor v u W v' u' W') (coMinorsAgainst v u W rest)

def coFit : List (Nat × Nat × Nat) → Nat
  | [] => 0
  | (v, u, W) :: rest => Nat.gcd (coMinorsAgainst v u W rest) (coFit rest)

theorem coFit_nil : coFit [] = 0 := rfl

theorem coFit_singleton (p : Nat × Nat × Nat) : coFit [p] = 0 := by
  rcases p with ⟨v, u, W⟩
  simp [coFit, coMinorsAgainst]

theorem coFit_pair (v u W v' u' W' : Nat) :
    coFit [(v, u, W), (v', u', W')] = coMinor v u W v' u' W' := by
  simp [coFit, coMinorsAgainst]

theorem coMinorsAgainst_append (v u W : Nat) :
    ∀ xs ys : List (Nat × Nat × Nat),
      coMinorsAgainst v u W (xs ++ ys) =
        Nat.gcd (coMinorsAgainst v u W xs) (coMinorsAgainst v u W ys)
  | [], ys => by simp [coMinorsAgainst, Nat.gcd_zero_left]
  | (v', u', W') :: rest, ys => by
    simp [coMinorsAgainst, coMinorsAgainst_append v u W rest ys, Nat.gcd_assoc]

theorem coFit_cons_dvd (p : Nat × Nat × Nat) (ps : List (Nat × Nat × Nat)) :
    coFit (p :: ps) ∣ coFit ps := by
  rcases p with ⟨v, u, W⟩
  simp [coFit]
  exact Nat.gcd_dvd_right _ _

theorem coFit_append_dvd :
    ∀ ps qs : List (Nat × Nat × Nat), coFit (ps ++ qs) ∣ coFit ps
  | [], qs => Nat.dvd_zero _
  | (v, u, W) :: rest, qs => by
    have ih : coFit (rest ++ qs) ∣ coFit rest := coFit_append_dvd rest qs
    have hm : coMinorsAgainst v u W (rest ++ qs) ∣ coMinorsAgainst v u W rest := by
      rw [coMinorsAgainst_append]
      exact Nat.gcd_dvd_left _ _
    simpa [coFit] using gcd_dvd_gcd_of_dvd hm ih

/-- Two `(2,1)` excursions with cofactors `u, u'` have cofactor Fitting
`18 |u − u'|`.  Not `0` unless the cofactor repeats, not `1`. -/
theorem coFit_two_light (u u' : Nat) :
    coFit [(2, u, 1), (2, u', 1)] = 18 * absNat u u' := by
  have h : coMinor 2 u 1 2 u' 1 = 3 ^ 2 * 2 ^ 1 * absNat u u' :=
    coMinor_same_type 2 u 1 u'
  simp [coFit_pair, h]

theorem coFit_two_light_distinct {u u' : Nat} (h : u ≠ u') :
    0 < coFit [(2, u, 1), (2, u', 1)] := by
  rw [coFit_two_light]
  have : 0 < absNat u u' := by
    have : absNat u u' ≠ 0 := by
      intro hz
      exact h ((absNat_eq_zero u u').mp hz)
    omega
  omega

/-- Two consecutive excursions contribute their cofactor-minor. -/
theorem coFit_of_two_excursions
    {n v u W e v' u' W' e' : Nat}
    (_h : IsExcursion n v u W e) (_h' : IsExcursion e v' u' W' e') :
    coFit [(v, u, W), (v', u', W')] = coMinor v u W v' u' W' :=
  coFit_pair v u W v' u' W'

end DeviceIdeal
end Collatz
