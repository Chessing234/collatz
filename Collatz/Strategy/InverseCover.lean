import Collatz.Strategy.ClassChild

/-!
# Uniform, size-bounded covering by inverse Collatz paths

An inverse word lists positive exponents `v`; each letter replaces `a` by
`(2^v*a-1)/3`, provided this is integral. A word of length `d` and total
valuation `V` costs strictly less than `2^V/3^d` times its root.

Its admissibility and endpoint modulo `3^k` depend only on the root modulo
`3^(k+d)`. Thus a finite ternary decision tree can certify coverage for ALL
positive roots prime to three, including roots outside every verified range.
The decision tree is data, and `check_sound` proves the checker correct.

These are finite-modulus covering statements, not convergence or density
claims. The inverse affine formula and modular lifting are classical; no
claim of literature novelty is made for the general mechanism.
-/

namespace Collatz.InverseCover

open TreeCount

def follow (a : Nat) : List Nat → Nat
  | [] => a
  | v :: w => follow (child a v) w

def Valid (a : Nat) : List Nat → Prop
  | [] => True
  | v :: w => 1 ≤ v ∧ (2 ^ v * a) % 3 = 1 ∧ Valid (child a v) w

instance instDecidableValid (a : Nat) (w : List Nat) : Decidable (Valid a w) :=
  match w with
  | [] => isTrue trivial
  | v :: w =>
      haveI : Decidable (Valid (child a v) w) := instDecidableValid (child a v) w
      inferInstanceAs (Decidable (1 ≤ v ∧ (2 ^ v * a) % 3 = 1 ∧ Valid (child a v) w))

theorem follow_orbit {a : Nat} {w : List Nat} (h : Valid a w) :
    acceleratedOrbit w.sum (follow a w) = a := by
  induction w generalizing a with
  | nil => rfl
  | cons v w ih =>
    obtain ⟨hv, hm, ht⟩ := h
    change acceleratedOrbit (v + w.sum) (follow (child a v) w) = a
    rw [← acceleratedOrbit_add, ih ht]
    exact orbit_child hv hm

theorem follow_pos {a : Nat} {w : List Nat} (ha : 0 < a) (h : Valid a w) :
    0 < follow a w := by
  induction w generalizing a with
  | nil => exact ha
  | cons v w ih => exact ih (child_pos ha h.1 h.2.1) h.2.2

theorem follow_odd {a : Nat} {w : List Nat} (hne : w ≠ []) (h : Valid a w) :
    follow a w % 2 = 1 := by
  induction w generalizing a with
  | nil => exact False.elim (hne rfl)
  | cons v w ih =>
    cases w with
    | nil => exact child_odd h.1 h.2.1
    | cons u t => exact ih (by simp) h.2.2

theorem follow_le {a : Nat} {w : List Nat} (h : Valid a w) :
    3 ^ w.length * follow a w ≤ 2 ^ w.sum * a := by
  induction w generalizing a with
  | nil => simp [follow]
  | cons v w ih =>
    have ht := Nat.mul_le_mul_left 3 (ih h.2.2)
    have hc := child_eq h.2.1
    have hb : 3 * child a v ≤ 2 ^ v * a := by omega
    have hb' := Nat.mul_le_mul_left (2 ^ w.sum) hb
    simp only [follow, List.length_cons, List.sum_cons, Nat.pow_succ, Nat.pow_add]
    calc
      3 ^ w.length * 3 * follow (child a v) w
          = 3 * (3 ^ w.length * follow (child a v) w) := by ac_rfl
      _ ≤ 3 * (2 ^ w.sum * child a v) := ht
      _ = 2 ^ w.sum * (3 * child a v) := by ac_rfl
      _ ≤ 2 ^ w.sum * (2 ^ v * a) := hb'
      _ = 2 ^ v * 2 ^ w.sum * a := by ac_rfl

theorem follow_lt {a : Nat} {w : List Nat} (hne : w ≠ []) (h : Valid a w) :
    3 ^ w.length * follow a w < 2 ^ w.sum * a := by
  cases w with
  | nil => exact False.elim (hne rfl)
  | cons v w =>
    have ht := Nat.mul_le_mul_left 3 (follow_le h.2.2)
    have hc := child_eq h.2.1
    have hb : 3 * child a v < 2 ^ v * a := by omega
    have hb' := Nat.mul_lt_mul_of_pos_left hb (Nat.two_pow_pos w.sum)
    simp only [follow, List.length_cons, List.sum_cons, Nat.pow_succ, Nat.pow_add]
    calc
      3 ^ w.length * 3 * follow (child a v) w
          = 3 * (3 ^ w.length * follow (child a v) w) := by ac_rfl
      _ ≤ 3 * (2 ^ w.sum * child a v) := ht
      _ = 2 ^ w.sum * (3 * child a v) := by ac_rfl
      _ < 2 ^ w.sum * (2 ^ v * a) := hb'
      _ = 2 ^ v * 2 ^ w.sum * a := by ac_rfl

theorem mod_pow_of_le {a b i j : Nat} (hij : i ≤ j)
    (h : a % 3 ^ j = b % 3 ^ j) : a % 3 ^ i = b % 3 ^ i := by
  have hd : (3 : Nat) ^ i ∣ 3 ^ j := Nat.pow_dvd_pow 3 hij
  have := congrArg (fun x => x % 3 ^ i) h
  simpa only [Nat.mod_mod_of_dvd _ hd] using this

/-- Each inverse division consumes one ternary digit of root precision. -/
theorem follow_congr {a b : Nat} {w : List Nat} (k : Nat)
    (hab : a % 3 ^ (k + w.length) = b % 3 ^ (k + w.length))
    (hb : Valid b w) : Valid a w ∧ follow a w % 3 ^ k = follow b w % 3 ^ k := by
  induction w generalizing a b with
  | nil => exact ⟨trivial, hab⟩
  | cons v w ih =>
    have hab3 : a % 3 = b % 3 := by
      simpa using mod_pow_of_le (i := 1) (by simp; omega) hab
    have hm : (2 ^ v * a) % 3 = 1 := by
      rw [Nat.mul_mod, hab3, ← Nat.mul_mod]
      exact hb.2.1
    have hmul : (2 ^ v * a) % 3 ^ (k + w.length + 1) =
        (2 ^ v * b) % 3 ^ (k + w.length + 1) := by
      have he : k + (v :: w).length = k + w.length + 1 := by simp; omega
      rw [he] at hab
      rw [Nat.mul_mod, hab, ← Nat.mul_mod]
    have hc : child a v % 3 ^ (k + w.length) = child b v % 3 ^ (k + w.length) := by
      rw [ClassChild.child_mod_pow hm, ClassChild.child_mod_pow hb.2.1, hmul]
    obtain ⟨ht, he⟩ := ih hc hb.2.2
    exact ⟨⟨hb.1, hm, ht⟩, he⟩

/-- A leaf gives a word; a split covers all three possibilities for the next digit. -/
inductive HitCert where
  | leaf : List Nat → HitCert
  | split : HitCert → HitCert → HitCert → HitCert

def check (k r B V b e : Nat) : HitCert → Bool
  | .leaf w => decide (w ≠ [] ∧ k + w.length ≤ e ∧ Valid b w ∧
      follow b w % 3 ^ k = r ∧ w.sum ≤ V ∧ 2 ^ w.sum ≤ B * 3 ^ w.length)
  | .split c0 c1 c2 =>
      check k r B V b (e + 1) c0 &&
      check k r B V (b + 3 ^ e) (e + 1) c1 &&
      check k r B V (b + 2 * 3 ^ e) (e + 1) c2

/-- A checked tree produces a genuine odd inverse orbit, with a uniform bound. -/
theorem check_sound {k r B V b e : Nat} {c : HitCert}
    (hc : check k r B V b e c = true) {a : Nat} (ha : 0 < a)
    (hab : a % 3 ^ e = b) :
    ∃ n t, 0 < n ∧ n % 2 = 1 ∧ n % 3 ^ k = r ∧
      t ≤ V ∧ acceleratedOrbit t n = a ∧ n < B * a := by
  induction c generalizing b e with
  | leaf w =>
    have hw : w ≠ [] ∧ k + w.length ≤ e ∧ Valid b w ∧
        follow b w % 3 ^ k = r ∧ w.sum ≤ V ∧ 2 ^ w.sum ≤ B * 3 ^ w.length :=
      of_decide_eq_true hc
    have hab' : a % 3 ^ e = b % 3 ^ e := by
      rw [← hab, Nat.mod_mod]
    obtain ⟨hv, he⟩ := follow_congr k (mod_pow_of_le hw.2.1 hab') hw.2.2.1
    refine ⟨follow a w, w.sum, follow_pos ha hv, follow_odd hw.1 hv,
      he.trans hw.2.2.2.1, hw.2.2.2.2.1, follow_orbit hv, ?_⟩
    have hlt := follow_lt hw.1 hv
    have hle := Nat.mul_le_mul_right a hw.2.2.2.2.2
    have hlt' : 3 ^ w.length * follow a w < 3 ^ w.length * (B * a) := by
      calc
        _ < 2 ^ w.sum * a := hlt
        _ ≤ (B * 3 ^ w.length) * a := hle
        _ = _ := by ac_rfl
    exact Nat.lt_of_mul_lt_mul_left hlt'
  | split c0 c1 c2 ih0 ih1 ih2 =>
    have hs : (check k r B V b (e + 1) c0 = true ∧
        check k r B V (b + 3 ^ e) (e + 1) c1 = true) ∧
        check k r B V (b + 2 * 3 ^ e) (e + 1) c2 = true := by
      simpa only [check, Bool.and_eq_true] using hc
    have hp : 0 < 3 ^ e := Nat.pow_pos (by decide)
    have hsmall : b < 3 ^ e := hab ▸ Nat.mod_lt a hp
    have hmod : (a % 3 ^ (e + 1)) % 3 ^ e = b := by
      rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 3 (by omega)), hab]
    have hbound : a % 3 ^ (e + 1) < 3 * 3 ^ e := by
      rw [← Nat.pow_succ']
      exact Nat.mod_lt _ (Nat.pow_pos (by decide))
    have hdiv := Nat.div_add_mod (a % 3 ^ (e + 1)) (3 ^ e)
    have hq : (a % 3 ^ (e + 1)) / 3 ^ e < 3 := by
      exact (Nat.div_lt_iff_lt_mul hp).2 (by omega)
    have hcases : a % 3 ^ (e + 1) = b ∨ a % 3 ^ (e + 1) = b + 3 ^ e ∨
        a % 3 ^ (e + 1) = b + 2 * 3 ^ e := by
      have hq' : (a % 3 ^ (e + 1)) / 3 ^ e = 0 ∨
          (a % 3 ^ (e + 1)) / 3 ^ e = 1 ∨
          (a % 3 ^ (e + 1)) / 3 ^ e = 2 := by
        have small_nat : ∀ q : Nat, q < 3 → q = 0 ∨ q = 1 ∨ q = 2 := by omega
        exact small_nat _ hq
      rcases hq' with h | h | h <;> rw [h, hmod] at hdiv <;> omega
    rcases hcases with h | h | h
    · exact ih0 hs.1.1 h
    · exact ih1 hs.1.2 h
    · exact ih2 hs.2 h

end Collatz.InverseCover
