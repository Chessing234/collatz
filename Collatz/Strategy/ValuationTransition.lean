import Collatz.Strategy.ScaleRecord
import Collatz.Structure.OddRuns

/-!
# Round XV — the valuation transition system, and what it can and cannot do

For odd `n` the Syracuse map is `S(n) = (3n+1) / 2^r` with `r = v₂(3n+1) ≥ 1`.
This file builds the **valuation transition system**: a step is recorded as the
triple `(n, r, m)` with `3n+1 = 2^r * m`, `m` odd, and a run of steps is a list
of valuations.  Three things are proved.

1. **The valuation is exactly a congruence mod `2^(r+1)`** (`val_iff_mod`,
   `val_mod_determined`, `val_class_unique`, `three_inv_exists`).  The residue
   `n % 2^(r+1)` decides `v₂(3n+1) = r`, and exactly one odd class mod `2^(r+1)`
   has valuation `r`.

2. **The exact two-sided affine law of a run** (`path_affine`), with the sharp
   upper bound on the accumulator, giving an exact **drop certificate**
   (`drop_of_certificate`) and its **necessary condition** (`drop_necessary`):
   a run of length `L` with valuation sum `S` can only drop if `3^L < 2^S`.

3. **The even branch is exactly what the criterion reads**
   (`no_drop_of_unit_valuation`, `expStep_fails_certificate`).  `expStep` has
   valuation identically `1`, hence `S = L`, hence `3^L < 2^S` is *false* for
   it at every length; so the criterion of this file is not satisfied by the
   Round X witness map, and is therefore not a consequence of
   affine law + parity word + heaviness + positivity.
-/

namespace Collatz
namespace ValuationTransition

/-! ## 1.  One step of the transition system -/

/-- One Syracuse step recorded with its valuation: `n` odd, `m` odd,
`3n+1 = 2^r * m`.  This *is* the statement `r = v₂(3n+1)` and `m = S(n)`,
written without a valuation function. -/
def SyrStep (n r m : Nat) : Prop := n % 2 = 1 ∧ m % 2 = 1 ∧ 3 * n + 1 = 2 ^ r * m

/-- The source of a step is positive. -/
theorem SyrStep.pos {n r m : Nat} (h : SyrStep n r m) : 0 < n := by
  obtain ⟨h1, _, _⟩ := h; omega

/-- **Every valuation is at least one**: the odd branch always feeds the even
branch at least once. -/
theorem SyrStep.one_le {n r m : Nat} (h : SyrStep n r m) : 1 ≤ r := by
  obtain ⟨hn, hm, he⟩ := h
  cases r with
  | zero => simp at he; omega
  | succ k => omega

/-- The target of a step is positive. -/
theorem SyrStep.target_pos {n r m : Nat} (h : SyrStep n r m) : 0 < m := by
  obtain ⟨_, hm, _⟩ := h; omega

/-- A step determines its target. -/
theorem SyrStep.target_unique {n r m m' : Nat} (h : SyrStep n r m) (h' : SyrStep n r m') :
    m = m' := by
  obtain ⟨_, _, he⟩ := h
  obtain ⟨_, _, he'⟩ := h'
  have hp : 0 < (2 : Nat) ^ r := Nat.two_pow_pos r
  exact Nat.eq_of_mul_eq_mul_left hp (by omega)

/-- A step determines its valuation. -/
theorem SyrStep.val_unique {n r r' m m' : Nat} (h : SyrStep n r m) (h' : SyrStep n r' m') :
    r = r' := by
  obtain ⟨_, hm, he⟩ := h
  obtain ⟨_, hm', he'⟩ := h'
  have key : ∀ a b u v : Nat, u % 2 = 1 → v % 2 = 1 → 2 ^ a * u = 2 ^ b * v → a = b := by
    intro a
    induction a with
    | zero =>
      intro b u v hu hv hE
      cases b with
      | zero => rfl
      | succ c =>
        exfalso
        have : (2:Nat) ^ (c + 1) = 2 * 2 ^ c := by
          rw [Nat.pow_succ]; omega
        rw [this, Nat.mul_assoc] at hE
        simp at hE
        omega
    | succ a ih =>
      intro b u v hu hv hE
      cases b with
      | zero =>
        exfalso
        have : (2:Nat) ^ (a + 1) = 2 * 2 ^ a := by rw [Nat.pow_succ]; omega
        rw [this, Nat.mul_assoc] at hE
        simp at hE
        omega
      | succ b =>
        have ha : (2:Nat) ^ (a + 1) = 2 * 2 ^ a := by rw [Nat.pow_succ]; omega
        have hb : (2:Nat) ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ]; omega
        rw [ha, hb, Nat.mul_assoc, Nat.mul_assoc] at hE
        have hE' : 2 ^ a * u = 2 ^ b * v := by omega
        have := ih b u v hu hv hE'
        omega
  exact key r r' m m' hm hm' (by omega)


/-! ## 2.  The valuation is exactly a congruence modulo `2^(r+1)` -/

/-- `2^(r+1) = 2 * 2^r`, in the orientation used below. -/
theorem two_pow_succ' (r : Nat) : (2 : Nat) ^ (r + 1) = 2 * 2 ^ r := by
  rw [Nat.pow_succ]; omega

/-- **The valuation is a congruence condition.**  For odd `n`,
`v₂(3n+1) = r` holds **iff** `3n+1 ≡ 2^r (mod 2^(r+1))`.  Since `n ↦ 3n+1`
is injective on residues mod `2^(r+1)`, this is exactly one condition on
`n % 2^(r+1)`. -/
theorem val_iff_mod {n : Nat} (hn : n % 2 = 1) (r : Nat) :
    (∃ m : Nat, SyrStep n r m) ↔ (3 * n + 1) % 2 ^ (r + 1) = 2 ^ r := by
  constructor
  · rintro ⟨m, _, hm, he⟩
    have hq : m = 2 * (m / 2) + 1 := by omega
    have hsplit : 3 * n + 1 = 2 ^ (r + 1) * (m / 2) + 2 ^ r := by
      rw [he, two_pow_succ']
      calc 2 ^ r * m = 2 ^ r * (2 * (m / 2) + 1) := by rw [← hq]
        _ = 2 * 2 ^ r * (m / 2) + 2 ^ r := by
            rw [Nat.mul_add, Nat.mul_one]
            have : 2 ^ r * (2 * (m / 2)) = 2 * 2 ^ r * (m / 2) := by
              rw [Nat.mul_left_comm, Nat.mul_assoc]
            omega
    rw [hsplit, Nat.mul_add_mod]
    have hlt : (2 : Nat) ^ r < 2 ^ (r + 1) := by
      rw [two_pow_succ']
      have := Nat.two_pow_pos r
      omega
    exact Nat.mod_eq_of_lt hlt
  · intro hmod
    refine ⟨2 * ((3 * n + 1) / 2 ^ (r + 1)) + 1, hn, by omega, ?_⟩
    have hd := Nat.mod_add_div (3 * n + 1) (2 ^ (r + 1))
    rw [hmod] at hd
    have hexp : 2 ^ r * (2 * ((3 * n + 1) / 2 ^ (r + 1)) + 1)
        = 2 ^ (r + 1) * ((3 * n + 1) / 2 ^ (r + 1)) + 2 ^ r := by
      rw [Nat.mul_add, Nat.mul_one, two_pow_succ', Nat.mul_left_comm, Nat.mul_assoc]
    omega

/-- **The valuation is read off `n % 2^(r+1)` alone.**  Two inputs congruent
mod `2^(r+1)` have the same answer to "is `v₂(3n+1) = r`?". -/
theorem val_mod_determined {n n' r : Nat} (hn : n % 2 = 1) (hn' : n' % 2 = 1)
    (hcong : n % 2 ^ (r + 1) = n' % 2 ^ (r + 1)) :
    ((∃ m : Nat, SyrStep n r m) ↔ (∃ m : Nat, SyrStep n' r m)) := by
  have hkey : (3 * n + 1) % 2 ^ (r + 1) = (3 * n' + 1) % 2 ^ (r + 1) := by
    rw [Nat.add_mod, Nat.mul_mod, hcong, ← Nat.mul_mod, ← Nat.add_mod]
  rw [val_iff_mod hn r, val_iff_mod hn' r, hkey]

/-- **Hensel lifting for the odd multiplier `3`.**  For every `k` there is an
`a` with `2^k ∣ 3a+1`.  The whole induction is "`c` odd forces `c+3` even",
i.e. it uses nothing about `3` except that it is odd. -/
theorem three_inv_exists : ∀ k : Nat, ∃ a : Nat, ∃ c : Nat, 3 * a + 1 = 2 ^ k * c := by
  intro k
  induction k with
  | zero => exact ⟨0, 1, by simp⟩
  | succ k ih =>
    obtain ⟨a, c, hac⟩ := ih
    by_cases hc : c % 2 = 0
    · exact ⟨a, c / 2, by rw [two_pow_succ']; rw [hac]
                          have : c = 2 * (c / 2) := by omega
                          calc 2 ^ k * c = 2 ^ k * (2 * (c / 2)) := by rw [← this]
                            _ = 2 * 2 ^ k * (c / 2) := by rw [Nat.mul_left_comm, Nat.mul_assoc]⟩
    · refine ⟨a + 2 ^ k, (c + 3) / 2, ?_⟩
      have hstep : 3 * (a + 2 ^ k) + 1 = 2 ^ k * (c + 3) := by
        rw [Nat.mul_add, Nat.mul_add]
        omega
      rw [hstep, two_pow_succ']
      have hhalf : c + 3 = 2 * ((c + 3) / 2) := by omega
      calc 2 ^ k * (c + 3) = 2 ^ k * (2 * ((c + 3) / 2)) := by rw [← hhalf]
        _ = 2 * 2 ^ k * ((c + 3) / 2) := by rw [Nat.mul_left_comm, Nat.mul_assoc]

/-- **Uniqueness of the valuation class.**  At most one residue class mod
`2^(r+1)` of odd numbers has `v₂(3n+1) = r`: the condition pins `n` mod
`2^(r+1)` completely, because `3` is invertible there. -/
theorem val_class_unique {n n' r m m' : Nat}
    (h : SyrStep n r m) (h' : SyrStep n' r m')
    (hlt : n < 2 ^ (r + 1)) (hlt' : n' < 2 ^ (r + 1)) : n = n' := by
  obtain ⟨hn, hm, he⟩ := h
  obtain ⟨hn', hm', he'⟩ := h'
  have hA : (3 * n + 1) % 2 ^ (r + 1) = 2 ^ r :=
    (val_iff_mod hn r).mp ⟨m, hn, hm, he⟩
  have hB : (3 * n' + 1) % 2 ^ (r + 1) = 2 ^ r :=
    (val_iff_mod hn' r).mp ⟨m', hn', hm', he'⟩
  have hdA := Nat.mod_add_div (3 * n + 1) (2 ^ (r + 1))
  have hdB := Nat.mod_add_div (3 * n' + 1) (2 ^ (r + 1))
  rw [hA] at hdA
  rw [hB] at hdB
  have key : ∀ a b : Nat, a < b → b < 2 ^ (r + 1) →
      2 ^ r + 2 ^ (r + 1) * ((3 * a + 1) / 2 ^ (r + 1)) = 3 * a + 1 →
      2 ^ r + 2 ^ (r + 1) * ((3 * b + 1) / 2 ^ (r + 1)) = 3 * b + 1 → False := by
    intro a b hab hb ha1 hb1
    have hpow : 0 < (2 : Nat) ^ (r + 1) := Nat.two_pow_pos _
    have hq : (3 * a + 1) / 2 ^ (r + 1) ≤ (3 * b + 1) / 2 ^ (r + 1) := by
      rcases Nat.lt_or_ge ((3 * b + 1) / 2 ^ (r + 1)) ((3 * a + 1) / 2 ^ (r + 1)) with hh | hh
      · exfalso
        have := (Nat.mul_lt_mul_left hpow).mpr hh
        omega
      · exact hh
    have hsub := Nat.mul_sub (2 ^ (r + 1)) ((3 * b + 1) / 2 ^ (r + 1)) ((3 * a + 1) / 2 ^ (r + 1))
    have hdvd : (2 : Nat) ^ (r + 1) ∣ 3 * (b - a) :=
      ⟨(3 * b + 1) / 2 ^ (r + 1) - (3 * a + 1) / 2 ^ (r + 1), by omega⟩
    obtain ⟨c, hc⟩ := OddRuns.dvd_of_three_mul (r + 1) (b - a) hdvd
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with hz | hz
      · exfalso; rw [hz] at hc; omega
      · exact hz
    have hge : (2 : Nat) ^ (r + 1) ≤ b - a := by
      have h1 : (2 : Nat) ^ (r + 1) * 1 ≤ 2 ^ (r + 1) * c := Nat.mul_le_mul_left _ hcpos
      omega
    omega
  rcases Nat.lt_trichotomy n n' with hh | hh | hh
  · exact absurd (key n n' hh hlt' hdA hdB) (fun x => x)
  · exact hh
  · exact absurd (key n' n hh hlt hdB hdA) (fun x => x)


/-! ## 3.  Runs: the valuation word and the exact two-sided affine law -/

/-- A run of Syracuse steps, recorded by its **valuation word** `rs`. -/
inductive SyrPath : Nat → List Nat → Nat → Prop where
  | nil (n : Nat) : SyrPath n [] n
  | cons {n r m e : Nat} {rs : List Nat} : SyrStep n r m → SyrPath m rs e → SyrPath n (r :: rs) e

/-- The valuation sum `S = Σ rᵢ` of a word: the total number of halvings. -/
def valSum : List Nat → Nat
  | [] => 0
  | r :: rs => r + valSum rs

@[simp] theorem valSum_nil : valSum [] = 0 := rfl

@[simp] theorem valSum_cons (r : Nat) (rs : List Nat) :
    valSum (r :: rs) = r + valSum rs := rfl

/-- **Length ≤ sum.**  Every letter of a realizable valuation word is `≥ 1`, so
the halving count is at least the step count.  Equality holds exactly when the
word is all ones — the `expStep` regime. -/
theorem path_len_le_sum {n e : Nat} {rs : List Nat} (h : SyrPath n rs e) : rs.length ≤ valSum rs := by
  induction h with
  | nil => simp
  | cons hstep _ ih =>
    have := hstep.one_le
    simp only [valSum_cons, List.length_cons]
    omega

/-- The endpoint of a run from an odd start is odd. -/
theorem path_odd {n e : Nat} {rs : List Nat} (hn : n % 2 = 1) (h : SyrPath n rs e) : e % 2 = 1 := by
  induction h with
  | nil => exact hn
  | cons hstep _ ih => exact ih hstep.2.1

/-- Pure arithmetic core of the accumulator bound. -/
theorem bound_step {A C P Q b1 : Nat}
    (hIH : A * b1 + Q * A ≤ Q * C) (hPQ : 2 * A ≤ P * Q) :
    2 * A * (C + P * b1) + P * Q * (2 * A) ≤ P * Q * (3 * C) := by
  have h2 : 2 * P * (A * b1 + Q * A) ≤ 2 * P * (Q * C) := Nat.mul_le_mul_left _ hIH
  have h3 : 2 * A * C ≤ P * Q * C := Nat.mul_le_mul_right C hPQ
  have e2 : 2 * P * (A * b1 + Q * A) = 2 * (P * (A * b1)) + 2 * (P * (Q * A)) := by
    simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have e3 : 2 * P * (Q * C) = 2 * (P * (Q * C)) := by simp [Nat.mul_assoc]
  have e1 : 2 * A * (C + P * b1) + P * Q * (2 * A)
      = 2 * A * C + (2 * (P * (A * b1)) + 2 * (P * (Q * A))) := by
    simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  have e4 : P * Q * (3 * C) = P * Q * C + 2 * (P * (Q * C)) := by
    have h : (3 : Nat) * C = C + 2 * C := by omega
    rw [h, Nat.mul_add]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [e1, e4]
  rw [e2, e3] at h2
  omega

/-- **The exact two-sided affine law of a run.**

With `L = |rs|` the number of Syracuse steps and `S = valSum rs` the number of
halvings, a run `n → e` satisfies `2^S · e = 3^L · n + b` with

* `b > 0` whenever `L > 0` (the *lower* bound `3^L · n < 2^S · e`), and
* `2^L · b + 2^S · 2^L ≤ 2^S · 3^L`, i.e. `b ≤ 2^(S−L)(3^L − 2^L)` (the *upper*
  bound).

Both are sharp: the all-ones word attains the upper bound. -/
theorem path_affine {n e : Nat} {rs : List Nat} (h : SyrPath n rs e) :
    ∃ b : Nat, 2 ^ valSum rs * e = 3 ^ rs.length * n + b
      ∧ 2 ^ rs.length * b + 2 ^ valSum rs * 2 ^ rs.length ≤ 2 ^ valSum rs * 3 ^ rs.length
      ∧ (0 < rs.length → 0 < b) := by
  induction h with
  | nil n =>
    refine ⟨0, by simp, by simp, by simp⟩
  | @cons n r m e rs hstep hpath ih =>
    obtain ⟨b1, heq, hbd, _⟩ := ih
    obtain ⟨hn, hm, hs⟩ := hstep
    have hr : 1 ≤ r := SyrStep.one_le ⟨hn, hm, hs⟩
    have hls : rs.length ≤ valSum rs := path_len_le_sum hpath
    refine ⟨3 ^ rs.length + 2 ^ r * b1, ?_, ?_, ?_⟩
    · have hL : (3 : Nat) ^ (rs.length + 1) = 3 * 3 ^ rs.length := by
        rw [Nat.pow_succ]; omega
      simp only [valSum_cons, List.length_cons]
      calc 2 ^ (r + valSum rs) * e = 2 ^ r * (2 ^ valSum rs * e) := by
            rw [Nat.pow_add, Nat.mul_assoc]
        _ = 2 ^ r * (3 ^ rs.length * m + b1) := by rw [heq]
        _ = 3 ^ rs.length * (2 ^ r * m) + 2 ^ r * b1 := by
            rw [Nat.mul_add, Nat.mul_left_comm]
        _ = 3 ^ rs.length * (3 * n + 1) + 2 ^ r * b1 := by rw [← hs]
        _ = 3 ^ (rs.length + 1) * n + (3 ^ rs.length + 2 ^ r * b1) := by
            rw [hL]
            simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
            omega
    · have g1 : (2 : Nat) ^ (rs.length + 1) = 2 * 2 ^ rs.length := by rw [Nat.pow_succ]; omega
      have g2 : (3 : Nat) ^ (rs.length + 1) = 3 * 3 ^ rs.length := by rw [Nat.pow_succ]; omega
      have g3 : (2 : Nat) ^ (r + valSum rs) = 2 ^ r * 2 ^ valSum rs := Nat.pow_add 2 r _
      have hPQ : 2 * 2 ^ rs.length ≤ 2 ^ r * 2 ^ valSum rs := by
        rw [← g3, ← g1]
        exact Nat.pow_le_pow_right (by omega) (by omega)
      simp only [valSum_cons, List.length_cons]
      rw [g1, g2, g3]
      exact bound_step hbd hPQ
    · intro _
      have : 0 < (3 : Nat) ^ rs.length := Nat.pow_pos (by omega)
      omega

/-- **Lower bound**: a nonempty run strictly beats the pure affine bound. -/
theorem path_lower {n e : Nat} {rs : List Nat} (h : SyrPath n rs e) (hne : 0 < rs.length) :
    3 ^ rs.length * n < 2 ^ valSum rs * e := by
  obtain ⟨b, heq, _, hpos⟩ := path_affine h
  have := hpos hne
  omega

/-! ## 4.  The drop certificate and its necessary condition -/

/-- **Necessity.**  A run can only end below its start if the halving count
strictly beats `log₂ 3` times the step count: `3^L < 2^S`.  This is the
*exact* form of "divergence forces `Σ rᵢ` below the critical threshold". -/
theorem drop_necessary {n e : Nat} {rs : List Nat} (h : SyrPath n rs e) (hn : 0 < n)
    (hne : 0 < rs.length) (hdrop : e < n) :
    3 ^ rs.length < 2 ^ valSum rs := by
  have hlow := path_lower h hne
  have hmono : 2 ^ valSum rs * e ≤ 2 ^ valSum rs * n := by
    exact Nat.mul_le_mul_left _ (by omega)
  have hlt : 3 ^ rs.length * n < 2 ^ valSum rs * n := by omega
  rcases Nat.lt_or_ge (3 ^ rs.length) (2 ^ valSum rs) with hh | hh
  · exact hh
  · exfalso
    have : 2 ^ valSum rs * n ≤ 3 ^ rs.length * n := Nat.mul_le_mul_right n hh
    omega

/-- **The drop certificate.**  If the word's exact budget inequality holds at
`n`, the run drops.  No estimate, no measurement: the hypothesis is a finite
inequality between integers determined by `n` and the valuation word. -/
theorem drop_of_certificate {n e : Nat} {rs : List Nat} (h : SyrPath n rs e)
    (hcert : 2 ^ rs.length * 3 ^ rs.length * n + 2 ^ valSum rs * 3 ^ rs.length
              < 2 ^ rs.length * 2 ^ valSum rs * n + 2 ^ valSum rs * 2 ^ rs.length) :
    e < n := by
  obtain ⟨b, heq, hbd, _⟩ := path_affine h
  have hkey : 2 ^ rs.length * 2 ^ valSum rs * e
      = 2 ^ rs.length * 3 ^ rs.length * n + 2 ^ rs.length * b := by
    calc 2 ^ rs.length * 2 ^ valSum rs * e = 2 ^ rs.length * (2 ^ valSum rs * e) := by
          rw [Nat.mul_assoc]
      _ = 2 ^ rs.length * (3 ^ rs.length * n + b) := by rw [heq]
      _ = 2 ^ rs.length * 3 ^ rs.length * n + 2 ^ rs.length * b := by
          rw [Nat.mul_add, Nat.mul_assoc]
  have hswap : 2 ^ rs.length * 2 ^ valSum rs * n = 2 ^ rs.length * (2 ^ valSum rs * n) := by
    rw [Nat.mul_assoc]
  have hswape : 2 ^ rs.length * 2 ^ valSum rs * e = 2 ^ rs.length * (2 ^ valSum rs * e) := by
    rw [Nat.mul_assoc]
  have hfin : 2 ^ rs.length * (2 ^ valSum rs * e) < 2 ^ rs.length * (2 ^ valSum rs * n) := by
    omega
  have h1 : 2 ^ valSum rs * e < 2 ^ valSum rs * n := Nat.lt_of_mul_lt_mul_left hfin
  exact Nat.lt_of_mul_lt_mul_left h1


/-! ## 5.  The criterion sees the even branch: `expStep` fails it -/

/-- **A map whose halving count equals its step count can never drop.**
If `2^j · e = 3^j · x + b` — the affine law with the *saturated* exponent
`S = L = j` — then `e ≥ x`.  No hypothesis about the map is used beyond the
law itself. -/
theorem no_drop_of_unit_valuation {j x e b : Nat} (_hx : 0 < x)
    (h : 2 ^ j * e = 3 ^ j * x + b) : ¬ (e < x) := by
  intro hlt
  have hheavy : (2 : Nat) ^ j ≤ 3 ^ j := Arith.two_pow_le_three_pow j
  have h1 : 2 ^ j * x ≤ 3 ^ j * x := Nat.mul_le_mul_right x hheavy
  have h2 : 2 ^ j * e ≤ 2 ^ j * x := Nat.mul_le_mul_left _ (by omega)
  have h3 : 2 ^ j * e < 2 ^ j * x := by
    rcases Nat.lt_or_ge (2 ^ j * e) (2 ^ j * x) with hh | hh
    · exact hh
    · exfalso
      have := Nat.le_of_eq (Nat.le_antisymm h2 hh)
      have hxe : x ≤ e := Nat.le_of_mul_le_mul_left (by omega) (Nat.two_pow_pos j)
      omega
  omega

/-- **`expStep` fails the drop certificate at every length.**  Its valuation
word is all ones, so `S = L = j`; the necessary condition `3^L < 2^S` reads
`3^j < 2^j`, which is false.  Hence the Round X witness map is *rejected* by
the criterion of this file, and the criterion is therefore not a consequence of
affine law + parity word + heaviness + positivity. -/
theorem expStep_fails_certificate (j x : Nat) (hx : 0 < x) :
    ¬ (ScaleRecord.expOrbit j x < x) := by
  obtain ⟨b, hb⟩ := ScaleRecord.expOrbit_affine j x
  exact no_drop_of_unit_valuation hx hb

/-- **The discriminating package.**  `expStep` satisfies the affine law with
`S = L`; the drop-necessity `3^L < 2^S` is unsatisfiable there; and indeed
`expStep` never drops.  Contrast `letter_realizable` below: the genuine
Syracuse valuation takes **every** value `r ≥ 1`, so `S` is not pinned to `L`. -/
theorem certificate_rejects_expStep :
    (∀ j x : Nat, ∃ b : Nat, 2 ^ j * ScaleRecord.expOrbit j x = 3 ^ j * x + b)
      ∧ (∀ j : Nat, ¬ (3 ^ j < 2 ^ j))
      ∧ (∀ j x : Nat, 0 < x → ¬ (ScaleRecord.expOrbit j x < x)) :=
  ⟨fun j x => ScaleRecord.expOrbit_affine j x,
   fun j hlt => absurd (Arith.two_pow_le_three_pow j) (by omega),
   fun j x hx => expStep_fails_certificate j x hx⟩

/-! ## 6.  Every letter is realizable: the alphabet is all of `{1,2,3,…}` -/

/-- **Every valuation `r ≥ 1` actually occurs.**  Concretely: `2^r ∣ 3a+1` for
some `a` (`three_inv_exists`), and if the cofactor is even the shift
`a ↦ a + 2^r` makes it odd.  So the valuation alphabet of the transition system
is the *whole* of `{1,2,3,…}`, not `{1}`. -/
theorem letter_realizable {r : Nat} (hr : 1 ≤ r) : ∃ n m : Nat, SyrStep n r m := by
  obtain ⟨k, rfl⟩ : ∃ k : Nat, r = k + 1 := ⟨r - 1, by omega⟩
  obtain ⟨a, c, hac⟩ := three_inv_exists (k + 1)
  have hsplit : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := two_pow_succ' k
  by_cases hc : c % 2 = 1
  · refine ⟨a, c, ?_, hc, hac⟩
    have h2 : 3 * a + 1 = 2 * (2 ^ k * c) := by
      rw [hac, hsplit, Nat.mul_assoc]
    omega
  · refine ⟨a + 2 ^ (k + 1), c + 3, ?_, by omega, ?_⟩
    · have h2 : 3 * (a + 2 ^ (k + 1)) + 1 = 2 * (2 ^ k * (c + 3)) := by
        rw [Nat.mul_add, Nat.mul_add]
        have e1 : 2 * (2 ^ k * c) = 2 ^ (k + 1) * c := by rw [hsplit, Nat.mul_assoc]
        have e2 : 2 * (2 ^ k * 3) = 2 ^ (k + 1) * 3 := by rw [hsplit, Nat.mul_assoc]
        omega
      omega
    · rw [Nat.mul_add, Nat.mul_add]
      omega

/-- Valuation `2` occurs: `3·1+1 = 4`. -/
theorem letter_two : SyrStep 1 2 1 := ⟨rfl, rfl, rfl⟩

/-- Valuation `1` occurs: `3·3+1 = 2·5`. -/
theorem letter_one : SyrStep 3 1 5 := ⟨rfl, rfl, rfl⟩


/-! ## 7.  Terras determinacy in valuation form: the word is a function of
`n mod 2^(S+1)` -/

/-- `2 ∣ 2^t` for `t ≥ 1`. -/
theorem two_dvd_two_pow {t : Nat} (ht : 1 ≤ t) : (2 : Nat) ∣ 2 ^ t := by
  obtain ⟨j, rfl⟩ : ∃ j : Nat, t = j + 1 := ⟨t - 1, by omega⟩
  exact ⟨2 ^ j, two_pow_succ' j⟩

/-- Oddness is decided by any congruence modulo `2^t` with `t ≥ 1`. -/
theorem odd_of_congr {a b t : Nat} (ht : 1 ≤ t) (h : a % 2 ^ t = b % 2 ^ t)
    (hb : b % 2 = 1) : a % 2 = 1 := by
  have hd := two_dvd_two_pow ht
  have h1 : a % 2 ^ t % 2 = a % 2 := Nat.mod_mod_of_dvd a hd
  have h2 : b % 2 ^ t % 2 = b % 2 := Nat.mod_mod_of_dvd b hd
  omega

/-- **Dividing a congruence by `2^r`.**  If `A ≡ B (mod 2^(r+M))` and
`B = 2^r · mm`, then `A = 2^r · mm'` with `mm' ≡ mm (mod 2^M)`. -/
theorem divide_congr (r M A B mm : Nat)
    (hA : A % 2 ^ (r + M) = B % 2 ^ (r + M)) (hB : B = 2 ^ r * mm) :
    ∃ mm' : Nat, A = 2 ^ r * mm' ∧ mm' % 2 ^ M = mm % 2 ^ M := by
  have hP : 0 < (2 : Nat) ^ r := Nat.two_pow_pos r
  have hsplit : (2 : Nat) ^ (r + M) = 2 ^ r * 2 ^ M := Nat.pow_add 2 r M
  have hdA := Nat.mod_add_div A (2 ^ (r + M))
  have hdB := Nat.mod_add_div B (2 ^ (r + M))
  have hq : 2 ^ r * (2 ^ M * (B / 2 ^ (r + M))) = 2 ^ (r + M) * (B / 2 ^ (r + M)) := by
    rw [hsplit, Nat.mul_assoc]
  have hle : 2 ^ r * (2 ^ M * (B / 2 ^ (r + M))) ≤ 2 ^ r * mm := by omega
  have hge : 2 ^ M * (B / 2 ^ (r + M)) ≤ mm := Nat.le_of_mul_le_mul_left hle hP
  have hu : 2 ^ r * (mm - 2 ^ M * (B / 2 ^ (r + M)))
      = 2 ^ r * mm - 2 ^ r * (2 ^ M * (B / 2 ^ (r + M))) := Nat.mul_sub _ _ _
  refine ⟨2 ^ M * (A / 2 ^ (r + M)) + (mm - 2 ^ M * (B / 2 ^ (r + M))), ?_, ?_⟩
  · have hd : 2 ^ r * (2 ^ M * (A / 2 ^ (r + M))) = 2 ^ (r + M) * (A / 2 ^ (r + M)) := by
      rw [hsplit, Nat.mul_assoc]
    have hexp : 2 ^ r * (2 ^ M * (A / 2 ^ (r + M)) + (mm - 2 ^ M * (B / 2 ^ (r + M))))
        = 2 ^ r * (2 ^ M * (A / 2 ^ (r + M))) + 2 ^ r * (mm - 2 ^ M * (B / 2 ^ (r + M))) :=
      Nat.mul_add _ _ _
    omega
  · have h1 : (2 ^ M * (A / 2 ^ (r + M)) + (mm - 2 ^ M * (B / 2 ^ (r + M)))) % 2 ^ M
        = (mm - 2 ^ M * (B / 2 ^ (r + M))) % 2 ^ M := Nat.mul_add_mod _ _ _
    have h2 : mm = 2 ^ M * (B / 2 ^ (r + M)) + (mm - 2 ^ M * (B / 2 ^ (r + M))) := by omega
    have h3 : mm % 2 ^ M = (mm - 2 ^ M * (B / 2 ^ (r + M))) % 2 ^ M := by
      conv => lhs; rw [h2]
      exact Nat.mul_add_mod _ _ _
    omega

/-- **The valuation word of a run is a function of `n mod 2^(S+k+1)`, and it
carries the endpoint mod `2^(k+1)` along with it.**

This is Terras' bijection restated in the valuation alphabet: knowing `n` to
`S + k + 1` binary places determines the *entire* valuation word of total mass
`S` **and** the endpoint to `k + 1` places.  Combined with `letter_realizable`
it says the transition system has **no forbidden transitions**: no property of a
finite valuation word constrains the next letter. -/
theorem path_congr {n e : Nat} {rs : List Nat} (h : SyrPath n rs e) :
    ∀ (k n' : Nat), n' % 2 ^ (valSum rs + (k + 1)) = n % 2 ^ (valSum rs + (k + 1)) →
      ∃ e' : Nat, SyrPath n' rs e' ∧ e' % 2 ^ (k + 1) = e % 2 ^ (k + 1) := by
  induction h with
  | nil n =>
    intro k n' hcong
    refine ⟨n', SyrPath.nil n', ?_⟩
    simpa using hcong
  | @cons n r m e rs hstep hpath ih =>
    intro k n' hcong
    obtain ⟨hn, hm, hs⟩ := hstep
    have hr : 1 ≤ r := SyrStep.one_le ⟨hn, hm, hs⟩
    have hassoc : valSum (r :: rs) + (k + 1) = r + (valSum rs + (k + 1)) := by
      simp only [valSum_cons]; omega
    rw [hassoc] at hcong
    have hMpos : 1 ≤ valSum rs + (k + 1) := by omega
    have hRM : 1 ≤ r + (valSum rs + (k + 1)) := by omega
    have hn' : n' % 2 = 1 := odd_of_congr hRM hcong hn
    have hstepcong : (3 * n' + 1) % 2 ^ (r + (valSum rs + (k + 1)))
        = (3 * n + 1) % 2 ^ (r + (valSum rs + (k + 1))) := by
      rw [Nat.add_mod, Nat.mul_mod, hcong, ← Nat.mul_mod, ← Nat.add_mod]
    obtain ⟨m', hm'eq, hm'cong⟩ :=
      divide_congr r (valSum rs + (k + 1)) (3 * n' + 1) (3 * n + 1) m hstepcong hs
    have hm'odd : m' % 2 = 1 := odd_of_congr hMpos hm'cong hm
    obtain ⟨e', hpath', hecong⟩ := ih k m' hm'cong
    exact ⟨e', SyrPath.cons ⟨hn', hm'odd, hm'eq⟩ hpath', hecong⟩

/-- **Corollary (the class of a word is a full residue class).**  If `n`
realizes the valuation word `rs` and `n' ≡ n (mod 2^(S+1))`, then `n'` realizes
the same word.  Hence realizability of a word is *exactly* a congruence
condition modulo `2^(S+1)`. -/
theorem word_class {n e : Nat} {rs : List Nat} (h : SyrPath n rs e)
    {n' : Nat} (hcong : n' % 2 ^ (valSum rs + 1) = n % 2 ^ (valSum rs + 1)) :
    ∃ e' : Nat, SyrPath n' rs e' := by
  have hz : valSum rs + 1 = valSum rs + (0 + 1) := by omega
  rw [hz] at hcong
  obtain ⟨e', hp, _⟩ := path_congr h 0 n' hcong
  exact ⟨e', hp⟩



/-! ## 8.  The free-shift theorem: **every** valuation word is realized by an
integer -/

/-- An explicit inverse of `3` modulo `2^k`: `3u = 2^k·c + 1`.  Hensel again,
using only that `3` is odd. -/
theorem three_unit_exists : ∀ k : Nat, ∃ u c : Nat, 3 * u = 2 ^ k * c + 1 := by
  intro k
  induction k with
  | zero => exact ⟨1, 2, by simp⟩
  | succ k ih =>
    obtain ⟨u, c, huc⟩ := ih
    have hsplit : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := two_pow_succ' k
    by_cases hc : c % 2 = 0
    · refine ⟨u, c / 2, ?_⟩
      have h : 2 ^ (k + 1) * (c / 2) = 2 ^ k * (2 * (c / 2)) := by
        rw [hsplit]; simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have h2 : c = 2 * (c / 2) := by omega
      rw [h, ← h2]; exact huc
    · refine ⟨u + 2 ^ k, (c + 3) / 2, ?_⟩
      have h : 2 ^ (k + 1) * ((c + 3) / 2) = 2 ^ k * (2 * ((c + 3) / 2)) := by
        rw [hsplit]; simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have h2 : c + 3 = 2 * ((c + 3) / 2) := by omega
      rw [h, ← h2, Nat.mul_add, Nat.mul_add]
      omega

/-- `3·(X·2P) = P·6X`, done by hand because numeral folding under AC is not
available here. -/
theorem mul_six_pow (X P : Nat) : 3 * (X * (2 * P)) = P * (6 * X) := by
  have a : X * (2 * P) = 2 * (X * P) := Nat.mul_left_comm _ _ _
  have b : P * (6 * X) = 6 * (P * X) := Nat.mul_left_comm _ _ _
  have c : P * X = X * P := Nat.mul_comm P X
  rw [a, b, c]
  omega

/-- **The predecessor can be steered onto any odd target class.**

Given one step `n₀ → m₀` with valuation `r`, and any odd `m₁ ≥ m₀`, there is a
step with the *same* valuation `r` whose target is congruent to `m₁` modulo
`2^(T+1)`, for **every** `T`.  The shift is explicit: slide `n₀` by
`(u·d)·2^(r+1)` where `3u ≡ 1 (mod 2^T)` and `2d = m₁ − m₀`; this moves the
target by `6ud ≡ m₁ − m₀ (mod 2^(T+1))`.

This is the exact reason the transition system is unconstrained: the map
`t ↦ m₀ + 6t` covers every odd class because `gcd(6, 2^(T+1)) = 2`. -/
theorem back_step {r n₀ m₀ m₁ : Nat} (hstep : SyrStep n₀ r m₀)
    (hm₁ : m₁ % 2 = 1) (hle : m₀ ≤ m₁) (T : Nat) :
    ∃ n m : Nat, SyrStep n r m ∧ m % 2 ^ (T + 1) = m₁ % 2 ^ (T + 1) := by
  obtain ⟨hn₀, hm₀, he₀⟩ := hstep
  have hr : 1 ≤ r := SyrStep.one_le ⟨hn₀, hm₀, he₀⟩
  obtain ⟨u, c, huc⟩ := three_unit_exists T
  have hd2 : m₁ - m₀ = 2 * ((m₁ - m₀) / 2) := by omega
  have h1 : (2 : Nat) ^ (r + 1) = 2 * 2 ^ r := two_pow_succ' r
  refine ⟨n₀ + (u * ((m₁ - m₀) / 2)) * 2 ^ (r + 1),
          m₀ + 6 * (u * ((m₁ - m₀) / 2)), ⟨?_, ?_, ?_⟩, ?_⟩
  · have hev : (u * ((m₁ - m₀) / 2)) * 2 ^ (r + 1)
        = 2 * ((u * ((m₁ - m₀) / 2)) * 2 ^ r) := by
      rw [h1]; simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  · omega
  · have hmul : 3 * ((u * ((m₁ - m₀) / 2)) * (2 * 2 ^ r))
        = 2 ^ r * (6 * (u * ((m₁ - m₀) / 2))) :=
      mul_six_pow (u * ((m₁ - m₀) / 2)) (2 ^ r)
    have hexp : 3 * (n₀ + (u * ((m₁ - m₀) / 2)) * 2 ^ (r + 1)) + 1
        = (3 * n₀ + 1) + 3 * ((u * ((m₁ - m₀) / 2)) * (2 * 2 ^ r)) := by
      rw [h1, Nat.mul_add]; omega
    rw [hexp, hmul, he₀, ← Nat.mul_add]
  · have hkey : 6 * (u * ((m₁ - m₀) / 2))
        = 2 * (2 ^ T * (c * ((m₁ - m₀) / 2))) + 2 * ((m₁ - m₀) / 2) := by
      have ha : 3 * u * ((m₁ - m₀) / 2) = (2 ^ T * c + 1) * ((m₁ - m₀) / 2) := by rw [huc]
      have hb : (2 ^ T * c + 1) * ((m₁ - m₀) / 2)
          = 2 ^ T * c * ((m₁ - m₀) / 2) + ((m₁ - m₀) / 2) := by
        rw [Nat.add_mul, Nat.one_mul]
      have hc2 : 2 ^ T * c * ((m₁ - m₀) / 2) = 2 ^ T * (c * ((m₁ - m₀) / 2)) :=
        Nat.mul_assoc _ _ _
      have hd : 3 * u * ((m₁ - m₀) / 2) = 3 * (u * ((m₁ - m₀) / 2)) := Nat.mul_assoc _ _ _
      omega
    have h9 : (2 : Nat) ^ (T + 1) * (c * ((m₁ - m₀) / 2))
        = 2 * (2 ^ T * (c * ((m₁ - m₀) / 2))) := by
      rw [two_pow_succ' T, Nat.mul_assoc]
    have hid : m₀ + 6 * (u * ((m₁ - m₀) / 2))
        = m₁ + 2 ^ (T + 1) * (c * ((m₁ - m₀) / 2)) := by omega
    rw [hid]
    exact Nat.add_mul_mod_self_left m₁ (2 ^ (T + 1)) (c * ((m₁ - m₀) / 2))

/-- **The free-shift theorem.**  Every finite word `rs` of valuations `≥ 1` is
the valuation word of an actual odd **integer** — not merely of a symbolic path.

**Consequence (the negative half of this round).**  The valuation transition
system is the *full shift* on `{1,2,3,…}`: it has no forbidden transition of any
order.  So no finite automaton on valuations can obstruct anything, and no
infinite valuation pattern is excluded by finite-order realizability.  Any
obstruction to divergence must therefore be archimedean/Diophantine, not
automaton-theoretic — precisely the `2^S` vs `3^L` comparison of
`drop_necessary`. -/
theorem word_realizable : ∀ rs : List Nat, (∀ r ∈ rs, 1 ≤ r) →
    ∃ n e : Nat, n % 2 = 1 ∧ SyrPath n rs e := by
  intro rs
  induction rs with
  | nil => intro _; exact ⟨1, 1, rfl, SyrPath.nil 1⟩
  | cons r rs ih =>
    intro hall
    have hr : 1 ≤ r := hall r (List.mem_cons_self)
    have htail : ∀ q ∈ rs, 1 ≤ q := fun q hq => hall q (List.mem_cons_of_mem r hq)
    obtain ⟨mIH, e, hmIH, hpIH⟩ := ih htail
    obtain ⟨n₀, m₀, hstep₀⟩ := letter_realizable hr
    have hm₀ : m₀ % 2 = 1 := hstep₀.2.1
    have hTge : 2 ≤ (2 : Nat) ^ (valSum rs + 1) := by
      have h : (2 : Nat) ^ 1 ≤ 2 ^ (valSum rs + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      simpa using h
    have hbig : m₀ ≤ mIH + 2 ^ (valSum rs + 1) * m₀ := by
      have h : 1 * m₀ ≤ 2 ^ (valSum rs + 1) * m₀ := Nat.mul_le_mul_right m₀ (by omega)
      omega
    have hm1odd : (mIH + 2 ^ (valSum rs + 1) * m₀) % 2 = 1 := by
      obtain ⟨w, hw⟩ : (2 : Nat) ∣ 2 ^ (valSum rs + 1) * m₀ :=
        Nat.dvd_trans (two_dvd_two_pow (by omega)) ⟨m₀, rfl⟩
      omega
    obtain ⟨n, m, hstep, hmod⟩ := back_step hstep₀ hm1odd hbig (valSum rs)
    have hmod2 : m % 2 ^ (valSum rs + 1) = mIH % 2 ^ (valSum rs + 1) := by
      rw [hmod]
      exact Nat.add_mul_mod_self_left mIH (2 ^ (valSum rs + 1)) m₀
    obtain ⟨e', hp'⟩ := word_class hpIH hmod2
    exact ⟨n, e', hstep.1, SyrPath.cons hstep hp'⟩


/-! ## 9.  The halving surplus, and a real theorem on an explicitly
characterized class -/

/-- **Section 9 without any probability.**  If a run of length `L` with halving
sum `S` does **not** drop, the exact accumulator bound forces
`(2^S − 3^L)·n ≤ 2^(S−L)·(3^L − 2^L)`.  Written without `Nat` subtraction:
`2^L·2^S·n + 2^S·2^L ≤ 2^L·3^L·n + 2^S·3^L`.

So a non-dropping start is *bounded* as soon as the halving sum has any surplus
over `L·log₂3`.  This is the deterministic replacement for "divergence forces
`Σ rᵢ` below the critical threshold": no independence assumption is used. -/
theorem no_drop_bounds {n e : Nat} {rs : List Nat} (h : SyrPath n rs e) (hnodrop : n ≤ e) :
    2 ^ rs.length * 2 ^ valSum rs * n + 2 ^ valSum rs * 2 ^ rs.length
      ≤ 2 ^ rs.length * 3 ^ rs.length * n + 2 ^ valSum rs * 3 ^ rs.length := by
  obtain ⟨b, heq, hbd, _⟩ := path_affine h
  have hmono : 2 ^ rs.length * (2 ^ valSum rs * n) ≤ 2 ^ rs.length * (2 ^ valSum rs * e) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hnodrop)
  have hkey : 2 ^ rs.length * (2 ^ valSum rs * e)
      = 2 ^ rs.length * 3 ^ rs.length * n + 2 ^ rs.length * b := by
    rw [heq, Nat.mul_add, Nat.mul_assoc]
  have hassoc : 2 ^ rs.length * 2 ^ valSum rs * n = 2 ^ rs.length * (2 ^ valSum rs * n) :=
    Nat.mul_assoc _ _ _
  omega

/-- The run `17 → 13 → 5` with valuation word `[2,3]`. -/
theorem path_seventeen : SyrPath 17 [2, 3] 5 :=
  SyrPath.cons (m := 13) ⟨rfl, rfl, rfl⟩ (SyrPath.cons (m := 5) ⟨rfl, rfl, rfl⟩ (SyrPath.nil 5))

/-- Every run with valuation word `[2,3]` from a start `≥ 2` drops.
Here `L = 2`, `S = 5`, and the certificate reads `36n + 288 < 128n + 128`. -/
theorem drop_word_two_three {n e : Nat} (h : SyrPath n [2, 3] e) (hn : 2 ≤ n) : e < n := by
  refine drop_of_certificate h ?_
  have hL : ([2, 3] : List Nat).length = 2 := rfl
  have hS : valSum [2, 3] = 5 := rfl
  rw [hL, hS]
  have e1 : (2 : Nat) ^ 2 * 3 ^ 2 = 36 := by decide
  have e2 : (2 : Nat) ^ 5 * 3 ^ 2 = 288 := by decide
  have e3 : (2 : Nat) ^ 2 * 2 ^ 5 = 128 := by decide
  rw [e1, e2, e3]
  omega

/-- **A genuine theorem of the restricted-class form.**  Every `n ≡ 17
(mod 64)` with `n ≥ 2` drops within two Syracuse steps.

The class is *explicitly characterized* — it is the residue class realizing the
valuation word `[2,3]`, and `64 = 2^(5+1) = 2^(S+1)` is exactly the modulus the
word determines (`word_class`).  This is the shape the brief asks for: not the
conjecture, but the conjecture's conclusion on a class named in advance. -/
theorem drop_of_seventeen_mod_64 {n : Nat} (hn : 2 ≤ n) (hc : n % 64 = 17) :
    ∃ e : Nat, SyrPath n [2, 3] e ∧ e < n := by
  have hmod : n % 2 ^ (valSum [2, 3] + 1) = 17 % 2 ^ (valSum [2, 3] + 1) := by
    have h1 : (2 : Nat) ^ (valSum [2, 3] + 1) = 64 := by decide
    rw [h1, hc]
  obtain ⟨e, hp⟩ := word_class path_seventeen hmod
  exact ⟨e, hp, drop_word_two_three hp hn⟩

/-! ## 10.  Summary of the round in one statement -/

/-- **What this file establishes, packaged.**

1. The valuation is exactly a congruence mod `2^(r+1)` and the whole word is a
   function of `n mod 2^(S+1)`.
2. Every valuation word of positive letters is realized by an **integer**
   (full shift — no obstruction of any finite order).
3. A drop forces `3^L < 2^S`, and the exact certificate is sufficient.
4. `expStep`, whose valuation word is all ones (`S = L`), fails 3 at every
   length — so 3 is not a consequence of the Round X inputs. -/
theorem round_XV_summary :
    (∀ (rs : List Nat), (∀ r ∈ rs, 1 ≤ r) → ∃ n e : Nat, n % 2 = 1 ∧ SyrPath n rs e)
      ∧ (∀ (n e : Nat) (rs : List Nat), SyrPath n rs e → 0 < n → 0 < rs.length → e < n →
          3 ^ rs.length < 2 ^ valSum rs)
      ∧ (∀ j x : Nat, 0 < x → ¬ (ScaleRecord.expOrbit j x < x)) :=
  ⟨word_realizable,
   fun _ _ _ h hn hne hd => drop_necessary h hn hne hd,
   fun j x hx => expStep_fails_certificate j x hx⟩

end ValuationTransition
end Collatz

section AxiomAudit
open Collatz.ValuationTransition
#print axioms word_realizable
#print axioms path_congr
#print axioms drop_necessary
#print axioms certificate_rejects_expStep
end AxiomAudit
