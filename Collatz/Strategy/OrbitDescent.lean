import Collatz.Strategy.ThreeObstruction

/-!
# Descending from anywhere on the orbit

`Descent` builds a smaller never-dropper by running the map backwards **from `m`
itself**.  That is unnecessarily restrictive.  If `n` reaches *any* point of the
orbit of `m`, then the orbit of `n` is a finite prefix followed by a tail of the
orbit of `m`, and every such tail is `≥ m`.  So the same conclusion holds
(`neverDrops_of_joins`), and the supply of candidate descents is far larger: one
per orbit point rather than one per number.

## The resulting constraint

Take the least never-dropper `m` and any orbit point `v = T^i(m)`.  If
`v ≡ 2 (mod 3)`, its odd preimage `n = (2v − 1)/3` satisfies `T(n) = v`, so `n`
never drops.  Minimality forces `n ≥ m`, that is

**every orbit point `v ≡ 2 (mod 3)` satisfies `v ≥ (3m + 1)/2`.**

Equivalently the window `[m, (3m+1)/2)` contains no orbit point congruent to
`2` modulo `3`.  Two backward steps give the same statement one level up:

**every `v` with two backward `p`-steps available satisfies `v ≥ (9m + 5)/4`.**

## Sharpness

Both bounds are attained exactly, and by the orbit itself:
`T(m) = (3m+1)/2` and `T²(m) = (9m+5)/4`, because `m ≡ 3 (mod 4)` means the
first two steps are odd (`RunValue.two_step_exact`).  So the constraint is tight
at every level and cannot be improved by this argument — the forbidden window
ends precisely where the orbit's own next point begins.

That is a genuine structural invariant of the minimal counterexample: a
forbidden region, of width proportional to `m`, in a fixed residue class.
-/

namespace Collatz
namespace OrbitDescent

open Reach Congruence NeverDrops Descent

/-! ## The generalised descent principle -/

/-- **Joining the orbit anywhere.**  If `n` reaches some point of the orbit of a
never-dropping `m` in `j` steps, never goes below itself during those `j` steps,
and is at most `m`, then `n` never drops. -/
theorem neverDrops_of_joins {n m i j : Nat} (hm : NeverDrops m)
    (hj : acceleratedOrbit j n = acceleratedOrbit i m)
    (hle : ∀ l : Nat, l < j → n ≤ acceleratedOrbit l n)
    (hnm : n ≤ m) : NeverDrops n := by
  intro t
  rcases Nat.lt_or_ge t j with hlt | hge
  · exact hle t hlt
  · have hsplit : acceleratedOrbit t n = acceleratedOrbit (t - j + i) m := by
      have h1 : acceleratedOrbit t n = acceleratedOrbit (t - j) (acceleratedOrbit j n) := by
        rw [acceleratedOrbit_add]
        congr 1
        omega
      rw [h1, hj, acceleratedOrbit_add]
    rw [hsplit]
    exact Nat.le_trans hnm (hm (t - j + i))

/-- `neverDrops_of_prefix` is the case `i = 0`. -/
theorem neverDrops_of_prefix' {n m j : Nat} (hm : NeverDrops m)
    (hj : acceleratedOrbit j n = m)
    (hle : ∀ l : Nat, l < j → n ≤ acceleratedOrbit l n)
    (hnm : n ≤ m) : NeverDrops n :=
  neverDrops_of_joins (i := 0) hm (by rw [hj, acceleratedOrbit]) hle hnm

/-! ## One backward step from an orbit point -/

/-- **The forbidden window.**  For the least never-dropper, no orbit point that
is `2 (mod 3)` lies below `(3m + 1)/2`. -/
theorem orbit_pred_ge {m i n : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x))
    (h : 3 * n + 1 = 2 * acceleratedOrbit i m) : m ≤ n := by
  rcases Nat.lt_or_ge n m with hlt | hge
  · exfalso
    have hge' : 307200 ≤ m := VerifiedSharp.neverDrops_ge_sharp hgt hnd
    have hv : m ≤ acceleratedOrbit i m := hnd i
    have hnpos : 0 < n := by omega
    have hstep : acceleratedOrbit 1 n = acceleratedOrbit i m := by
      show acceleratedStep n = acceleratedOrbit i m
      exact accStep_pred hnpos h
    have hnd' : NeverDrops n := by
      refine neverDrops_of_joins hnd hstep ?_ (by omega)
      intro l hl
      have hl0 : l = 0 := by omega
      subst hl0
      rw [acceleratedOrbit]
      omega
    exact hmin n hlt ⟨by omega, hnd'⟩
  · exact hge

/-- Restated as the window: an orbit point below `(3m+1)/2` is never `2 (mod 3)`. -/
theorem orbit_not_two_mod_three_below {m i : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x))
    (hsmall : 2 * acceleratedOrbit i m < 3 * m + 1) :
    acceleratedOrbit i m % 3 ≠ 2 := by
  intro h3
  have hv : m ≤ acceleratedOrbit i m := hnd i
  obtain ⟨n, hn⟩ : ∃ n : Nat, 3 * n + 1 = 2 * acceleratedOrbit i m :=
    ⟨(2 * acceleratedOrbit i m - 1) / 3, by omega⟩
  have := orbit_pred_ge hgt hnd hmin hn
  omega

/-! ## Two backward steps -/

/-- **The forbidden window, one level up.**  An orbit point supporting two
backward steps lies at or above `(9m + 5)/4`. -/
theorem orbit_pred_two_ge {m i n₁ n₂ : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x))
    (h1 : 3 * n₁ + 1 = 2 * acceleratedOrbit i m) (h2 : 3 * n₂ + 1 = 2 * n₁) :
    m ≤ n₂ := by
  rcases Nat.lt_or_ge n₂ m with hlt | hge
  · exfalso
    have hge' : 307200 ≤ m := VerifiedSharp.neverDrops_ge_sharp hgt hnd
    have hv : m ≤ acceleratedOrbit i m := hnd i
    have h1pos : 0 < n₁ := by omega
    have h2pos : 0 < n₂ := by omega
    have hs1 : acceleratedOrbit 1 n₂ = n₁ := by
      show acceleratedStep n₂ = n₁
      exact accStep_pred h2pos h2
    have hs2 : acceleratedOrbit 2 n₂ = acceleratedOrbit i m := by
      rw [show acceleratedOrbit 2 n₂ = acceleratedStep (acceleratedOrbit 1 n₂) from
        acceleratedOrbit_succ_step 1 n₂, hs1]
      exact accStep_pred h1pos h1
    have hnd' : NeverDrops n₂ := by
      refine neverDrops_of_joins hnd hs2 ?_ (by omega)
      intro l hl
      match l, hl with
      | 0, _ => rw [acceleratedOrbit]; omega
      | 1, _ => rw [hs1]; omega
    exact hmin n₂ hlt ⟨by omega, hnd'⟩
  · exact hge

/-! ## Sharpness -/

/-- The level-one bound is attained: `T(m) = (3m+1)/2`, since the least
never-dropper is odd. -/
theorem step_eq_bound {m : Nat} (hgt : 1 < m) (hnd : NeverDrops m) :
    2 * acceleratedOrbit 1 m = 3 * m + 1 := by
  have hodd : m % 2 = 1 := odd_of_neverDrops hgt hnd
  show 2 * acceleratedStep m = 3 * m + 1
  rw [acceleratedStep, if_neg (by omega)]
  omega

/-- The level-two bound is attained: `T²(m) = (9m+5)/4`, since the least
never-dropper is `3 (mod 4)` and so opens with two odd steps. -/
theorem two_step_eq_bound {m : Nat} (hgt : 1 < m) (hnd : NeverDrops m) :
    4 * acceleratedOrbit 2 m = 9 * m + 5 := by
  have h := climb_of_neverDrops hgt hnd
  omega

/-- **The window is exactly right.**  The forbidden region for `2 (mod 3)` orbit
points is `[m, T(m))`, and the two-step region is `[m, T²(m))`; both end
precisely at the orbit's own next point, so neither can be widened by this
argument. -/
theorem windows_sharp {m : Nat} (hgt : 1 < m) (hnd : NeverDrops m) :
    2 * acceleratedOrbit 1 m = 3 * m + 1 ∧ 4 * acceleratedOrbit 2 m = 9 * m + 5 :=
  ⟨step_eq_bound hgt hnd, two_step_eq_bound hgt hnd⟩

/-! ## The programme, restated -/

/-- **The full constraint set on the least never-dropper.**  Size, parity,
residues, the descent exclusions, and the two forbidden windows on its orbit. -/
theorem minimal_orbit_profile {m : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x)) :
    307200 ≤ m ∧ m % 4 = 3 ∧ m % 3 ≠ 2 ∧ m % 9 ≠ 4 ∧
    (∀ i : Nat, 2 * acceleratedOrbit i m < 3 * m + 1 →
      acceleratedOrbit i m % 3 ≠ 2) ∧
    (∀ i n₁ n₂ : Nat, 3 * n₁ + 1 = 2 * acceleratedOrbit i m →
      3 * n₂ + 1 = 2 * n₁ → m ≤ n₂) := by
  refine ⟨VerifiedSharp.neverDrops_ge_sharp hgt hnd, mod_four_of_neverDrops hgt hnd,
    minimal_not_two_mod_three hgt hnd hmin, minimal_not_four_mod_nine hgt hnd hmin,
    fun i h => orbit_not_two_mod_three_below hgt hnd hmin h,
    fun i n₁ n₂ h1 h2 => orbit_pred_two_ge hgt hnd hmin h1 h2⟩

end OrbitDescent
end Collatz
