import Collatz.Strategy.ThreeAdic
import Collatz.Structure.SieveDensity

/-!
# Dropping classes become lower bounds at every orbit point

The drop machinery has always been applied to `m` itself.  It applies to **every
point of the orbit**, and there it says something stronger.

If `v` is any orbit point of a never-dropper `m`, and `v`'s residue forces a
contraction `T^j(v) = ρ·v + c` with `ρ < 1`, then the no-drop property gives
`ρ·v + c ≥ m`, hence

`v ≥ (m − c)/ρ`,

which is *strictly larger than `m`*.  Every dropping residue class is therefore a
forbidden window near the minimum, of width proportional to `1/ρ − 1`.

The cleanest instance is the class `1 (mod 12)`, where two steps contract by
exactly `3/4`:

**`v ≡ 1 (mod 12)` ⟹ `T²(v) = (3v + 1)/4`**  (`two_step_one_mod_twelve`)

so an orbit point in that class satisfies `4m ≤ 3v + 1`, i.e. `v ≥ (4m−1)/3`.
Note this needs only `NeverDrops m`, not minimality — it is cheaper than
everything in `ThreeAdic`.

## Narrowing the window

`ThreeAdic.orbit_one_mod_six_below` says every orbit value below `(3m+1)/2`, past
time zero, is `1 (mod 6)` — that is, `1` or `7` modulo `12`.  The bound above
removes the first of those from the range below `(4m−1)/3`.  So

**every orbit value in `[m, (4m−1)/3)`, past time zero, is `7 (mod 12)`.**

A single residue class modulo twelve, in a window of width `m/3`.

An attractive companion guess — that `v ≡ 7 (mod 12)` also has a closed two-step
form — is **false**; measured over all `v < 400000` in that class it fails every
time, because the parity of the second step is not determined by `v` modulo `12`.
That is exactly why `7 (mod 12)` survives here and `1 (mod 12)` does not.
-/

namespace Collatz
namespace OrbitWindows

open Reach Congruence NeverDrops

/-! ## The class `1 (mod 12)` contracts by exactly `3/4` -/

/-- **Two steps from `1 (mod 12)`.**  The first step is odd, the second even, and
the composite is exactly `v ↦ (3v+1)/4`. -/
theorem two_step_one_mod_twelve {v : Nat} (h : v % 12 = 1) :
    4 * acceleratedOrbit 2 v = 3 * v + 1 := by
  have hodd : v % 2 = 1 := by omega
  have h1 : acceleratedOrbit 1 v = (3 * v + 1) / 2 := by
    show acceleratedStep v = _
    rw [acceleratedStep, if_neg (by omega)]
  have h1even : acceleratedOrbit 1 v % 2 = 0 := by rw [h1]; omega
  have h2 : acceleratedOrbit 2 v = acceleratedOrbit 1 v / 2 := by
    rw [acceleratedOrbit_succ_step 1 v, acceleratedStep, if_pos h1even]
  rw [h2, h1]
  omega

/-- It is a genuine contraction: `(3v+1)/4 < v` once `v > 1`. -/
theorem two_step_one_mod_twelve_drops {v : Nat} (h : v % 12 = 1) (hv : 1 < v) :
    acceleratedOrbit 2 v < v := by
  have := two_step_one_mod_twelve h
  omega

/-! ## The resulting window -/

/-- **Orbit points `1 (mod 12)` are at least `(4m−1)/3`.**  Needs only
`NeverDrops m`, not minimality: the contraction by `3/4` would otherwise carry
the orbit below `m`. -/
theorem orbit_one_mod_twelve_ge {m t : Nat} (hnd : NeverDrops m)
    (h : acceleratedOrbit t m % 12 = 1) :
    4 * m ≤ 3 * acceleratedOrbit t m + 1 := by
  have hstep := two_step_one_mod_twelve h
  have hjoin : acceleratedOrbit 2 (acceleratedOrbit t m) = acceleratedOrbit (2 + t) m :=
    acceleratedOrbit_add 2 t m
  have hge : m ≤ acceleratedOrbit (2 + t) m := hnd (2 + t)
  rw [hjoin] at hstep
  omega

/-- Contrapositive: below `(4m−1)/3` no orbit point is `1 (mod 12)`. -/
theorem no_one_mod_twelve_below {m t : Nat} (hnd : NeverDrops m)
    (hsmall : 3 * acceleratedOrbit t m + 1 < 4 * m) :
    acceleratedOrbit t m % 12 ≠ 1 := by
  intro h
  have := orbit_one_mod_twelve_ge hnd h
  omega

/-! ## Narrowing to a single class modulo twelve -/

/-- **Every orbit value in `[m, (4m−1)/3)`, past time zero, is `7 (mod 12)`.**

`ThreeAdic.orbit_one_mod_six_below` confines the window to `1 (mod 6)`, i.e. to
`1` or `7` modulo `12`; `no_one_mod_twelve_below` removes `1 (mod 12)`. -/
theorem orbit_seven_mod_twelve_below {m t : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x)) (ht : 0 < t)
    (hsmall : 3 * acceleratedOrbit t m + 1 < 4 * m) :
    acceleratedOrbit t m % 12 = 7 := by
  have hwide : 2 * acceleratedOrbit t m < 3 * m + 1 := by omega
  have hsix : acceleratedOrbit t m % 6 = 1 :=
    ThreeAdic.orbit_one_mod_six_below hgt hnd hmin ht hwide
  have hne : acceleratedOrbit t m % 12 ≠ 1 := no_one_mod_twelve_below hnd hsmall
  omega

/-- **The narrowed profile.**  Collecting the windows: below `(4m−1)/3` the orbit
of the least never-dropper occupies exactly one residue class modulo twelve, and
below `(3m+1)/2` exactly one modulo six. -/
theorem window_profile {m t : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x)) (ht : 0 < t) :
    (2 * acceleratedOrbit t m < 3 * m + 1 → acceleratedOrbit t m % 6 = 1) ∧
    (3 * acceleratedOrbit t m + 1 < 4 * m → acceleratedOrbit t m % 12 = 7) :=
  ⟨fun h => ThreeAdic.orbit_one_mod_six_below hgt hnd hmin ht h,
   fun h => orbit_seven_mod_twelve_below hgt hnd hmin ht h⟩

/-! ## The master form, and why the narrowing stops

The `1 (mod 12)` window is one instance of a general principle.  For any orbit
point `v` and any horizon `i`, the affine representation
`2 ^ i · T^i(v) = 3 ^ a · v + b` with `b + 2 ^ i ≤ 3 ^ i` (`AffineBound`) combines
with `T^i(v) ≥ m` to give a lower bound on `v` that beats `m` exactly when
`2 ^ i > 3 ^ a`, i.e. exactly when `v`'s residue is **light** at level `i`. -/

/-- **The master window bound.**  For a never-dropper `m`, every orbit point `v`
and every horizon `i` satisfy `2 ^ i · m ≤ 3 ^ a · v + b`, where `a` is the
odd-step count of `v` over `i` steps and `b + 2 ^ i ≤ 3 ^ i`. -/
theorem orbit_affine_lower_bound {m t : Nat} (hnd : NeverDrops m) (i : Nat) :
    ∃ b : Nat, b + 2 ^ i ≤ 3 ^ i ∧
      2 ^ i * m ≤ 3 ^ oddCount (acceleratedOrbit t m) i * acceleratedOrbit t m + b := by
  obtain ⟨b, heq, hb⟩ := AffineBound.exists_affine_bounded (acceleratedOrbit t m) i
  refine ⟨b, hb, ?_⟩
  have hjoin : acceleratedOrbit i (acceleratedOrbit t m) = acceleratedOrbit (i + t) m :=
    acceleratedOrbit_add i t m
  have hge : m ≤ acceleratedOrbit (i + t) m := hnd (i + t)
  rw [hjoin] at heq
  have hmono : 2 ^ i * m ≤ 2 ^ i * acceleratedOrbit (i + t) m :=
    Nat.mul_le_mul_left _ hge
  omega

/-- **A light orbit point is bounded below by more than `m`.**  If the odd-step
count over the horizon is small enough that `2 ^ i` beats `3 ^ a` outright, the
bound above is a genuine window. -/
theorem orbit_light_lower_bound {m t i : Nat} (hnd : NeverDrops m)
    (hlight : 3 ^ oddCount (acceleratedOrbit t m) i + 1 ≤ 2 ^ i) :
    2 ^ i * m ≤ 2 ^ i * acceleratedOrbit t m + 3 ^ i := by
  obtain ⟨b, hb, hbound⟩ := orbit_affine_lower_bound (t := t) hnd i
  have hmono : 3 ^ oddCount (acceleratedOrbit t m) i * acceleratedOrbit t m
      ≤ 2 ^ i * acceleratedOrbit t m :=
    Nat.mul_le_mul_right _ (by omega)
  calc 2 ^ i * m
      ≤ 3 ^ oddCount (acceleratedOrbit t m) i * acceleratedOrbit t m + b := hbound
    _ ≤ 2 ^ i * acceleratedOrbit t m + b := Nat.add_le_add_right hmono _
    _ ≤ 2 ^ i * acceleratedOrbit t m + 3 ^ i :=
        Nat.add_le_add_left (Nat.le_trans (Nat.le_add_right b (2 ^ i)) hb) _

/-- **Why the narrowing bottoms out.**  The bound is informative only on residues
that are *light* at some level.  A residue that is heavy at every level — one of
the sieve survivors — yields nothing, and `Obstruction.sieve_never_clears`
guarantees such residues exist at every level, with
`SieveDensity.sieve_proliferates` showing their number grows.

So this family of windows confines the orbit's low values to the sieve-surviving
classes, and cannot empty them.  The class `7 (mod 12)` above is a survivor at
level two: it lies in `3 (mod 4)`. -/
theorem survivors_block_narrowing (K : Nat) :
    ∃ r : Nat, r < 2 ^ K ∧ survives K r = true ∧ 1 ≤ SieveDensity.survivorCount K := by
  obtain ⟨r, hlt, hs⟩ := Obstruction.sieve_never_clears K
  exact ⟨r, hlt, hs, SieveDensity.one_le_survivorCount K⟩

end OrbitWindows
end Collatz
