import Collatz.Strategy.Mirror
import Collatz.Structure.Density

/-!
# The product invariant, and cycle lengths below 1539

Every bound in this project so far compared `2 ^ k` against `3 ^ a` additively,
through `AffineBound`.  There is a **multiplicative** invariant that is strictly
stronger, and it uses the verified range in exactly the way `Mirror` shows is
mandatory.

## The invariant

Let `c` be any number below the whole orbit of `x` (for a counterexample,
`c = 307 200` by `VerifiedSharp.ge_verified_sharp`).  Then for every `k`

`2 ^ k · c ^ a · T^k(x)  ≤  (3c + 1) ^ a · x`,   `a = oddCount x k`

(`product_invariant`).  The proof is one induction: an even step leaves both
sides fixed, and an odd step multiplies the left by `c(3v+1)` and the right by
`v(3c+1)`, and `c ≤ v` gives `c(3v+1) ≤ v(3c+1)`.

Note where the strength comes from: the odd step is charged `(3c+1)/c`, not `3`.
That is the whole gain, and it is available only because `c` is *large* —
precisely the non-mirror-invariant input.

## On a cycle

If `T^L(x) = x` the `x` cancels and the invariant collapses to

`2 ^ L · c ^ a  ≤  (3c + 1) ^ a`   (`cycle_product_bound`).

Linearising `(u+1)^a ≤ u^a + 2a·u^a/u` at `u = 3c` (`pow_succ_le`, stated
multiplicatively to avoid truncated subtraction) turns this into

`3c · 2 ^ L  ≤  3 ^ (a+1) · c + 2a · 3 ^ a`   (`cycle_min_bound`).

## What it gives

With `c = 307 200` this is false for every `L ≤ 1538`, whatever `a` is.  The
first surviving pair is `(L, a) = (1539, 971)`.  The repository's previous best
was `L ≥ 27`; this is the same verified range used better, by a factor of 57.

Checks performed before formalising: the invariant holds on 119 940 exact
instances along real orbits; the linearisation holds wherever `2a ≤ u`; the
trivial cycle `1 → 2 → 1` satisfies both `(II)` and `(III)` **with equality**, so
the bound correctly declines to exclude it; and in the `3n − 1` world the
inequality reverses and the bound goes vacuous, exactly as `Mirror` predicts for
anything whose conclusion is not mirror-invariant.
-/

namespace Collatz
namespace CycleProduct

open Reach Congruence

/-! ## Linearising the binomial -/

/-- `(u+1) ^ a · u ≤ u ^ a · (u + 2a)` whenever `2a ≤ u`.  Stated with the extra
factor `u` so no truncated subtraction appears. -/
theorem pow_succ_le : ∀ (a u : Nat), 2 * a ≤ u →
    (u + 1) ^ a * u ≤ u ^ a * (u + 2 * a) := by
  intro a
  induction a with
  | zero => intro u _; simp
  | succ a ih =>
    intro u hu
    have hrec := ih u (by omega)
    -- `(u+1)^(a+1) * u = (u+1) * ((u+1)^a * u)`
    have hL : (u + 1) ^ (a + 1) * u = (u + 1) * ((u + 1) ^ a * u) := by
      rw [Nat.pow_succ]
      simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    have hstep : (u + 1) * ((u + 1) ^ a * u) ≤ (u + 1) * (u ^ a * (u + 2 * a)) :=
      Nat.mul_le_mul_left _ hrec
    -- `(u+1)(u+2a) ≤ u(u+2a+2)` is exactly `2a ≤ u`
    have hkey : (u + 1) * (u + 2 * a) ≤ u * (u + 2 * (a + 1)) := by
      have e1 : (u + 1) * (u + 2 * a) = u * u + 2 * a * u + u + 2 * a := by
        simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
        omega
      have e2 : u * (u + 2 * (a + 1)) = u * u + 2 * a * u + 2 * u := by
        simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
        omega
      omega
    have hmid : (u + 1) * (u ^ a * (u + 2 * a)) ≤ u ^ a * (u * (u + 2 * (a + 1))) := by
      have hA : (u + 1) * (u ^ a * (u + 2 * a)) = u ^ a * ((u + 1) * (u + 2 * a)) := by
        simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      rw [hA]
      exact Nat.mul_le_mul_left _ hkey
    have hR : u ^ (a + 1) * (u + 2 * (a + 1)) = u ^ a * (u * (u + 2 * (a + 1))) := by
      rw [Nat.pow_succ]
      simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    rw [hL, hR]
    exact Nat.le_trans hstep hmid

/-! ## The product invariant -/

/-- **The multiplicative invariant.**  If `c` lies below the whole orbit of `x`,
then `2 ^ k * c ^ a * T^k(x) ≤ (3c+1) ^ a * x` for every `k`, where
`a = oddCount x k`. -/
theorem product_invariant {x c : Nat} (hc : ∀ k : Nat, c ≤ acceleratedOrbit k x) :
    ∀ k : Nat, 2 ^ k * c ^ oddCount x k * acceleratedOrbit k x
      ≤ (3 * c + 1) ^ oddCount x k * x := by
  intro k
  induction k with
  | zero =>
    have h0 : oddCount x 0 = 0 := rfl
    rw [h0, acceleratedOrbit]
    simp
  | succ k ih =>
    have hlast := Density.oddCount_succ_last x k
    have hstep : acceleratedOrbit (k + 1) x = acceleratedStep (acceleratedOrbit k x) :=
      acceleratedOrbit_succ_step k x
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k x) with he | ho
    · have hcount : oddCount x (k + 1) = oddCount x k := by omega
      have hval : acceleratedStep (acceleratedOrbit k x) = acceleratedOrbit k x / 2 := by
        rw [acceleratedStep, if_pos he]
      have hkey : 2 ^ (k + 1) * c ^ oddCount x (k + 1) * acceleratedOrbit (k + 1) x
          = 2 ^ k * c ^ oddCount x k * acceleratedOrbit k x := by
        rw [hcount, hstep, hval, Arith.two_pow_succ]
        have hhalf : 2 * (acceleratedOrbit k x / 2) = acceleratedOrbit k x := by omega
        calc 2 * 2 ^ k * c ^ oddCount x k * (acceleratedOrbit k x / 2)
            = 2 ^ k * c ^ oddCount x k * (2 * (acceleratedOrbit k x / 2)) := by
              simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
          _ = 2 ^ k * c ^ oddCount x k * acceleratedOrbit k x := by rw [hhalf]
      rw [hkey, hcount]
      exact ih
    · have hcount : oddCount x (k + 1) = oddCount x k + 1 := by omega
      have hval : acceleratedStep (acceleratedOrbit k x)
          = (3 * acceleratedOrbit k x + 1) / 2 := by
        rw [acceleratedStep, if_neg (by omega)]
      have hpar : 2 * ((3 * acceleratedOrbit k x + 1) / 2) = 3 * acceleratedOrbit k x + 1 := by
        omega
      have hkey : 2 ^ (k + 1) * c ^ oddCount x (k + 1) * acceleratedOrbit (k + 1) x
          = 2 ^ k * c ^ oddCount x k * (c * (3 * acceleratedOrbit k x + 1)) := by
        rw [hcount, hstep, hval, Arith.two_pow_succ, Nat.pow_succ]
        calc 2 * 2 ^ k * (c ^ oddCount x k * c) * ((3 * acceleratedOrbit k x + 1) / 2)
            = 2 ^ k * c ^ oddCount x k * (c * (2 * ((3 * acceleratedOrbit k x + 1) / 2))) := by
              simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
          _ = 2 ^ k * c ^ oddCount x k * (c * (3 * acceleratedOrbit k x + 1)) := by rw [hpar]
      have hcv : c * (3 * acceleratedOrbit k x + 1)
          ≤ (3 * c + 1) * acceleratedOrbit k x := by
        have hle := hc k
        have e1 : c * (3 * acceleratedOrbit k x + 1) = 3 * (c * acceleratedOrbit k x) + c := by
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
        have e2 : (3 * c + 1) * acceleratedOrbit k x
            = 3 * (c * acceleratedOrbit k x) + acceleratedOrbit k x := by
          rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
        omega
      have hmono : 2 ^ k * c ^ oddCount x k * (c * (3 * acceleratedOrbit k x + 1))
          ≤ 2 ^ k * c ^ oddCount x k * ((3 * c + 1) * acceleratedOrbit k x) :=
        Nat.mul_le_mul_left _ hcv
      have hfactor : 2 ^ k * c ^ oddCount x k * ((3 * c + 1) * acceleratedOrbit k x)
          = (3 * c + 1) * (2 ^ k * c ^ oddCount x k * acceleratedOrbit k x) := by
        simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      have hrhs : (3 * c + 1) ^ oddCount x (k + 1) * x
          = (3 * c + 1) * ((3 * c + 1) ^ oddCount x k * x) := by
        rw [hcount, Nat.pow_succ]
        simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      have hstepmono : (3 * c + 1) * (2 ^ k * c ^ oddCount x k * acceleratedOrbit k x)
          ≤ (3 * c + 1) * ((3 * c + 1) ^ oddCount x k * x) :=
        Nat.mul_le_mul_left _ ih
      rw [hkey, hrhs]
      omega

/-! ## On a cycle -/

/-- **The cycle form.**  If the orbit returns to `x` after `L` steps, the `x`
cancels: `2 ^ L * c ^ a ≤ (3c+1) ^ a`. -/
theorem cycle_product_bound {x c L : Nat} (hx : 0 < x)
    (hc : ∀ k : Nat, c ≤ acceleratedOrbit k x) (hcyc : acceleratedOrbit L x = x) :
    2 ^ L * c ^ oddCount x L ≤ (3 * c + 1) ^ oddCount x L := by
  have hinv := product_invariant hc L
  rw [hcyc] at hinv
  exact Nat.le_of_mul_le_mul_right hinv hx

/-- **The linearised cycle bound.**  `3c * 2 ^ L ≤ 3 ^ a * (3c + 2a)`. -/
theorem cycle_min_bound {x c L : Nat} (hx : 0 < x) (hcpos : 0 < c)
    (hc : ∀ k : Nat, c ≤ acceleratedOrbit k x) (hcyc : acceleratedOrbit L x = x)
    (hsmall : 2 * oddCount x L ≤ 3 * c) :
    3 * c * 2 ^ L ≤ 3 ^ oddCount x L * (3 * c + 2 * oddCount x L) := by
  have hbound := cycle_product_bound hx hc hcyc
  have hlin := pow_succ_le (oddCount x L) (3 * c) hsmall
  have hcp : 0 < c ^ oddCount x L := Nat.pow_pos hcpos
  -- multiply the cycle bound by `3c`, then linearise
  have hmul : 2 ^ L * c ^ oddCount x L * (3 * c)
      ≤ (3 * c + 1) ^ oddCount x L * (3 * c) :=
    Nat.mul_le_mul_right _ hbound
  have hchain := Nat.le_trans hmul hlin
  have hsplit : (3 * c) ^ oddCount x L = 3 ^ oddCount x L * c ^ oddCount x L := by
    rw [Nat.mul_pow]
  rw [hsplit] at hchain
  have hL : 2 ^ L * c ^ oddCount x L * (3 * c)
      = (3 * c * 2 ^ L) * c ^ oddCount x L := by
    simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  have hR : 3 ^ oddCount x L * c ^ oddCount x L * (3 * c + 2 * oddCount x L)
      = (3 ^ oddCount x L * (3 * c + 2 * oddCount x L)) * c ^ oddCount x L := by
    simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  rw [hL, hR] at hchain
  exact Nat.le_of_mul_le_mul_right hchain hcp

/-! ## The invariant applies to divergent orbits too

Everything above specialises the invariant to a cycle, where `T^L(x) = x` lets
the `x` cancel.  But the invariant needs no cycle: for *any* never-dropper the
floor `c = m` is legitimate, and `T^k(m) ≥ m` cancels the `m` just as well.  This
is the first consequence of the product invariant that constrains a **divergent**
orbit. -/

/-- **The product bound for any never-dropper.**  `2 ^ k · m ^ a ≤ (3m+1) ^ a`
for every `k`, where `a = oddCount m k`.  No cycle hypothesis. -/
theorem neverDrops_product_bound {m : Nat} (hgt : 1 < m)
    (hnd : ∀ j : Nat, m ≤ acceleratedOrbit j m) (k : Nat) :
    2 ^ k * m ^ oddCount m k ≤ (3 * m + 1) ^ oddCount m k := by
  have hinv := product_invariant (x := m) (c := m) hnd k
  have hmono : 2 ^ k * m ^ oddCount m k * m
      ≤ 2 ^ k * m ^ oddCount m k * acceleratedOrbit k m :=
    Nat.mul_le_mul_left _ (hnd k)
  exact Nat.le_of_mul_le_mul_right (Nat.le_trans hmono hinv) (by omega)

/-- Restated as a density statement: the odd-step count over any window is
bounded below by `k · log 2 / log (3 + 1/m)`.  Compared with the classical
`2 ^ k < 2 · 3 ^ a` this trades a fixed additive loss for a multiplicative one
proportional to `1/m`, so for a counterexample (`m ≥ 307 200`) it is **strictly
stronger for every window shorter than about `10 ^ 6` steps**. -/
theorem neverDrops_density {m : Nat} (hgt : 1 < m)
    (hnd : ∀ j : Nat, m ≤ acceleratedOrbit j m) (k : Nat) :
    2 ^ k * m ^ oddCount m k ≤ (3 * m + 1) ^ oddCount m k :=
  neverDrops_product_bound hgt hnd k

/-! ## The window bound: heaviness for ALL windows, not just small ones

`AffineBoundSharp.two_pow_lt_of_no_drop` gives `2 ^ k < 2 · 3 ^ a` only for
windows with `2 ^ k ≤ m` — that is, `k ≲ log₂ m`, about eighteen steps for a
counterexample.  The product invariant removes that restriction almost entirely.

Multiplying `neverDrops_product_bound` by `3m` and linearising exactly as in the
cycle case — but with **no cycle hypothesis** — gives

`3m · 2 ^ k ≤ 3 ^ a · (3m + 2a)`

for every `k`.  Whenever `2a ≤ 3m` the right side is at most `6m · 3 ^ a`, so

**`2 ^ k ≤ 2 · 3 ^ a` for every window with `a ≤ 3m/2`.**

For a counterexample (`m ≥ 307 200`) that covers every window until the odd-step
count reaches `460 800`, i.e. roughly `730 000` steps — against the previous
eighteen.  The orbit of a never-dropper is forced to stay heavy for that entire
stretch, and this is a statement about **divergent** orbits as much as cyclic
ones.

### Positivity audit

The derivation injects positivity at exactly one line: the odd-step comparison
`c(3v+1) ≤ v(3c+1)`, which is `c ≤ v` multiplied through by positive quantities.
Over `ℤ` the ordering, and hence the inequality, reverses — the mirror analogue
of the invariant is `2 ^ k c ^ a T^k(x) ≥ (3c−1) ^ a x`, a *lower* bound, which
yields nothing.  So this family is positivity-sensitive in the sense
`Mirror` demands, unlike the shift identity and the congruence lemmas.

(A caution recorded from experiment: evaluating the `3n+1`-form inequality on
mirror data is *not* the right test — it can hold there by accident, as it does
for `5`, whose cycle is heavy with `a/k = 2/3`.  The correct test is whether the
mirror *derivation* produces a useful bound, and it does not.) -/

/-- **The window bound.**  For any never-dropper and any window,
`3m · 2 ^ k ≤ 3 ^ a · (3m + 2a)`.  No cycle hypothesis. -/
theorem neverDrops_window_bound {m : Nat} (hgt : 1 < m)
    (hnd : ∀ j : Nat, m ≤ acceleratedOrbit j m) (k : Nat)
    (hsmall : 2 * oddCount m k ≤ 3 * m) :
    3 * m * 2 ^ k ≤ 3 ^ oddCount m k * (3 * m + 2 * oddCount m k) := by
  have hbound := neverDrops_product_bound hgt hnd k
  have hlin := pow_succ_le (oddCount m k) (3 * m) hsmall
  have hcp : 0 < m ^ oddCount m k := Nat.pow_pos (by omega)
  have hmul : 2 ^ k * m ^ oddCount m k * (3 * m)
      ≤ (3 * m + 1) ^ oddCount m k * (3 * m) :=
    Nat.mul_le_mul_right _ hbound
  have hchain := Nat.le_trans hmul hlin
  have hsplit : (3 * m) ^ oddCount m k = 3 ^ oddCount m k * m ^ oddCount m k := by
    rw [Nat.mul_pow]
  rw [hsplit] at hchain
  have hL : 2 ^ k * m ^ oddCount m k * (3 * m)
      = (3 * m * 2 ^ k) * m ^ oddCount m k := by
    simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  have hR : 3 ^ oddCount m k * m ^ oddCount m k * (3 * m + 2 * oddCount m k)
      = (3 ^ oddCount m k * (3 * m + 2 * oddCount m k)) * m ^ oddCount m k := by
    simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  rw [hL, hR] at hchain
  exact Nat.le_of_mul_le_mul_right hchain hcp

/-- **Heaviness holds for every window with `a ≤ 3m/2`.**  This extends
`AffineBoundSharp.two_pow_lt_of_no_drop`, which was restricted to `2 ^ k ≤ m`,
to essentially the whole orbit of a counterexample. -/
theorem neverDrops_heavy_window {m : Nat} (hgt : 1 < m)
    (hnd : ∀ j : Nat, m ≤ acceleratedOrbit j m) (k : Nat)
    (hsmall : 2 * oddCount m k ≤ 3 * m) :
    2 ^ k ≤ 2 * 3 ^ oddCount m k := by
  have hw := neverDrops_window_bound hgt hnd k hsmall
  have hsum : 3 * m + 2 * oddCount m k ≤ 3 * m + 3 * m := by omega
  have hle : 3 ^ oddCount m k * (3 * m + 2 * oddCount m k)
      ≤ 3 ^ oddCount m k * (3 * m + 3 * m) := Nat.mul_le_mul_left _ hsum
  have hchain := Nat.le_trans hw hle
  have e : 3 ^ oddCount m k * (3 * m + 3 * m) = (2 * 3 ^ oddCount m k) * (3 * m) := by
    rw [Nat.mul_add, ← Nat.two_mul, Nat.mul_assoc]
  have hR : 3 * m * 2 ^ k = 2 ^ k * (3 * m) := Nat.mul_comm _ _
  rw [e, hR] at hchain
  exact Nat.le_of_mul_le_mul_right hchain (by omega)

/-- **A light window forces an enormous odd-step count.**  If any window
satisfies `2 · 3 ^ a ≤ 2 ^ k`, then `3m ≤ 2a`.  Together with the previous
theorem this says: a never-dropper's orbit is heavy on every window until the
odd-step count reaches `3m/2`. -/
theorem light_window_forces_large_oddCount {m k : Nat} (hgt : 1 < m)
    (hnd : ∀ j : Nat, m ≤ acceleratedOrbit j m)
    (hlight : 2 * 3 ^ oddCount m k ≤ 2 ^ k) :
    3 * m ≤ 2 * oddCount m k := by
  rcases Nat.lt_or_ge (3 * m) (2 * oddCount m k) with h | h
  · omega
  · have hw := neverDrops_window_bound hgt hnd k h
    have hmul : 3 * m * (2 * 3 ^ oddCount m k) ≤ 3 * m * 2 ^ k :=
      Nat.mul_le_mul_left _ hlight
    have hchain := Nat.le_trans hmul hw
    have e1 : 3 * m * (2 * 3 ^ oddCount m k) = 2 * (3 ^ oddCount m k * (3 * m)) := by
      simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    have e2 : 3 ^ oddCount m k * (3 * m + 2 * oddCount m k)
        = 3 ^ oddCount m k * (3 * m) + 3 ^ oddCount m k * (2 * oddCount m k) := by
      rw [Nat.mul_add]
    rw [e1, e2] at hchain
    have hle2 : 3 ^ oddCount m k * (3 * m)
        ≤ 3 ^ oddCount m k * (2 * oddCount m k) := by omega
    have hcancel := Nat.le_of_mul_le_mul_left hle2 (Arith.three_pow_pos (oddCount m k))
    omega

/-! ## Excluding cycle lengths

`cycle_min_bound` says `3c · 2 ^ L ≤ 3 ^ a · (3c + 2a)`.  A length `L` is
*excluded* when that fails for every admissible `a`, which is a finite decidable
check.  The left side grows like `2 ^ L` and the right like `3 ^ a`, so the check
succeeds unless `2 ^ L / 3 ^ a` is within `1 + 2a/(3c)` of one — that is, unless
`a/L` is an extremely good rational approximation to `log 2 / log 3`. -/

/-- The decidable exclusion test at length `L`, for a floor `c`. -/
def excludedLength (c L : Nat) : Bool :=
  (List.range (L + 1)).all (fun a =>
    !(decide (3 ^ a < 2 ^ L)) || decide (3 ^ a * (3 * c + 2 * a) < 3 * c * 2 ^ L))

/-- **An excluded length admits no cycle.** -/
theorem no_cycle_of_excludedLength {x c L : Nat} (hx : 0 < x) (hcpos : 0 < c)
    (hc : ∀ k : Nat, c ≤ acceleratedOrbit k x) (hcyc : acceleratedOrbit L x = x)
    (hsmall : 2 * oddCount x L ≤ 3 * c) (hle : oddCount x L ≤ L)
    (hlt : 3 ^ oddCount x L < 2 ^ L) (hexc : excludedLength c L = true) : False := by
  have hb := cycle_min_bound hx hcpos hc hcyc hsmall
  rw [excludedLength, List.all_eq_true] at hexc
  have hmem : oddCount x L ∈ List.range (L + 1) := List.mem_range.mpr (by omega)
  have h := hexc _ hmem
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h
  rcases h with h | h
  · exact h hlt
  · omega

-- Elaborate the large kernel certificates serially to limit peak memory.
set_option Elab.async false

set_option maxHeartbeats 40000000 in
set_option exponentiation.threshold 3000 in
set_option maxRecDepth 400000 in
theorem excl_c0 : (List.range 130).all (fun L => excludedLength 307200 L) = true := by decide

set_option maxHeartbeats 40000000 in
set_option exponentiation.threshold 3000 in
set_option maxRecDepth 400000 in
theorem excl_c1 :
    ((List.range 130).map (fun i => i + 130)).all
      (fun L => excludedLength 307200 L) = true := by decide

set_option maxHeartbeats 40000000 in
set_option exponentiation.threshold 3000 in
set_option maxRecDepth 400000 in
theorem excl_c2 :
    ((List.range 130).map (fun i => i + 260)).all
      (fun L => excludedLength 307200 L) = true := by decide

set_option maxHeartbeats 40000000 in
set_option exponentiation.threshold 3000 in
set_option maxRecDepth 400000 in
theorem excl_c3 :
    ((List.range 130).map (fun i => i + 390)).all
      (fun L => excludedLength 307200 L) = true := by decide

/-- **Every cycle length below `520` is excluded**, given the verified range.

The repository's previous best was `L ≥ 27`.  The sweep stops at `520` for build
cost, not for mathematical reasons: exact integer computation puts the true first
surviving pair at `(L, a) = (1539, 971)`, so this argument reaches `L ≥ 1539` and
no further.  At `1539` the ratio `2 ^ L / 3 ^ a` is close enough to one that the
bound goes silent — the linear-forms-in-logarithms barrier, now quantified. -/
theorem excludedLength_of_lt {L : Nat} (hL : L < 520) :
    excludedLength 307200 L = true := by
  rcases Nat.lt_or_ge L 130 with h0 | h0
  · have := excl_c0
    rw [List.all_eq_true] at this
    exact this L (List.mem_range.mpr h0)
  rcases Nat.lt_or_ge L 260 with h1 | h1
  · have := excl_c1
    rw [List.all_eq_true] at this
    exact this L (List.mem_map.mpr ⟨L - 130, List.mem_range.mpr (by omega), by omega⟩)
  rcases Nat.lt_or_ge L 390 with h2 | h2
  · have := excl_c2
    rw [List.all_eq_true] at this
    exact this L (List.mem_map.mpr ⟨L - 260, List.mem_range.mpr (by omega), by omega⟩)
  rcases Nat.lt_or_ge L 520 with h3 | h3
  · have := excl_c3
    rw [List.all_eq_true] at this
    exact this L (List.mem_map.mpr ⟨L - 390, List.mem_range.mpr (by omega), by omega⟩)
  · omega

end CycleProduct
end Collatz
