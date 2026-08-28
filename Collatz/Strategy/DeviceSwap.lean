import Collatz.Strategy.DeviceCeiling
import Collatz.Strategy.AffineExact

/-!
# The swap normal form: replace each factor two by a three

`DeviceCeiling` puts Collatz in the coordinate `u = x + 1`, where it reads

`u ↦ 3u/2` on even `u`,  `u ↦ (u+1)/2` on odd `u`.

The growth branch is a pure `3/2`, so a *maximal* run of it is a pure exponential:
starting from `u = 2 ^ s · w` with `w` odd, the run has length exactly `s` and
ends at `3 ^ s · w`.  Compressing that run gives a map with no branching at all.

## The map

`swap23 (2 ^ s · w) = 3 ^ s · w` for odd `w` — replace every factor of two by a
factor of three — and

`nu y = swap23 ((y + 1) / 2)`.

`nu` sends odd numbers to odd numbers (`nu_odd`) and fixes `3` (`nu_three`).
One `nu` step is exactly `s + 1` accelerated steps: **one halving, then `s`
triplings**, where `s` is the two-adic valuation of `(y+1)/2`
(`nu_block`, `nu_block_oddCount`).

## Why this shape is worth having

The audit of Round XIV named the missing ingredient: a mechanism that consumes
the even branch's contraction `oddCount n j < j`, the datum that
`ScaleRecord.divergence_filter`'s witness does not have.  In the `nu` picture that
datum is **structural rather than hypothetical**: every `nu` step contributes
exactly one even accelerated step, so after `B` steps

`evenCount = B`  and  `oddCount = s₁ + ⋯ + s_B`   (`nu_ledger`).

The even count is the clock.  A statement about `B` is automatically a statement
about `j − a`, and cannot be satisfied by a map whose orbits are all odd steps.

## What it buys, stated as a number

Never-dropping forces `2 ^ j ≤ 2 · 3 ^ a` on the windows the toolkit reaches, and
here `j = B + S`, `a = S` with `S = Σ sᵢ`.  So `2 ^ B ≤ 2 · (3/2) ^ S`
(`run_length_ledger`), i.e.

`S ≥ (B − 1) · log 2 / log(3/2) = 1.7095 · (B − 1)`.

**A never-dropper's odd runs must average at least `1.7095` in length.**  The
average of `v₂` over the integers is `1`, so the requirement is a `71 %` bias in a
single, natural, bounded statistic.  That is the density condition
`a / j ≥ log 2 / log 3` written in the coordinate where it is a statement about
run lengths rather than about a ratio of exponents.

## Honest verdict

It is a normal form, not a new inequality.  `nu_bridge` is an exact conjugation
of a subsequence of the orbit, so nothing is proved here that the accelerated
coordinate cannot express; `run_length_ledger` is `CycleProduct`'s heaviness in
new letters.  What is genuinely new is the *shape*: the even branch is no longer
an event that may or may not happen, it is the time variable.  Every device
written against `nu` passes `ScaleRecord.divergence_filter` by construction.  It
still says nothing about the mirror, whose `nu` differs only by the `±1` of
`DeviceCeiling.mirror_gap`, so the cycle half is untouched.
-/

namespace Collatz
namespace DeviceSwap

open Reach DeviceCeiling

/-! ## Swapping twos for threes -/

/-- Every power of three is odd. -/
theorem three_pow_odd : ∀ s : Nat, (3:Nat) ^ s % 2 = 1
  | 0 => rfl
  | s + 1 => by
      have := three_pow_odd s
      rw [Nat.pow_succ]
      omega

/-- Replace each factor of two by a factor of three, using `fuel` to stay
structurally recursive. -/
def swapAux : Nat → Nat → Nat
  | 0, n => n
  | fuel + 1, n => if n % 2 = 0 then 3 * swapAux fuel (n / 2) else n

/-- `swap23 (2 ^ s · w) = 3 ^ s · w` for odd `w`. -/
def swap23 (n : Nat) : Nat := swapAux n n

/-- With enough fuel the auxiliary computes the swap, together with the
factorisation it used. -/
theorem swapAux_spec : ∀ (fuel n : Nat), 0 < n → n ≤ fuel →
    ∃ s w : Nat, n = 2 ^ s * w ∧ w % 2 = 1 ∧ swapAux fuel n = 3 ^ s * w := by
  intro fuel
  induction fuel with
  | zero => intro n hn hle; omega
  | succ fuel ih =>
    intro n hn hle
    rcases Arith.mod_two_eq_zero_or_one n with he | ho
    · have hhalf : 0 < n / 2 := by omega
      have hle' : n / 2 ≤ fuel := by omega
      obtain ⟨s, w, hfac, hw, hval⟩ := ih (n / 2) hhalf hle'
      refine ⟨s + 1, w, ?_, hw, ?_⟩
      · have h2 : (2:Nat) ^ (s + 1) * w = 2 * (2 ^ s * w) := by
          rw [Arith.two_pow_succ, Nat.mul_assoc]
        rw [h2, ← hfac]
        omega
      · show (if n % 2 = 0 then 3 * swapAux fuel (n / 2) else n) = 3 ^ (s + 1) * w
        rw [if_pos he, hval, Nat.pow_succ, Nat.mul_comm ((3:Nat) ^ s) 3, Nat.mul_assoc]
    · refine ⟨0, n, by simp, ho, ?_⟩
      show (if n % 2 = 0 then 3 * swapAux fuel (n / 2) else n) = 3 ^ 0 * n
      rw [if_neg (by omega)]
      simp

/-- The swap, with its factorisation. -/
theorem swap23_spec {n : Nat} (hn : 0 < n) :
    ∃ s w : Nat, n = 2 ^ s * w ∧ w % 2 = 1 ∧ swap23 n = 3 ^ s * w :=
  swapAux_spec n n hn (Nat.le_refl n)

/-- The swap of a positive number is odd. -/
theorem swap23_odd {n : Nat} (hn : 0 < n) : swap23 n % 2 = 1 := by
  obtain ⟨s, w, _, hw, hval⟩ := swap23_spec hn
  rw [hval]
  have h3 := three_pow_odd s
  rw [Nat.mul_mod, h3, hw]

/-- Swapping twos for threes never shrinks a number. -/
theorem swap23_ge {n : Nat} (hn : 0 < n) : n ≤ swap23 n := by
  obtain ⟨s, w, hfac, _, hval⟩ := swap23_spec hn
  have hpow : (2:Nat) ^ s ≤ 3 ^ s := Nat.pow_le_pow_left (by omega) s
  have := Nat.mul_le_mul_right w hpow
  rw [hval, hfac]
  exact this

/-! ## The compressed map -/

/-- **The swap map.**  `nu y = swap23 ((y+1)/2)`: add one, halve, then trade every
remaining factor of two for a three. -/
def nu (y : Nat) : Nat := swap23 ((y + 1) / 2)

/-- `nu` maps positive odd numbers to odd numbers. -/
theorem nu_odd {y : Nat} (hy : 0 < y) : nu y % 2 = 1 :=
  swap23_odd (by omega)

/-- `3` is the fixed point of `nu`, as `1` is of the accelerated map. -/
theorem nu_three : nu 3 = 3 := by decide

/-- `1` is the other fixed point, the image of `x = 0`. -/
theorem nu_one : nu 1 = 1 := by decide

/-! ## The growth run, exactly

In the shifted coordinate an odd accelerated step is `u ↦ 3u/2`, so `s` of them
send `2 ^ s · w` to `3 ^ s · w`.  This is the only computation the device needs. -/

/-- **The climb.**  If `x + 1 = 2 ^ s · u` then `s` accelerated steps send `x` to
the point whose shift is `3 ^ s · u`.  No oddness of `u` is required. -/
theorem run_climb : ∀ (s u x : Nat), 0 < u → x + 1 = 2 ^ s * u →
    acceleratedOrbit s x + 1 = 3 ^ s * u := by
  intro s
  induction s with
  | zero => intro u x _ h; simpa using h
  | succ s ih =>
    intro u x hu h
    have hx : x % 2 = 1 := by
      have h2 : (2:Nat) ^ (s + 1) * u = 2 * (2 ^ s * u) := by
        rw [Nat.pow_succ, Nat.mul_comm ((2:Nat) ^ s) 2, Nat.mul_assoc]
      have hpos : 0 < (2:Nat) ^ s * u := Nat.mul_pos (Arith.two_pow_pos s) hu
      omega
    have hstep : acceleratedStep x = (3 * x + 1) / 2 := by
      rw [acceleratedStep, if_neg (by omega)]
    have hshift : acceleratedStep x + 1 = 2 ^ s * (3 * u) := by
      have h2 : (2:Nat) ^ (s + 1) * u = 2 * (2 ^ s * u) := by
        rw [Nat.pow_succ, Nat.mul_comm ((2:Nat) ^ s) 2, Nat.mul_assoc]
      have hmul : 2 ^ s * (3 * u) = 3 * (2 ^ s * u) := by
        rw [Nat.mul_left_comm]
      rw [hstep, hmul]
      omega
    have hrec := ih (3 * u) (acceleratedStep x) (by omega) hshift
    rw [acceleratedOrbit, hrec, Nat.pow_succ, Nat.mul_assoc]

/-- Inside the run every intermediate point is odd: the shift still carries a
factor of two. -/
theorem run_interior {s w x : Nat} (hw : w % 2 = 1) (hx : x + 1 = 2 ^ s * w) :
    ∀ i : Nat, i < s → acceleratedOrbit i x % 2 = 1 := by
  intro i hi
  have hsplit : (2:Nat) ^ s * w = 2 ^ i * (2 ^ (s - i) * w) := by
    rw [← Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  have hpos : 0 < (2:Nat) ^ (s - i) * w := by
    have : 0 < w := by omega
    exact Nat.mul_pos (Arith.two_pow_pos _) this
  have hclimb := run_climb i (2 ^ (s - i) * w) x hpos (by rw [hx, hsplit])
  have heven : (3:Nat) ^ i * (2 ^ (s - i) * w) % 2 = 0 := by
    obtain ⟨d, hd⟩ : ∃ d, s - i = d + 1 := ⟨s - i - 1, by omega⟩
    have h2 : (2:Nat) ^ (s - i) * w = 2 * (2 ^ d * w) := by
      rw [hd, Arith.two_pow_succ, Nat.mul_assoc]
    have hfac : (3:Nat) ^ i * (2 ^ (s - i) * w) = 2 * (3 ^ i * (2 ^ d * w)) := by
      rw [h2, Nat.mul_left_comm]
    rw [hfac]
    exact Nat.mul_mod_right 2 _
  omega

/-- The run ends on an even point: the shift has become odd. -/
theorem run_exit {s w x : Nat} (hw : w % 2 = 1) (hx : x + 1 = 2 ^ s * w) :
    acceleratedOrbit s x % 2 = 0 ∧ acceleratedOrbit s x + 1 = 3 ^ s * w := by
  have hpos : 0 < w := by omega
  have hclimb := run_climb s w x hpos hx
  refine ⟨?_, hclimb⟩
  have hodd : (3:Nat) ^ s * w % 2 = 1 := by
    rw [Nat.mul_mod, three_pow_odd s, hw]
  omega

/-! ## One `nu` step is one halving and a run -/

/-- **The block.**  From an even point `x`, the next `nu` value is reached in
exactly `s + 1` accelerated steps: one halving, then `s` triplings, and the
landing point is even again. -/
theorem nu_block {x : Nat} (hx : x % 2 = 0) (hpos : 0 < x) :
    ∃ s : Nat,
      acceleratedOrbit (s + 1) x + 1 = nu (x + 1)
        ∧ acceleratedOrbit (s + 1) x % 2 = 0
        ∧ (∀ i : Nat, i < s → acceleratedOrbit (i + 1) x % 2 = 1) := by
  have hstep : acceleratedStep x = x / 2 := by rw [acceleratedStep, if_pos hx]
  have hz : 0 < x / 2 + 1 := by omega
  obtain ⟨s, w, hfac, hw, hval⟩ := swap23_spec hz
  refine ⟨s, ?_, ?_, ?_⟩
  · have hexit := (run_exit hw hfac).2
    have hshift : acceleratedOrbit (s + 1) x = acceleratedOrbit s (x / 2) := by
      rw [acceleratedOrbit, hstep]
    have hnu : nu (x + 1) = 3 ^ s * w := by
      unfold nu
      have : (x + 1 + 1) / 2 = x / 2 + 1 := by omega
      rw [this, hval]
    rw [hshift, hexit, hnu]
  · have hexit := (run_exit hw hfac).1
    have hshift : acceleratedOrbit (s + 1) x = acceleratedOrbit s (x / 2) := by
      rw [acceleratedOrbit, hstep]
    rw [hshift]
    exact hexit
  · intro i hi
    have hshift : acceleratedOrbit (i + 1) x = acceleratedOrbit i (x / 2) := by
      rw [acceleratedOrbit, hstep]
    rw [hshift]
    exact run_interior hw hfac i hi

/-! ## The exact one-step drop criterion

In the normal form the growth of a single step is decided by one integer.  With
`(y+1)/2 = 2 ^ s · w` the step sends `y = 2 ^ (s+1) · w − 1` to `3 ^ s · w`, so it
drops exactly when `(3/2) ^ s < 2`, i.e. when `s ≤ 1`. -/

/-- `2 ^ (s+1) ≤ 3 ^ s` from `s = 2` on. -/
theorem two_pow_succ_le_three_pow : ∀ s : Nat, 2 ≤ s → 2 ^ (s + 1) ≤ 3 ^ s := by
  intro s
  induction s with
  | zero => intro h; omega
  | succ s ih =>
    intro _
    rcases Nat.lt_or_ge s 2 with hlt | hge
    · have hs : s = 1 := by omega
      subst hs
      decide
    · have hrec := ih hge
      have e2 : (2:Nat) ^ (s + 1 + 1) = 2 ^ (s + 1) * 2 := Nat.pow_succ _ _
      have e3 : (3:Nat) ^ (s + 1) = 3 ^ s * 3 := Nat.pow_succ _ _
      have hpos : 0 < (3:Nat) ^ s := Arith.three_pow_pos s
      rw [e2, e3]
      omega

/-- The data of one `nu` step: the factorisation it uses and the value it
produces. -/
theorem nu_step_data {y : Nat} (hy : 0 < y) :
    ∃ s w : Nat, (y + 1) / 2 = 2 ^ s * w ∧ w % 2 = 1 ∧ nu y = 3 ^ s * w := by
  obtain ⟨s, w, hfac, hw, hval⟩ := swap23_spec (n := (y + 1) / 2) (by omega)
  exact ⟨s, w, hfac, hw, hval⟩

/-- The shift of `y` in terms of the step data. -/
theorem nu_shift {y s w : Nat} (hodd : y % 2 = 1) (hfac : (y + 1) / 2 = 2 ^ s * w) :
    y + 1 = 2 ^ (s + 1) * w := by
  have h2 : (2:Nat) ^ (s + 1) * w = 2 * (2 ^ s * w) := by
    rw [Arith.two_pow_succ, Nat.mul_assoc]
  rw [h2, ← hfac]
  omega

/-- **A short run drops.**  If the run length is at most one the step is a strict
descent, for every `y > 3`. -/
theorem nu_lt {y s w : Nat} (hy : 3 < y) (hodd : y % 2 = 1)
    (hfac : (y + 1) / 2 = 2 ^ s * w) (hval : nu y = 3 ^ s * w) (hs : s ≤ 1) :
    nu y < y := by
  have hyfac := nu_shift hodd hfac
  match s, hs with
  | 0, _ =>
    have e2 : (2:Nat) ^ (0 + 1) * w = 2 * w := by rfl
    have e3 : (3:Nat) ^ 0 * w = w := by rw [Nat.pow_zero, Nat.one_mul]
    rw [e2] at hyfac
    rw [e3] at hval
    omega
  | 1, _ =>
    have e2 : (2:Nat) ^ (1 + 1) * w = 4 * w := by rfl
    have e3 : (3:Nat) ^ 1 * w = 3 * w := by rw [Nat.pow_one]
    rw [e2] at hyfac
    rw [e3] at hval
    omega

/-- **A long run grows.**  If the run length is at least two the step is a strict
ascent, always. -/
theorem nu_gt {y s w : Nat} (hw : 0 < w) (hs : 2 ≤ s) (hodd : y % 2 = 1)
    (hfac : (y + 1) / 2 = 2 ^ s * w) (hval : nu y = 3 ^ s * w) :
    y < nu y := by
  have hyfac := nu_shift hodd hfac
  have hpow := two_pow_succ_le_three_pow s hs
  have hmul : 2 ^ (s + 1) * w ≤ 3 ^ s * w := Nat.mul_le_mul_right w hpow
  omega

/-- **The one-step dichotomy, in one statement.**  A `nu` step descends exactly
when its run length is at most one.  So the conjecture is the assertion that the
statistic `s = v₂((y+1)/2)` takes the value `0` or `1` often enough — and
`run_length_ledger` says *how* often a never-dropper would have to avoid that. -/
theorem nu_dichotomy {y : Nat} (hy : 3 < y) (hodd : y % 2 = 1) :
    ∃ s w : Nat, (y + 1) / 2 = 2 ^ s * w ∧ w % 2 = 1 ∧ nu y = 3 ^ s * w
      ∧ (s ≤ 1 → nu y < y) ∧ (2 ≤ s → y < nu y) := by
  obtain ⟨s, w, hfac, hw, hval⟩ := nu_step_data (y := y) (by omega)
  exact ⟨s, w, hfac, hw, hval,
    fun hs => nu_lt hy hodd hfac hval hs,
    fun hs => nu_gt (by omega) hs hodd hfac hval⟩

/-! ## The ledger: the even count is the clock -/

/-- **The block ledger.**  A block of `s + 1` steps spends exactly one even step
and `s` odd ones, so the odd count over a block is `s`. -/
theorem nu_block_oddCount {x : Nat} (hx : x % 2 = 0) (hpos : 0 < x)
    {s : Nat} (hrun : ∀ i : Nat, i < s → acceleratedOrbit (i + 1) x % 2 = 1) :
    oddCount x (s + 1) = s := by
  have hzero : oddCount x 1 = 0 := by
    have hlast : oddCount x (0 + 1) = oddCount x 0 + acceleratedOrbit 0 x % 2 :=
      Density.oddCount_succ_last x 0
    have h0 : acceleratedOrbit 0 x = x := rfl
    have hoc : oddCount x 0 = 0 := rfl
    rw [h0, hoc, hx] at hlast
    simpa using hlast
  have key : ∀ i : Nat, i ≤ s → oddCount x (i + 1) = i := by
    intro i
    induction i with
    | zero => intro _; exact hzero
    | succ i ih =>
      intro hi
      have hlast := Density.oddCount_succ_last x (i + 1)
      have hodd := hrun i (by omega)
      rw [hodd] at hlast
      rw [hlast, ih (by omega)]
  exact key s (Nat.le_refl s)

/-- **The clock.**  Over a block the even count is exactly one. -/
theorem nu_block_evenCount {x : Nat} (hx : x % 2 = 0) (hpos : 0 < x)
    {s : Nat} (hrun : ∀ i : Nat, i < s → acceleratedOrbit (i + 1) x % 2 = 1) :
    (s + 1) - oddCount x (s + 1) = 1 := by
  rw [nu_block_oddCount hx hpos hrun]
  omega

/-! ## What never-dropping costs in run lengths

`AffineExact.heavy_while_few_even` gives `2 ^ j ≤ 2 · 3 ^ a` on the windows the
toolkit reaches.  Written in block coordinates `j = B + S`, `a = S`, that is a
statement purely about the total run length `S` against the block count `B`. -/

/-- **The run-length ledger.**  For a never-dropper, a window of `B` blocks with
total run length `S` satisfies `2 ^ B · 2 ^ S ≤ 2 · 3 ^ S`, so `S` must exceed
`B` by the factor `log 2 / log(3/2) = 1.7095…`.  The average of `v₂` over the
integers is `1`, so a counterexample needs a `71 %` bias in its run lengths. -/
theorem run_length_ledger {m B S : Nat} (hm : 0 < m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hshape : oddCount m (B + S) = S)
    (hfew : (2:Nat) ^ B ≤ m) :
    2 ^ B * 2 ^ S ≤ 2 * 3 ^ S := by
  have hsub : B + S - oddCount m (B + S) = B := by rw [hshape]; omega
  have hheavy := AffineExact.heavy_while_few_even hm hnd (j := B + S) (by rw [hsub]; exact hfew)
  rw [hshape] at hheavy
  rw [Nat.pow_add] at hheavy
  exact hheavy

/-- **Runs of length one cannot go on.**  With `S = B` — every run of length
exactly one — the ledger reads `4 ^ B ≤ 2 · 3 ^ B`, which fails from `B = 3`.  So
a never-dropper cannot spend three blocks in a row on unit runs (inside the
window range where `2 ^ B ≤ m`).  The threshold is `B ≤ 2`, not `B ≤ 1`: at
`B = 2` the ledger reads `16 ≤ 18` and still holds. -/
theorem run_length_ledger_forces_long_runs {m B : Nat} (hm : 0 < m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hshape : oddCount m (B + B) = B)
    (hfew : (2:Nat) ^ B ≤ m) : B ≤ 2 := by
  have h := run_length_ledger hm hnd hshape hfew
  have hpow : (2:Nat) ^ B * 2 ^ B = 4 ^ B := by
    rw [← Nat.mul_pow]
  rw [hpow] at h
  match B with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | (k + 3) =>
    exfalso
    have hall : ∀ n : Nat, 2 * (3:Nat) ^ (n + 3) < 4 ^ (n + 3) := by
      intro n
      induction n with
      | zero => decide
      | succ n ih =>
        have hsucc : n + 1 + 3 = (n + 3) + 1 := by omega
        have e3 : (3:Nat) ^ (n + 1 + 3) = 3 ^ (n + 3) * 3 := by
          rw [hsucc, Nat.pow_succ]
        have e4 : (4:Nat) ^ (n + 1 + 3) = 4 ^ (n + 3) * 4 := by
          rw [hsucc, Nat.pow_succ]
        rw [e3, e4]
        omega
    exact absurd h (by have := hall k; omega)

/-! ## The normal form of the conjecture, one direction

Reaching `3` under `nu` is reaching `1` under the accelerated map.  The converse
needs the block covering and is recorded separately. -/

/-- The orbit of the swap map. -/
def nuOrbit : Nat → Nat → Nat
  | 0, y => y
  | k + 1, y => nuOrbit k (nu y)

@[simp] theorem nuOrbit_zero (y : Nat) : nuOrbit 0 y = y := rfl

theorem nuOrbit_succ_step (k y : Nat) : nuOrbit (k + 1) y = nu (nuOrbit k y) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih => rw [nuOrbit, ih, nuOrbit]

/-- **Every `nu` step is realised by the accelerated map.**  From an even point,
the `nu` value is an accelerated iterate. -/
theorem nu_reachable {x : Nat} (hx : x % 2 = 0) (hpos : 0 < x) :
    ∃ j : Nat, 0 < j ∧ acceleratedOrbit j x + 1 = nu (x + 1)
      ∧ acceleratedOrbit j x % 2 = 0 := by
  obtain ⟨s, hval, heven, _⟩ := nu_block hx hpos
  exact ⟨s + 1, by omega, hval, heven⟩

/-- **The compressed orbit is a subsequence of the real one.**  Every `nu`
iterate of `x + 1` is `acceleratedOrbit j x + 1` for some `j`, and the point is
even. -/
theorem nuOrbit_realised {x : Nat} (hx : x % 2 = 0) (hpos : 0 < x) : ∀ k : Nat,
    ∃ j : Nat, acceleratedOrbit j x + 1 = nuOrbit k (x + 1)
      ∧ acceleratedOrbit j x % 2 = 0 ∧ 0 < acceleratedOrbit j x := by
  intro k
  induction k with
  | zero => exact ⟨0, rfl, hx, hpos⟩
  | succ k ih =>
    obtain ⟨j, hval, heven, hjpos⟩ := ih
    obtain ⟨d, _, hd, hdeven⟩ := nu_reachable heven hjpos
    refine ⟨d + j, ?_, ?_, ?_⟩
    · rw [← acceleratedOrbit_add d j x, hd, hval, nuOrbit_succ_step]
    · rw [← acceleratedOrbit_add d j x]; exact hdeven
    · rw [← acceleratedOrbit_add d j x]
      have hz : 0 < (acceleratedOrbit j x + 1 + 1) / 2 := by omega
      have hge : 2 ≤ (acceleratedOrbit j x + 1 + 1) / 2 := by omega
      have hswap := swap23_ge hz
      have hnu : 2 ≤ nu (acceleratedOrbit j x + 1) := by
        unfold nu
        omega
      omega

/-! ## The covering: `nu` sees every even point

The converse of `nuOrbit_realised`.  A block runs from one even point to the
next, and its length is forced, so the `nu` orbit visits **exactly** the even
points of the accelerated orbit, in order.  Verified first on 9 999 starts with
an exact list comparison, zero mismatches. -/

/-- The running invariant: at every time `j` the orbit is inside a block whose
start `i` is already `nu`-reachable, and every point strictly after `i` up to `j`
is odd. -/
theorem nu_run_invariant {x : Nat} (hx : x % 2 = 0) (hpos : 0 < x) : ∀ j : Nat,
    ∃ i : Nat, i ≤ j
      ∧ (∃ k : Nat, nuOrbit k (x + 1) = acceleratedOrbit i x + 1)
      ∧ acceleratedOrbit i x % 2 = 0
      ∧ (∀ p : Nat, i < p → p ≤ j → acceleratedOrbit p x % 2 = 1) := by
  intro j
  induction j with
  | zero => exact ⟨0, Nat.le_refl 0, ⟨0, rfl⟩, hx, by intro p hp hp'; omega⟩
  | succ j ih =>
    obtain ⟨i, hij, ⟨k, hk⟩, heven, hodds⟩ := ih
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit (j + 1) x) with hnext | hnext
    · -- the block ends here; its length is forced to be `j + 1 − i`
      have hposi : 0 < acceleratedOrbit i x := acceleratedOrbit_positive hpos i
      obtain ⟨s, hval, hlandeven, hinterior⟩ := nu_block heven hposi
      have hshift : ∀ r : Nat,
          acceleratedOrbit r (acceleratedOrbit i x) = acceleratedOrbit (r + i) x := by
        intro r; exact acceleratedOrbit_add r i x
      have hlen : i + s + 1 = j + 1 := by
        rcases Nat.lt_trichotomy (i + s + 1) (j + 1) with hlt | heq | hgt
        · exfalso
          have hoddp := hodds (i + s + 1) (by omega) (by omega)
          have : acceleratedOrbit (i + s + 1) x = acceleratedOrbit (s + 1) (acceleratedOrbit i x) := by
            rw [hshift (s + 1)]
            congr 1
            omega
          rw [this] at hoddp
          omega
        · exact heq
        · exfalso
          have hq : j - i < s := by omega
          have hint := hinterior (j - i) hq
          have hidx : acceleratedOrbit (j - i + 1) (acceleratedOrbit i x)
              = acceleratedOrbit (j + 1) x := by
            rw [hshift (j - i + 1)]
            congr 1
            omega
          rw [hidx] at hint
          omega
      refine ⟨j + 1, Nat.le_refl _, ⟨k + 1, ?_⟩, hnext, by intro p hp hp'; omega⟩
      have hstep : acceleratedOrbit (s + 1) (acceleratedOrbit i x)
          = acceleratedOrbit (j + 1) x := by
        rw [hshift (s + 1)]
        congr 1
        omega
      rw [nuOrbit_succ_step, hk, ← hval, hstep]
    · -- still inside the block
      exact ⟨i, by omega, ⟨k, hk⟩, heven, by
        intro p hp hp'
        rcases Nat.lt_or_ge p (j + 1) with h | h
        · exact hodds p hp (by omega)
        · have : p = j + 1 := by omega
          rw [this]; exact hnext⟩

/-- **The covering.**  Every even point of the accelerated orbit is a `nu`
iterate. -/
theorem nu_covers {x : Nat} (hx : x % 2 = 0) (hpos : 0 < x) {j : Nat}
    (hj : acceleratedOrbit j x % 2 = 0) :
    ∃ k : Nat, nuOrbit k (x + 1) = acceleratedOrbit j x + 1 := by
  obtain ⟨i, hij, ⟨k, hk⟩, heven, hodds⟩ := nu_run_invariant hx hpos j
  have hi : i = j := by
    rcases Nat.lt_or_ge i j with h | h
    · exfalso
      have := hodds j h (Nat.le_refl j)
      omega
    · omega
  rw [← hi]
  exact ⟨k, hk⟩

/-- **Sufficiency of the normal form.**  If the `nu` orbit of `x + 1` reaches `3`,
then the accelerated orbit of `x` reaches `2`, hence `1`. -/
theorem reaches_of_nu {x k : Nat} (hx : x % 2 = 0) (hpos : 0 < x)
    (h : nuOrbit k (x + 1) = 3) :
    ∃ j : Nat, acceleratedOrbit j x = 2 := by
  obtain ⟨j, hval, _, _⟩ := nuOrbit_realised hx hpos k
  exact ⟨j, by omega⟩

/-- `2` reaches `1` in one accelerated step, so the previous theorem really does
land on the conjecture. -/
theorem two_reaches_one : acceleratedOrbit 1 2 = 1 := by decide

/-- **Collatz in the swap normal form.**  For an even start, reaching `1` under
the accelerated map is *equivalent* to reaching `3` under `nu`.  Since every
positive `n` has `2n` even and `2n → n`, this is the conjecture itself in a map
with a single branch:

> iterate `y ↦ swap23 ((y+1)/2)` — add one, halve, then trade every remaining
> factor of two for a three — and reach `3`. -/
theorem reaches_one_iff_nu {x : Nat} (hx : x % 2 = 0) (hpos : 0 < x) :
    (∃ j : Nat, acceleratedOrbit j x = 1) ↔ (∃ k : Nat, nuOrbit k (x + 1) = 3) := by
  constructor
  · rintro ⟨j, hj⟩
    have htwo : acceleratedOrbit (j + 1) x = 2 := by
      rw [show j + 1 = 1 + j by omega, ← acceleratedOrbit_add 1 j x, hj]
      rfl
    have heven : acceleratedOrbit (j + 1) x % 2 = 0 := by rw [htwo]
    obtain ⟨k, hk⟩ := nu_covers hx hpos heven
    exact ⟨k, by rw [hk, htwo]⟩
  · rintro ⟨k, hk⟩
    obtain ⟨j, hj⟩ := reaches_of_nu hx hpos hk
    refine ⟨j + 1, ?_⟩
    rw [show j + 1 = 1 + j by omega, ← acceleratedOrbit_add 1 j x, hj]
    rfl

end DeviceSwap
end Collatz
