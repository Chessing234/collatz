import Collatz.Strategy.TreeBranching
import Collatz.Strategy.TreeHalf

/-!
# A balanced tree of `1` is a fat tree of `1`

**Novelty tag: NEW (conditional theorem; Round LXXVII).**  Companion to
`Strategy/TreeStochastic` and `Devices/StochasticTree.md` §6.

Let `T` be the set of positive integers reaching `1` (here: within `X`
accelerated steps, for the count up to `X`, as in `reachesOneUpToCount`).
Write `M c X` for the odd members of `T` below `X` in class `c mod 3`,
`N9 R X` for those in class `R mod 9`, and `M1 c X` for those in class `c`
that are `1 mod 4`.

Two *balance* hypotheses, both trivially true below the verified range
(where `T` is everything) and both implied by "`T` has positive density and
is equidistributed modulo `36`":

* `Equi`: within each class mod `3`, each of its three classes mod `9` carries
  at least `1/3 − 1/64` of the members (`61 · M ≤ 192 · N9`);
* `Bal4`: within each class mod `3`, the residue `1 mod 4` carries at most
  `1/2 + 1/64` of the members (`128 · M1 ≤ 66 · M`).

**Theorem** (`count_balance`): under `Equi` and `Bal4`, for every `N ≥ 1`

    N ^ 89 < 20 ^ 89 · 10 ^ 1500 · (reachesOneUpToCount N) ^ 100,

i.e. at least `c · N ^ 0.89` integers up to `N` reach `1`.  Unconditionally
the kernel-checked record is `7/10` (`TreeSevenTenths`) and the
computer-verified one `0.852`.

## Why balance is enough

Every member `n ≡ 1 (mod 4)` of `T` in class `c` is the child `(2^v m − 1)/3`,
`v = v₂(3n+1) ≥ 2`, of a member `m ≤ (3X+1)/2^v` of `T` in the class
`parentRes c v ≡ 2^(−v)(3c+1) (mod 9)`; distinct `(m, v)` give distinct
children (`family_count`).  So `M1 c X ≥ Σ_{v ≥ 2} N9 (parentRes c v) ((3X+1)/2^v)`.
`Equi` turns the right side into class counts mod `3`, `Bal4` turns the left
side into `M c X`, and the result is a recursion of `M` at scale `X` in terms
of `M` at the scales `3X/2^v`, `v ≥ 2` — all **retarded**.  The `v = 1`
children (the advanced terms of Krasikov–Lagarias) never appear: the 2-adic
balance accounts for them.  At exponent `1` the recursion is exactly critical
(`TreeStochastic`: the lift-averaged transfer is column-stochastic), so any
slack in the balance is converted into an exponent below `1`; with `1/64` on
both sides the certificate closes at `2 ^ (0.8995)` (ratio `(79/75)^12`).

## The lattice

Claims are indexed by scales `3^j · 2^y` with weight `(79/75)^(12y + 19j)`:
`19/12` approximates `log₂ 3` from below and `3^12 > 2^19`, so a claim at
type `j ≥ 12` follows from the one at `(j − 12, y + 19)` by monotonicity with
no change of weight, and the induction on the absolute bound `3^j 2^y` needs
only `j < 12` in the step.  One certificate inequality (`cert`, two weights
equal to `1`) and one base bound (`base_bound`) close it.
-/

set_option exponentiation.threshold 5000
set_option maxRecDepth 100000

namespace Collatz
namespace TreeBalance

open TreeCount TreeBranching Collatz.Sum Papers.KrasikovLagarias2003

/-! ## 1. The counts and the hypotheses -/

def K : Nat := 10 ^ 15

/-- Odd members of `T` up to `X` in class `c mod 3`. -/
def M (c X : Nat) : Nat :=
  countUpTo (fun n => n % 2 = 1 ∧ n % 3 = c ∧ reachesOneBy n X = true) X

/-- Odd members of `T` up to `X` in class `R mod 9`. -/
def N9 (R X : Nat) : Nat :=
  countUpTo (fun n => n % 2 = 1 ∧ n % 9 = R ∧ reachesOneBy n X = true) X

/-- Members of `T` up to `X` that are `1 mod 4` and in class `c mod 3`. -/
def M1 (c X : Nat) : Nat :=
  countUpTo (fun n => n % 4 = 1 ∧ n % 3 = c ∧ reachesOneBy n X = true) X

/-- **3-adic balance**: above `2^20`, each class mod `9` carries at least
`1/3 − 1/64` of its class mod `3`. -/
def Equi : Prop :=
  ∀ X, 2 ^ 20 ≤ X → ∀ R, R < 9 → R % 3 ≠ 0 → 61 * M (R % 3) X ≤ 192 * N9 R X

/-- **2-adic balance**: above `2^20`, the residue `1 mod 4` carries at most
`1/2 + 1/64` of each class mod `3`. -/
def Bal4 : Prop :=
  ∀ X, 2 ^ 20 ≤ X → ∀ c, 128 * M1 c X ≤ 66 * M c X

/-- The class mod `9` of the parents at valuation `v` of the children in
class `c mod 3`: `2^(−v) (3c + 1)`, using `2^6 ≡ 1 (mod 9)`. -/
def parentRes (c v : Nat) : Nat := (2 ^ (6 - v % 6) * (3 * c + 1)) % 9

/-- The scale of the parents: `(3X + 1) / 2^v`. -/
def Y (X v : Nat) : Nat := (3 * X + 1) / 2 ^ v

theorem M_mono {c X X' : Nat} (h : X ≤ X') : M c X ≤ M c X' := by
  unfold M
  apply Nat.le_trans (countUpTo_le_of_le
    (p := fun n => n % 2 = 1 ∧ n % 3 = c ∧ reachesOneBy n X = true) h)
  apply countUpTo_mono
  intro n _ _ ⟨h1, h2, h3⟩
  exact ⟨h1, h2, reachesOneBy_mono h h3⟩

theorem M_five : 1 ≤ M 1 5 ∧ 1 ≤ M 2 5 := by decide

theorem M_pos {c X : Nat} (hc : c = 1 ∨ c = 2) (hX : 5 ≤ X) : 1 ≤ M c X := by
  have h := M_mono (c := c) hX
  rcases hc with rfl | rfl
  · exact Nat.le_trans M_five.1 h
  · exact Nat.le_trans M_five.2 h

/-! ## 2. Residues -/

theorem two_pow_mod_nine_aux (q r : Nat) : 2 ^ (6 * q + r) % 9 = 2 ^ r % 9 := by
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
  have h64 : (2:Nat) ^ 6 % 9 = 1 := by decide
  rw [h64, Nat.one_pow, show (1:Nat) % 9 = 1 from rfl, Nat.one_mul, Nat.mod_mod]

theorem two_pow_mod_nine (v : Nat) : 2 ^ v % 9 = 2 ^ (v % 6) % 9 := by
  have h := two_pow_mod_nine_aux (v / 6) (v % 6)
  have e : 2 ^ v = 2 ^ (6 * (v / 6) + v % 6) := by rw [Nat.div_add_mod]
  rw [e]
  exact h

theorem two_pow_mod_three (k : Nat) : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
  induction k with
  | zero => left; rfl
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> simp

theorem parentRes_lt (c v : Nat) : parentRes c v < 9 := Nat.mod_lt _ (by decide)

theorem parentRes_mod_three (c v : Nat) : parentRes c v % 3 ≠ 0 := by
  unfold parentRes
  rw [Nat.mod_mod_of_dvd _ (⟨3, rfl⟩ : (3:Nat) ∣ 9), Nat.mul_mod]
  have h3c : (3 * c + 1) % 3 = 1 := by omega
  rw [h3c]
  rcases two_pow_mod_three (6 - v % 6) with h | h <;> rw [h] <;> decide

theorem parentRes_class {c v : Nat} (hc : c = 1 ∨ c = 2) :
    parentRes c v % 3 = 1 ∨ parentRes c v % 3 = 2 := by
  have _ := hc
  have := parentRes_mod_three c v
  have := Nat.mod_lt (parentRes c v) (show 0 < 3 by decide)
  omega

/-- A parent in class `parentRes c v` has `2^v m ≡ 3c + 1 (mod 9)`. -/
theorem parent_pow_mod {c v m : Nat} (hm : m % 9 = parentRes c v) :
    (2 ^ v * m) % 9 = (3 * c + 1) % 9 := by
  unfold parentRes at hm
  have hp := two_pow_mod_nine v
  have h6 : v % 6 + (6 - v % 6) = 6 := by
    have := Nat.mod_lt v (show 0 < 6 by decide); omega
  calc (2 ^ v * m) % 9 = ((2 ^ v % 9) * (m % 9)) % 9 := Nat.mul_mod _ _ _
    _ = ((2 ^ (v % 6) % 9) * ((2 ^ (6 - v % 6) * (3 * c + 1)) % 9)) % 9 := by rw [hp, hm]
    _ = (2 ^ (v % 6) * (2 ^ (6 - v % 6) * (3 * c + 1))) % 9 := by rw [← Nat.mul_mod]
    _ = (2 ^ 6 * (3 * c + 1)) % 9 := by rw [← Nat.mul_assoc, ← Nat.pow_add, h6]
    _ = (3 * c + 1) % 9 := by
        have : (2:Nat) ^ 6 = 64 := by decide
        rw [this]; omega

/-- The child of such a parent: admissible, in class `c mod 3`, `1 mod 4`, positive. -/
theorem child_props {c v m : Nat} (hc : c = 1 ∨ c = 2) (hv : 2 ≤ v)
    (hm : m % 9 = parentRes c v) (hpos : 1 ≤ m) :
    (2 ^ v * m) % 3 = 1 ∧ child m v % 3 = c ∧ child m v % 4 = 1 ∧ 1 ≤ child m v := by
  have h9 := parent_pow_mod hm
  obtain ⟨w, rfl⟩ : ∃ w, v = w + 2 := ⟨v - 2, by omega⟩
  have h4 : 2 ^ (w + 2) * m = 4 * (2 ^ w * m) := two_pow_add_two_mul w m
  have hw : 1 ≤ 2 ^ w * m := Nat.mul_pos (Nat.pow_pos (by decide)) hpos
  unfold child
  generalize hx : 2 ^ (w + 2) * m = x at h9 h4 ⊢
  rcases hc with rfl | rfl <;> omega

/-- Two odd numbers times powers of two agree only at the same power. -/
theorem odd_pow_eq {a b i j : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1)
    (h : 2 ^ i * a = 2 ^ j * b) : i = j := by
  rcases Nat.lt_or_ge i j with hij | hij
  · exfalso
    obtain ⟨d, rfl⟩ : ∃ d, j = i + (d + 1) := ⟨j - i - 1, by omega⟩
    rw [Nat.pow_add, Nat.mul_assoc] at h
    have h' : a = 2 ^ (d + 1) * b := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) h
    rw [two_pow_succ_mul] at h'
    omega
  · rcases Nat.lt_or_ge j i with hji | hji
    · exfalso
      obtain ⟨d, rfl⟩ : ∃ d, i = j + (d + 1) := ⟨i - j - 1, by omega⟩
      rw [Nat.pow_add, Nat.mul_assoc] at h
      have h' : 2 ^ (d + 1) * a = b := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) h
      rw [two_pow_succ_mul] at h'
      omega
    · omega

/-! ## 3. The children of the parents, counted -/

theorem Y_le {X v : Nat} (hv : 2 ≤ v) : Y X v ≤ (3 * X + 1) / 4 := by
  unfold Y
  apply Nat.div_le_div_left _ (by decide)
  calc (4:Nat) = 2 ^ 2 := rfl
    _ ≤ 2 ^ v := Nat.pow_le_pow_right (by decide) hv

/-- Each parent's child is in the tree, below `X`, in class `c`, and `1 mod 4`. -/
theorem child_into {c v m X : Nat} (hc : c = 1 ∨ c = 2) (hv : 2 ≤ v) (hv16 : v ≤ 16)
    (hX : 68 ≤ X) (hm1 : 1 ≤ m) (hmY : m ≤ Y X v)
    (hP : m % 2 = 1 ∧ m % 9 = parentRes c v ∧ reachesOneBy m (Y X v) = true) :
    1 ≤ child m v ∧ child m v ≤ X ∧
      (child m v % 4 = 1 ∧ child m v % 3 = c ∧ reachesOneBy (child m v) X = true) := by
  obtain ⟨_, hm9, hmr⟩ := hP
  obtain ⟨h3, hc3, hc4, hc1⟩ := child_props hc hv hm9 hm1
  have heq := child_eq h3
  have hle : 2 ^ v * m ≤ 3 * X + 1 := by
    have := (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))).1 hmY
    rw [Nat.mul_comm] at this
    exact this
  refine ⟨hc1, by omega, hc4, hc3, ?_⟩
  obtain ⟨j, hj, hj1⟩ := (reachesOneBy_iff m (Y X v)).1 hmr
  apply reachesOneBy_of_orbit (j := j + v)
  · rw [← acceleratedOrbit_add, orbit_child (by omega) h3, hj1]
  · have := Y_le (X := X) hv
    have : (3 * X + 1) / 4 + 17 ≤ X := by omega
    omega

/-- **The children count.**  Parents at valuations `2, …, 16` in the classes
`parentRes c v` map injectively and disjointly into the `1 mod 4` members of
class `c` below `X`. -/
theorem family {c X : Nat} (hc : c = 1 ∨ c = 2) (hX : 68 ≤ X) :
    sumRange 15 (fun i => N9 (parentRes c (i + 2)) (Y X (i + 2))) ≤ M1 c X := by
  unfold N9 M1
  apply family_count (f := fun i m => child m (i + 2))
    (P := fun i m => m % 2 = 1 ∧ m % 9 = parentRes c (i + 2) ∧
      reachesOneBy m (Y X (i + 2)) = true)
    (Y := fun i => Y X (i + 2))
  · -- injective
    intro i hi a b ha1 haY hb1 hbY hPa hPb hab
    have h3a := (child_props hc (by omega) hPa.2.1 ha1).1
    have h3b := (child_props hc (by omega) hPb.2.1 hb1).1
    have ea := child_eq h3a
    have eb := child_eq h3b
    have : 2 ^ (i + 2) * a = 2 ^ (i + 2) * b := by omega
    exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) this
  · -- disjoint
    intro i j hi hj hij a b ha1 haY hb1 hbY hPa hPb hab
    have h3a := (child_props hc (by omega) hPa.2.1 ha1).1
    have h3b := (child_props hc (by omega) hPb.2.1 hb1).1
    have ea := child_eq h3a
    have eb := child_eq h3b
    have : 2 ^ (i + 2) * a = 2 ^ (j + 2) * b := by omega
    have := odd_pow_eq hPa.1 hPb.1 this
    omega
  · -- into
    intro i hi a ha1 haY hPa
    exact child_into hc (by omega) (by omega) hX ha1 haY hPa

/-- **The recursion under balance.**  For `X ≥ 2^36`,
`61 · Σ_{v=2}^{16} M (parentRes c v mod 3) ((3X+1)/2^v) ≤ 99 · M c X`. -/
theorem count_rec (hE : Equi) (hB : Bal4) {c X : Nat} (hc : c = 1 ∨ c = 2)
    (hX : 2 ^ 36 ≤ X) :
    61 * sumRange 15 (fun i => M (parentRes c (i + 2) % 3) (Y X (i + 2))) ≤ 99 * M c X := by
  have hX68 : 68 ≤ X := by
    have : (68:Nat) ≤ 2 ^ 36 := by decide
    omega
  have hfam := family hc hX68
  have h20 : 2 ^ 20 ≤ X := by
    have : (2:Nat) ^ 20 ≤ 2 ^ 36 := by decide
    omega
  have hbal := hB X h20 c
  have hY : ∀ i, i < 15 → 2 ^ 20 ≤ Y X (i + 2) := by
    intro i hi
    unfold Y
    rw [Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))]
    have h1 : 2 ^ (i + 2) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2 ^ 20 * 2 ^ (i + 2) ≤ 2 ^ 20 * 2 ^ 16 := Nat.mul_le_mul_left _ h1
    have h3 : (2:Nat) ^ 20 * 2 ^ 16 = 2 ^ 36 := by decide
    omega
  have hE' : ∀ i, i < 15 →
      61 * M (parentRes c (i + 2) % 3) (Y X (i + 2)) ≤ 192 * N9 (parentRes c (i + 2)) (Y X (i + 2)) :=
    fun i hi => hE _ (hY i hi) _ (parentRes_lt _ _) (parentRes_mod_three _ _)
  have hsum : sumRange 15 (fun i => 61 * M (parentRes c (i + 2) % 3) (Y X (i + 2)))
      ≤ sumRange 15 (fun i => 192 * N9 (parentRes c (i + 2)) (Y X (i + 2))) :=
    sumRange_le hE'
  rw [sumRange_const_mul, sumRange_const_mul] at hsum
  omega

/-! ## 4. The claims, the certificate, the induction -/

/-- The claim at scale `3^j · 2^y`, class `c`: weight `(79/75)^(12y + 19j)`. -/
def claim (j y c : Nat) : Prop :=
  5 ≤ 3 ^ j * 2 ^ y →
    79 ^ (12 * y + 19 * j) ≤ 75 ^ (12 * y + 19 * j) * K * M c (3 ^ j * 2 ^ y)

/-- **The certificate**: the recursion's weights at ratio `(79/75)^12` beat the
loss `61/99` of the two balance hypotheses. -/
theorem cert :
    99 * 79 ^ (12 * 14 + 5) ≤ 61 * sumRange 15 (fun i => 79 ^ (12 * (14 - i)) * 75 ^ (12 * i + 5)) := by
  decide

/-- The base bound: below scale index `36` and type `12`, the weight is at most `K`. -/
theorem base_bound : ∀ j, j < 12 → ∀ y, y < 36 →
    79 ^ (12 * y + 19 * j) ≤ 75 ^ (12 * y + 19 * j) * K := by
  decide

theorem base {j y c : Nat} (hc : c = 1 ∨ c = 2) (hj : j < 12) (hy : y < 36) : claim j y c := by
  intro h5
  have hb := base_bound j hj y hy
  have hM := M_pos hc (X := 3 ^ j * 2 ^ y) h5
  calc 79 ^ (12 * y + 19 * j) ≤ 75 ^ (12 * y + 19 * j) * K := hb
    _ = 75 ^ (12 * y + 19 * j) * K * 1 := (Nat.mul_one _).symm
    _ ≤ 75 ^ (12 * y + 19 * j) * K * M c (3 ^ j * 2 ^ y) := Nat.mul_le_mul_left _ hM

theorem drop_scale (j y : Nat) (hj : 12 ≤ j) : 3 ^ (j - 12) * 2 ^ (y + 19) < 3 ^ j * 2 ^ y := by
  obtain ⟨d, rfl⟩ : ∃ d, j = d + 12 := ⟨j - 12, by omega⟩
  have e : d + 12 - 12 = d := by omega
  rw [e, Nat.pow_add 3 d 12, Nat.pow_add 2 y 19]
  have h : (2:Nat) ^ 19 < 3 ^ 12 := by decide
  have hp : 0 < 3 ^ d * 2 ^ y := Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  calc 3 ^ d * (2 ^ y * 2 ^ 19) = (3 ^ d * 2 ^ y) * 2 ^ 19 := by ac_rfl
    _ < (3 ^ d * 2 ^ y) * 3 ^ 12 := Nat.mul_lt_mul_of_pos_left h hp
    _ = 3 ^ d * 3 ^ 12 * 2 ^ y := by ac_rfl

/-- A claim of type `j ≥ 12` follows from the claim at `(j − 12, y + 19)`. -/
theorem drop {j y c : Nat} (hj : 12 ≤ j) (h : claim (j - 12) (y + 19) c) : claim j y c := by
  intro _
  have h5 : 5 ≤ 3 ^ (j - 12) * 2 ^ (y + 19) := by
    have h1 : (5:Nat) ≤ 2 ^ 19 := by decide
    have h2 : 1 ≤ 3 ^ (j - 12) := Nat.pow_pos (by decide)
    have h3 := Nat.mul_le_mul_right (2 ^ (y + 19)) h2
    have h4 : 2 ^ 19 ≤ 2 ^ (y + 19) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.one_mul] at h3
    exact Nat.le_trans (Nat.le_trans h1 h4) h3
  have hcl := h h5
  have e : 12 * (y + 19) + 19 * (j - 12) = 12 * y + 19 * j := by omega
  rw [e] at hcl
  have hmono := M_mono (c := c) (Nat.le_of_lt (drop_scale j y hj))
  exact Nat.le_trans hcl (Nat.mul_le_mul_left _ hmono)

/-- One summand of the step: the child claim, moved to the parents' scale. -/
theorem term {j y' i c' : Nat} (hy : 20 ≤ y') (hi : i < 15)
    (h : claim (j + 1) (y' + 14 - i) c') :
    79 ^ (12 * y' + 19 * j + 19 + 12 * (14 - i)) * 75 ^ (12 * i + 5)
      ≤ 75 ^ (12 * (y' + 16) + 19 * j) * K * M c' (Y (3 ^ j * 2 ^ (y' + 16)) (i + 2)) := by
  have h5 : 5 ≤ 3 ^ (j + 1) * 2 ^ (y' + 14 - i) := by
    have h1 : 1 ≤ 3 ^ (j + 1) := Nat.pow_pos (by decide)
    have h2 : 8 ≤ 2 ^ (y' + 14 - i) := by
      calc (8:Nat) = 2 ^ 3 := rfl
        _ ≤ 2 ^ (y' + 14 - i) := Nat.pow_le_pow_right (by decide) (by omega)
    have := Nat.mul_le_mul h1 h2
    rw [Nat.one_mul] at this
    exact Nat.le_trans (by decide) this
  have hcl := h h5
  have e1 : 12 * (y' + 14 - i) + 19 * (j + 1) = 12 * y' + 19 * j + 19 + 12 * (14 - i) := by omega
  rw [e1] at hcl
  -- the child's scale is at most the parents' scale `Y`
  have hscale : 3 ^ (j + 1) * 2 ^ (y' + 14 - i) ≤ Y (3 ^ j * 2 ^ (y' + 16)) (i + 2) := by
    unfold Y
    rw [Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))]
    have e2 : y' + 16 = (y' + 14 - i) + (i + 2) := by omega
    have : 3 ^ (j + 1) * 2 ^ (y' + 14 - i) * 2 ^ (i + 2) = 3 * (3 ^ j * 2 ^ (y' + 16)) := by
      rw [e2, Nat.pow_add 2 (y' + 14 - i) (i + 2), Nat.pow_succ]
      ac_rfl
    omega
  have hmono := M_mono (c := c') hscale
  have e3 : 12 * y' + 19 * j + 19 + 12 * (14 - i) + (12 * i + 5) = 12 * (y' + 16) + 19 * j := by
    omega
  calc 79 ^ (12 * y' + 19 * j + 19 + 12 * (14 - i)) * 75 ^ (12 * i + 5)
      ≤ 75 ^ (12 * y' + 19 * j + 19 + 12 * (14 - i)) * K * M c' (3 ^ (j + 1) * 2 ^ (y' + 14 - i))
          * 75 ^ (12 * i + 5) := Nat.mul_le_mul_right _ hcl
    _ = 75 ^ (12 * (y' + 16) + 19 * j) * K * M c' (3 ^ (j + 1) * 2 ^ (y' + 14 - i)) := by
        rw [← e3, Nat.pow_add 75 (12 * y' + 19 * j + 19 + 12 * (14 - i)) (12 * i + 5)]
        ac_rfl
    _ ≤ 75 ^ (12 * (y' + 16) + 19 * j) * K * M c' (Y (3 ^ j * 2 ^ (y' + 16)) (i + 2)) :=
        Nat.mul_le_mul_left _ hmono

/-- **The step.**  For `j < 12` and `y = y' + 16 ≥ 36`, the claim follows from the
claims at the fifteen child scales, all with strictly smaller bound. -/
theorem step (hE : Equi) (hB : Bal4) {j y' c : Nat} (hc : c = 1 ∨ c = 2) (hy : 20 ≤ y')
    (ih : ∀ i, i < 15 → ∀ c', (c' = 1 ∨ c' = 2) → claim (j + 1) (y' + 14 - i) c') :
    claim j (y' + 16) c := by
  intro _
  have hX : 2 ^ 36 ≤ 3 ^ j * 2 ^ (y' + 16) := by
    have h1 : 1 ≤ 3 ^ j := Nat.pow_pos (by decide)
    have h2 : 2 ^ 36 ≤ 2 ^ (y' + 16) := Nat.pow_le_pow_right (by decide) (by omega)
    have := Nat.mul_le_mul h1 h2
    rw [Nat.one_mul] at this
    exact this
  have hrec := count_rec hE hB hc hX
  -- the summed child claims
  have hterms : sumRange 15 (fun i => 79 ^ (12 * y' + 19 * j + 19 + 12 * (14 - i)) * 75 ^ (12 * i + 5))
      ≤ sumRange 15 (fun i => 75 ^ (12 * (y' + 16) + 19 * j) * K *
          M (parentRes c (i + 2) % 3) (Y (3 ^ j * 2 ^ (y' + 16)) (i + 2))) :=
    sumRange_le (fun i hi => term hy hi (ih i hi _ (parentRes_class hc)))
  rw [sumRange_const_mul] at hterms
  -- factor `79^f` out of the left side
  have hfact : sumRange 15 (fun i => 79 ^ (12 * y' + 19 * j + 19 + 12 * (14 - i)) * 75 ^ (12 * i + 5))
      = 79 ^ (12 * y' + 19 * j + 19) *
          sumRange 15 (fun i => 79 ^ (12 * (14 - i)) * 75 ^ (12 * i + 5)) := by
    rw [← sumRange_const_mul]
    exact sumRange_congr (fun i _ => by
      rw [Nat.pow_add 79 (12 * y' + 19 * j + 19) (12 * (14 - i)), Nat.mul_assoc])
  rw [hfact] at hterms
  have hef : 12 * (y' + 16) + 19 * j = 12 * y' + 19 * j + 19 + (12 * 14 + 5) := by omega
  -- assemble
  have h1 : 99 * 79 ^ (12 * (y' + 16) + 19 * j)
      ≤ 61 * (79 ^ (12 * y' + 19 * j + 19) *
          sumRange 15 (fun i => 79 ^ (12 * (14 - i)) * 75 ^ (12 * i + 5))) := by
    rw [hef, Nat.pow_add 79 (12 * y' + 19 * j + 19) (12 * 14 + 5), Nat.mul_left_comm 99,
      Nat.mul_left_comm 61]
    exact Nat.mul_le_mul_left _ cert
  have h2 := Nat.mul_le_mul_left 61 hterms
  have h3 : 61 * (75 ^ (12 * (y' + 16) + 19 * j) * K *
        sumRange 15 (fun i => M (parentRes c (i + 2) % 3) (Y (3 ^ j * 2 ^ (y' + 16)) (i + 2))))
      ≤ 99 * (75 ^ (12 * (y' + 16) + 19 * j) * K * M c (3 ^ j * 2 ^ (y' + 16))) := by
    rw [Nat.mul_left_comm 61, Nat.mul_left_comm 99]
    exact Nat.mul_le_mul_left _ hrec
  have h4 := Nat.le_trans h1 (Nat.le_trans h2 h3)
  exact Nat.le_of_mul_le_mul_left h4 (by decide)

/-- Every claim whose bound is at most `n`. -/
theorem claims_aux (hE : Equi) (hB : Bal4) : ∀ n, ∀ j y c, (c = 1 ∨ c = 2) →
    3 ^ j * 2 ^ y ≤ n → claim j y c := by
  intro n
  induction n with
  | zero =>
    intro j y c _ h
    have : 0 < 3 ^ j * 2 ^ y := Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
    omega
  | succ n ih =>
    intro j y c hc hbound
    rcases Nat.lt_or_ge (3 ^ j * 2 ^ y) (n + 1) with hlt | hge
    · exact ih j y c hc (by omega)
    · rcases Nat.lt_or_ge j 12 with hj | hj
      · rcases Nat.lt_or_ge y 36 with hy | hy
        · exact base hc hj hy
        · obtain ⟨y', rfl⟩ : ∃ y', y = y' + 16 := ⟨y - 16, by omega⟩
          apply step hE hB hc (by omega)
          intro i hi c' hc'
          apply ih (j + 1) (y' + 14 - i) c' hc'
          -- the child bound is below the parent bound
          have e2 : y' + 16 = (y' + 14 - i) + (i + 2) := by omega
          have h1 : 3 ^ (j + 1) * 2 ^ (y' + 14 - i) * 2 ^ (i + 2) = 3 * (3 ^ j * 2 ^ (y' + 16)) := by
            rw [e2, Nat.pow_add 2 (y' + 14 - i) (i + 2), Nat.pow_succ]
            ac_rfl
          have hX : 2 ^ 36 ≤ 3 ^ j * 2 ^ (y' + 16) := by
            have h1 : 1 ≤ 3 ^ j := Nat.pow_pos (by decide)
            have h2 : 2 ^ 36 ≤ 2 ^ (y' + 16) := Nat.pow_le_pow_right (by decide) (by omega)
            have := Nat.mul_le_mul h1 h2
            rw [Nat.one_mul] at this
            exact this
          have h2 : 4 ≤ 2 ^ (i + 2) := by
            have : (2:Nat) ^ 2 ≤ 2 ^ (i + 2) := Nat.pow_le_pow_right (by decide) (by omega)
            omega
          have h3 : 3 ^ (j + 1) * 2 ^ (y' + 14 - i) * 4 ≤ 3 ^ (j + 1) * 2 ^ (y' + 14 - i) * 2 ^ (i + 2) :=
            Nat.mul_le_mul_left _ h2
          omega
      · exact drop hj (ih (j - 12) (y + 19) c hc (by
          have := drop_scale j y hj
          omega))

/-- **Every claim holds.** -/
theorem claims (hE : Equi) (hB : Bal4) (j y c : Nat) (hc : c = 1 ∨ c = 2) : claim j y c :=
  claims_aux hE hB _ j y c hc (Nat.le_refl _)

/-! ## 5. The exponent `0.89` -/

theorem two_classes_le_count (X : Nat) : M 1 X + M 2 X ≤ reachesOneUpToCount X := by
  unfold reachesOneUpToCount
  rw [countUpTo_split (fun n => decide (n % 3 = 1)) X]
  apply Nat.add_le_add
  · unfold M
    apply countUpTo_mono
    intro n h1 h2 ⟨_, h3, h4⟩
    exact ⟨⟨by omega, h2, h4⟩, by show decide (n % 3 = 1) = true; rw [h3]; rfl⟩
  · unfold M
    apply countUpTo_mono
    intro n h1 h2 ⟨_, h3, h4⟩
    exact ⟨⟨by omega, h2, h4⟩, by show decide (n % 3 = 1) = false; rw [h3]; rfl⟩

theorem pow_ineq (y : Nat) : 2 ^ (89 * y) * 75 ^ (1200 * y) ≤ 79 ^ (1200 * y) := by
  rw [Nat.pow_mul, Nat.pow_mul, Nat.pow_mul, ← Nat.mul_pow]
  exact Nat.pow_le_pow_left (by decide) y

theorem pow_ineq2 (y : Nat) :
    2 ^ (89 * y) * 75 ^ (1200 * y + 3100) ≤ 79 ^ (1200 * y + 3100) := by
  rw [Nat.pow_add 75, Nat.pow_add 79, ← Nat.mul_assoc]
  exact Nat.mul_le_mul (pow_ineq y) (Nat.pow_le_pow_left (by decide) 3100)

/-- The cancellation at the end, with the products abstracted. -/
theorem arith_core {x P a b Q T : Nat} (hb : 0 < b) (hab : P * b ≤ a)
    (h : 2 ^ 100 * a ≤ b * Q) (hN : x < T * P) : x < T * Q := by
  have h1 : x * (b * 2 ^ 100) < T * P * (b * 2 ^ 100) :=
    Nat.mul_lt_mul_of_pos_right hN (Nat.mul_pos hb (Nat.pow_pos (by decide)))
  have h2 : T * P * (b * 2 ^ 100) ≤ (T * Q) * b := by
    calc T * P * (b * 2 ^ 100) = T * (P * b * 2 ^ 100) := by ac_rfl
      _ ≤ T * (a * 2 ^ 100) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hab)
      _ = T * (2 ^ 100 * a) := by ac_rfl
      _ ≤ T * (b * Q) := Nat.mul_le_mul_left _ h
      _ = (T * Q) * b := by ac_rfl
  have e : x * (b * 2 ^ 100) = (x * 2 ^ 100) * b := by ac_rfl
  rw [e] at h1
  have h3 := Nat.lt_of_mul_lt_mul_right (Nat.lt_of_lt_of_le h1 h2)
  have h5 : x ≤ x * 2 ^ 100 := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))
  omega

theorem K_pow : K ^ 100 = 10 ^ 1500 := by
  unfold K
  rw [← Nat.pow_mul]

/-- **At least `N ^ 0.89 / c` integers up to `N` reach `1`, if the tree of `1`
is balanced modulo `9` and modulo `4` within its classes modulo `3`.** -/
theorem count_balance (hE : Equi) (hB : Bal4) {N : Nat} (hN : 1 ≤ N) :
    N ^ 89 < 20 ^ 89 * 10 ^ 1500 * reachesOneUpToCount N ^ 100 := by
  have hc1 : 1 ≤ reachesOneUpToCount N := by
    have h := TreeHalf.count_mono hN
    have h1 : reachesOneUpToCount 1 = 1 := by decide
    omega
  rcases Nat.lt_or_ge N 10 with hsmall | hbig
  · have h1 : 1 ≤ reachesOneUpToCount N ^ 100 := Nat.pow_pos hc1
    have h2 : N ^ 89 ≤ 9 ^ 89 := Nat.pow_le_pow_left (by omega) 89
    have h3 : (9:Nat) ^ 89 < 20 ^ 89 * 10 ^ 1500 :=
      Nat.lt_of_lt_of_le (Nat.pow_lt_pow_left (by decide) (by decide))
        (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide)))
    have h4 : 20 ^ 89 * 10 ^ 1500 * 1 ≤ 20 ^ 89 * 10 ^ 1500 * reachesOneUpToCount N ^ 100 :=
      Nat.mul_le_mul_left _ h1
    omega
  obtain ⟨y, hy1, hy2⟩ := TreeHalf.exists_bracket_ten N hbig
  -- the two class claims at scale `3 · 2^(y+1) = 6 · 2^y ≤ N`
  have h2y : 1 ≤ 2 ^ y := Nat.pow_pos (by decide)
  have e3 : (3:Nat) ^ 1 = 3 := rfl
  have e21 : (2:Nat) ^ (y + 1) = 2 ^ y * 2 := Nat.pow_succ 2 y
  have h5 : 5 ≤ 3 ^ 1 * 2 ^ (y + 1) := by
    rw [e3, e21]; omega
  have hcl1 := claims hE hB 1 (y + 1) 1 (Or.inl rfl) h5
  have hcl2 := claims hE hB 1 (y + 1) 2 (Or.inr rfl) h5
  have hsc : 3 ^ 1 * 2 ^ (y + 1) ≤ N := by
    rw [e3, e21]; omega
  have hM : M 1 (3 ^ 1 * 2 ^ (y + 1)) + M 2 (3 ^ 1 * 2 ^ (y + 1)) ≤ reachesOneUpToCount N := by
    apply Nat.le_trans (Nat.add_le_add (M_mono hsc) (M_mono hsc))
    exact two_classes_le_count N
  have e : 12 * (y + 1) + 19 * 1 = 12 * y + 31 := by omega
  rw [e] at hcl1 hcl2
  have h1 : 2 * 79 ^ (12 * y + 31) ≤ 75 ^ (12 * y + 31) * K * reachesOneUpToCount N := by
    have := Nat.mul_le_mul_left (75 ^ (12 * y + 31) * K) hM
    rw [Nat.mul_add] at this
    omega
  have hh : 2 ^ 100 * 79 ^ (1200 * y + 3100)
      ≤ 75 ^ (1200 * y + 3100) * (K ^ 100 * reachesOneUpToCount N ^ 100) := by
    have h2 := Nat.pow_le_pow_left h1 100
    have eL : (2 * 79 ^ (12 * y + 31)) ^ 100 = 2 ^ 100 * 79 ^ (1200 * y + 3100) := by
      rw [Nat.mul_pow, ← Nat.pow_mul, show (12 * y + 31) * 100 = 1200 * y + 3100 by omega]
    have eR : (75 ^ (12 * y + 31) * K * reachesOneUpToCount N) ^ 100
        = 75 ^ (1200 * y + 3100) * (K ^ 100 * reachesOneUpToCount N ^ 100) := by
      rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul,
        show (12 * y + 31) * 100 = 1200 * y + 3100 by omega, Nat.mul_assoc]
    rw [eL, eR] at h2
    exact h2
  have hN2 : N ^ 89 < 20 ^ 89 * 2 ^ (89 * y) := by
    have := Nat.pow_lt_pow_left hy2 (show 89 ≠ 0 by decide)
    rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm y 89] at this
    exact this
  have hres := arith_core (Nat.pow_pos (by decide)) (pow_ineq2 y) hh hN2
  rw [K_pow] at hres
  calc N ^ 89 < 20 ^ 89 * (10 ^ 1500 * reachesOneUpToCount N ^ 100) := hres
    _ = 20 ^ 89 * 10 ^ 1500 * reachesOneUpToCount N ^ 100 := by rw [Nat.mul_assoc]

end TreeBalance
end Collatz
