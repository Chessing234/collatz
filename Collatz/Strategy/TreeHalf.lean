import Collatz.Strategy.Subtree
import Collatz.Strategy.ClassChild
import Collatz.Strategy.TreeCertificate

/-!
# At least `√N / c` integers up to `N` reach `1`

**Novelty tag: FORMALIZATION-OF-KNOWN** (the residue-class difference
inequalities of Krasikov 1989 / Krasikov–Lagarias 2003, at classes modulo `81`;
their exponent at this level is `0.53`, and `0.84` at classes modulo `3^11`).

## The claims

For a *root* `a` — odd, prime to `3`, at least `5`, reaching `1` — and the
subtree count `S a Y` of `Subtree`, with the certificate tables `A`, `B` of
`TreeCertificate` indexed by `a mod 81`, ratio `λ = 71/50` and scale `K`:

    claimF y a :  A (a % 81) · 71 ^ y ≤ 50 ^ y · K · S a (2 ^ y · a)
    claimH y a :  B (a % 81) · 71 ^ y ≤ 50 ^ y · K · S a (3 · 2 ^ y · a)

`claims` proves both for every `y` and every root, by a double induction:
strong in `y`, and for fixed `y` strong in the root `a`.  The base `y ≤ 22`
is `S ≥ 1` against `base_bound`.  The step `y ≥ 23` feeds each fertile child
`c = fch a i` (valuation `v = fval a i ≤ 18`, `3c + 1 = 2 ^ v a`) into
`Subtree.S_rec` at the bound `3 · 2 ^ (y−v) · c` (F-step) or
`3 · 2 ^ (y−v+1) · c` (H-step) — exactly `2 ^ y a − 2 ^ (y−v)` resp.
`2 ^ (y+1) a − 2 ^ (y−v+1)`, so the child bounds fit under the parent's with
slack `≥ 2 ^ 5 ≥ 18` — and reads off, for each child, the better of two
induction hypotheses: the H-claim one index down, or the F-claim reached
through `S_mono`.  The only child below its parent is the one at `v = 1`,
whose claim at the *same* index is supplied by the inner induction.  The
child's class is known modulo `27` only (`ClassChild.fch_mod_27`), so the
certificate carries the minimum of the tables over the three lifts
(`amin_le`).  The 108 resulting integer inequalities are `certF`, `certH`,
closed by `decide` in the generated file.

## The theorem

    count_sqrt : 1 ≤ N → N < 2 · 10 ^ 21 · (reachesOneUpToCount N) ^ 2

from `claimF y 5` and `(71/50) ^ 2 ≥ 2`.  The scalar of standing problem G6
moves from `3/8` to `1/2`.  The constant is what the trivial base case
`S ≥ 1` costs; it is not optimised.
-/

namespace Collatz
namespace TreeHalf

open TreeCount TreeBranching Subtree ClassChild TreeCertificate Collatz.Sum
  Papers.KrasikovLagarias2003

/-! ## 1. Roots and claims -/

/-- A root: odd, prime to `3`, at least `5`, reaching `1`. -/
def Root (a : Nat) : Prop := Good a ∧ 5 ≤ a ∧ ∃ t, acceleratedOrbit t a = 1

def claimF (y a : Nat) : Prop := A (a % 81) * 71 ^ y ≤ 50 ^ y * K * S a (2 ^ y * a)

def claimH (y a : Nat) : Prop := B (a % 81) * 71 ^ y ≤ 50 ^ y * K * S a (3 * 2 ^ y * a)

/-! ## 2. Children of a root -/

theorem fvalR_eq_fval (r i : Nat) : fvalR r i = fval r i := rfl

theorem fvalR_mod (a i : Nat) : fvalR (a % 81) i = fval a i := by
  rw [fvalR_eq_fval, ← fval_eq_mod_81]

theorem childRes_eq {a : Nat} (ha : Good a) (i : Nat) :
    childRes (a % 81) (fval a i) = fch a i % 27 := by
  unfold childRes
  rw [fch_mod_27 ha i, fval_eq_mod_81]

theorem root_fch {a : Nat} (ha : Root a) (i : Nat) : Root (fch a i) := by
  obtain ⟨hg, h5, t, ht⟩ := ha
  have hgc := fch_good hg i
  have h3 := three_fch hg i
  refine ⟨hgc, ?_, t + fval a i, ?_⟩
  · have hpow : 2 ^ fval a i * a ≥ 5 := by
      have : 1 ≤ 2 ^ fval a i := Nat.pow_pos (by decide)
      have := Nat.mul_le_mul this (Nat.le_refl a)
      omega
    have hne1 : fch a i ≠ 1 := by intro h; rw [h] at h3; omega
    have := hgc.1
    have := hgc.2
    omega
  · rw [← acceleratedOrbit_add, orbit_fch hg, ht]

theorem lift_le {a : Nat} (ha : Good a) (i : Nat) :
    Amin (fch a i % 27) ≤ A (fch a i % 81) ∧ Bmin (fch a i % 27) ≤ B (fch a i % 81) := by
  have h3 : (fch a i % 81) % 3 ≠ 0 := by
    rw [Nat.mod_mod_of_dvd _ (⟨27, rfl⟩ : (3:Nat) ∣ 81)]
    exact (fch_good ha i).2
  have h := amin_le (fch a i % 81) (Nat.mod_lt _ (by decide)) h3
  rw [Nat.mod_mod_of_dvd _ (⟨3, rfl⟩ : (27:Nat) ∣ 81)] at h
  exact h

theorem lt_of_val_one {a c : Nat} (h5 : 5 ≤ a) (h : 3 * c + 1 = 2 ^ 1 * a) : c < a := by
  rw [Nat.pow_one] at h
  omega

/-! ## 3. Scales -/

/-- `3 · 2 ^ (y−v) · c + 2 ^ (y−v) = 2 ^ y · a` when `3c + 1 = 2 ^ v a`. -/
theorem scale_identity {a c v y : Nat} (hv : v ≤ y) (h : 3 * c + 1 = 2 ^ v * a) :
    3 * (2 ^ (y - v) * c) + 2 ^ (y - v) = 2 ^ y * a := by
  have e : 2 ^ y = 2 ^ (y - v) * 2 ^ v := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [e, Nat.mul_assoc, ← h, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]

theorem two_pow_succ_mul' (n c : Nat) : 2 ^ (n + 1) * c = 2 * (2 ^ n * c) := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc]

theorem two_pow_add_two_mul' (n c : Nat) : 2 ^ (n + 2) * c = 4 * (2 ^ n * c) := by
  rw [Nat.pow_add, show (2:Nat) ^ 2 = 4 from rfl, Nat.mul_comm (2 ^ n) 4, Nat.mul_assoc]

theorem thirtytwo_le {y v : Nat} (h : v + 5 ≤ y) : 32 ≤ 2 ^ (y - v) := by
  have : 2 ^ 5 ≤ 2 ^ (y - v) := Nat.pow_le_pow_right (by decide) (by omega)
  exact this

/-! ## 4. One summand -/

theorem rearr {y e f s bb : Nat} (h : y - 18 + e = f) :
    71 ^ (y - 18) * (s * 71 ^ e * bb) = s * (71 ^ f * bb) := by
  rw [← h, Nat.pow_add, Nat.mul_assoc s, Nat.mul_left_comm (71 ^ (y - 18)) s,
    ← Nat.mul_assoc (71 ^ (y - 18))]

theorem term_le {m n y bb b t : Nat} (hmn : m + n = y) (hb : bb ≤ b)
    (h : b * 71 ^ n ≤ 50 ^ n * K * t) :
    50 ^ m * (71 ^ n * bb) ≤ 50 ^ y * K * t := by
  have h1 : 50 ^ m * (71 ^ n * bb) ≤ 50 ^ m * (b * 71 ^ n) := by
    rw [Nat.mul_comm b]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb)
  have h2 : 50 ^ m * (b * 71 ^ n) ≤ 50 ^ m * (50 ^ n * K * t) := Nat.mul_le_mul_left _ h
  have h3 : 50 ^ m * (50 ^ n * K * t) = 50 ^ y * K * t := by
    rw [← hmn, Nat.pow_add, Nat.mul_assoc (50 ^ m) (50 ^ n) K, Nat.mul_assoc (50 ^ m)]
  rw [← h3]
  exact Nat.le_trans h1 h2

theorem mul_max_le {x u w T : Nat} (hu : x * u ≤ T) (hw : x * w ≤ T) : x * max u w ≤ T := by
  rcases Nat.le_total u w with h | h
  · rw [Nat.max_eq_right h]; exact hw
  · rw [Nat.max_eq_left h]; exact hu

/-- The `F`-step summand of a child at valuation `v`. -/
theorem childF_bound {y v c cr Ar Br : Nat} (hy : 18 ≤ y) (hv1 : 1 ≤ v) (hv : v ≤ 18)
    (hA : Amin cr ≤ Ar) (hB : Bmin cr ≤ Br)
    (hH : Br * 71 ^ (y - v) ≤ 50 ^ (y - v) * K * S c (3 * 2 ^ (y - v) * c))
    (hF : Ar * 71 ^ (y - v + 1) ≤ 50 ^ (y - v + 1) * K * S c (3 * 2 ^ (y - v) * c)) :
    71 ^ (y - 18) * max (50 ^ v * 71 ^ (18 - v) * Bmin cr)
        (50 ^ (v - 1) * 71 ^ (18 - v + 1) * Amin cr)
      ≤ 50 ^ y * K * S c (3 * 2 ^ (y - v) * c) := by
  apply mul_max_le
  · rw [rearr (e := 18 - v) (f := y - v) (by omega)]
    exact term_le (by omega) hB hH
  · rw [rearr (e := 18 - v + 1) (f := y - v + 1) (by omega)]
    exact term_le (by omega) hA hF

/-- The `H`-step summand of a child at valuation `v`. -/
theorem childH_bound {y v c cr Ar Br : Nat} (hy : 18 ≤ y) (hv1 : 1 ≤ v) (hv : v ≤ 18)
    (hA : Amin cr ≤ Ar) (hB : Bmin cr ≤ Br)
    (hH : Br * 71 ^ (y - v + 1) ≤ 50 ^ (y - v + 1) * K * S c (3 * 2 ^ (y - v + 1) * c))
    (hF : 3 ≤ v → Ar * 71 ^ (y - v + 2) ≤ 50 ^ (y - v + 2) * K * S c (3 * 2 ^ (y - v + 1) * c)) :
    71 ^ (y - 18) * max (50 ^ (v - 1) * 71 ^ (18 - v + 1) * Bmin cr)
        (if 3 ≤ v then 50 ^ (v - 2) * 71 ^ (18 - v + 2) * Amin cr else 0)
      ≤ 50 ^ y * K * S c (3 * 2 ^ (y - v + 1) * c) := by
  apply mul_max_le
  · rw [rearr (e := 18 - v + 1) (f := y - v + 1) (by omega)]
    exact term_le (by omega) hB hH
  · by_cases h3 : 3 ≤ v
    · rw [if_pos h3, rearr (e := 18 - v + 2) (f := y - v + 2) (by omega)]
      exact term_le (by omega) hA (hF h3)
    · rw [if_neg h3, Nat.mul_zero]
      exact Nat.zero_le _

/-! ## 5. Assembly -/

theorem assemble {y Ar Y a : Nat} {c Yi term : Nat → Nat} (hy : 18 ≤ y)
    (hcert : Ar * 71 ^ 18 ≤ sumRange 6 term)
    (hrec : sumRange 6 (fun i => S (c i) (Yi i)) ≤ S a Y)
    (hterm : ∀ i, i < 6 → 71 ^ (y - 18) * term i ≤ 50 ^ y * K * S (c i) (Yi i)) :
    Ar * 71 ^ y ≤ 50 ^ y * K * S a Y := by
  have h1 : Ar * 71 ^ y = 71 ^ (y - 18) * (Ar * 71 ^ 18) := by
    rw [Nat.mul_left_comm, ← Nat.pow_add]
    congr 2
    omega
  have h2 : 71 ^ (y - 18) * (Ar * 71 ^ 18) ≤ 71 ^ (y - 18) * sumRange 6 term :=
    Nat.mul_le_mul_left _ hcert
  have h3 : 71 ^ (y - 18) * sumRange 6 term = sumRange 6 (fun i => 71 ^ (y - 18) * term i) :=
    (sumRange_const_mul 6 _ term).symm
  have h4 : sumRange 6 (fun i => 71 ^ (y - 18) * term i)
      ≤ sumRange 6 (fun i => 50 ^ y * K * S (c i) (Yi i)) := sumRange_le hterm
  have h5 : sumRange 6 (fun i => 50 ^ y * K * S (c i) (Yi i))
      = 50 ^ y * K * sumRange 6 (fun i => S (c i) (Yi i)) :=
    sumRange_const_mul 6 _ _
  have h6 : 50 ^ y * K * sumRange 6 (fun i => S (c i) (Yi i)) ≤ 50 ^ y * K * S a Y :=
    Nat.mul_le_mul_left _ hrec
  rw [h1]
  exact Nat.le_trans h2 (Nat.le_trans (h3 ▸ h4) (Nat.le_trans (h5 ▸ Nat.le_refl _) h6))

/-! ## 6. The inductive step -/

theorem step {y a : Nat} (hy : 23 ≤ y) (ha : Root a)
    (ihO : ∀ y' c, y' < y → Root c → claimF y' c ∧ claimH y' c)
    (ihI : ∀ c, c < a → Root c → claimF y c ∧ claimH y c) :
    claimF y a ∧ claimH y a := by
  obtain ⟨hg, h5, ht⟩ := ha
  have r_lt : a % 81 < 81 := Nat.mod_lt _ (by decide)
  have r_3 : (a % 81) % 3 ≠ 0 := by
    rw [Nat.mod_mod_of_dvd a (⟨27, rfl⟩ : (3:Nat) ∣ 81)]
    exact hg.2
  have hy18 : 18 ≤ y := by omega
  -- per-child data
  have hv1 : ∀ i, 1 ≤ fval a i := fun i => fval_pos a i
  have hv18 : ∀ i, i < 6 → fval a i ≤ 18 := fun i hi =>
    Nat.le_trans (fval_le_tmpl a i) (tmpl_le_18 hi)
  have h3c : ∀ i, 3 * fch a i + 1 = 2 ^ fval a i * a := fun i => three_fch hg i
  have hroot : ∀ i, Root (fch a i) := fun i => root_fch ⟨hg, h5, ht⟩ i
  have hlift := lift_le hg
  -- the child at v = 1 is below its parent
  have hlt : ∀ i, fval a i = 1 → fch a i < a := by
    intro i h1
    have h := h3c i
    rw [h1] at h
    exact lt_of_val_one h5 h
  constructor
  · -- the F-claim
    unfold claimF
    have hbudget : ∀ i, i < 6 → 3 * 2 ^ (y - fval a i) * fch a i + 18 ≤ 2 ^ y * a := by
      intro i hi
      have hid := scale_identity (y := y) (by have := hv18 i hi; omega) (h3c i)
      have h32 := thirtytwo_le (y := y) (v := fval a i) (by have := hv18 i hi; omega)
      rw [Nat.mul_assoc]
      omega
    apply assemble hy18 (certF (a % 81) r_lt r_3)
      (S_rec (fun i => 3 * 2 ^ (y - fval a i) * fch a i) hg h5 ht hbudget)
    intro i hi
    rw [fvalR_mod, childRes_eq hg i]
    have hv := hv18 i hi
    -- the H-claim of the child one index down
    have hH := (ihO (y - fval a i) (fch a i) (by have := hv1 i; omega) (hroot i)).2
    unfold claimH at hH
    -- the F-claim of the child at index y - v + 1, moved to the same bound
    have hF : claimF (y - fval a i + 1) (fch a i) := by
      rcases Nat.lt_or_ge 1 (fval a i) with h2 | h2
      · exact (ihO (y - fval a i + 1) (fch a i) (by omega) (hroot i)).1
      · have h1 : fval a i = 1 := by have := hv1 i; omega
        have e : y - fval a i + 1 = y := by omega
        rw [e]
        exact (ihI (fch a i) (hlt i h1) (hroot i)).1
    unfold claimF at hF
    have hmono : S (fch a i) (2 ^ (y - fval a i + 1) * fch a i)
        ≤ S (fch a i) (3 * 2 ^ (y - fval a i) * fch a i) := by
      apply S_mono
      rw [two_pow_succ_mul', Nat.mul_assoc]
      omega
    have hF' := Nat.le_trans hF (Nat.mul_le_mul_left _ hmono)
    exact childF_bound hy18 (hv1 i) hv (hlift i).1 (hlift i).2 hH hF'
  · -- the H-claim
    unfold claimH
    have hbudget : ∀ i, i < 6 →
        3 * 2 ^ (y - fval a i + 1) * fch a i + 18 ≤ 3 * 2 ^ y * a := by
      intro i hi
      have hid := scale_identity (y := y) (by have := hv18 i hi; omega) (h3c i)
      have h32 := thirtytwo_le (y := y) (v := fval a i) (by have := hv18 i hi; omega)
      rw [Nat.mul_assoc, two_pow_succ_mul', Nat.mul_assoc 3 (2 ^ y) a]
      omega
    apply assemble hy18 (certH (a % 81) r_lt r_3)
      (S_rec (fun i => 3 * 2 ^ (y - fval a i + 1) * fch a i) hg h5 ht hbudget)
    intro i hi
    rw [fvalR_mod, childRes_eq hg i]
    have hv := hv18 i hi
    -- the H-claim of the child at index y - v + 1
    have hH : claimH (y - fval a i + 1) (fch a i) := by
      rcases Nat.lt_or_ge 1 (fval a i) with h2 | h2
      · exact (ihO (y - fval a i + 1) (fch a i) (by omega) (hroot i)).2
      · have h1 : fval a i = 1 := by have := hv1 i; omega
        have e : y - fval a i + 1 = y := by omega
        rw [e]
        exact (ihI (fch a i) (hlt i h1) (hroot i)).2
    unfold claimH at hH
    -- the F-claim of the child at index y - v + 2, when v ≥ 3
    have hF : 3 ≤ fval a i → A (fch a i % 81) * 71 ^ (y - fval a i + 2)
        ≤ 50 ^ (y - fval a i + 2) * K * S (fch a i) (3 * 2 ^ (y - fval a i + 1) * fch a i) := by
      intro h3
      have h := (ihO (y - fval a i + 2) (fch a i) (by omega) (hroot i)).1
      unfold claimF at h
      have hmono : S (fch a i) (2 ^ (y - fval a i + 2) * fch a i)
          ≤ S (fch a i) (3 * 2 ^ (y - fval a i + 1) * fch a i) := by
        apply S_mono
        rw [two_pow_add_two_mul', Nat.mul_assoc, two_pow_succ_mul']
        omega
      exact Nat.le_trans h (Nat.mul_le_mul_left _ hmono)
    exact childH_bound hy18 (hv1 i) hv (hlift i).1 (hlift i).2 hH hF

/-! ## 7. The double induction -/

theorem base {y a : Nat} (hy : y ≤ 22) (ha : Root a) : claimF y a ∧ claimH y a := by
  obtain ⟨hg, _, _⟩ := ha
  have hb := base_bound (a % 81) (Nat.mod_lt _ (by decide)) y hy
  have hpow : 1 ≤ 2 ^ y := Nat.pow_pos (by decide)
  have hle1 : a ≤ 2 ^ y * a := by
    have := Nat.mul_le_mul_right a hpow
    omega
  have hle2 : a ≤ 3 * 2 ^ y * a := by
    have := Nat.mul_le_mul_right a (show 1 ≤ 3 * 2 ^ y by omega)
    omega
  have hS1 := S_pos hg hle1
  have hS2 := S_pos hg hle2
  constructor
  · unfold claimF
    have := Nat.mul_le_mul_left (50 ^ y * K) hS1
    omega
  · unfold claimH
    have := Nat.mul_le_mul_left (50 ^ y * K) hS2
    omega

theorem claims_aux : ∀ n, ∀ y, y ≤ n → ∀ N, ∀ a, a < N → Root a → claimF y a ∧ claimH y a := by
  intro n
  induction n with
  | zero =>
    intro y hy N a _ ha
    exact base (by omega) ha
  | succ n ihn =>
    intro y hy N
    induction N with
    | zero => intro a ha; omega
    | succ N ihN =>
      intro a haN ha
      rcases Nat.lt_or_ge a N with hlt | hge
      · exact ihN a hlt ha
      · have haN' : a = N := by omega
        subst haN'
        by_cases hyn : y ≤ n
        · exact ihn y hyn (a + 1) a (Nat.lt_succ_self a) ha
        · have hy' : y = n + 1 := by omega
          by_cases h22 : y ≤ 22
          · exact base h22 ha
          · apply step (by omega) ha
            · intro y' c hy'c hc
              exact ihn y' (by omega) (c + 1) c (Nat.lt_succ_self c) hc
            · intro c hc hcr
              exact ihN c hc hcr

/-- **Both claims hold for every root at every scale.** -/
theorem claims (y a : Nat) (ha : Root a) : claimF y a ∧ claimH y a :=
  claims_aux y y (Nat.le_refl y) (a + 1) a (Nat.lt_succ_self a) ha

/-! ## 8. The exponent `1/2` -/

theorem root_five : Root 5 := ⟨⟨rfl, by decide⟩, Nat.le_refl 5, 4, by decide⟩

theorem A_five_pos : 1 ≤ A 5 := by decide

theorem count_mono {M N : Nat} (h : M ≤ N) : reachesOneUpToCount M ≤ reachesOneUpToCount N := by
  unfold reachesOneUpToCount
  apply Nat.le_trans (countUpTo_le_of_le (p := fun n => 0 < n ∧ n ≤ M ∧ reachesOneBy n M = true) h)
  apply countUpTo_mono
  intro n _ _ ⟨h1, h2, h3⟩
  exact ⟨h1, by omega, TreeBranching.reachesOneBy_mono h h3⟩

theorem exists_bracket_ten : ∀ N, 10 ≤ N → ∃ y, 10 * 2 ^ y ≤ N ∧ N < 20 * 2 ^ y := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ N ih =>
    intro hN
    by_cases h10 : N < 10
    · have : N + 1 = 10 := by omega
      exact ⟨0, by omega, by omega⟩
    · obtain ⟨y, hy1, hy2⟩ := ih (by omega)
      by_cases hlt : N + 1 < 20 * 2 ^ y
      · exact ⟨y, by omega, hlt⟩
      · refine ⟨y + 1, ?_, ?_⟩
        · rw [Nat.pow_succ]; omega
        · rw [Nat.pow_succ]
          have : 1 ≤ 2 ^ y := Nat.pow_pos (by decide)
          omega

theorem seventyone_sq (y : Nat) : 2 ^ y * 2500 ^ y ≤ 71 ^ (2 * y) := by
  rw [Nat.pow_mul, ← Nat.mul_pow]
  exact Nat.pow_le_pow_left (by decide) y

theorem K_sq : K ^ 2 = 100000000000000000000 := by decide

/-- **At least `√N / c` integers up to `N` reach `1`.**  For every `N ≥ 1`,
`N < 2 · 10 ^ 21 · (reachesOneUpToCount N) ^ 2`. -/
theorem count_sqrt {N : Nat} (hN : 1 ≤ N) :
    N < 2000000000000000000000 * reachesOneUpToCount N ^ 2 := by
  have hc1 : 1 ≤ reachesOneUpToCount N := by
    have h := count_mono hN
    have h1 : reachesOneUpToCount 1 = 1 := by decide
    omega
  rcases Nat.lt_or_ge N 10 with hsmall | hbig
  · have : 1 ≤ reachesOneUpToCount N ^ 2 := Nat.pow_pos hc1
    omega
  obtain ⟨y, hy1, hy2⟩ := exists_bracket_ten N hbig
  have hcl := (claims y 5 root_five).1
  unfold claimF at hcl
  have hA := A_five_pos
  have hS : S 5 (2 ^ y * 5) ≤ reachesOneUpToCount N := by
    apply Nat.le_trans (S_five_le_count (2 ^ y * 5))
    apply count_mono
    omega
  -- 71 ^ y ≤ 50 ^ y * K * count N
  have h1 : 71 ^ y ≤ 50 ^ y * K * reachesOneUpToCount N := by
    have h5 : 5 % 81 = 5 := rfl
    rw [h5] at hcl
    have : 1 * 71 ^ y ≤ A 5 * 71 ^ y := Nat.mul_le_mul_right _ hA
    have := Nat.mul_le_mul_left (50 ^ y * K) hS
    omega
  -- square it
  have h2 : (71 ^ y) ^ 2 ≤ (50 ^ y * K * reachesOneUpToCount N) ^ 2 := Nat.pow_le_pow_left h1 2
  have hL : (71 ^ y) ^ 2 = 71 ^ (2 * y) := by rw [← Nat.pow_mul, Nat.mul_comm]
  have hR : (50 ^ y * K * reachesOneUpToCount N) ^ 2
      = 2500 ^ y * (K ^ 2 * reachesOneUpToCount N ^ 2) := by
    rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm y 2, Nat.pow_mul,
      show (50:Nat) ^ 2 = 2500 from rfl, Nat.mul_assoc]
  rw [hL, hR, K_sq] at h2
  have h3 := Nat.le_trans (seventyone_sq y) h2
  -- cancel 2500 ^ y
  have h4 : 2500 ^ y * 2 ^ y ≤ 2500 ^ y * (100000000000000000000 * reachesOneUpToCount N ^ 2) := by
    rw [Nat.mul_comm (2500 ^ y) (2 ^ y)]
    exact h3
  have h5 : 2 ^ y ≤ 100000000000000000000 * reachesOneUpToCount N ^ 2 :=
    Nat.le_of_mul_le_mul_left h4 (Nat.pow_pos (by decide))
  omega

end TreeHalf
end Collatz
