import Collatz.Basic

/-!
# Turning a block lower bound into a one-step lower bound

This is an elementary positive-operator identity, not a solution of Collatz.
It records the algebra needed by `Devices/MultiscaleSyracuse.md` without
assuming the unproved block bound in that investigation.

All coefficients are natural numbers, so a rational finite transfer can be
handled after clearing its denominator. The hypotheses on `L` are explicit.
-/

namespace Collatz.BlockPotential

variable {ι : Type}

def orbit (L : (ι → Nat) → (ι → Nat)) (g : ι → Nat) : Nat → ι → Nat
  | 0 => g
  | n + 1 => L (orbit L g n)

/-- `B^(n-1) g + B^(n-2) Lg + ... + L^(n-1)g`. -/
def potential (L : (ι → Nat) → (ι → Nat)) (g : ι → Nat) (B : Nat) :
    Nat → ι → Nat
  | 0 => fun _ => 0
  | n + 1 => fun x => B * potential L g B n x + orbit L g n x

/-- The exact telescoping identity; no positivity or block bound is assumed. -/
theorem telescope (L : (ι → Nat) → (ι → Nat))
    (hzero : L (fun _ => 0) = fun _ => 0)
    (hadd : ∀ f h, L (fun x => f x + h x) = fun x => L f x + L h x)
    (hscale : ∀ b f, L (fun x => b * f x) = fun x => b * L f x)
    (g : ι → Nat) (B n : Nat) (x : ι) :
    L (potential L g B n) x + B ^ n * g x =
      B * potential L g B n x + orbit L g n x := by
  induction n with
  | zero => simp [potential, orbit, hzero]
  | succ n ih =>
    change L (fun y => B * potential L g B n y + orbit L g n y) x +
      B ^ (n + 1) * g x =
      B * (B * potential L g B n x + orbit L g n x) +
        L (orbit L g n) x
    rw [hadd, hscale, Nat.pow_succ']
    have hm := congrArg (fun z => B * z) ih
    simp only [Nat.mul_add, Nat.mul_assoc] at hm ⊢
    omega

/-- A certified block bound gives a certified one-step bound. Proving its
block-bound hypothesis for useful Collatz operators remains separate work. -/
theorem one_step_of_block (L : (ι → Nat) → (ι → Nat))
    (hzero : L (fun _ => 0) = fun _ => 0)
    (hadd : ∀ f h, L (fun x => f x + h x) = fun x => L f x + L h x)
    (hscale : ∀ b f, L (fun x => b * f x) = fun x => b * L f x)
    (g : ι → Nat) (B n : Nat)
    (hblock : ∀ x, B ^ n * g x ≤ orbit L g n x) :
    ∀ x, B * potential L g B n x ≤ L (potential L g B n) x := by
  intro x
  have := telescope L hzero hadd hscale g B n x
  have := hblock x
  omega

theorem potential_pos (L : (ι → Nat) → (ι → Nat))
    (g : ι → Nat) {B n : Nat} (hB : 0 < B) (hn : 0 < n)
    {x : ι} (hg : 0 < g x) : 0 < potential L g B n x := by
  cases n with
  | zero => omega
  | succ n =>
    induction n with
    | zero => simpa [potential, orbit] using hg
    | succ n ih =>
      have hp : 0 < B * potential L g B (n + 1) x :=
        Nat.mul_pos hB (ih (by omega))
      change 0 < B * potential L g B (n + 1) x + orbit L g (n + 1) x
      omega

/-- Iteration preserves pointwise comparison for an order-preserving operator. -/
theorem orbit_mono (L : (ι → Nat) → (ι → Nat))
    (hmono : ∀ f h, (∀ x, f x ≤ h x) → ∀ x, L f x ≤ L h x)
    {f h : ι → Nat} (hle : ∀ x, f x ≤ h x) (n : Nat) :
    ∀ x, orbit L f n x ≤ orbit L h n x := by
  induction n with
  | zero => exact hle
  | succ n ih => exact hmono _ _ ih

theorem orbit_scale (L : (ι → Nat) → (ι → Nat))
    (hscale : ∀ b f, L (fun x => b * f x) = fun x => b * L f x)
    (b : Nat) (g : ι → Nat) (n : Nat) :
    orbit L (fun x => b * g x) n = fun x => b * orbit L g n x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [orbit, ih, hscale]

theorem orbit_subeigen (L : (ι → Nat) → (ι → Nat))
    (hmono : ∀ f h, (∀ x, f x ≤ h x) → ∀ x, L f x ≤ L h x)
    (hscale : ∀ b f, L (fun x => b * f x) = fun x => b * L f x)
    (w : ι → Nat) (B : Nat) (hstep : ∀ x, B * w x ≤ L w x)
    (n : Nat) : ∀ x, B ^ n * w x ≤ orbit L w n x := by
  induction n with
  | zero => intro x; simp [orbit]
  | succ n ih =>
    intro x
    have h := hmono _ _ ih x
    rw [hscale] at h
    have hs := Nat.mul_le_mul_left (B ^ n) (hstep x)
    rw [Nat.pow_succ]
    exact Nat.le_trans (by simpa only [Nat.mul_assoc] using hs) h

/-- Conversely, a uniformly bounded positive certificate forces exponential
block lower bounds, up to its fixed upper/lower comparison constants.
Thus searching for block bounds does not by itself add a new source of
Collatz estimates to the one-step certificate method. -/
theorem block_of_certificate (L : (ι → Nat) → (ι → Nat))
    (hmono : ∀ f h, (∀ x, f x ≤ h x) → ∀ x, L f x ≤ L h x)
    (hscale : ∀ b f, L (fun x => b * f x) = fun x => b * L f x)
    (g w : ι → Nat) (a b B : Nat)
    (hlow : ∀ x, a * g x ≤ w x)
    (hupp : ∀ x, w x ≤ b * g x)
    (hstep : ∀ x, B * w x ≤ L w x) (n : Nat) (x : ι) :
    B ^ n * (a * g x) ≤ b * orbit L g n x := by
  have h1 := Nat.mul_le_mul_left (B ^ n) (hlow x)
  have h2 := orbit_subeigen L hmono hscale w B hstep n x
  have h3 := orbit_mono L hmono hupp n x
  rw [orbit_scale L hscale] at h3
  exact Nat.le_trans h1 (Nat.le_trans h2 h3)

end Collatz.BlockPotential
