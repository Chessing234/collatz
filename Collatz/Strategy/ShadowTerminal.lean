import Collatz.Strategy.ShadowDecoder

/-! Exact dependence of a finite shadow on its terminal value. These are
finite identities; they supply no uniform bound over prefix lengths. -/
namespace Collatz.ShadowTerminal
open ShadowDecoder

def multiplier : Nat → (Nat → Nat) → Rat
  | 0, _ => 1
  | L + 1, c => (c 0 : Rat) / 3 * multiplier L (fun i => c (i + 1))

def backward : Nat → (Nat → Nat) → Rat → Rat
  | 0, _, z => z
  | L + 1, c, z => ((c 0 : Rat) * backward L (fun i => c (i + 1)) z + 1) / 3

theorem backward_one (L : Nat) (c : Nat → Nat) :
    backward L c 1 = encode L c 0 := by
  induction L generalizing c with
  | zero => rfl
  | succ L ih => simp only [backward, encode, ih]

/-- Terminal uncertainty is multiplied by the exact inverse orbit multiplier. -/
theorem terminal_difference (L : Nat) (c : Nat → Nat) (z w : Rat) :
    backward L c z - backward L c w = multiplier L c * (z - w) := by
  induction L generalizing c with
  | zero => simp [backward, multiplier]
  | succ L ih =>
    have h := ih (fun i => c (i + 1))
    simp only [backward, multiplier]
    grind

/-- The same multiplier also transports the actual integer endpoint.
Changing the certificate horizon therefore cannot be treated as fixing
its start value. -/
theorem endpoint_identity (L : Nat) (c x : Nat → Nat)
    (hstep : ∀ i < L, c i * x (i + 1) = 3 * x i + 1) :
    (x 0 : Rat) + encode L c 0 = multiplier L c * ((x L : Rat) + 1) := by
  induction L generalizing c x with
  | zero => simp [encode, multiplier]
  | succ L ih =>
    have ht := ih (fun i => c (i + 1)) (fun i => x (i + 1))
      (fun i hi => hstep (i + 1) (by omega))
    have hs := congrArg (fun n : Nat => (n : Rat)) (hstep 0 (by omega))
    simp only [Rat.natCast_mul, Rat.natCast_add] at hs
    simp only [encode, multiplier]
    grind

theorem all_two_encoder (L : Nat) : encode L (fun _ => 2) 0 = 1 := by
  induction L with
  | zero => rfl
  | succ L ih => simp only [encode]; rw [ih]; grind

/-- Perfectly compatible constant shadows do not guarantee an infinite
natural-number trajectory with that coefficient word. -/
theorem all_two_not_realizable (x : Nat → Nat) :
    ¬ (∀ i, 2 * x (i + 1) = 3 * x i + 1) := by
  intro h
  have hd (L : Nat) : 2 ^ L ∣ x 0 + 1 := by
    apply even_block_dvd L (fun _ => 2) (fun i => x i + 1)
    · intro i hi; exact Nat.dvd_refl 2
    · intro i hi; have := h i; omega
  have hb := Nat.le_of_dvd (by omega : 0 < x 0 + 1) (hd (x 0 + 1))
  have hp := Arith.lt_two_pow_self (x 0 + 1)
  omega

theorem constant_multiplier (L c : Nat) :
    multiplier L (fun _ => c) = ((c : Rat) / 3) ^ L := by
  induction L with
  | zero => simp [multiplier]
  | succ L ih => simp only [multiplier, ih]; grind

/-- Even the actual fixed orbit at 1 has an exponentially growing sequence
of terminal-one encodings. A uniform encoder bound is not automatic. -/
theorem fixed_one_encoder (L : Nat) :
    encode L (fun _ => 4) 0 = 2 * (4 / 3 : Rat) ^ L - 1 := by
  have h := endpoint_identity L (fun _ => 4) (fun _ => 1) (by intros; decide)
  rw [constant_multiplier] at h
  grind

end Collatz.ShadowTerminal
