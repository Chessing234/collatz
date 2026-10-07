import Collatz.Basic

/-! Division-free certificates for the fifty terminal transition prefixes.
Interval bounds and halving/3x+1 equations are explicit premises. Parity is not needed.
The rational generator guides the proof; Lean checks every leaf. -/
namespace Collatz.Exploration.FiveBandArithmetic

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- Transition prefix `000` cannot remain in [b,5b] for b>1. -/
theorem prefix_000
    (b x0 x1 x2 x3 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h3 : b ≤ x3 ∧ x3 ≤ 5*b)
    (r0 : 2*x1 = x0)
    (r1 : 2*x2 = x1)
    (r2 : 2*x3 = x2)
    : False := by
  omega

/-- Transition prefix `001000` cannot remain in [b,5b] for b>1. -/
theorem prefix_001000
    (b x0 x1 x2 x3 x4 x5 x6 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h6 : b ≤ x6 ∧ x6 ≤ 5*b)
    (r0 : 2*x1 = x0)
    (r1 : 2*x2 = x1)
    (r2 : x3 = 3*x2+1)
    (r3 : 2*x4 = x3)
    (r4 : 2*x5 = x4)
    (r5 : 2*x6 = x5)
    : False := by
  omega

/-- Transition prefix `00100100` cannot remain in [b,5b] for b>1. -/
theorem prefix_00100100
    (b x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h8 : b ≤ x8 ∧ x8 ≤ 5*b)
    (r0 : 2*x1 = x0)
    (r1 : 2*x2 = x1)
    (r2 : x3 = 3*x2+1)
    (r3 : 2*x4 = x3)
    (r4 : 2*x5 = x4)
    (r5 : x6 = 3*x5+1)
    (r6 : 2*x7 = x6)
    (r7 : 2*x8 = x7)
    : False := by
  omega

/-- Transition prefix `00100101` cannot remain in [b,5b] for b>1. -/
theorem prefix_00100101
    (b x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h5 : b ≤ x5 ∧ x5 ≤ 5*b)
    (h8 : b ≤ x8 ∧ x8 ≤ 5*b)
    (r0 : 2*x1 = x0)
    (r1 : 2*x2 = x1)
    (r2 : x3 = 3*x2+1)
    (r3 : 2*x4 = x3)
    (r4 : 2*x5 = x4)
    (r5 : x6 = 3*x5+1)
    (r6 : 2*x7 = x6)
    (r7 : x8 = 3*x7+1)
    : False := by
  omega

/-- Transition prefix `0010011` cannot remain in [b,5b] for b>1. -/
theorem prefix_0010011
    (b x2 x3 x4 x5 x6 x7 : Nat) (hb : 1 < b)
    (h2 : b ≤ x2 ∧ x2 ≤ 5*b)
    (h7 : b ≤ x7 ∧ x7 ≤ 5*b)
    (r2 : x3 = 3*x2+1)
    (r3 : 2*x4 = x3)
    (r4 : 2*x5 = x4)
    (r5 : x6 = 3*x5+1)
    (r6 : x7 = 3*x6+1)
    : False := by
  omega

/-- Transition prefix `00101000` cannot remain in [b,5b] for b>1. -/
theorem prefix_00101000
    (b x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h8 : b ≤ x8 ∧ x8 ≤ 5*b)
    (r0 : 2*x1 = x0)
    (r1 : 2*x2 = x1)
    (r2 : x3 = 3*x2+1)
    (r3 : 2*x4 = x3)
    (r4 : x5 = 3*x4+1)
    (r5 : 2*x6 = x5)
    (r6 : 2*x7 = x6)
    (r7 : 2*x8 = x7)
    : False := by
  omega

/-- Transition prefix `0010100100` cannot remain in [b,5b] for b>1. -/
theorem prefix_0010100100
    (b x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat) (hb : 1 < b)
    (h2 : b ≤ x2 ∧ x2 ≤ 5*b)
    (h5 : b ≤ x5 ∧ x5 ≤ 5*b)
    (h10 : b ≤ x10 ∧ x10 ≤ 5*b)
    (r2 : x3 = 3*x2+1)
    (r3 : 2*x4 = x3)
    (r4 : x5 = 3*x4+1)
    (r5 : 2*x6 = x5)
    (r6 : 2*x7 = x6)
    (r7 : x8 = 3*x7+1)
    (r8 : 2*x9 = x8)
    (r9 : 2*x10 = x9)
    : False := by
  omega

/-- Transition prefix `0010100101` cannot remain in [b,5b] for b>1. -/
theorem prefix_0010100101
    (b x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat) (hb : 1 < b)
    (h2 : b ≤ x2 ∧ x2 ≤ 5*b)
    (h10 : b ≤ x10 ∧ x10 ≤ 5*b)
    (r2 : x3 = 3*x2+1)
    (r3 : 2*x4 = x3)
    (r4 : x5 = 3*x4+1)
    (r5 : 2*x6 = x5)
    (r6 : 2*x7 = x6)
    (r7 : x8 = 3*x7+1)
    (r8 : 2*x9 = x8)
    (r9 : x10 = 3*x9+1)
    : False := by
  omega

/-- Transition prefix `001010011` cannot remain in [b,5b] for b>1. -/
theorem prefix_001010011
    (b x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ x1 ≤ 5*b)
    (h9 : b ≤ x9 ∧ x9 ≤ 5*b)
    (r1 : 2*x2 = x1)
    (r2 : x3 = 3*x2+1)
    (r3 : 2*x4 = x3)
    (r4 : x5 = 3*x4+1)
    (r5 : 2*x6 = x5)
    (r6 : 2*x7 = x6)
    (r7 : x8 = 3*x7+1)
    (r8 : x9 = 3*x8+1)
    : False := by
  omega

/-- Transition prefix `0010101` cannot remain in [b,5b] for b>1. -/
theorem prefix_0010101
    (b x2 x3 x4 x5 x6 x7 : Nat) (hb : 1 < b)
    (h2 : b ≤ x2 ∧ x2 ≤ 5*b)
    (h7 : b ≤ x7 ∧ x7 ≤ 5*b)
    (r2 : x3 = 3*x2+1)
    (r3 : 2*x4 = x3)
    (r4 : x5 = 3*x4+1)
    (r5 : 2*x6 = x5)
    (r6 : x7 = 3*x6+1)
    : False := by
  omega

/-- Transition prefix `001011` cannot remain in [b,5b] for b>1. -/
theorem prefix_001011
    (b x1 x2 x3 x4 x5 x6 : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ x1 ≤ 5*b)
    (h6 : b ≤ x6 ∧ x6 ≤ 5*b)
    (r1 : 2*x2 = x1)
    (r2 : x3 = 3*x2+1)
    (r3 : 2*x4 = x3)
    (r4 : x5 = 3*x4+1)
    (r5 : x6 = 3*x5+1)
    : False := by
  omega

/-- Transition prefix `0011` cannot remain in [b,5b] for b>1. -/
theorem prefix_0011
    (b x2 x3 x4 : Nat) (hb : 1 < b)
    (h2 : b ≤ x2 ∧ x2 ≤ 5*b)
    (h4 : b ≤ x4 ∧ x4 ≤ 5*b)
    (r2 : x3 = 3*x2+1)
    (r3 : x4 = 3*x3+1)
    : False := by
  omega

/-- Transition prefix `01000` cannot remain in [b,5b] for b>1. -/
theorem prefix_01000
    (b x2 x3 x4 x5 : Nat) (hb : 1 < b)
    (h2 : b ≤ x2 ∧ x2 ≤ 5*b)
    (h5 : b ≤ x5 ∧ x5 ≤ 5*b)
    (r2 : 2*x3 = x2)
    (r3 : 2*x4 = x3)
    (r4 : 2*x5 = x4)
    : False := by
  omega

/-- Transition prefix `01001000` cannot remain in [b,5b] for b>1. -/
theorem prefix_01001000
    (b x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h8 : b ≤ x8 ∧ x8 ≤ 5*b)
    (r0 : 2*x1 = x0)
    (r1 : x2 = 3*x1+1)
    (r2 : 2*x3 = x2)
    (r3 : 2*x4 = x3)
    (r4 : x5 = 3*x4+1)
    (r5 : 2*x6 = x5)
    (r6 : 2*x7 = x6)
    (r7 : 2*x8 = x7)
    : False := by
  omega

/-- Transition prefix `0100100100` cannot remain in [b,5b] for b>1. -/
theorem prefix_0100100100
    (b x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat) (hb : 1 < b)
    (h2 : b ≤ x2 ∧ x2 ≤ 5*b)
    (h10 : b ≤ x10 ∧ x10 ≤ 5*b)
    (r2 : 2*x3 = x2)
    (r3 : 2*x4 = x3)
    (r4 : x5 = 3*x4+1)
    (r5 : 2*x6 = x5)
    (r6 : 2*x7 = x6)
    (r7 : x8 = 3*x7+1)
    (r8 : 2*x9 = x8)
    (r9 : 2*x10 = x9)
    : False := by
  omega

/-- Transition prefix `0100100101` cannot remain in [b,5b] for b>1. -/
theorem prefix_0100100101
    (b x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat) (hb : 1 < b)
    (h2 : b ≤ x2 ∧ x2 ≤ 5*b)
    (h7 : b ≤ x7 ∧ x7 ≤ 5*b)
    (h10 : b ≤ x10 ∧ x10 ≤ 5*b)
    (r2 : 2*x3 = x2)
    (r3 : 2*x4 = x3)
    (r4 : x5 = 3*x4+1)
    (r5 : 2*x6 = x5)
    (r6 : 2*x7 = x6)
    (r7 : x8 = 3*x7+1)
    (r8 : 2*x9 = x8)
    (r9 : x10 = 3*x9+1)
    : False := by
  omega

/-- Transition prefix `010010011` cannot remain in [b,5b] for b>1. -/
theorem prefix_010010011
    (b x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ x1 ≤ 5*b)
    (h9 : b ≤ x9 ∧ x9 ≤ 5*b)
    (r1 : x2 = 3*x1+1)
    (r2 : 2*x3 = x2)
    (r3 : 2*x4 = x3)
    (r4 : x5 = 3*x4+1)
    (r5 : 2*x6 = x5)
    (r6 : 2*x7 = x6)
    (r7 : x8 = 3*x7+1)
    (r8 : x9 = 3*x8+1)
    : False := by
  omega

/-- Transition prefix `0100101000` cannot remain in [b,5b] for b>1. -/
theorem prefix_0100101000
    (b x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat) (hb : 1 < b)
    (h2 : b ≤ x2 ∧ x2 ≤ 5*b)
    (h10 : b ≤ x10 ∧ x10 ≤ 5*b)
    (r2 : 2*x3 = x2)
    (r3 : 2*x4 = x3)
    (r4 : x5 = 3*x4+1)
    (r5 : 2*x6 = x5)
    (r6 : x7 = 3*x6+1)
    (r7 : 2*x8 = x7)
    (r8 : 2*x9 = x8)
    (r9 : 2*x10 = x9)
    : False := by
  omega

/-- Transition prefix `010010100100` cannot remain in [b,5b] for b>1. -/
theorem prefix_010010100100
    (b x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat) (hb : 1 < b)
    (h4 : b ≤ x4 ∧ x4 ≤ 5*b)
    (h7 : b ≤ x7 ∧ x7 ≤ 5*b)
    (h12 : b ≤ x12 ∧ x12 ≤ 5*b)
    (r4 : x5 = 3*x4+1)
    (r5 : 2*x6 = x5)
    (r6 : x7 = 3*x6+1)
    (r7 : 2*x8 = x7)
    (r8 : 2*x9 = x8)
    (r9 : x10 = 3*x9+1)
    (r10 : 2*x11 = x10)
    (r11 : 2*x12 = x11)
    : False := by
  omega

/-- Transition prefix `010010100101` cannot remain in [b,5b] for b>1. -/
theorem prefix_010010100101
    (b x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat) (hb : 1 < b)
    (h4 : b ≤ x4 ∧ x4 ≤ 5*b)
    (h12 : b ≤ x12 ∧ x12 ≤ 5*b)
    (r4 : x5 = 3*x4+1)
    (r5 : 2*x6 = x5)
    (r6 : x7 = 3*x6+1)
    (r7 : 2*x8 = x7)
    (r8 : 2*x9 = x8)
    (r9 : x10 = 3*x9+1)
    (r10 : 2*x11 = x10)
    (r11 : x12 = 3*x11+1)
    : False := by
  omega

/-- Transition prefix `01001010011` cannot remain in [b,5b] for b>1. -/
theorem prefix_01001010011
    (b x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ x1 ≤ 5*b)
    (h11 : b ≤ x11 ∧ x11 ≤ 5*b)
    (r1 : x2 = 3*x1+1)
    (r2 : 2*x3 = x2)
    (r3 : 2*x4 = x3)
    (r4 : x5 = 3*x4+1)
    (r5 : 2*x6 = x5)
    (r6 : x7 = 3*x6+1)
    (r7 : 2*x8 = x7)
    (r8 : 2*x9 = x8)
    (r9 : x10 = 3*x9+1)
    (r10 : x11 = 3*x10+1)
    : False := by
  omega

/-- Transition prefix `010010101` cannot remain in [b,5b] for b>1. -/
theorem prefix_010010101
    (b x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ x1 ≤ 5*b)
    (h9 : b ≤ x9 ∧ x9 ≤ 5*b)
    (r1 : x2 = 3*x1+1)
    (r2 : 2*x3 = x2)
    (r3 : 2*x4 = x3)
    (r4 : x5 = 3*x4+1)
    (r5 : 2*x6 = x5)
    (r6 : x7 = 3*x6+1)
    (r7 : 2*x8 = x7)
    (r8 : x9 = 3*x8+1)
    : False := by
  omega

/-- Transition prefix `01001011` cannot remain in [b,5b] for b>1. -/
theorem prefix_01001011
    (b x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h8 : b ≤ x8 ∧ x8 ≤ 5*b)
    (r0 : 2*x1 = x0)
    (r1 : x2 = 3*x1+1)
    (r2 : 2*x3 = x2)
    (r3 : 2*x4 = x3)
    (r4 : x5 = 3*x4+1)
    (r5 : 2*x6 = x5)
    (r6 : x7 = 3*x6+1)
    (r7 : x8 = 3*x7+1)
    : False := by
  omega

/-- Transition prefix `010011` cannot remain in [b,5b] for b>1. -/
theorem prefix_010011
    (b x1 x2 x3 x4 x5 x6 : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ x1 ≤ 5*b)
    (h6 : b ≤ x6 ∧ x6 ≤ 5*b)
    (r1 : x2 = 3*x1+1)
    (r2 : 2*x3 = x2)
    (r3 : 2*x4 = x3)
    (r4 : x5 = 3*x4+1)
    (r5 : x6 = 3*x5+1)
    : False := by
  omega

/-- Transition prefix `0101000` cannot remain in [b,5b] for b>1. -/
theorem prefix_0101000
    (b x4 x5 x6 x7 : Nat) (hb : 1 < b)
    (h4 : b ≤ x4 ∧ x4 ≤ 5*b)
    (h7 : b ≤ x7 ∧ x7 ≤ 5*b)
    (r4 : 2*x5 = x4)
    (r5 : 2*x6 = x5)
    (r6 : 2*x7 = x6)
    : False := by
  omega

/-- Transition prefix `010100100` cannot remain in [b,5b] for b>1. -/
theorem prefix_010100100
    (b x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ x1 ≤ 5*b)
    (h4 : b ≤ x4 ∧ x4 ≤ 5*b)
    (h9 : b ≤ x9 ∧ x9 ≤ 5*b)
    (r1 : x2 = 3*x1+1)
    (r2 : 2*x3 = x2)
    (r3 : x4 = 3*x3+1)
    (r4 : 2*x5 = x4)
    (r5 : 2*x6 = x5)
    (r6 : x7 = 3*x6+1)
    (r7 : 2*x8 = x7)
    (r8 : 2*x9 = x8)
    : False := by
  omega

/-- Transition prefix `010100101` cannot remain in [b,5b] for b>1. -/
theorem prefix_010100101
    (b x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ x1 ≤ 5*b)
    (h9 : b ≤ x9 ∧ x9 ≤ 5*b)
    (r1 : x2 = 3*x1+1)
    (r2 : 2*x3 = x2)
    (r3 : x4 = 3*x3+1)
    (r4 : 2*x5 = x4)
    (r5 : 2*x6 = x5)
    (r6 : x7 = 3*x6+1)
    (r7 : 2*x8 = x7)
    (r8 : x9 = 3*x8+1)
    : False := by
  omega

/-- Transition prefix `01010011` cannot remain in [b,5b] for b>1. -/
theorem prefix_01010011
    (b x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h8 : b ≤ x8 ∧ x8 ≤ 5*b)
    (r0 : 2*x1 = x0)
    (r1 : x2 = 3*x1+1)
    (r2 : 2*x3 = x2)
    (r3 : x4 = 3*x3+1)
    (r4 : 2*x5 = x4)
    (r5 : 2*x6 = x5)
    (r6 : x7 = 3*x6+1)
    (r7 : x8 = 3*x7+1)
    : False := by
  omega

/-- Transition prefix `010101` cannot remain in [b,5b] for b>1. -/
theorem prefix_010101
    (b x1 x2 x3 x4 x5 x6 : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ x1 ≤ 5*b)
    (h6 : b ≤ x6 ∧ x6 ≤ 5*b)
    (r1 : x2 = 3*x1+1)
    (r2 : 2*x3 = x2)
    (r3 : x4 = 3*x3+1)
    (r4 : 2*x5 = x4)
    (r5 : x6 = 3*x5+1)
    : False := by
  omega

/-- Transition prefix `01011` cannot remain in [b,5b] for b>1. -/
theorem prefix_01011
    (b x0 x1 x2 x3 x4 x5 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h5 : b ≤ x5 ∧ x5 ≤ 5*b)
    (r0 : 2*x1 = x0)
    (r1 : x2 = 3*x1+1)
    (r2 : 2*x3 = x2)
    (r3 : x4 = 3*x3+1)
    (r4 : x5 = 3*x4+1)
    : False := by
  omega

/-- Transition prefix `011` cannot remain in [b,5b] for b>1. -/
theorem prefix_011
    (b x1 x2 x3 : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ x1 ≤ 5*b)
    (h3 : b ≤ x3 ∧ x3 ≤ 5*b)
    (r1 : x2 = 3*x1+1)
    (r2 : x3 = 3*x2+1)
    : False := by
  omega

/-- Transition prefix `1000` cannot remain in [b,5b] for b>1. -/
theorem prefix_1000
    (b x1 x2 x3 x4 : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ x1 ≤ 5*b)
    (h4 : b ≤ x4 ∧ x4 ≤ 5*b)
    (r1 : 2*x2 = x1)
    (r2 : 2*x3 = x2)
    (r3 : 2*x4 = x3)
    : False := by
  omega

/-- Transition prefix `1001000` cannot remain in [b,5b] for b>1. -/
theorem prefix_1001000
    (b x1 x2 x3 x4 x5 x6 x7 : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ x1 ≤ 5*b)
    (h7 : b ≤ x7 ∧ x7 ≤ 5*b)
    (r1 : 2*x2 = x1)
    (r2 : 2*x3 = x2)
    (r3 : x4 = 3*x3+1)
    (r4 : 2*x5 = x4)
    (r5 : 2*x6 = x5)
    (r6 : 2*x7 = x6)
    : False := by
  omega

/-- Transition prefix `100100100` cannot remain in [b,5b] for b>1. -/
theorem prefix_100100100
    (b x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ x1 ≤ 5*b)
    (h9 : b ≤ x9 ∧ x9 ≤ 5*b)
    (r1 : 2*x2 = x1)
    (r2 : 2*x3 = x2)
    (r3 : x4 = 3*x3+1)
    (r4 : 2*x5 = x4)
    (r5 : 2*x6 = x5)
    (r6 : x7 = 3*x6+1)
    (r7 : 2*x8 = x7)
    (r8 : 2*x9 = x8)
    : False := by
  omega

/-- Transition prefix `100100101` cannot remain in [b,5b] for b>1. -/
theorem prefix_100100101
    (b x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ x1 ≤ 5*b)
    (h6 : b ≤ x6 ∧ x6 ≤ 5*b)
    (h9 : b ≤ x9 ∧ x9 ≤ 5*b)
    (r1 : 2*x2 = x1)
    (r2 : 2*x3 = x2)
    (r3 : x4 = 3*x3+1)
    (r4 : 2*x5 = x4)
    (r5 : 2*x6 = x5)
    (r6 : x7 = 3*x6+1)
    (r7 : 2*x8 = x7)
    (r8 : x9 = 3*x8+1)
    : False := by
  omega

/-- Transition prefix `10010011` cannot remain in [b,5b] for b>1. -/
theorem prefix_10010011
    (b x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h8 : b ≤ x8 ∧ x8 ≤ 5*b)
    (r0 : x1 = 3*x0+1)
    (r1 : 2*x2 = x1)
    (r2 : 2*x3 = x2)
    (r3 : x4 = 3*x3+1)
    (r4 : 2*x5 = x4)
    (r5 : 2*x6 = x5)
    (r6 : x7 = 3*x6+1)
    (r7 : x8 = 3*x7+1)
    : False := by
  omega

/-- Transition prefix `100101000` cannot remain in [b,5b] for b>1. -/
theorem prefix_100101000
    (b x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ x1 ≤ 5*b)
    (h9 : b ≤ x9 ∧ x9 ≤ 5*b)
    (r1 : 2*x2 = x1)
    (r2 : 2*x3 = x2)
    (r3 : x4 = 3*x3+1)
    (r4 : 2*x5 = x4)
    (r5 : x6 = 3*x5+1)
    (r6 : 2*x7 = x6)
    (r7 : 2*x8 = x7)
    (r8 : 2*x9 = x8)
    : False := by
  omega

/-- Transition prefix `10010100100` cannot remain in [b,5b] for b>1. -/
theorem prefix_10010100100
    (b x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat) (hb : 1 < b)
    (h3 : b ≤ x3 ∧ x3 ≤ 5*b)
    (h6 : b ≤ x6 ∧ x6 ≤ 5*b)
    (h11 : b ≤ x11 ∧ x11 ≤ 5*b)
    (r3 : x4 = 3*x3+1)
    (r4 : 2*x5 = x4)
    (r5 : x6 = 3*x5+1)
    (r6 : 2*x7 = x6)
    (r7 : 2*x8 = x7)
    (r8 : x9 = 3*x8+1)
    (r9 : 2*x10 = x9)
    (r10 : 2*x11 = x10)
    : False := by
  omega

/-- Transition prefix `10010100101` cannot remain in [b,5b] for b>1. -/
theorem prefix_10010100101
    (b x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat) (hb : 1 < b)
    (h3 : b ≤ x3 ∧ x3 ≤ 5*b)
    (h11 : b ≤ x11 ∧ x11 ≤ 5*b)
    (r3 : x4 = 3*x3+1)
    (r4 : 2*x5 = x4)
    (r5 : x6 = 3*x5+1)
    (r6 : 2*x7 = x6)
    (r7 : 2*x8 = x7)
    (r8 : x9 = 3*x8+1)
    (r9 : 2*x10 = x9)
    (r10 : x11 = 3*x10+1)
    : False := by
  omega

/-- Transition prefix `1001010011` cannot remain in [b,5b] for b>1. -/
theorem prefix_1001010011
    (b x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h10 : b ≤ x10 ∧ x10 ≤ 5*b)
    (r0 : x1 = 3*x0+1)
    (r1 : 2*x2 = x1)
    (r2 : 2*x3 = x2)
    (r3 : x4 = 3*x3+1)
    (r4 : 2*x5 = x4)
    (r5 : x6 = 3*x5+1)
    (r6 : 2*x7 = x6)
    (r7 : 2*x8 = x7)
    (r8 : x9 = 3*x8+1)
    (r9 : x10 = 3*x9+1)
    : False := by
  omega

/-- Transition prefix `10010101` cannot remain in [b,5b] for b>1. -/
theorem prefix_10010101
    (b x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h8 : b ≤ x8 ∧ x8 ≤ 5*b)
    (r0 : x1 = 3*x0+1)
    (r1 : 2*x2 = x1)
    (r2 : 2*x3 = x2)
    (r3 : x4 = 3*x3+1)
    (r4 : 2*x5 = x4)
    (r5 : x6 = 3*x5+1)
    (r6 : 2*x7 = x6)
    (r7 : x8 = 3*x7+1)
    : False := by
  omega

/-- Transition prefix `1001011` cannot remain in [b,5b] for b>1. -/
theorem prefix_1001011
    (b x0 x1 x2 x3 x4 x5 x6 x7 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h7 : b ≤ x7 ∧ x7 ≤ 5*b)
    (r0 : x1 = 3*x0+1)
    (r1 : 2*x2 = x1)
    (r2 : 2*x3 = x2)
    (r3 : x4 = 3*x3+1)
    (r4 : 2*x5 = x4)
    (r5 : x6 = 3*x5+1)
    (r6 : x7 = 3*x6+1)
    : False := by
  omega

/-- Transition prefix `10011` cannot remain in [b,5b] for b>1. -/
theorem prefix_10011
    (b x0 x1 x2 x3 x4 x5 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h5 : b ≤ x5 ∧ x5 ≤ 5*b)
    (r0 : x1 = 3*x0+1)
    (r1 : 2*x2 = x1)
    (r2 : 2*x3 = x2)
    (r3 : x4 = 3*x3+1)
    (r4 : x5 = 3*x4+1)
    : False := by
  omega

/-- Transition prefix `101000` cannot remain in [b,5b] for b>1. -/
theorem prefix_101000
    (b x3 x4 x5 x6 : Nat) (hb : 1 < b)
    (h3 : b ≤ x3 ∧ x3 ≤ 5*b)
    (h6 : b ≤ x6 ∧ x6 ≤ 5*b)
    (r3 : 2*x4 = x3)
    (r4 : 2*x5 = x4)
    (r5 : 2*x6 = x5)
    : False := by
  omega

/-- Transition prefix `10100100` cannot remain in [b,5b] for b>1. -/
theorem prefix_10100100
    (b x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h3 : b ≤ x3 ∧ x3 ≤ 5*b)
    (h8 : b ≤ x8 ∧ x8 ≤ 5*b)
    (r0 : x1 = 3*x0+1)
    (r1 : 2*x2 = x1)
    (r2 : x3 = 3*x2+1)
    (r3 : 2*x4 = x3)
    (r4 : 2*x5 = x4)
    (r5 : x6 = 3*x5+1)
    (r6 : 2*x7 = x6)
    (r7 : 2*x8 = x7)
    : False := by
  omega

/-- Transition prefix `10100101` cannot remain in [b,5b] for b>1. -/
theorem prefix_10100101
    (b x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h8 : b ≤ x8 ∧ x8 ≤ 5*b)
    (r0 : x1 = 3*x0+1)
    (r1 : 2*x2 = x1)
    (r2 : x3 = 3*x2+1)
    (r3 : 2*x4 = x3)
    (r4 : 2*x5 = x4)
    (r5 : x6 = 3*x5+1)
    (r6 : 2*x7 = x6)
    (r7 : x8 = 3*x7+1)
    : False := by
  omega

/-- Transition prefix `1010011` cannot remain in [b,5b] for b>1. -/
theorem prefix_1010011
    (b x0 x1 x2 x3 x4 x5 x6 x7 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h7 : b ≤ x7 ∧ x7 ≤ 5*b)
    (r0 : x1 = 3*x0+1)
    (r1 : 2*x2 = x1)
    (r2 : x3 = 3*x2+1)
    (r3 : 2*x4 = x3)
    (r4 : 2*x5 = x4)
    (r5 : x6 = 3*x5+1)
    (r6 : x7 = 3*x6+1)
    : False := by
  omega

/-- Transition prefix `10101` cannot remain in [b,5b] for b>1. -/
theorem prefix_10101
    (b x0 x1 x2 x3 x4 x5 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h5 : b ≤ x5 ∧ x5 ≤ 5*b)
    (r0 : x1 = 3*x0+1)
    (r1 : 2*x2 = x1)
    (r2 : x3 = 3*x2+1)
    (r3 : 2*x4 = x3)
    (r4 : x5 = 3*x4+1)
    : False := by
  omega

/-- Transition prefix `1011` cannot remain in [b,5b] for b>1. -/
theorem prefix_1011
    (b x0 x1 x2 x3 x4 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h4 : b ≤ x4 ∧ x4 ≤ 5*b)
    (r0 : x1 = 3*x0+1)
    (r1 : 2*x2 = x1)
    (r2 : x3 = 3*x2+1)
    (r3 : x4 = 3*x3+1)
    : False := by
  omega

/-- Transition prefix `11` cannot remain in [b,5b] for b>1. -/
theorem prefix_11
    (b x0 x1 x2 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h2 : b ≤ x2 ∧ x2 ≤ 5*b)
    (r0 : x1 = 3*x0+1)
    (r1 : x2 = 3*x1+1)
    : False := by
  omega

/-- No thirteen sampled states can satisfy the band and map equations. -/
theorem impossible_trace
    (b x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ x0 ≤ 5*b)
    (h1 : b ≤ x1 ∧ x1 ≤ 5*b)
    (h2 : b ≤ x2 ∧ x2 ≤ 5*b)
    (h3 : b ≤ x3 ∧ x3 ≤ 5*b)
    (h4 : b ≤ x4 ∧ x4 ≤ 5*b)
    (h5 : b ≤ x5 ∧ x5 ≤ 5*b)
    (h6 : b ≤ x6 ∧ x6 ≤ 5*b)
    (h7 : b ≤ x7 ∧ x7 ≤ 5*b)
    (h8 : b ≤ x8 ∧ x8 ≤ 5*b)
    (h9 : b ≤ x9 ∧ x9 ≤ 5*b)
    (h10 : b ≤ x10 ∧ x10 ≤ 5*b)
    (h11 : b ≤ x11 ∧ x11 ≤ 5*b)
    (h12 : b ≤ x12 ∧ x12 ≤ 5*b)
    (r0 : 2*x1 = x0 ∨ x1 = 3*x0+1)
    (r1 : 2*x2 = x1 ∨ x2 = 3*x1+1)
    (r2 : 2*x3 = x2 ∨ x3 = 3*x2+1)
    (r3 : 2*x4 = x3 ∨ x4 = 3*x3+1)
    (r4 : 2*x5 = x4 ∨ x5 = 3*x4+1)
    (r5 : 2*x6 = x5 ∨ x6 = 3*x5+1)
    (r6 : 2*x7 = x6 ∨ x7 = 3*x6+1)
    (r7 : 2*x8 = x7 ∨ x8 = 3*x7+1)
    (r8 : 2*x9 = x8 ∨ x9 = 3*x8+1)
    (r9 : 2*x10 = x9 ∨ x10 = 3*x9+1)
    (r10 : 2*x11 = x10 ∨ x11 = 3*x10+1)
    (r11 : 2*x12 = x11 ∨ x12 = 3*x11+1)
    : False := by
  revert r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0
  intro r0
  rcases r0 with r0 | r0
  · -- even transition at time 0
    intro r1
    rcases r1 with r1 | r1
    · -- even transition at time 1
      intro r2
      rcases r2 with r2 | r2
      · -- even transition at time 2
        exact False.elim (prefix_000 b x0 x1 x2 x3 hb h0 h3 r0 r1 r2)
      · -- odd transition at time 2
        intro r3
        rcases r3 with r3 | r3
        · -- even transition at time 3
          intro r4
          rcases r4 with r4 | r4
          · -- even transition at time 4
            intro r5
            rcases r5 with r5 | r5
            · -- even transition at time 5
              exact False.elim (prefix_001000 b x0 x1 x2 x3 x4 x5 x6 hb h0 h6 r0 r1 r2 r3 r4 r5)
            · -- odd transition at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- even transition at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- even transition at time 7
                  exact False.elim (prefix_00100100 b x0 x1 x2 x3 x4 x5 x6 x7 x8 hb h0 h8 r0 r1 r2 r3 r4 r5 r6 r7)
                · -- odd transition at time 7
                  exact False.elim (prefix_00100101 b x0 x1 x2 x3 x4 x5 x6 x7 x8 hb h0 h5 h8 r0 r1 r2 r3 r4 r5 r6 r7)
              · -- odd transition at time 6
                exact False.elim (prefix_0010011 b x2 x3 x4 x5 x6 x7 hb h2 h7 r2 r3 r4 r5 r6)
          · -- odd transition at time 4
            intro r5
            rcases r5 with r5 | r5
            · -- even transition at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- even transition at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- even transition at time 7
                  exact False.elim (prefix_00101000 b x0 x1 x2 x3 x4 x5 x6 x7 x8 hb h0 h8 r0 r1 r2 r3 r4 r5 r6 r7)
                · -- odd transition at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- even transition at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- even transition at time 9
                      exact False.elim (prefix_0010100100 b x2 x3 x4 x5 x6 x7 x8 x9 x10 hb h2 h5 h10 r2 r3 r4 r5 r6 r7 r8 r9)
                    · -- odd transition at time 9
                      exact False.elim (prefix_0010100101 b x2 x3 x4 x5 x6 x7 x8 x9 x10 hb h2 h10 r2 r3 r4 r5 r6 r7 r8 r9)
                  · -- odd transition at time 8
                    exact False.elim (prefix_001010011 b x1 x2 x3 x4 x5 x6 x7 x8 x9 hb h1 h9 r1 r2 r3 r4 r5 r6 r7 r8)
              · -- odd transition at time 6
                exact False.elim (prefix_0010101 b x2 x3 x4 x5 x6 x7 hb h2 h7 r2 r3 r4 r5 r6)
            · -- odd transition at time 5
              exact False.elim (prefix_001011 b x1 x2 x3 x4 x5 x6 hb h1 h6 r1 r2 r3 r4 r5)
        · -- odd transition at time 3
          exact False.elim (prefix_0011 b x2 x3 x4 hb h2 h4 r2 r3)
    · -- odd transition at time 1
      intro r2
      rcases r2 with r2 | r2
      · -- even transition at time 2
        intro r3
        rcases r3 with r3 | r3
        · -- even transition at time 3
          intro r4
          rcases r4 with r4 | r4
          · -- even transition at time 4
            exact False.elim (prefix_01000 b x2 x3 x4 x5 hb h2 h5 r2 r3 r4)
          · -- odd transition at time 4
            intro r5
            rcases r5 with r5 | r5
            · -- even transition at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- even transition at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- even transition at time 7
                  exact False.elim (prefix_01001000 b x0 x1 x2 x3 x4 x5 x6 x7 x8 hb h0 h8 r0 r1 r2 r3 r4 r5 r6 r7)
                · -- odd transition at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- even transition at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- even transition at time 9
                      exact False.elim (prefix_0100100100 b x2 x3 x4 x5 x6 x7 x8 x9 x10 hb h2 h10 r2 r3 r4 r5 r6 r7 r8 r9)
                    · -- odd transition at time 9
                      exact False.elim (prefix_0100100101 b x2 x3 x4 x5 x6 x7 x8 x9 x10 hb h2 h7 h10 r2 r3 r4 r5 r6 r7 r8 r9)
                  · -- odd transition at time 8
                    exact False.elim (prefix_010010011 b x1 x2 x3 x4 x5 x6 x7 x8 x9 hb h1 h9 r1 r2 r3 r4 r5 r6 r7 r8)
              · -- odd transition at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- even transition at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- even transition at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- even transition at time 9
                      exact False.elim (prefix_0100101000 b x2 x3 x4 x5 x6 x7 x8 x9 x10 hb h2 h10 r2 r3 r4 r5 r6 r7 r8 r9)
                    · -- odd transition at time 9
                      intro r10
                      rcases r10 with r10 | r10
                      · -- even transition at time 10
                        intro r11
                        rcases r11 with r11 | r11
                        · -- even transition at time 11
                          exact False.elim (prefix_010010100100 b x4 x5 x6 x7 x8 x9 x10 x11 x12 hb h4 h7 h12 r4 r5 r6 r7 r8 r9 r10 r11)
                        · -- odd transition at time 11
                          exact False.elim (prefix_010010100101 b x4 x5 x6 x7 x8 x9 x10 x11 x12 hb h4 h12 r4 r5 r6 r7 r8 r9 r10 r11)
                      · -- odd transition at time 10
                        exact False.elim (prefix_01001010011 b x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 hb h1 h11 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10)
                  · -- odd transition at time 8
                    exact False.elim (prefix_010010101 b x1 x2 x3 x4 x5 x6 x7 x8 x9 hb h1 h9 r1 r2 r3 r4 r5 r6 r7 r8)
                · -- odd transition at time 7
                  exact False.elim (prefix_01001011 b x0 x1 x2 x3 x4 x5 x6 x7 x8 hb h0 h8 r0 r1 r2 r3 r4 r5 r6 r7)
            · -- odd transition at time 5
              exact False.elim (prefix_010011 b x1 x2 x3 x4 x5 x6 hb h1 h6 r1 r2 r3 r4 r5)
        · -- odd transition at time 3
          intro r4
          rcases r4 with r4 | r4
          · -- even transition at time 4
            intro r5
            rcases r5 with r5 | r5
            · -- even transition at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- even transition at time 6
                exact False.elim (prefix_0101000 b x4 x5 x6 x7 hb h4 h7 r4 r5 r6)
              · -- odd transition at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- even transition at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- even transition at time 8
                    exact False.elim (prefix_010100100 b x1 x2 x3 x4 x5 x6 x7 x8 x9 hb h1 h4 h9 r1 r2 r3 r4 r5 r6 r7 r8)
                  · -- odd transition at time 8
                    exact False.elim (prefix_010100101 b x1 x2 x3 x4 x5 x6 x7 x8 x9 hb h1 h9 r1 r2 r3 r4 r5 r6 r7 r8)
                · -- odd transition at time 7
                  exact False.elim (prefix_01010011 b x0 x1 x2 x3 x4 x5 x6 x7 x8 hb h0 h8 r0 r1 r2 r3 r4 r5 r6 r7)
            · -- odd transition at time 5
              exact False.elim (prefix_010101 b x1 x2 x3 x4 x5 x6 hb h1 h6 r1 r2 r3 r4 r5)
          · -- odd transition at time 4
            exact False.elim (prefix_01011 b x0 x1 x2 x3 x4 x5 hb h0 h5 r0 r1 r2 r3 r4)
      · -- odd transition at time 2
        exact False.elim (prefix_011 b x1 x2 x3 hb h1 h3 r1 r2)
  · -- odd transition at time 0
    intro r1
    rcases r1 with r1 | r1
    · -- even transition at time 1
      intro r2
      rcases r2 with r2 | r2
      · -- even transition at time 2
        intro r3
        rcases r3 with r3 | r3
        · -- even transition at time 3
          exact False.elim (prefix_1000 b x1 x2 x3 x4 hb h1 h4 r1 r2 r3)
        · -- odd transition at time 3
          intro r4
          rcases r4 with r4 | r4
          · -- even transition at time 4
            intro r5
            rcases r5 with r5 | r5
            · -- even transition at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- even transition at time 6
                exact False.elim (prefix_1001000 b x1 x2 x3 x4 x5 x6 x7 hb h1 h7 r1 r2 r3 r4 r5 r6)
              · -- odd transition at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- even transition at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- even transition at time 8
                    exact False.elim (prefix_100100100 b x1 x2 x3 x4 x5 x6 x7 x8 x9 hb h1 h9 r1 r2 r3 r4 r5 r6 r7 r8)
                  · -- odd transition at time 8
                    exact False.elim (prefix_100100101 b x1 x2 x3 x4 x5 x6 x7 x8 x9 hb h1 h6 h9 r1 r2 r3 r4 r5 r6 r7 r8)
                · -- odd transition at time 7
                  exact False.elim (prefix_10010011 b x0 x1 x2 x3 x4 x5 x6 x7 x8 hb h0 h8 r0 r1 r2 r3 r4 r5 r6 r7)
            · -- odd transition at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- even transition at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- even transition at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- even transition at time 8
                    exact False.elim (prefix_100101000 b x1 x2 x3 x4 x5 x6 x7 x8 x9 hb h1 h9 r1 r2 r3 r4 r5 r6 r7 r8)
                  · -- odd transition at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- even transition at time 9
                      intro r10
                      rcases r10 with r10 | r10
                      · -- even transition at time 10
                        exact False.elim (prefix_10010100100 b x3 x4 x5 x6 x7 x8 x9 x10 x11 hb h3 h6 h11 r3 r4 r5 r6 r7 r8 r9 r10)
                      · -- odd transition at time 10
                        exact False.elim (prefix_10010100101 b x3 x4 x5 x6 x7 x8 x9 x10 x11 hb h3 h11 r3 r4 r5 r6 r7 r8 r9 r10)
                    · -- odd transition at time 9
                      exact False.elim (prefix_1001010011 b x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 hb h0 h10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
                · -- odd transition at time 7
                  exact False.elim (prefix_10010101 b x0 x1 x2 x3 x4 x5 x6 x7 x8 hb h0 h8 r0 r1 r2 r3 r4 r5 r6 r7)
              · -- odd transition at time 6
                exact False.elim (prefix_1001011 b x0 x1 x2 x3 x4 x5 x6 x7 hb h0 h7 r0 r1 r2 r3 r4 r5 r6)
          · -- odd transition at time 4
            exact False.elim (prefix_10011 b x0 x1 x2 x3 x4 x5 hb h0 h5 r0 r1 r2 r3 r4)
      · -- odd transition at time 2
        intro r3
        rcases r3 with r3 | r3
        · -- even transition at time 3
          intro r4
          rcases r4 with r4 | r4
          · -- even transition at time 4
            intro r5
            rcases r5 with r5 | r5
            · -- even transition at time 5
              exact False.elim (prefix_101000 b x3 x4 x5 x6 hb h3 h6 r3 r4 r5)
            · -- odd transition at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- even transition at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- even transition at time 7
                  exact False.elim (prefix_10100100 b x0 x1 x2 x3 x4 x5 x6 x7 x8 hb h0 h3 h8 r0 r1 r2 r3 r4 r5 r6 r7)
                · -- odd transition at time 7
                  exact False.elim (prefix_10100101 b x0 x1 x2 x3 x4 x5 x6 x7 x8 hb h0 h8 r0 r1 r2 r3 r4 r5 r6 r7)
              · -- odd transition at time 6
                exact False.elim (prefix_1010011 b x0 x1 x2 x3 x4 x5 x6 x7 hb h0 h7 r0 r1 r2 r3 r4 r5 r6)
          · -- odd transition at time 4
            exact False.elim (prefix_10101 b x0 x1 x2 x3 x4 x5 hb h0 h5 r0 r1 r2 r3 r4)
        · -- odd transition at time 3
          exact False.elim (prefix_1011 b x0 x1 x2 x3 x4 hb h0 h4 r0 r1 r2 r3)
    · -- odd transition at time 1
      exact False.elim (prefix_11 b x0 x1 x2 hb h0 h2 r0 r1)

end Collatz.Exploration.FiveBandArithmetic
