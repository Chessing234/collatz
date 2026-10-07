import Collatz.Exploration.ElevenHalvesArithmetic.Part18

namespace Collatz.Exploration.ElevenHalvesArithmetic

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- Terminal branch `100101001001011` cannot satisfy the band bounds. -/
theorem exclude_100101001001011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_10010100100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
  omega

/-- Terminal branch `1001010010011` cannot satisfy the band bounds. -/
theorem exclude_1001010010011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12⟩ := parameters_100101001001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hparity := r12.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11
  omega

/-- Terminal branch `10010100101000` cannot satisfy the band bounds. -/
theorem exclude_10010100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Nat)
    (b : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ 2*x1 ≤ 11*b)
    (h14 : b ≤ x14 ∧ 2*x14 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_10010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  clear p0 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
  omega

/-- Terminal branch `10010100101001000` cannot satisfy the band bounds. -/
theorem exclude_10010100101001000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : Nat)
    (b : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ 2*x1 ≤ 11*b)
    (h17 : b ≤ x17 ∧ 2*x17 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17⟩ := parameters_10010100101001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
  clear p0 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16
  omega

/-- Terminal branch `1001010010100100100` cannot satisfy the band bounds. -/
theorem exclude_1001010010100100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : Nat)
    (b : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ 2*x1 ≤ 11*b)
    (h19 : b ≤ x19 ∧ 2*x19 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_1001010010100100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  clear p0 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
  omega

/-- Terminal branch `1001010010100100101000` cannot satisfy the band bounds. -/
theorem exclude_1001010010100100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : Nat)
    (b : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ 2*x1 ≤ 11*b)
    (h22 : b ≤ x22 ∧ 2*x22 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22⟩ := parameters_1001010010100100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  clear p0 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21
  omega

/-- Terminal branch `100101001010010010100100` cannot satisfy the band bounds. -/
theorem exclude_100101001010010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 : Nat)
    (b : Nat) (hb : 1 < b)
    (h6 : b ≤ x6 ∧ 2*x6 ≤ 11*b)
    (h24 : b ≤ x24 ∧ 2*x24 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (x22 = 3*x21+1 ∧ x21%2 = 1))
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24⟩ := parameters_100101001010010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
  clear p0 p1 p2 p3 p4 p5 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23
  omega

/-- Terminal branch `100101001010010010100101000` cannot satisfy the band bounds. -/
theorem exclude_100101001010010010100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : Nat)
    (b : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ 2*x1 ≤ 11*b)
    (h27 : b ≤ x27 ∧ 2*x27 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (x22 = 3*x21+1 ∧ x21%2 = 1))
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    (r23 : (x24 = 3*x23+1 ∧ x23%2 = 1))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    (r26 : (2*x27 = x26 ∧ x26%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27⟩ := parameters_100101001010010010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
  clear p0 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26
  omega

/-- Terminal branch `10010100101001001010010100100` cannot satisfy the band bounds. -/
theorem exclude_10010100101001001010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 : Nat)
    (b : Nat) (hb : 1 < b)
    (h11 : b ≤ x11 ∧ 2*x11 ≤ 11*b)
    (h29 : b ≤ x29 ∧ 2*x29 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (x22 = 3*x21+1 ∧ x21%2 = 1))
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    (r23 : (x24 = 3*x23+1 ∧ x23%2 = 1))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    (r26 : (x27 = 3*x26+1 ∧ x26%2 = 1))
    (r27 : (2*x28 = x27 ∧ x27%2 = 0))
    (r28 : (2*x29 = x28 ∧ x28%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29⟩ := parameters_10010100101001001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28
  clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28
  omega

/-- Terminal branch `10010100101001001010010100101` cannot satisfy the band bounds. -/
theorem exclude_10010100101001001010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 : Nat)
    (b : Nat) (hb : 1 < b)
    (h16 : b ≤ x16 ∧ 2*x16 ≤ 11*b)
    (h29 : b ≤ x29 ∧ 2*x29 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (x22 = 3*x21+1 ∧ x21%2 = 1))
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    (r23 : (x24 = 3*x23+1 ∧ x23%2 = 1))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    (r26 : (x27 = 3*x26+1 ∧ x26%2 = 1))
    (r27 : (2*x28 = x27 ∧ x27%2 = 0))
    (r28 : (x29 = 3*x28+1 ∧ x28%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29⟩ := parameters_10010100101001001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28
  clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28
  omega

/-- Terminal branch `1001010010100100101001010011` cannot satisfy the band bounds. -/
theorem exclude_1001010010100100101001010011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (x22 = 3*x21+1 ∧ x21%2 = 1))
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    (r23 : (x24 = 3*x23+1 ∧ x23%2 = 1))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    (r26 : (x27 = 3*x26+1 ∧ x26%2 = 1))
    (r27 : (x28 = 3*x27+1 ∧ x27%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27⟩ := parameters_100101001010010010100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
  have hparity := r27.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27
  clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26
  omega

/-- Terminal branch `10010100101001001010010101` cannot satisfy the band bounds. -/
theorem exclude_10010100101001001010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 : Nat)
    (b : Nat) (hb : 1 < b)
    (h3 : b ≤ x3 ∧ 2*x3 ≤ 11*b)
    (h26 : b ≤ x26 ∧ 2*x26 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (x22 = 3*x21+1 ∧ x21%2 = 1))
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    (r23 : (x24 = 3*x23+1 ∧ x23%2 = 1))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    (r25 : (x26 = 3*x25+1 ∧ x25%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26⟩ := parameters_10010100101001001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
  clear p0 p1 p2 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25
  omega

/-- Terminal branch `1001010010100100101001011` cannot satisfy the band bounds. -/
theorem exclude_1001010010100100101001011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (x22 = 3*x21+1 ∧ x21%2 = 1))
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    (r23 : (x24 = 3*x23+1 ∧ x23%2 = 1))
    (r24 : (x25 = 3*x24+1 ∧ x24%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24⟩ := parameters_100101001010010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
  have hparity := r24.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24
  clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23
  omega

/-- Terminal branch `10010100101001001010011` cannot satisfy the band bounds. -/
theorem exclude_10010100101001001010011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (x22 = 3*x21+1 ∧ x21%2 = 1))
    (r22 : (x23 = 3*x22+1 ∧ x22%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22⟩ := parameters_1001010010100100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  have hparity := r22.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
  clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21
  omega

/-- Terminal branch `100101001010010010101` cannot satisfy the band bounds. -/
theorem exclude_100101001010010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 : Nat)
    (b : Nat) (hb : 1 < b)
    (h3 : b ≤ x3 ∧ 2*x3 ≤ 11*b)
    (h21 : b ≤ x21 ∧ 2*x21 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (x21 = 3*x20+1 ∧ x20%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21⟩ := parameters_100101001010010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
  clear p0 p1 p2 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
  omega

/-- Terminal branch `10010100101001001011` cannot satisfy the band bounds. -/
theorem exclude_10010100101001001011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (x20 = 3*x19+1 ∧ x19%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_1001010010100100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hparity := r19.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
  clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
  omega

/-- Terminal branch `100101001010010011` cannot satisfy the band bounds. -/
theorem exclude_100101001010010011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17⟩ := parameters_10010100101001001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
  have hparity := r17.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
  clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16
  omega

/-- Terminal branch `1001010010100101` cannot satisfy the band bounds. -/
theorem exclude_1001010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : Nat)
    (b : Nat) (hb : 1 < b)
    (h3 : b ≤ x3 ∧ 2*x3 ≤ 11*b)
    (h16 : b ≤ x16 ∧ 2*x16 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16⟩ := parameters_1001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  clear p0 p1 p2 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
  omega

/-- Terminal branch `100101001010011` cannot satisfy the band bounds. -/
theorem exclude_100101001010011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_10010100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
  omega

/-- Terminal branch `1001010010101` cannot satisfy the band bounds. -/
theorem exclude_1001010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Nat)
    (b : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 2*x0 ≤ 11*b)
    (h13 : b ≤ x13 ∧ 2*x13 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13⟩ := parameters_1001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  clear p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12
  omega

/-- Terminal branch `100101001011` cannot satisfy the band bounds. -/
theorem exclude_100101001011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_10010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hparity := r11.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
  omega

/-- Terminal branch `1001010011` cannot satisfy the band bounds. -/
theorem exclude_1001010011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
  have hparity := r9.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  clear p0 p1 p2 p3 p4 p5 p6 p7 p8
  omega

/-- Terminal branch `10010101` cannot satisfy the band bounds. -/
theorem exclude_10010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (b : Nat) (hb : 1 < b)
    (h3 : b ≤ x3 ∧ 2*x3 ≤ 11*b)
    (h8 : b ≤ x8 ∧ 2*x8 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_10010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  clear r0 r1 r2 r3 r4 r5 r6 r7
  clear p0 p1 p2 p4 p5 p6 p7
  omega

/-- Terminal branch `1001011` cannot satisfy the band bounds. -/
theorem exclude_1001011
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6⟩ := parameters_100101 x0 x1 x2 x3 x4 x5 x6 r0 r1 r2 r3 r4 r5
  have hparity := r6.2
  clear r0 r1 r2 r3 r4 r5 r6
  clear p0 p1 p2 p3 p4 p5
  omega

/-- Terminal branch `10011` cannot satisfy the band bounds. -/
theorem exclude_10011
    (x0 x1 x2 x3 x4 x5 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4⟩ := parameters_1001 x0 x1 x2 x3 x4 r0 r1 r2 r3
  have hparity := r4.2
  clear r0 r1 r2 r3 r4
  clear p0 p1 p2 p3
  omega

/-- Terminal branch `101000` cannot satisfy the band bounds. -/
theorem exclude_101000
    (x0 x1 x2 x3 x4 x5 x6 : Nat)
    (b : Nat) (hb : 1 < b)
    (h3 : b ≤ x3 ∧ 2*x3 ≤ 11*b)
    (h6 : b ≤ x6 ∧ 2*x6 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6⟩ := parameters_101000 x0 x1 x2 x3 x4 x5 x6 r0 r1 r2 r3 r4 r5
  clear r0 r1 r2 r3 r4 r5
  clear p0 p1 p2 p4 p5
  omega

/-- Terminal branch `101001000` cannot satisfy the band bounds. -/
theorem exclude_101001000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (b : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ 2*x1 ≤ 11*b)
    (h9 : b ≤ x9 ∧ 2*x9 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_101001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  clear p0 p2 p3 p4 p5 p6 p7 p8
  omega

/-- Terminal branch `10100100100` cannot satisfy the band bounds. -/
theorem exclude_10100100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
    (b : Nat) (hb : 1 < b)
    (h3 : b ≤ x3 ∧ 2*x3 ≤ 11*b)
    (h11 : b ≤ x11 ∧ 2*x11 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_10100100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  clear p0 p1 p2 p4 p5 p6 p7 p8 p9 p10
  omega

/-- Terminal branch `10100100101000` cannot satisfy the band bounds. -/
theorem exclude_10100100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Nat)
    (b : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ 2*x1 ≤ 11*b)
    (h14 : b ≤ x14 ∧ 2*x14 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_10100100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  clear p0 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
  omega

/-- Terminal branch `1010010010100100` cannot satisfy the band bounds. -/
theorem exclude_1010010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : Nat)
    (b : Nat) (hb : 1 < b)
    (h3 : b ≤ x3 ∧ 2*x3 ≤ 11*b)
    (h16 : b ≤ x16 ∧ 2*x16 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16⟩ := parameters_1010010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  clear p0 p1 p2 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
  omega

/-- Terminal branch `1010010010100101000` cannot satisfy the band bounds. -/
theorem exclude_1010010010100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : Nat)
    (b : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ 2*x1 ≤ 11*b)
    (h19 : b ≤ x19 ∧ 2*x19 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_1010010010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  clear p0 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
  omega

/-- Terminal branch `101001001010010100100` cannot satisfy the band bounds. -/
theorem exclude_101001001010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 : Nat)
    (b : Nat) (hb : 1 < b)
    (h3 : b ≤ x3 ∧ 2*x3 ≤ 11*b)
    (h21 : b ≤ x21 ∧ 2*x21 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21⟩ := parameters_101001001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
  clear p0 p1 p2 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
  omega

/-- Terminal branch `101001001010010100101` cannot satisfy the band bounds. -/
theorem exclude_101001001010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 : Nat)
    (b : Nat) (hb : 1 < b)
    (h8 : b ≤ x8 ∧ 2*x8 ≤ 11*b)
    (h21 : b ≤ x21 ∧ 2*x21 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (x21 = 3*x20+1 ∧ x20%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21⟩ := parameters_101001001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
  clear p0 p1 p2 p3 p4 p5 p6 p7 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
  omega

/-- Terminal branch `10100100101001010011` cannot satisfy the band bounds. -/
theorem exclude_10100100101001010011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (x20 = 3*x19+1 ∧ x19%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_1010010010100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hparity := r19.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
  clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
  omega

/-- Terminal branch `101001001010010101` cannot satisfy the band bounds. -/
theorem exclude_101001001010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : Nat)
    (b : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 2*x0 ≤ 11*b)
    (h18 : b ≤ x18 ∧ 2*x18 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18⟩ := parameters_101001001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
  clear p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17
  omega

/-- Terminal branch `10100100101001011` cannot satisfy the band bounds. -/
theorem exclude_10100100101001011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16⟩ := parameters_1010010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  have hparity := r16.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
  clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
  omega

/-- Terminal branch `101001001010011` cannot satisfy the band bounds. -/
theorem exclude_101001001010011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_10100100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
  omega

/-- Terminal branch `1010010010101` cannot satisfy the band bounds. -/
theorem exclude_1010010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Nat)
    (b : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 2*x0 ≤ 11*b)
    (h13 : b ≤ x13 ∧ 2*x13 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13⟩ := parameters_1010010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  clear p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12
  omega

/-- Terminal branch `101001001011` cannot satisfy the band bounds. -/
theorem exclude_101001001011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_10100100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hparity := r11.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
  omega

/-- Terminal branch `1010010011` cannot satisfy the band bounds. -/
theorem exclude_1010010011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_101001001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
  have hparity := r9.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  clear p0 p1 p2 p3 p4 p5 p6 p7 p8
  omega

/-- Terminal branch `10100101000` cannot satisfy the band bounds. -/
theorem exclude_10100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
    (b : Nat) (hb : 1 < b)
    (h3 : b ≤ x3 ∧ 2*x3 ≤ 11*b)
    (h11 : b ≤ x11 ∧ 2*x11 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_10100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  clear p0 p1 p2 p4 p5 p6 p7 p8 p9 p10
  omega

/-- Terminal branch `10100101001000` cannot satisfy the band bounds. -/
theorem exclude_10100101001000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Nat)
    (b : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ 2*x1 ≤ 11*b)
    (h14 : b ≤ x14 ∧ 2*x14 ≤ 11*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_10100101001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  clear p0 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
  omega


end Collatz.Exploration.ElevenHalvesArithmetic
