import Collatz.Exploration.ElevenHalvesArithmetic.Part08

namespace Collatz.Exploration.ElevenHalvesArithmetic

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- Exact source residue and full affine trace for branch `1010010010100101000`. -/
theorem parameters_1010010010100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : Nat)
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
    : ∃ q : Nat, x0 = 4096*q+1131 ∧ x1 = 12288*q+3394 ∧ x2 = 6144*q+1697 ∧ x3 = 18432*q+5092 ∧ x4 = 9216*q+2546 ∧ x5 = 4608*q+1273 ∧ x6 = 13824*q+3820 ∧ x7 = 6912*q+1910 ∧ x8 = 3456*q+955 ∧ x9 = 10368*q+2866 ∧ x10 = 5184*q+1433 ∧ x11 = 15552*q+4300 ∧ x12 = 7776*q+2150 ∧ x13 = 3888*q+1075 ∧ x14 = 11664*q+3226 ∧ x15 = 5832*q+1613 ∧ x16 = 17496*q+4840 ∧ x17 = 8748*q+2420 ∧ x18 = 4374*q+1210 ∧ x19 = 2187*q+605 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18⟩ := parameters_101001001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
  have hstep := r18.1
  have hparity := r18.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17
    omega

/-- Exact source residue and full affine trace for branch `1010010010100101001`. -/
theorem parameters_1010010010100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : Nat)
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
    : ∃ q : Nat, x0 = 4096*q+3179 ∧ x1 = 12288*q+9538 ∧ x2 = 6144*q+4769 ∧ x3 = 18432*q+14308 ∧ x4 = 9216*q+7154 ∧ x5 = 4608*q+3577 ∧ x6 = 13824*q+10732 ∧ x7 = 6912*q+5366 ∧ x8 = 3456*q+2683 ∧ x9 = 10368*q+8050 ∧ x10 = 5184*q+4025 ∧ x11 = 15552*q+12076 ∧ x12 = 7776*q+6038 ∧ x13 = 3888*q+3019 ∧ x14 = 11664*q+9058 ∧ x15 = 5832*q+4529 ∧ x16 = 17496*q+13588 ∧ x17 = 8748*q+6794 ∧ x18 = 4374*q+3397 ∧ x19 = 13122*q+10192 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18⟩ := parameters_101001001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
  have hstep := r18.1
  have hparity := r18.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17
    omega

/-- Exact source residue and full affine trace for branch `1010010100100101000`. -/
theorem parameters_1010010100100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : Nat)
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
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    : ∃ q : Nat, x0 = 4096*q+3963 ∧ x1 = 12288*q+11890 ∧ x2 = 6144*q+5945 ∧ x3 = 18432*q+17836 ∧ x4 = 9216*q+8918 ∧ x5 = 4608*q+4459 ∧ x6 = 13824*q+13378 ∧ x7 = 6912*q+6689 ∧ x8 = 20736*q+20068 ∧ x9 = 10368*q+10034 ∧ x10 = 5184*q+5017 ∧ x11 = 15552*q+15052 ∧ x12 = 7776*q+7526 ∧ x13 = 3888*q+3763 ∧ x14 = 11664*q+11290 ∧ x15 = 5832*q+5645 ∧ x16 = 17496*q+16936 ∧ x17 = 8748*q+8468 ∧ x18 = 4374*q+4234 ∧ x19 = 2187*q+2117 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18⟩ := parameters_101001010010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
  have hstep := r18.1
  have hparity := r18.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17
    omega

/-- Exact source residue and full affine trace for branch `1010010100100101001`. -/
theorem parameters_1010010100100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : Nat)
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
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    : ∃ q : Nat, x0 = 4096*q+1915 ∧ x1 = 12288*q+5746 ∧ x2 = 6144*q+2873 ∧ x3 = 18432*q+8620 ∧ x4 = 9216*q+4310 ∧ x5 = 4608*q+2155 ∧ x6 = 13824*q+6466 ∧ x7 = 6912*q+3233 ∧ x8 = 20736*q+9700 ∧ x9 = 10368*q+4850 ∧ x10 = 5184*q+2425 ∧ x11 = 15552*q+7276 ∧ x12 = 7776*q+3638 ∧ x13 = 3888*q+1819 ∧ x14 = 11664*q+5458 ∧ x15 = 5832*q+2729 ∧ x16 = 17496*q+8188 ∧ x17 = 8748*q+4094 ∧ x18 = 4374*q+2047 ∧ x19 = 13122*q+6142 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18⟩ := parameters_101001010010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
  have hstep := r18.1
  have hparity := r18.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17
    omega

/-- Exact source residue and full affine trace for branch `00101001001010010100`. -/
theorem parameters_00101001001010010100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    : ∃ q : Nat, x0 = 8192*q+4524 ∧ x1 = 4096*q+2262 ∧ x2 = 2048*q+1131 ∧ x3 = 6144*q+3394 ∧ x4 = 3072*q+1697 ∧ x5 = 9216*q+5092 ∧ x6 = 4608*q+2546 ∧ x7 = 2304*q+1273 ∧ x8 = 6912*q+3820 ∧ x9 = 3456*q+1910 ∧ x10 = 1728*q+955 ∧ x11 = 5184*q+2866 ∧ x12 = 2592*q+1433 ∧ x13 = 7776*q+4300 ∧ x14 = 3888*q+2150 ∧ x15 = 1944*q+1075 ∧ x16 = 5832*q+3226 ∧ x17 = 2916*q+1613 ∧ x18 = 8748*q+4840 ∧ x19 = 4374*q+2420 ∧ x20 = 2187*q+1210 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_0010100100101001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hstep := r19.1
  have hparity := r19.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega

/-- Exact source residue and full affine trace for branch `00101001001010010101`. -/
theorem parameters_00101001001010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (x20 = 3*x19+1 ∧ x19%2 = 1))
    : ∃ q : Nat, x0 = 8192*q+428 ∧ x1 = 4096*q+214 ∧ x2 = 2048*q+107 ∧ x3 = 6144*q+322 ∧ x4 = 3072*q+161 ∧ x5 = 9216*q+484 ∧ x6 = 4608*q+242 ∧ x7 = 2304*q+121 ∧ x8 = 6912*q+364 ∧ x9 = 3456*q+182 ∧ x10 = 1728*q+91 ∧ x11 = 5184*q+274 ∧ x12 = 2592*q+137 ∧ x13 = 7776*q+412 ∧ x14 = 3888*q+206 ∧ x15 = 1944*q+103 ∧ x16 = 5832*q+310 ∧ x17 = 2916*q+155 ∧ x18 = 8748*q+466 ∧ x19 = 4374*q+233 ∧ x20 = 13122*q+700 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_0010100100101001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hstep := r19.1
  have hparity := r19.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega

/-- Exact source residue and full affine trace for branch `00101001010010010100`. -/
theorem parameters_00101001010010010100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    : ∃ q : Nat, x0 = 8192*q+7660 ∧ x1 = 4096*q+3830 ∧ x2 = 2048*q+1915 ∧ x3 = 6144*q+5746 ∧ x4 = 3072*q+2873 ∧ x5 = 9216*q+8620 ∧ x6 = 4608*q+4310 ∧ x7 = 2304*q+2155 ∧ x8 = 6912*q+6466 ∧ x9 = 3456*q+3233 ∧ x10 = 10368*q+9700 ∧ x11 = 5184*q+4850 ∧ x12 = 2592*q+2425 ∧ x13 = 7776*q+7276 ∧ x14 = 3888*q+3638 ∧ x15 = 1944*q+1819 ∧ x16 = 5832*q+5458 ∧ x17 = 2916*q+2729 ∧ x18 = 8748*q+8188 ∧ x19 = 4374*q+4094 ∧ x20 = 2187*q+2047 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_0010100101001001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hstep := r19.1
  have hparity := r19.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega

/-- Exact source residue and full affine trace for branch `00101001010010010101`. -/
theorem parameters_00101001010010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (x20 = 3*x19+1 ∧ x19%2 = 1))
    : ∃ q : Nat, x0 = 8192*q+3564 ∧ x1 = 4096*q+1782 ∧ x2 = 2048*q+891 ∧ x3 = 6144*q+2674 ∧ x4 = 3072*q+1337 ∧ x5 = 9216*q+4012 ∧ x6 = 4608*q+2006 ∧ x7 = 2304*q+1003 ∧ x8 = 6912*q+3010 ∧ x9 = 3456*q+1505 ∧ x10 = 10368*q+4516 ∧ x11 = 5184*q+2258 ∧ x12 = 2592*q+1129 ∧ x13 = 7776*q+3388 ∧ x14 = 3888*q+1694 ∧ x15 = 1944*q+847 ∧ x16 = 5832*q+2542 ∧ x17 = 2916*q+1271 ∧ x18 = 8748*q+3814 ∧ x19 = 4374*q+1907 ∧ x20 = 13122*q+5722 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_0010100101001001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hstep := r19.1
  have hparity := r19.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega

/-- Exact source residue and full affine trace for branch `01001001010010100100`. -/
theorem parameters_01001001010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    : ∃ q : Nat, x0 = 8192*q+1346 ∧ x1 = 4096*q+673 ∧ x2 = 12288*q+2020 ∧ x3 = 6144*q+1010 ∧ x4 = 3072*q+505 ∧ x5 = 9216*q+1516 ∧ x6 = 4608*q+758 ∧ x7 = 2304*q+379 ∧ x8 = 6912*q+1138 ∧ x9 = 3456*q+569 ∧ x10 = 10368*q+1708 ∧ x11 = 5184*q+854 ∧ x12 = 2592*q+427 ∧ x13 = 7776*q+1282 ∧ x14 = 3888*q+641 ∧ x15 = 11664*q+1924 ∧ x16 = 5832*q+962 ∧ x17 = 2916*q+481 ∧ x18 = 8748*q+1444 ∧ x19 = 4374*q+722 ∧ x20 = 2187*q+361 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_0100100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hstep := r19.1
  have hparity := r19.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega

/-- Exact source residue and full affine trace for branch `01001001010010100101`. -/
theorem parameters_01001001010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (x20 = 3*x19+1 ∧ x19%2 = 1))
    : ∃ q : Nat, x0 = 8192*q+5442 ∧ x1 = 4096*q+2721 ∧ x2 = 12288*q+8164 ∧ x3 = 6144*q+4082 ∧ x4 = 3072*q+2041 ∧ x5 = 9216*q+6124 ∧ x6 = 4608*q+3062 ∧ x7 = 2304*q+1531 ∧ x8 = 6912*q+4594 ∧ x9 = 3456*q+2297 ∧ x10 = 10368*q+6892 ∧ x11 = 5184*q+3446 ∧ x12 = 2592*q+1723 ∧ x13 = 7776*q+5170 ∧ x14 = 3888*q+2585 ∧ x15 = 11664*q+7756 ∧ x16 = 5832*q+3878 ∧ x17 = 2916*q+1939 ∧ x18 = 8748*q+5818 ∧ x19 = 4374*q+2909 ∧ x20 = 13122*q+8728 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_0100100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hstep := r19.1
  have hparity := r19.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega

/-- Exact source residue and full affine trace for branch `01001010010010100100`. -/
theorem parameters_01001010010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    : ∃ q : Nat, x0 = 8192*q+1650 ∧ x1 = 4096*q+825 ∧ x2 = 12288*q+2476 ∧ x3 = 6144*q+1238 ∧ x4 = 3072*q+619 ∧ x5 = 9216*q+1858 ∧ x6 = 4608*q+929 ∧ x7 = 13824*q+2788 ∧ x8 = 6912*q+1394 ∧ x9 = 3456*q+697 ∧ x10 = 10368*q+2092 ∧ x11 = 5184*q+1046 ∧ x12 = 2592*q+523 ∧ x13 = 7776*q+1570 ∧ x14 = 3888*q+785 ∧ x15 = 11664*q+2356 ∧ x16 = 5832*q+1178 ∧ x17 = 2916*q+589 ∧ x18 = 8748*q+1768 ∧ x19 = 4374*q+884 ∧ x20 = 2187*q+442 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_0100101001001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hstep := r19.1
  have hparity := r19.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega

/-- Exact source residue and full affine trace for branch `01001010010010100101`. -/
theorem parameters_01001010010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (x20 = 3*x19+1 ∧ x19%2 = 1))
    : ∃ q : Nat, x0 = 8192*q+5746 ∧ x1 = 4096*q+2873 ∧ x2 = 12288*q+8620 ∧ x3 = 6144*q+4310 ∧ x4 = 3072*q+2155 ∧ x5 = 9216*q+6466 ∧ x6 = 4608*q+3233 ∧ x7 = 13824*q+9700 ∧ x8 = 6912*q+4850 ∧ x9 = 3456*q+2425 ∧ x10 = 10368*q+7276 ∧ x11 = 5184*q+3638 ∧ x12 = 2592*q+1819 ∧ x13 = 7776*q+5458 ∧ x14 = 3888*q+2729 ∧ x15 = 11664*q+8188 ∧ x16 = 5832*q+4094 ∧ x17 = 2916*q+2047 ∧ x18 = 8748*q+6142 ∧ x19 = 4374*q+3071 ∧ x20 = 13122*q+9214 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_0100101001001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hstep := r19.1
  have hparity := r19.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega

/-- Exact source residue and full affine trace for branch `01001010010100100100`. -/
theorem parameters_01001010010100100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    : ∃ q : Nat, x0 = 8192*q+1010 ∧ x1 = 4096*q+505 ∧ x2 = 12288*q+1516 ∧ x3 = 6144*q+758 ∧ x4 = 3072*q+379 ∧ x5 = 9216*q+1138 ∧ x6 = 4608*q+569 ∧ x7 = 13824*q+1708 ∧ x8 = 6912*q+854 ∧ x9 = 3456*q+427 ∧ x10 = 10368*q+1282 ∧ x11 = 5184*q+641 ∧ x12 = 15552*q+1924 ∧ x13 = 7776*q+962 ∧ x14 = 3888*q+481 ∧ x15 = 11664*q+1444 ∧ x16 = 5832*q+722 ∧ x17 = 2916*q+361 ∧ x18 = 8748*q+1084 ∧ x19 = 4374*q+542 ∧ x20 = 2187*q+271 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_0100101001010010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hstep := r19.1
  have hparity := r19.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega

/-- Exact source residue and full affine trace for branch `01001010010100100101`. -/
theorem parameters_01001010010100100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (x20 = 3*x19+1 ∧ x19%2 = 1))
    : ∃ q : Nat, x0 = 8192*q+5106 ∧ x1 = 4096*q+2553 ∧ x2 = 12288*q+7660 ∧ x3 = 6144*q+3830 ∧ x4 = 3072*q+1915 ∧ x5 = 9216*q+5746 ∧ x6 = 4608*q+2873 ∧ x7 = 13824*q+8620 ∧ x8 = 6912*q+4310 ∧ x9 = 3456*q+2155 ∧ x10 = 10368*q+6466 ∧ x11 = 5184*q+3233 ∧ x12 = 15552*q+9700 ∧ x13 = 7776*q+4850 ∧ x14 = 3888*q+2425 ∧ x15 = 11664*q+7276 ∧ x16 = 5832*q+3638 ∧ x17 = 2916*q+1819 ∧ x18 = 8748*q+5458 ∧ x19 = 4374*q+2729 ∧ x20 = 13122*q+8188 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_0100101001010010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hstep := r19.1
  have hparity := r19.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega

/-- Exact source residue and full affine trace for branch `01010010010100101000`. -/
theorem parameters_01010010010100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    : ∃ q : Nat, x0 = 8192*q+2262 ∧ x1 = 4096*q+1131 ∧ x2 = 12288*q+3394 ∧ x3 = 6144*q+1697 ∧ x4 = 18432*q+5092 ∧ x5 = 9216*q+2546 ∧ x6 = 4608*q+1273 ∧ x7 = 13824*q+3820 ∧ x8 = 6912*q+1910 ∧ x9 = 3456*q+955 ∧ x10 = 10368*q+2866 ∧ x11 = 5184*q+1433 ∧ x12 = 15552*q+4300 ∧ x13 = 7776*q+2150 ∧ x14 = 3888*q+1075 ∧ x15 = 11664*q+3226 ∧ x16 = 5832*q+1613 ∧ x17 = 17496*q+4840 ∧ x18 = 8748*q+2420 ∧ x19 = 4374*q+1210 ∧ x20 = 2187*q+605 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_0101001001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hstep := r19.1
  have hparity := r19.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega

/-- Exact source residue and full affine trace for branch `01010010010100101001`. -/
theorem parameters_01010010010100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (x20 = 3*x19+1 ∧ x19%2 = 1))
    : ∃ q : Nat, x0 = 8192*q+6358 ∧ x1 = 4096*q+3179 ∧ x2 = 12288*q+9538 ∧ x3 = 6144*q+4769 ∧ x4 = 18432*q+14308 ∧ x5 = 9216*q+7154 ∧ x6 = 4608*q+3577 ∧ x7 = 13824*q+10732 ∧ x8 = 6912*q+5366 ∧ x9 = 3456*q+2683 ∧ x10 = 10368*q+8050 ∧ x11 = 5184*q+4025 ∧ x12 = 15552*q+12076 ∧ x13 = 7776*q+6038 ∧ x14 = 3888*q+3019 ∧ x15 = 11664*q+9058 ∧ x16 = 5832*q+4529 ∧ x17 = 17496*q+13588 ∧ x18 = 8748*q+6794 ∧ x19 = 4374*q+3397 ∧ x20 = 13122*q+10192 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_0101001001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hstep := r19.1
  have hparity := r19.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega

/-- Exact source residue and full affine trace for branch `01010010100100101000`. -/
theorem parameters_01010010100100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    : ∃ q : Nat, x0 = 8192*q+7926 ∧ x1 = 4096*q+3963 ∧ x2 = 12288*q+11890 ∧ x3 = 6144*q+5945 ∧ x4 = 18432*q+17836 ∧ x5 = 9216*q+8918 ∧ x6 = 4608*q+4459 ∧ x7 = 13824*q+13378 ∧ x8 = 6912*q+6689 ∧ x9 = 20736*q+20068 ∧ x10 = 10368*q+10034 ∧ x11 = 5184*q+5017 ∧ x12 = 15552*q+15052 ∧ x13 = 7776*q+7526 ∧ x14 = 3888*q+3763 ∧ x15 = 11664*q+11290 ∧ x16 = 5832*q+5645 ∧ x17 = 17496*q+16936 ∧ x18 = 8748*q+8468 ∧ x19 = 4374*q+4234 ∧ x20 = 2187*q+2117 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_0101001010010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hstep := r19.1
  have hparity := r19.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega

/-- Exact source residue and full affine trace for branch `01010010100100101001`. -/
theorem parameters_01010010100100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (x20 = 3*x19+1 ∧ x19%2 = 1))
    : ∃ q : Nat, x0 = 8192*q+3830 ∧ x1 = 4096*q+1915 ∧ x2 = 12288*q+5746 ∧ x3 = 6144*q+2873 ∧ x4 = 18432*q+8620 ∧ x5 = 9216*q+4310 ∧ x6 = 4608*q+2155 ∧ x7 = 13824*q+6466 ∧ x8 = 6912*q+3233 ∧ x9 = 20736*q+9700 ∧ x10 = 10368*q+4850 ∧ x11 = 5184*q+2425 ∧ x12 = 15552*q+7276 ∧ x13 = 7776*q+3638 ∧ x14 = 3888*q+1819 ∧ x15 = 11664*q+5458 ∧ x16 = 5832*q+2729 ∧ x17 = 17496*q+8188 ∧ x18 = 8748*q+4094 ∧ x19 = 4374*q+2047 ∧ x20 = 13122*q+6142 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_0101001010010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hstep := r19.1
  have hparity := r19.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega

/-- Exact source residue and full affine trace for branch `10010100100101001010`. -/
theorem parameters_10010100100101001010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Nat)
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
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    : ∃ q : Nat, x0 = 4096*q+2873 ∧ x1 = 12288*q+8620 ∧ x2 = 6144*q+4310 ∧ x3 = 3072*q+2155 ∧ x4 = 9216*q+6466 ∧ x5 = 4608*q+3233 ∧ x6 = 13824*q+9700 ∧ x7 = 6912*q+4850 ∧ x8 = 3456*q+2425 ∧ x9 = 10368*q+7276 ∧ x10 = 5184*q+3638 ∧ x11 = 2592*q+1819 ∧ x12 = 7776*q+5458 ∧ x13 = 3888*q+2729 ∧ x14 = 11664*q+8188 ∧ x15 = 5832*q+4094 ∧ x16 = 2916*q+2047 ∧ x17 = 8748*q+6142 ∧ x18 = 4374*q+3071 ∧ x19 = 13122*q+9214 ∧ x20 = 6561*q+4607 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_1001010010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hstep := r19.1
  have hparity := r19.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · exact p8
  · exact p9
  · exact p10
  · exact p11
  · exact p12
  · exact p13
  · exact p14
  · exact p15
  · exact p16
  · exact p17
  · exact p18
  · exact p19
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega

/-- Exact source residue and full affine trace for branch `10010100101001001010`. -/
theorem parameters_10010100101001001010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Nat)
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
    : ∃ q : Nat, x0 = 4096*q+2553 ∧ x1 = 12288*q+7660 ∧ x2 = 6144*q+3830 ∧ x3 = 3072*q+1915 ∧ x4 = 9216*q+5746 ∧ x5 = 4608*q+2873 ∧ x6 = 13824*q+8620 ∧ x7 = 6912*q+4310 ∧ x8 = 3456*q+2155 ∧ x9 = 10368*q+6466 ∧ x10 = 5184*q+3233 ∧ x11 = 15552*q+9700 ∧ x12 = 7776*q+4850 ∧ x13 = 3888*q+2425 ∧ x14 = 11664*q+7276 ∧ x15 = 5832*q+3638 ∧ x16 = 2916*q+1819 ∧ x17 = 8748*q+5458 ∧ x18 = 4374*q+2729 ∧ x19 = 13122*q+8188 ∧ x20 = 6561*q+4094 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_1001010010100100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hstep := r19.1
  have hparity := r19.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · exact p8
  · exact p9
  · exact p10
  · exact p11
  · exact p12
  · exact p13
  · exact p14
  · exact p15
  · exact p16
  · exact p17
  · exact p18
  · exact p19
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega

/-- Exact source residue and full affine trace for branch `10100100101001010010`. -/
theorem parameters_10100100101001010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Nat)
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
    : ∃ q : Nat, x0 = 4096*q+3179 ∧ x1 = 12288*q+9538 ∧ x2 = 6144*q+4769 ∧ x3 = 18432*q+14308 ∧ x4 = 9216*q+7154 ∧ x5 = 4608*q+3577 ∧ x6 = 13824*q+10732 ∧ x7 = 6912*q+5366 ∧ x8 = 3456*q+2683 ∧ x9 = 10368*q+8050 ∧ x10 = 5184*q+4025 ∧ x11 = 15552*q+12076 ∧ x12 = 7776*q+6038 ∧ x13 = 3888*q+3019 ∧ x14 = 11664*q+9058 ∧ x15 = 5832*q+4529 ∧ x16 = 17496*q+13588 ∧ x17 = 8748*q+6794 ∧ x18 = 4374*q+3397 ∧ x19 = 13122*q+10192 ∧ x20 = 6561*q+5096 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩ := parameters_1010010010100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  have hstep := r19.1
  have hparity := r19.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · exact p8
  · exact p9
  · exact p10
  · exact p11
  · exact p12
  · exact p13
  · exact p14
  · exact p15
  · exact p16
  · exact p17
  · exact p18
  · exact p19
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18
    omega


end Collatz.Exploration.ElevenHalvesArithmetic
