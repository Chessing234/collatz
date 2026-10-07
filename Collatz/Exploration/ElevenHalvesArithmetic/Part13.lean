import Collatz.Exploration.ElevenHalvesArithmetic.Part12

namespace Collatz.Exploration.ElevenHalvesArithmetic

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- Exact source residue and full affine trace for branch `0100101001001010010100100`. -/
theorem parameters_0100101001001010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : Nat)
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
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    (r22 : (x23 = 3*x22+1 ∧ x22%2 = 1))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    : ∃ q : Nat, x0 = 65536*q+30322 ∧ x1 = 32768*q+15161 ∧ x2 = 98304*q+45484 ∧ x3 = 49152*q+22742 ∧ x4 = 24576*q+11371 ∧ x5 = 73728*q+34114 ∧ x6 = 36864*q+17057 ∧ x7 = 110592*q+51172 ∧ x8 = 55296*q+25586 ∧ x9 = 27648*q+12793 ∧ x10 = 82944*q+38380 ∧ x11 = 41472*q+19190 ∧ x12 = 20736*q+9595 ∧ x13 = 62208*q+28786 ∧ x14 = 31104*q+14393 ∧ x15 = 93312*q+43180 ∧ x16 = 46656*q+21590 ∧ x17 = 23328*q+10795 ∧ x18 = 69984*q+32386 ∧ x19 = 34992*q+16193 ∧ x20 = 104976*q+48580 ∧ x21 = 52488*q+24290 ∧ x22 = 26244*q+12145 ∧ x23 = 78732*q+36436 ∧ x24 = 39366*q+18218 ∧ x25 = 19683*q+9109 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24⟩ := parameters_010010100100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
  have hstep := r24.1
  have hparity := r24.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p22 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23
    omega

/-- Exact source residue and full affine trace for branch `0100101001001010010100101`. -/
theorem parameters_0100101001001010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : Nat)
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
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    (r22 : (x23 = 3*x22+1 ∧ x22%2 = 1))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (x25 = 3*x24+1 ∧ x24%2 = 1))
    : ∃ q : Nat, x0 = 65536*q+63090 ∧ x1 = 32768*q+31545 ∧ x2 = 98304*q+94636 ∧ x3 = 49152*q+47318 ∧ x4 = 24576*q+23659 ∧ x5 = 73728*q+70978 ∧ x6 = 36864*q+35489 ∧ x7 = 110592*q+106468 ∧ x8 = 55296*q+53234 ∧ x9 = 27648*q+26617 ∧ x10 = 82944*q+79852 ∧ x11 = 41472*q+39926 ∧ x12 = 20736*q+19963 ∧ x13 = 62208*q+59890 ∧ x14 = 31104*q+29945 ∧ x15 = 93312*q+89836 ∧ x16 = 46656*q+44918 ∧ x17 = 23328*q+22459 ∧ x18 = 69984*q+67378 ∧ x19 = 34992*q+33689 ∧ x20 = 104976*q+101068 ∧ x21 = 52488*q+50534 ∧ x22 = 26244*q+25267 ∧ x23 = 78732*q+75802 ∧ x24 = 39366*q+37901 ∧ x25 = 118098*q+113704 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24⟩ := parameters_010010100100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
  have hstep := r24.1
  have hparity := r24.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p22 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23
    omega

/-- Exact source residue and full affine trace for branch `0100101001010010010100100`. -/
theorem parameters_0100101001010010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : Nat)
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
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    (r22 : (x23 = 3*x22+1 ∧ x22%2 = 1))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    : ∃ q : Nat, x0 = 65536*q+37874 ∧ x1 = 32768*q+18937 ∧ x2 = 98304*q+56812 ∧ x3 = 49152*q+28406 ∧ x4 = 24576*q+14203 ∧ x5 = 73728*q+42610 ∧ x6 = 36864*q+21305 ∧ x7 = 110592*q+63916 ∧ x8 = 55296*q+31958 ∧ x9 = 27648*q+15979 ∧ x10 = 82944*q+47938 ∧ x11 = 41472*q+23969 ∧ x12 = 124416*q+71908 ∧ x13 = 62208*q+35954 ∧ x14 = 31104*q+17977 ∧ x15 = 93312*q+53932 ∧ x16 = 46656*q+26966 ∧ x17 = 23328*q+13483 ∧ x18 = 69984*q+40450 ∧ x19 = 34992*q+20225 ∧ x20 = 104976*q+60676 ∧ x21 = 52488*q+30338 ∧ x22 = 26244*q+15169 ∧ x23 = 78732*q+45508 ∧ x24 = 39366*q+22754 ∧ x25 = 19683*q+11377 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24⟩ := parameters_010010100101001001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
  have hstep := r24.1
  have hparity := r24.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p22 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23
    omega

/-- Exact source residue and full affine trace for branch `0100101001010010010100101`. -/
theorem parameters_0100101001010010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : Nat)
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
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    (r22 : (x23 = 3*x22+1 ∧ x22%2 = 1))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (x25 = 3*x24+1 ∧ x24%2 = 1))
    : ∃ q : Nat, x0 = 65536*q+5106 ∧ x1 = 32768*q+2553 ∧ x2 = 98304*q+7660 ∧ x3 = 49152*q+3830 ∧ x4 = 24576*q+1915 ∧ x5 = 73728*q+5746 ∧ x6 = 36864*q+2873 ∧ x7 = 110592*q+8620 ∧ x8 = 55296*q+4310 ∧ x9 = 27648*q+2155 ∧ x10 = 82944*q+6466 ∧ x11 = 41472*q+3233 ∧ x12 = 124416*q+9700 ∧ x13 = 62208*q+4850 ∧ x14 = 31104*q+2425 ∧ x15 = 93312*q+7276 ∧ x16 = 46656*q+3638 ∧ x17 = 23328*q+1819 ∧ x18 = 69984*q+5458 ∧ x19 = 34992*q+2729 ∧ x20 = 104976*q+8188 ∧ x21 = 52488*q+4094 ∧ x22 = 26244*q+2047 ∧ x23 = 78732*q+6142 ∧ x24 = 39366*q+3071 ∧ x25 = 118098*q+9214 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24⟩ := parameters_010010100101001001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
  have hstep := r24.1
  have hparity := r24.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p22 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23
    omega

/-- Exact source residue and full affine trace for branch `0101001010010010100101000`. -/
theorem parameters_0101001010010010100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : Nat)
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
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (x22 = 3*x21+1 ∧ x21%2 = 1))
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    : ∃ q : Nat, x0 = 65536*q+52982 ∧ x1 = 32768*q+26491 ∧ x2 = 98304*q+79474 ∧ x3 = 49152*q+39737 ∧ x4 = 147456*q+119212 ∧ x5 = 73728*q+59606 ∧ x6 = 36864*q+29803 ∧ x7 = 110592*q+89410 ∧ x8 = 55296*q+44705 ∧ x9 = 165888*q+134116 ∧ x10 = 82944*q+67058 ∧ x11 = 41472*q+33529 ∧ x12 = 124416*q+100588 ∧ x13 = 62208*q+50294 ∧ x14 = 31104*q+25147 ∧ x15 = 93312*q+75442 ∧ x16 = 46656*q+37721 ∧ x17 = 139968*q+113164 ∧ x18 = 69984*q+56582 ∧ x19 = 34992*q+28291 ∧ x20 = 104976*q+84874 ∧ x21 = 52488*q+42437 ∧ x22 = 157464*q+127312 ∧ x23 = 78732*q+63656 ∧ x24 = 39366*q+31828 ∧ x25 = 19683*q+15914 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24⟩ := parameters_010100101001001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
  have hstep := r24.1
  have hparity := r24.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p22 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23
    omega

/-- Exact source residue and full affine trace for branch `0101001010010010100101001`. -/
theorem parameters_0101001010010010100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : Nat)
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
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (x22 = 3*x21+1 ∧ x21%2 = 1))
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (x25 = 3*x24+1 ∧ x24%2 = 1))
    : ∃ q : Nat, x0 = 65536*q+20214 ∧ x1 = 32768*q+10107 ∧ x2 = 98304*q+30322 ∧ x3 = 49152*q+15161 ∧ x4 = 147456*q+45484 ∧ x5 = 73728*q+22742 ∧ x6 = 36864*q+11371 ∧ x7 = 110592*q+34114 ∧ x8 = 55296*q+17057 ∧ x9 = 165888*q+51172 ∧ x10 = 82944*q+25586 ∧ x11 = 41472*q+12793 ∧ x12 = 124416*q+38380 ∧ x13 = 62208*q+19190 ∧ x14 = 31104*q+9595 ∧ x15 = 93312*q+28786 ∧ x16 = 46656*q+14393 ∧ x17 = 139968*q+43180 ∧ x18 = 69984*q+21590 ∧ x19 = 34992*q+10795 ∧ x20 = 104976*q+32386 ∧ x21 = 52488*q+16193 ∧ x22 = 157464*q+48580 ∧ x23 = 78732*q+24290 ∧ x24 = 39366*q+12145 ∧ x25 = 118098*q+36436 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24⟩ := parameters_010100101001001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
  have hstep := r24.1
  have hparity := r24.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p22 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23
    omega

/-- Exact source residue and full affine trace for branch `1001010010100100101001010`. -/
theorem parameters_1001010010100100101001010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : Nat)
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
    : ∃ q : Nat, x0 = 32768*q+2553 ∧ x1 = 98304*q+7660 ∧ x2 = 49152*q+3830 ∧ x3 = 24576*q+1915 ∧ x4 = 73728*q+5746 ∧ x5 = 36864*q+2873 ∧ x6 = 110592*q+8620 ∧ x7 = 55296*q+4310 ∧ x8 = 27648*q+2155 ∧ x9 = 82944*q+6466 ∧ x10 = 41472*q+3233 ∧ x11 = 124416*q+9700 ∧ x12 = 62208*q+4850 ∧ x13 = 31104*q+2425 ∧ x14 = 93312*q+7276 ∧ x15 = 46656*q+3638 ∧ x16 = 23328*q+1819 ∧ x17 = 69984*q+5458 ∧ x18 = 34992*q+2729 ∧ x19 = 104976*q+8188 ∧ x20 = 52488*q+4094 ∧ x21 = 26244*q+2047 ∧ x22 = 78732*q+6142 ∧ x23 = 39366*q+3071 ∧ x24 = 118098*q+9214 ∧ x25 = 59049*q+4607 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24⟩ := parameters_100101001010010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
  have hstep := r24.1
  have hparity := r24.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · exact p20
  · exact p21
  · exact p22
  · exact p23
  · exact p24
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23
    omega

/-- Exact source residue and full affine trace for branch `1010010100100101001010010`. -/
theorem parameters_1010010100100101001010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : Nat)
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
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (x21 = 3*x20+1 ∧ x20%2 = 1))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    (r23 : (x24 = 3*x23+1 ∧ x23%2 = 1))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    : ∃ q : Nat, x0 = 32768*q+10107 ∧ x1 = 98304*q+30322 ∧ x2 = 49152*q+15161 ∧ x3 = 147456*q+45484 ∧ x4 = 73728*q+22742 ∧ x5 = 36864*q+11371 ∧ x6 = 110592*q+34114 ∧ x7 = 55296*q+17057 ∧ x8 = 165888*q+51172 ∧ x9 = 82944*q+25586 ∧ x10 = 41472*q+12793 ∧ x11 = 124416*q+38380 ∧ x12 = 62208*q+19190 ∧ x13 = 31104*q+9595 ∧ x14 = 93312*q+28786 ∧ x15 = 46656*q+14393 ∧ x16 = 139968*q+43180 ∧ x17 = 69984*q+21590 ∧ x18 = 34992*q+10795 ∧ x19 = 104976*q+32386 ∧ x20 = 52488*q+16193 ∧ x21 = 157464*q+48580 ∧ x22 = 78732*q+24290 ∧ x23 = 39366*q+12145 ∧ x24 = 118098*q+36436 ∧ x25 = 59049*q+18218 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24⟩ := parameters_101001010010010100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
  have hstep := r24.1
  have hparity := r24.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · exact p20
  · exact p21
  · exact p22
  · exact p23
  · exact p24
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23
    omega

/-- Exact source residue and full affine trace for branch `00101001010010010100101000`. -/
theorem parameters_00101001010010010100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 : Nat)
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
    (r20 : (x21 = 3*x20+1 ∧ x20%2 = 1))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    (r22 : (x23 = 3*x22+1 ∧ x22%2 = 1))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    : ∃ q : Nat, x0 = 131072*q+105964 ∧ x1 = 65536*q+52982 ∧ x2 = 32768*q+26491 ∧ x3 = 98304*q+79474 ∧ x4 = 49152*q+39737 ∧ x5 = 147456*q+119212 ∧ x6 = 73728*q+59606 ∧ x7 = 36864*q+29803 ∧ x8 = 110592*q+89410 ∧ x9 = 55296*q+44705 ∧ x10 = 165888*q+134116 ∧ x11 = 82944*q+67058 ∧ x12 = 41472*q+33529 ∧ x13 = 124416*q+100588 ∧ x14 = 62208*q+50294 ∧ x15 = 31104*q+25147 ∧ x16 = 93312*q+75442 ∧ x17 = 46656*q+37721 ∧ x18 = 139968*q+113164 ∧ x19 = 69984*q+56582 ∧ x20 = 34992*q+28291 ∧ x21 = 104976*q+84874 ∧ x22 = 52488*q+42437 ∧ x23 = 157464*q+127312 ∧ x24 = 78732*q+63656 ∧ x25 = 39366*q+31828 ∧ x26 = 19683*q+15914 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25⟩ := parameters_0010100101001001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24
  have hstep := r25.1
  have hparity := r25.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p22 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p25 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24
    omega

/-- Exact source residue and full affine trace for branch `00101001010010010100101001`. -/
theorem parameters_00101001010010010100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 : Nat)
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
    (r20 : (x21 = 3*x20+1 ∧ x20%2 = 1))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    (r22 : (x23 = 3*x22+1 ∧ x22%2 = 1))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    (r25 : (x26 = 3*x25+1 ∧ x25%2 = 1))
    : ∃ q : Nat, x0 = 131072*q+40428 ∧ x1 = 65536*q+20214 ∧ x2 = 32768*q+10107 ∧ x3 = 98304*q+30322 ∧ x4 = 49152*q+15161 ∧ x5 = 147456*q+45484 ∧ x6 = 73728*q+22742 ∧ x7 = 36864*q+11371 ∧ x8 = 110592*q+34114 ∧ x9 = 55296*q+17057 ∧ x10 = 165888*q+51172 ∧ x11 = 82944*q+25586 ∧ x12 = 41472*q+12793 ∧ x13 = 124416*q+38380 ∧ x14 = 62208*q+19190 ∧ x15 = 31104*q+9595 ∧ x16 = 93312*q+28786 ∧ x17 = 46656*q+14393 ∧ x18 = 139968*q+43180 ∧ x19 = 69984*q+21590 ∧ x20 = 34992*q+10795 ∧ x21 = 104976*q+32386 ∧ x22 = 52488*q+16193 ∧ x23 = 157464*q+48580 ∧ x24 = 78732*q+24290 ∧ x25 = 39366*q+12145 ∧ x26 = 118098*q+36436 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25⟩ := parameters_0010100101001001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24
  have hstep := r25.1
  have hparity := r25.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p22 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p25 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24
    omega

/-- Exact source residue and full affine trace for branch `01001010010100100101001010`. -/
theorem parameters_01001010010100100101001010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 : Nat)
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
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    (r22 : (x23 = 3*x22+1 ∧ x22%2 = 1))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (x25 = 3*x24+1 ∧ x24%2 = 1))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    : ∃ q : Nat, x0 = 65536*q+5106 ∧ x1 = 32768*q+2553 ∧ x2 = 98304*q+7660 ∧ x3 = 49152*q+3830 ∧ x4 = 24576*q+1915 ∧ x5 = 73728*q+5746 ∧ x6 = 36864*q+2873 ∧ x7 = 110592*q+8620 ∧ x8 = 55296*q+4310 ∧ x9 = 27648*q+2155 ∧ x10 = 82944*q+6466 ∧ x11 = 41472*q+3233 ∧ x12 = 124416*q+9700 ∧ x13 = 62208*q+4850 ∧ x14 = 31104*q+2425 ∧ x15 = 93312*q+7276 ∧ x16 = 46656*q+3638 ∧ x17 = 23328*q+1819 ∧ x18 = 69984*q+5458 ∧ x19 = 34992*q+2729 ∧ x20 = 104976*q+8188 ∧ x21 = 52488*q+4094 ∧ x22 = 26244*q+2047 ∧ x23 = 78732*q+6142 ∧ x24 = 39366*q+3071 ∧ x25 = 118098*q+9214 ∧ x26 = 59049*q+4607 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25⟩ := parameters_0100101001010010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24
  have hstep := r25.1
  have hparity := r25.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · exact p20
  · exact p21
  · exact p22
  · exact p23
  · exact p24
  · exact p25
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24
    omega

/-- Exact source residue and full affine trace for branch `01010010100100101001010010`. -/
theorem parameters_01010010100100101001010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 : Nat)
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
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (x22 = 3*x21+1 ∧ x21%2 = 1))
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (x25 = 3*x24+1 ∧ x24%2 = 1))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    : ∃ q : Nat, x0 = 65536*q+20214 ∧ x1 = 32768*q+10107 ∧ x2 = 98304*q+30322 ∧ x3 = 49152*q+15161 ∧ x4 = 147456*q+45484 ∧ x5 = 73728*q+22742 ∧ x6 = 36864*q+11371 ∧ x7 = 110592*q+34114 ∧ x8 = 55296*q+17057 ∧ x9 = 165888*q+51172 ∧ x10 = 82944*q+25586 ∧ x11 = 41472*q+12793 ∧ x12 = 124416*q+38380 ∧ x13 = 62208*q+19190 ∧ x14 = 31104*q+9595 ∧ x15 = 93312*q+28786 ∧ x16 = 46656*q+14393 ∧ x17 = 139968*q+43180 ∧ x18 = 69984*q+21590 ∧ x19 = 34992*q+10795 ∧ x20 = 104976*q+32386 ∧ x21 = 52488*q+16193 ∧ x22 = 157464*q+48580 ∧ x23 = 78732*q+24290 ∧ x24 = 39366*q+12145 ∧ x25 = 118098*q+36436 ∧ x26 = 59049*q+18218 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25⟩ := parameters_0101001010010010100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24
  have hstep := r25.1
  have hparity := r25.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · exact p20
  · exact p21
  · exact p22
  · exact p23
  · exact p24
  · exact p25
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24
    omega

/-- Exact source residue and full affine trace for branch `10010100101001001010010100`. -/
theorem parameters_10010100101001001010010100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 : Nat)
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
    : ∃ q : Nat, x0 = 65536*q+35321 ∧ x1 = 196608*q+105964 ∧ x2 = 98304*q+52982 ∧ x3 = 49152*q+26491 ∧ x4 = 147456*q+79474 ∧ x5 = 73728*q+39737 ∧ x6 = 221184*q+119212 ∧ x7 = 110592*q+59606 ∧ x8 = 55296*q+29803 ∧ x9 = 165888*q+89410 ∧ x10 = 82944*q+44705 ∧ x11 = 248832*q+134116 ∧ x12 = 124416*q+67058 ∧ x13 = 62208*q+33529 ∧ x14 = 186624*q+100588 ∧ x15 = 93312*q+50294 ∧ x16 = 46656*q+25147 ∧ x17 = 139968*q+75442 ∧ x18 = 69984*q+37721 ∧ x19 = 209952*q+113164 ∧ x20 = 104976*q+56582 ∧ x21 = 52488*q+28291 ∧ x22 = 157464*q+84874 ∧ x23 = 78732*q+42437 ∧ x24 = 236196*q+127312 ∧ x25 = 118098*q+63656 ∧ x26 = 59049*q+31828 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25⟩ := parameters_1001010010100100101001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24
  have hstep := r25.1
  have hparity := r25.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p22 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p25 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24
    omega

/-- Exact source residue and full affine trace for branch `10010100101001001010010101`. -/
theorem parameters_10010100101001001010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 : Nat)
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
    : ∃ q : Nat, x0 = 65536*q+2553 ∧ x1 = 196608*q+7660 ∧ x2 = 98304*q+3830 ∧ x3 = 49152*q+1915 ∧ x4 = 147456*q+5746 ∧ x5 = 73728*q+2873 ∧ x6 = 221184*q+8620 ∧ x7 = 110592*q+4310 ∧ x8 = 55296*q+2155 ∧ x9 = 165888*q+6466 ∧ x10 = 82944*q+3233 ∧ x11 = 248832*q+9700 ∧ x12 = 124416*q+4850 ∧ x13 = 62208*q+2425 ∧ x14 = 186624*q+7276 ∧ x15 = 93312*q+3638 ∧ x16 = 46656*q+1819 ∧ x17 = 139968*q+5458 ∧ x18 = 69984*q+2729 ∧ x19 = 209952*q+8188 ∧ x20 = 104976*q+4094 ∧ x21 = 52488*q+2047 ∧ x22 = 157464*q+6142 ∧ x23 = 78732*q+3071 ∧ x24 = 236196*q+9214 ∧ x25 = 118098*q+4607 ∧ x26 = 354294*q+13822 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25⟩ := parameters_1001010010100100101001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24
  have hstep := r25.1
  have hparity := r25.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p22 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p25 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24
    omega

/-- Exact source residue and full affine trace for branch `10100101001001010010100100`. -/
theorem parameters_10100101001001010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 : Nat)
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
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (x21 = 3*x20+1 ∧ x20%2 = 1))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    (r23 : (x24 = 3*x23+1 ∧ x23%2 = 1))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    : ∃ q : Nat, x0 = 65536*q+10107 ∧ x1 = 196608*q+30322 ∧ x2 = 98304*q+15161 ∧ x3 = 294912*q+45484 ∧ x4 = 147456*q+22742 ∧ x5 = 73728*q+11371 ∧ x6 = 221184*q+34114 ∧ x7 = 110592*q+17057 ∧ x8 = 331776*q+51172 ∧ x9 = 165888*q+25586 ∧ x10 = 82944*q+12793 ∧ x11 = 248832*q+38380 ∧ x12 = 124416*q+19190 ∧ x13 = 62208*q+9595 ∧ x14 = 186624*q+28786 ∧ x15 = 93312*q+14393 ∧ x16 = 279936*q+43180 ∧ x17 = 139968*q+21590 ∧ x18 = 69984*q+10795 ∧ x19 = 209952*q+32386 ∧ x20 = 104976*q+16193 ∧ x21 = 314928*q+48580 ∧ x22 = 157464*q+24290 ∧ x23 = 78732*q+12145 ∧ x24 = 236196*q+36436 ∧ x25 = 118098*q+18218 ∧ x26 = 59049*q+9109 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25⟩ := parameters_1010010100100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24
  have hstep := r25.1
  have hparity := r25.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p22 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p25 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24
    omega

/-- Exact source residue and full affine trace for branch `10100101001001010010100101`. -/
theorem parameters_10100101001001010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 : Nat)
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
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (x21 = 3*x20+1 ∧ x20%2 = 1))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    (r23 : (x24 = 3*x23+1 ∧ x23%2 = 1))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    (r25 : (x26 = 3*x25+1 ∧ x25%2 = 1))
    : ∃ q : Nat, x0 = 65536*q+42875 ∧ x1 = 196608*q+128626 ∧ x2 = 98304*q+64313 ∧ x3 = 294912*q+192940 ∧ x4 = 147456*q+96470 ∧ x5 = 73728*q+48235 ∧ x6 = 221184*q+144706 ∧ x7 = 110592*q+72353 ∧ x8 = 331776*q+217060 ∧ x9 = 165888*q+108530 ∧ x10 = 82944*q+54265 ∧ x11 = 248832*q+162796 ∧ x12 = 124416*q+81398 ∧ x13 = 62208*q+40699 ∧ x14 = 186624*q+122098 ∧ x15 = 93312*q+61049 ∧ x16 = 279936*q+183148 ∧ x17 = 139968*q+91574 ∧ x18 = 69984*q+45787 ∧ x19 = 209952*q+137362 ∧ x20 = 104976*q+68681 ∧ x21 = 314928*q+206044 ∧ x22 = 157464*q+103022 ∧ x23 = 78732*q+51511 ∧ x24 = 236196*q+154534 ∧ x25 = 118098*q+77267 ∧ x26 = 354294*q+231802 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25⟩ := parameters_1010010100100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24
  have hstep := r25.1
  have hparity := r25.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p22 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p25 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24
    omega

/-- Exact source residue and full affine trace for branch `001010010100100101001010010`. -/
theorem parameters_001010010100100101001010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : Nat)
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
    (r20 : (x21 = 3*x20+1 ∧ x20%2 = 1))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    (r22 : (x23 = 3*x22+1 ∧ x22%2 = 1))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    (r25 : (x26 = 3*x25+1 ∧ x25%2 = 1))
    (r26 : (2*x27 = x26 ∧ x26%2 = 0))
    : ∃ q : Nat, x0 = 131072*q+40428 ∧ x1 = 65536*q+20214 ∧ x2 = 32768*q+10107 ∧ x3 = 98304*q+30322 ∧ x4 = 49152*q+15161 ∧ x5 = 147456*q+45484 ∧ x6 = 73728*q+22742 ∧ x7 = 36864*q+11371 ∧ x8 = 110592*q+34114 ∧ x9 = 55296*q+17057 ∧ x10 = 165888*q+51172 ∧ x11 = 82944*q+25586 ∧ x12 = 41472*q+12793 ∧ x13 = 124416*q+38380 ∧ x14 = 62208*q+19190 ∧ x15 = 31104*q+9595 ∧ x16 = 93312*q+28786 ∧ x17 = 46656*q+14393 ∧ x18 = 139968*q+43180 ∧ x19 = 69984*q+21590 ∧ x20 = 34992*q+10795 ∧ x21 = 104976*q+32386 ∧ x22 = 52488*q+16193 ∧ x23 = 157464*q+48580 ∧ x24 = 78732*q+24290 ∧ x25 = 39366*q+12145 ∧ x26 = 118098*q+36436 ∧ x27 = 59049*q+18218 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26⟩ := parameters_00101001010010010100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
  have hstep := r26.1
  have hparity := r26.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · exact p20
  · exact p21
  · exact p22
  · exact p23
  · exact p24
  · exact p25
  · exact p26
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25
    omega

/-- Exact source residue and full affine trace for branch `010010100101001001010010100`. -/
theorem parameters_010010100101001001010010100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : Nat)
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
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    (r22 : (x23 = 3*x22+1 ∧ x22%2 = 1))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (x25 = 3*x24+1 ∧ x24%2 = 1))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    (r26 : (2*x27 = x26 ∧ x26%2 = 0))
    : ∃ q : Nat, x0 = 131072*q+70642 ∧ x1 = 65536*q+35321 ∧ x2 = 196608*q+105964 ∧ x3 = 98304*q+52982 ∧ x4 = 49152*q+26491 ∧ x5 = 147456*q+79474 ∧ x6 = 73728*q+39737 ∧ x7 = 221184*q+119212 ∧ x8 = 110592*q+59606 ∧ x9 = 55296*q+29803 ∧ x10 = 165888*q+89410 ∧ x11 = 82944*q+44705 ∧ x12 = 248832*q+134116 ∧ x13 = 124416*q+67058 ∧ x14 = 62208*q+33529 ∧ x15 = 186624*q+100588 ∧ x16 = 93312*q+50294 ∧ x17 = 46656*q+25147 ∧ x18 = 139968*q+75442 ∧ x19 = 69984*q+37721 ∧ x20 = 209952*q+113164 ∧ x21 = 104976*q+56582 ∧ x22 = 52488*q+28291 ∧ x23 = 157464*q+84874 ∧ x24 = 78732*q+42437 ∧ x25 = 236196*q+127312 ∧ x26 = 118098*q+63656 ∧ x27 = 59049*q+31828 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26⟩ := parameters_01001010010100100101001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
  have hstep := r26.1
  have hparity := r26.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p22 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p25 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p26 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25
    omega


end Collatz.Exploration.ElevenHalvesArithmetic
