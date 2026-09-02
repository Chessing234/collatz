#!/usr/bin/env python3
import random
import math

def discrete_localization(prefix, prefix_len, num_particles=1000, steps=20):
    """
    Reveal one bit at a time, maintain a particle cloud of consistent 2-adic tails,
    estimate kappa by Monte Carlo on the tail.
    """
    tails = [random.getrandbits(64) for _ in range(num_particles)]
    for step in range(steps):
        v2_histogram = {}
        for tail in tails:
            n = prefix | (tail << prefix_len)
            if n % 2 != 0:
                nxt = 3 * n + 1
                v2 = 0
                while nxt % 2 == 0 and nxt > 0:
                    nxt //= 2
                    v2 += 1
                v2_histogram[v2] = v2_histogram.get(v2, 0) + 1
        
        if v2_histogram:
            total_v2 = sum(k * v for k, v in v2_histogram.items())
            kappa = total_v2 / sum(v2_histogram.values())
        else:
            kappa = 0.0
            
        print(f"Step {step}: Prefix {bin(prefix)}, kappa ~ {kappa:.3f}")
        next_bit = random.choice([0, 1])
        prefix = prefix | (next_bit << prefix_len)
        prefix_len += 1
        
if __name__ == "__main__":
    discrete_localization(0b1, 1, num_particles=1000, steps=10)
