import sys

def S(n):
    """Syracuse step: 3n+1 with all factors of 2 stripped."""
    n = 3 * n + 1
    while n % 2 == 0:
        n //= 2
    return n

def burst_gap(n):
    """One burst of odd steps, followed by one gap of even steps."""
    # Burst
    while True:
        n = (3 * n + 1) // 2
        if n % 2 == 0:
            break
    # Gap
    while n % 2 == 0:
        n //= 2
    return n

def mine():
    limit = 2**20
    print(f"Mining odd n <= {limit}...")
    
    # Example statistics to mine:
    # 1. n mod 3
    # 2. S(n) mod 3
    # 3. Size/length drops
    # 4. Chang's 1-bit coordinate (e.g., bit 4 of the orbit value at burst-end)
    
    for n in range(1, limit + 1, 2):
        s_val = S(n)
        s2_val = S(s_val)
        bg_val = burst_gap(n)
        
        # Here we would evaluate boolean candidates over our mined data
        # Example dummy condition to track drops:
        if bg_val < n:
            pass # Boolean condition evaluating to True for drop
            
    print("Mining complete. Output boolean formula candidate: ...")

if __name__ == "__main__":
    mine()
