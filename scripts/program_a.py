import math

def v2(n):
    if n == 0: return math.inf
    res = 0
    while n % 2 == 0:
        res += 1
        n //= 2
    return res

def v3(n):
    if n == 0: return math.inf
    res = 0
    while n % 3 == 0:
        res += 1
        n //= 3
    return res

def lambda_sigma(word):
    k = len(word)
    val = 0
    m_after = sum(word)
    for i in range(k):
        if word[i] == 1:
            m_after -= 1
            val += (3 ** m_after) * (2 ** i)
    return val

def explore_words(max_len):
    # Sample and compute the 3-place height.
    # Looking for: h(x) = log|x|_2 + log|x|_3 + log|x|_inf
    for length in range(1, max_len + 1):
        print(f"Length {length} exploration:")
        for _ in range(10): # Sample 10 for demonstration
            import random
            word = tuple(random.choice([0, 1]) for _ in range(length))
            L = lambda_sigma(word)
            if L > 0:
                h2 = -v2(L) * math.log(2)
                h3 = -v3(L) * math.log(3)
                hinf = math.log(L)
                htot = h2 + h3 + hinf
                print(f"Word: {word}, Lambda: {L}, Total Height: {htot}")

if __name__ == "__main__":
    explore_words(40)
