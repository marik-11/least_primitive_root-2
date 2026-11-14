import sys
import numpy as np


def spf_table(n):
    s = np.zeros(n + 1, dtype=np.int64)
    for i in range(2, int(n ** 0.5) + 1):
        if s[i] == 0:
            t = s[i * i::i]
            t[t == 0] = i
    return s


def factor(m, s):
    f = []
    while m > 1:
        q = int(s[m]) or m
        e = 0
        while m % q == 0:
            m //= q
            e += 1
        f.append((q, e))
    return f


def jacobi(a, n):
    a %= n
    r = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                r = -r
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            r = -r
        a %= n
    return r if n == 1 else 0


def leaves(u, parts, p, out):
    if len(parts) == 1:
        q, f = parts[0]
        out[q] = pow(u, q ** (f - 1), p)
        return
    parts = sorted(parts, key=lambda t: -(t[0] ** t[1]))
    a, b, na, nb = [], [], 1, 1
    for t in parts:
        if na <= nb:
            a.append(t)
            na *= t[0] ** t[1]
        else:
            b.append(t)
            nb *= t[0] ** t[1]
    leaves(pow(u, nb, p), a, p, out)
    leaves(pow(u, na, p), b, p, out)


def least_primitive_root(p, fac):
    e2 = dict(fac).get(2, 0)
    odd = [(q, e) for q, e in fac if q != 2]
    cache = {}

    def prime_leaves(l):
        if l not in cache:
            u = pow(l, 1 << e2, p)
            out = {}
            if odd:
                leaves(u, odd, p, out)
            cache[l] = (u, out)
        return cache[l]

    a = 2
    while True:
        f = factor(a, SPF)
        if any(e % 2 for _, e in f) and jacobi(a, p) == -1:
            ok = True
            for q, _ in odd:
                y = 1
                for l, e in f:
                    y = y * pow(prime_leaves(l)[1][q], e, p) % p
                if y == 1:
                    ok = False
                    break
            if ok:
                return a
        a += 1


def wieferich(p, g):
    return pow(g, p - 1, p * p) == 1


def run(n):
    global SPF
    SPF = spf_table(max(n, 4096))
    rec, bad, cnt, sumg = 0, [], 0, 0
    records = []
    for p in range(3, n, 2):
        if SPF[p]:
            continue
        g = least_primitive_root(p, factor(p - 1, SPF))
        cnt += 1
        sumg += g
        if g > rec:
            rec = g
            records.append((p, g))
        if wieferich(p, g):
            bad.append((p, g))
    return cnt, sumg, records, bad


if __name__ == "__main__":
    print(run(int(sys.argv[1])))
