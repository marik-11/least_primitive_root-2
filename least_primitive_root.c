#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef uint64_t u64;
typedef uint32_t u32;
typedef uint16_t u16;
typedef uint8_t u8;
typedef int8_t i8;
typedef unsigned __int128 u128;

#define LIM 2048
#define MAXF 12
#define SEG (1 << 19)
#define CAP (SEG / 3 + 1024)

static u64 CNT[2];
#ifdef COUNT
#define TICK(c) (CNT[(c)->w]++)
#else
#define TICK(c) ((void)0)
#endif

typedef struct { u64 n, ninv, r1; int w; } mctx;
typedef struct { u64 v[LIM + 1]; int top; } mtab;
typedef struct { u64 p; int e2, s; u32 q[MAXF]; u8 f[MAXF]; } PF;

static inline u64 inv64(u64 n) { u64 x = n; for (int i = 0; i < 5; i++) x *= 2 - n * x; return x; }
static inline void mset(mctx *c, u64 n, int w) { c->n = n; c->ninv = inv64(n); c->r1 = (0 - n) % n; c->w = w; }
static inline u64 mred(u128 t, const mctx *c) {
    u64 m = (u64)t * c->ninv;
    u64 a = (u64)(t >> 64);
    u64 b = (u64)(((u128)m * c->n) >> 64);
    return a >= b ? a - b : a - b + c->n;
}
static inline u64 mmul(u64 a, u64 b, const mctx *c) { TICK(c); return mred((u128)a * b, c); }
static inline u64 mpow(u64 x, u64 e, const mctx *c) {
    if (e == 1) return x;
    int t = 63 - __builtin_clzll(e);
    u64 r = x;
    for (int i = t - 1; i >= 0; i--) {
        r = mmul(r, r, c);
        if ((e >> i) & 1) r = mmul(r, x, c);
    }
    return r;
}
static inline void mtinit(mtab *t, const mctx *c) { t->v[1] = c->r1; t->top = 1; }
static inline u64 msmall(mtab *t, const mctx *c, int a) {
    while (t->top < a) {
        u64 y = t->v[t->top];
        u64 x = y + c->r1;
        if (x < y || x >= c->n) x -= c->n;
        t->v[++t->top] = x;
    }
    return t->v[a];
}

static i8 *legt[LIM];
static u8 afn[LIM], afe[LIM][6], asq[LIM];
static u16 afp[LIM][6];

static void init_tables(void) {
    static u16 spf[LIM];
    for (int i = 2; i < LIM; i++) if (!spf[i]) for (int j = i; j < LIM; j += i) if (!spf[j]) spf[j] = i;
    for (int a = 2; a < LIM; a++) {
        int x = a, k = 0, sq = 1;
        while (x > 1) {
            int l = spf[x], e = 0;
            while (x % l == 0) { x /= l; e++; }
            afp[a][k] = l; afe[a][k] = e; k++;
            if (e & 1) sq = 0;
        }
        afn[a] = k; asq[a] = sq;
    }
    for (int l = 3; l < LIM; l += 2) {
        if (spf[l] != l) continue;
        legt[l] = calloc(l, 1);
        for (int x = 1; x < l; x++) legt[l][(x * x) % l] = 1;
        for (int r = 1; r < l; r++) if (!legt[l][r]) legt[l][r] = -1;
    }
}

static u64 P, PINV;
static u32 ST;
static u32 chist[LIM];
static i8 chiv[LIM];
static u32 ystamp[LIM];
static u64 Ym[LIM][MAXF], Um[LIM];
static mctx C;
static mtab MT;
static int S, E2, ORD[MAXF];
static u64 QF[MAXF], QP[MAXF];

static inline int chi_prime(int l) {
    if (chist[l] == ST) return chiv[l];
    int v;
    if (l == 2) { u32 r = P & 7; v = (r == 1 || r == 7) ? 1 : -1; }
    else { v = legt[l][(u32)P % l]; if ((l & 3) == 3 && (P & 3) == 3) v = -v; }
    chist[l] = ST; chiv[l] = v;
    return v;
}
static inline int chi_comp(int a) {
    int s = 1;
    for (int k = 0; k < afn[a]; k++) if (afe[a][k] & 1) s *= chi_prime(afp[a][k]);
    return s;
}
static inline u64 fmodp(u64 x) {
    u64 q = (u64)(((u128)x * PINV) >> 64);
    u64 r = x - q * P;
    return r >= P ? r - P : r;
}

static void rec(int *idx, int n, u64 v, int l) {
    if (n == 1) {
        int i = idx[0];
        Ym[l][i] = QP[i] > 1 ? mpow(v, QP[i], &C) : v;
        return;
    }
    int a[MAXF], b[MAXF], na = 0, nb = 0;
    u64 n1 = 1, n2 = 1;
    for (int k = 0; k < n; k++) {
        int i = idx[k];
        if (n1 <= n2) { a[na++] = i; n1 *= QF[i]; } else { b[nb++] = i; n2 *= QF[i]; }
    }
    u64 v1 = mpow(v, n2, &C), v2 = mpow(v, n1, &C);
    rec(a, na, v1, l);
    rec(b, nb, v2, l);
}
static void tree(int l) {
    u64 x = msmall(&MT, &C, l);
    for (int k = 0; k < E2; k++) x = mmul(x, x, &C);
    Um[l] = x; ystamp[l] = ST;
    if (S) rec(ORD, S, x, l);
}
static inline u64 ycomp(int a, int i) {
    u64 y = 0; int first = 1;
    for (int k = 0; k < afn[a]; k++) {
        u64 yl = Ym[afp[a][k]][i];
        for (int e = 0; e < afe[a][k]; e++) { y = first ? yl : mmul(y, yl, &C); first = 0; }
    }
    return y;
}
static void prep(const PF *pf) {
    P = pf->p; ST++; S = pf->s; E2 = pf->e2;
    for (int i = 0; i < S; i++) {
        u64 f = 1;
        for (int k = 0; k < pf->f[i]; k++) f *= pf->q[i];
        QF[i] = f; QP[i] = f / pf->q[i];
        int j = i;
        while (j > 0 && QF[ORD[j - 1]] < f) { ORD[j] = ORD[j - 1]; j--; }
        ORD[j] = i;
    }
}
static int wief_sep(u64 p, int g) {
    mctx cn; mtab tn;
    mset(&cn, p * p, 1); mtinit(&tn, &cn);
    return mpow(msmall(&tn, &cn, g), p - 1, &cn) == cn.r1;
}

static int base_g(const PF *pf, int *wief) {
    u64 p = pf->p;
    mctx cp; mtab tp;
    mset(&cp, p, 0); mtinit(&tp, &cp);
    u64 qs[MAXF + 1]; int nq = 0;
    qs[nq++] = 2;
    for (int i = 0; i < pf->s; i++) qs[nq++] = pf->q[i];
    int g = 0;
    for (int a = 2; a < LIM; a++) {
        u64 x = msmall(&tp, &cp, a); int ok = 1;
        for (int k = 0; k < nq; k++) if (mpow(x, (p - 1) / qs[k], &cp) == cp.r1) { ok = 0; break; }
        if (ok) { g = a; break; }
    }
    *wief = wief_sep(p, g);
    return g;
}

static int quad_g(const PF *pf, int *wief) {
    u64 p = pf->p;
    prep(pf);
    mctx cp; mtab tp;
    mset(&cp, p, 0); mtinit(&tp, &cp);
    int g = 0;
    for (int a = 2; a < LIM; a++) {
        if (asq[a] || chi_comp(a) > 0) continue;
        u64 x = msmall(&tp, &cp, a); int ok = 1;
        for (int i = 0; i < pf->s; i++) if (mpow(x, (p - 1) / pf->q[i], &cp) == cp.r1) { ok = 0; break; }
        if (ok) { g = a; break; }
    }
    *wief = wief_sep(p, g);
    return g;
}

static int fast_g(const PF *pf, int *wief, int fused) {
    u64 p = pf->p;
    prep(pf);
    if (fused) { mset(&C, p * p, 1); PINV = ~0ULL / p; } else mset(&C, p, 0);
    mtinit(&MT, &C);
    int g = 0;
    for (int a = 2; a < LIM; a++) {
        if (asq[a] || chi_comp(a) > 0) continue;
        if (S == 0) { g = a; break; }
        for (int k = 0; k < afn[a]; k++) if (ystamp[afp[a][k]] != ST) tree(afp[a][k]);
        int ok = 1;
        for (int i = 0; i < S; i++) {
            u64 y = ycomp(a, i);
            if (fused) { if (fmodp(mred((u128)y, &C)) == 1) { ok = 0; break; } }
            else if (y == C.r1) { ok = 0; break; }
        }
        if (ok) { g = a; break; }
    }
    if (fused) {
        u64 G = 0; int first = 1;
        for (int k = 0; k < afn[g]; k++) {
            int l = afp[g][k];
            if (ystamp[l] != ST) tree(l);
            u64 gl = S == 0 ? Um[l] : mpow(Ym[l][0], pf->q[0], &C);
            for (int e = 0; e < afe[g][k]; e++) { G = first ? gl : mmul(G, gl, &C); first = 0; }
        }
        *wief = (G == C.r1);
    } else *wief = wief_sep(p, g);
    return g;
}

static int run(int mode, const PF *pf, int *w) {
    switch (mode) {
        case 0: return base_g(pf, w);
        case 1: return fast_g(pf, w, 1);
        case 2: return fast_g(pf, w, 0);
        default: return quad_g(pf, w);
    }
}

static u64 now_ns(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec * 1000000000ULL + ts.tv_nsec; }

static u8 comp[SEG];
static int32_t pid[SEG];
static u32 prem[CAP], px[CAP], pq[CAP][MAXF];
static u8 pn[CAP], pe2[CAP], pfx[CAP][MAXF];
static u32 sp[7000];
static u64 hist[LIM];

int main(int argc, char **argv) {
    if (argc < 4) return 1;
    int mode = atoi(argv[1]);
    u64 lo = strtoull(argv[2], 0, 10), hi = strtoull(argv[3], 0, 10);
    int dump = argc > 4;
    if (hi > 4294967296ULL) return 2;
    init_tables();
    int nsp = 0;
    {
        static u8 c[65537];
        for (u32 i = 3; i < 65537; i += 2) if (!c[i]) { sp[nsp++] = i; for (u32 j = i * i; j < 65537; j += 2 * i) c[j] = 1; }
    }
    if (lo < 3) lo = 3;
    if (!(lo & 1)) lo++;
    u64 base = lo, cnt = 0, sumg = 0, nw = 0, tengine = 0;
    int maxg = 0;
    u64 t0 = now_ns();
    while (base < hi) {
        u64 n = (hi - base + 1) / 2;
        if (n > SEG) n = SEG;
        u64 top = base + 2 * n;
        memset(comp, 0, n);
        for (int k = 0; k < nsp; k++) {
            u64 r = sp[k];
            if (r * r >= top) break;
            u64 m = r * r;
            if (m < base) { m = ((base + r - 1) / r) * r; if (!(m & 1)) m += r; }
            for (u64 i = (m - base) / 2; i < n; i += r) comp[i] = 1;
        }
        int np = 0;
        for (u64 i = 0; i < n; i++) if (!comp[i]) {
            u32 x = base + 2 * i;
            pid[i] = np; px[np] = x;
            int e = __builtin_ctz(x - 1);
            pe2[np] = e; prem[np] = (x - 1) >> e; pn[np] = 0;
            np++;
        }
        for (int k = 0; k < nsp; k++) {
            u64 q = sp[k];
            if (q * q >= top) break;
            u64 t = (1 + q - base % q) % q;
            for (u64 j = (t * ((q + 1) / 2)) % q; j < n; j += q) {
                if (comp[j]) continue;
                int id = pid[j];
                u32 r = prem[id];
                if (r % q == 0) {
                    int f = 0;
                    do { r /= q; f++; } while (r % q == 0);
                    prem[id] = r; pq[id][pn[id]] = q; pfx[id][pn[id]] = f; pn[id]++;
                }
            }
        }
        u64 te = now_ns();
        for (int id = 0; id < np; id++) {
            if (prem[id] > 1) { pq[id][pn[id]] = prem[id]; pfx[id][pn[id]] = 1; pn[id]++; }
            PF pf;
            pf.p = px[id]; pf.e2 = pe2[id]; pf.s = pn[id];
            for (int i = 0; i < pf.s; i++) { pf.q[i] = pq[id][i]; pf.f[i] = pfx[id][i]; }
            int w, g;
            if (mode == 3) {
                int w0, w1, w2, w4;
                int g0 = run(0, &pf, &w0), g1 = run(1, &pf, &w1), g2 = run(2, &pf, &w2), g4 = run(4, &pf, &w4);
                if (g0 != g1 || g0 != g2 || g0 != g4 || w0 != w1 || w0 != w2 || w0 != w4)
                    printf("MISMATCH p=%llu g=%d %d %d %d w=%d %d %d %d\n", (unsigned long long)pf.p, g0, g1, g2, g4, w0, w1, w2, w4);
                g = g0; w = w0;
            } else g = run(mode, &pf, &w);
            cnt++; sumg += g; hist[g]++;
            if (w) { nw++; printf("W p=%llu g=%d\n", (unsigned long long)pf.p, g); }
            if (g > maxg) { maxg = g; printf("R p=%llu g=%d\n", (unsigned long long)pf.p, g); }
            if (dump) printf("%llu %d %d\n", (unsigned long long)pf.p, g, w);
        }
        tengine += now_ns() - te;
        base = top;
    }
    u64 tt = now_ns() - t0;
    printf("primes=%llu sumg=%llu wief=%llu maxg=%d total_s=%.3f engine_s=%.3f us_per_prime=%.4f mulP=%llu mulN=%llu\n",
           (unsigned long long)cnt, (unsigned long long)sumg, (unsigned long long)nw, maxg, tt / 1e9, tengine / 1e9,
           tengine / 1e3 / (cnt ? cnt : 1), (unsigned long long)CNT[0], (unsigned long long)CNT[1]);
    return 0;
}
