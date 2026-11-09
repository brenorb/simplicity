/* p256_fe_multiply : TWO^256 * TWO^256 |- TWO^256   (standalone sketch, not consensus code)
 * The exact Solinas sequence of JetDiscovery.Corpus.P256.mulmod, so non-canonical inputs
 * give the same word as the reference: acc = canon(s1) + 2 s2 + 2 s3 + s4 + s5
 * - s6 - s7 - s8 - s9, every term passed through canon and every step through
 * the reference's addmod/submod. */
#include "sketch.h"
#include "limbs.h"
JD_SKETCH(p256_fe_multiply, 512, 256)

static const uint64_t P[4] = { 0xffffffffffffffffu, 0x00000000ffffffffu, 0x0000000000000000u, 0xffffffff00000001u };

static void canon(uint64_t* x) { uint64_t d[4]; if (!jd_sub4(d, x, P)) jd_copy4(x, d); }
static void addmod(uint64_t* acc, const uint64_t* b) {
  uint64_t s[4], d[4];
  uint64_t carry = jd_add4(s, acc, b);
  uint64_t borrow = jd_sub4(d, s, P);
  jd_copy4(acc, carry ? d : (borrow ? s : d));
}
static void submod(uint64_t* acc, const uint64_t* b) {
  uint64_t d[4];
  if (jd_sub4(d, acc, b)) jd_add4(d, d, P);
  jd_copy4(acc, d);
}
/* Eight 32-bit words, most significant first; index -1 is zero. */
static void build(uint64_t* r, const uint32_t* c, const signed char* idx) {
  uint32_t w[8];
  for (int i = 0; i < 8; ++i) w[i] = idx[i] < 0 ? 0 : c[idx[i]];
  for (int i = 0; i < 4; ++i) r[3 - i] = (uint64_t)w[2 * i] << 32 | w[2 * i + 1];
}

bool jd_p256_fe_multiply(frameItem* dst, frameItem src, const txEnv* env) {
  (void)env;
  static const signed char S[9][8] = {
    { 7, 6, 5, 4, 3, 2, 1, 0 }, { 15, 14, 13, 12, 11, -1, -1, -1 }, { -1, 15, 14, 13, 12, -1, -1, -1 },
    { 15, 14, -1, -1, -1, 10, 9, 8 }, { 8, 13, 15, 14, 13, 11, 10, 9 }, { 10, 8, -1, -1, -1, 13, 12, 11 },
    { 11, 9, -1, -1, 15, 14, 13, 12 }, { 12, -1, 10, 9, 8, 15, 14, 13 }, { 13, -1, 11, 10, 9, -1, 15, 14 } };
  static const signed char ops[10] = { 1, 1, 2, 2, 3, 4, -5, -6, -7, -8 };  /* +s(k+1) or -s(-k+1) */
  uint64_t a[4], b[4], prod[8], acc[4], t[4];
  uint32_t c[16];
  jd_read_le(a, 4, &src);
  jd_read_le(b, 4, &src);
  jd_mul(prod, a, 4, b, 4);
  for (int i = 0; i < 8; ++i) { c[2 * i] = (uint32_t)prod[i]; c[2 * i + 1] = (uint32_t)(prod[i] >> 32); }
  build(acc, c, S[0]); canon(acc);
  for (int k = 0; k < 10; ++k) {
    int term = ops[k] > 0 ? ops[k] : -ops[k];
    build(t, c, S[term]); canon(t);
    if (ops[k] > 0) addmod(acc, t); else submod(acc, t);
  }
  jd_write_le(dst, acc, 4);
  return true;
}
