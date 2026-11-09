/* ed25519_fe_multiply : TWO^256 * TWO^256 |- TWO^256   (standalone sketch, not consensus code)
 * The exact folding sequence of JetDiscovery.Corpus.Ed25519.mulmod: fold the high half by
 * 38 twice (2^256 = 38 mod p), then two conditional subtractions of p = 2^255 - 19. */
#include "sketch.h"
#include "limbs.h"
JD_SKETCH(ed25519_fe_multiply, 512, 256)

static const uint64_t P[4] = { 0xffffffffffffffedu, 0xffffffffffffffffu, 0xffffffffffffffffu, 0x7fffffffffffffffu };
static void canon(uint64_t* x) { uint64_t d[4]; if (!jd_sub4(d, x, P)) jd_copy4(x, d); }
static void mul_small(uint64_t* lo, uint64_t* hi_limb, const uint64_t* a, uint64_t k) {
  uint64_t c = 0;
  for (int i = 0; i < 4; ++i) { jd_u128 t = (jd_u128)a[i] * k + c; lo[i] = (uint64_t)t; c = (uint64_t)(t >> 64); }
  *hi_limb = c;
}

bool jd_ed25519_fe_multiply(frameItem* dst, frameItem src, const txEnv* env) {
  (void)env;
  static const uint64_t K38[4] = { 38, 0, 0, 0 }, ONE[4] = { 1, 0, 0, 0 };
  uint64_t a[4], b[4], prod[8], L[4], s[4], k[4], k38[4], x[4], h;
  jd_read_le(a, 4, &src);
  jd_read_le(b, 4, &src);
  jd_mul(prod, a, 4, b, 4);
  mul_small(L, &h, prod + 4, 38);            /* hi * 38 = h 2^256 + L */
  uint64_t carry = jd_add4(s, L, prod);      /* L + lo */
  uint64_t H[4] = { h, 0, 0, 0 };
  if (carry) jd_add4(k, H, ONE); else jd_copy4(k, H);
  mul_small(k38, &h, k, 38);                 /* low 256 bits of k * 38 */
  if (jd_add4(x, s, k38)) jd_add4(x, x, K38);
  canon(x); canon(x);
  jd_write_le(dst, x, 4);
  return true;
}
