/* bn254_fp_multiply : TWO^256 * TWO^256 |- TWO^256   (standalone sketch, not consensus code)
 * a * b mod p for any 256-bit a, b, as JetDiscovery.Corpus.BN254.fpMul.  Inputs are first
 * reduced below p (2^256 < 6p), then a * b = mont(mont(a, b), R^2 mod p) with 4-limb CIOS
 * Montgomery multiplication, R = 2^256. */
#include "sketch.h"
#include "limbs.h"
JD_SKETCH(bn254_fp_multiply, 512, 256)

static const uint64_t P[4] = { 0x3c208c16d87cfd47u, 0x97816a916871ca8du, 0xb85045b68181585du, 0x30644e72e131a029u };
static const uint64_t R2[4] = { 0xf32cfc5b538afa89u, 0xb5e71911d44501fbu, 0x47ab1eff0a417ff6u, 0x06d89f71cab8351fu };
static const uint64_t N0 = 0x87d20782e4866389u;   /* -p^-1 mod 2^64 */

static void reduce_input(uint64_t* a) { while (!jd_lt4(a, P)) jd_sub4(a, a, P); }
static void mont(uint64_t* r, const uint64_t* a, const uint64_t* b) {
  uint64_t t[6] = { 0 };
  for (int i = 0; i < 4; ++i) {
    uint64_t c = 0;
    for (int j = 0; j < 4; ++j) { jd_u128 x = (jd_u128)a[j] * b[i] + t[j] + c; t[j] = (uint64_t)x; c = (uint64_t)(x >> 64); }
    jd_u128 x = (jd_u128)t[4] + c; t[4] = (uint64_t)x; t[5] = (uint64_t)(x >> 64);
    uint64_t m = t[0] * N0;
    x = (jd_u128)m * P[0] + t[0]; c = (uint64_t)(x >> 64);
    for (int j = 1; j < 4; ++j) { x = (jd_u128)m * P[j] + t[j] + c; t[j - 1] = (uint64_t)x; c = (uint64_t)(x >> 64); }
    x = (jd_u128)t[4] + c; t[3] = (uint64_t)x; t[4] = t[5] + (uint64_t)(x >> 64);
  }
  uint64_t d[4];
  if (t[4] || !jd_lt4(t, P)) { jd_sub4(d, t, P); jd_copy4(r, d); } else jd_copy4(r, t);
}

bool jd_bn254_fp_multiply(frameItem* dst, frameItem src, const txEnv* env) {
  (void)env;
  uint64_t a[4], b[4], t[4];
  jd_read_le(a, 4, &src);
  jd_read_le(b, 4, &src);
  reduce_input(a); reduce_input(b);
  mont(t, a, b);
  mont(t, t, R2);
  jd_write_le(dst, t, 4);
  return true;
}
