/* m31_mul : TWO^32 * TWO^32 |- TWO^32   (standalone sketch, not consensus code)
 * Mirrors JetDiscovery.Corpus.Stark.m31Mul on every input word:
 *   x = a*b; s = ((hi<<1)|(lo>>31)) + (lo & p) mod 2^32;
 *   t = (s & p) + (s >> 31) mod 2^32; result = t < p ? t : t - p.
 */
#include "sketch.h"
JD_SKETCH(m31_mul, 64, 32)

bool jd_m31_mul(frameItem* dst, frameItem src, const txEnv* env) {
  (void)env;
  const uint32_t p = 0x7fffffffu;
  uint64_t x = (uint64_t)simplicity_read32(&src) * (uint64_t)simplicity_read32(&src);
  uint32_t hi = (uint32_t)(x >> 32), lo = (uint32_t)x;
  uint32_t s = ((hi << 1) | (lo >> 31)) + (lo & p);
  uint32_t t = (s & p) + (s >> 31);
  simplicity_write32(dst, t < p ? t : t - p);
  return true;
}
