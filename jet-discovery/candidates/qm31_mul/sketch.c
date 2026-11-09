/* qm31_mul : QM31 * QM31 |- QM31, QM31 = (CM31, CM31), CM31 = (M31, M31), M31 = TWO^32
 * (standalone sketch, not consensus code).  Mirrors JetDiscovery.Corpus.Stark.qm31Mul
 * operation for operation, including its behaviour on non-canonical words:
 *   m31Add = fix(a + b mod 2^32); m31Sub = a - b, plus p (mod 2^32) on borrow;
 *   cm31Mul((a,b),(c,d)) = (ac - bd, ad + bc); cm31MulR(a,b) = (2a - b, a + 2b);
 *   qm31Mul((x0,x1),(y0,y1)) = (x0 y0 + R(x1 y1), x0 y1 + x1 y0).
 */
#include "sketch.h"
JD_SKETCH(qm31_mul, 256, 128)

#define P 0x7fffffffu
static inline uint32_t fix(uint32_t x) { return x < P ? x : x - P; }
static inline uint32_t add(uint32_t a, uint32_t b) { return fix(a + b); }
static inline uint32_t sub(uint32_t a, uint32_t b) { return a < b ? a - b + P : a - b; }
static inline uint32_t mul(uint32_t a, uint32_t b) {
  uint64_t x = (uint64_t)a * b;
  uint32_t hi = (uint32_t)(x >> 32), lo = (uint32_t)x;
  uint32_t s = ((hi << 1) | (lo >> 31)) + (lo & P);
  return fix((s & P) + (s >> 31));
}
typedef struct { uint32_t a, b; } cm31;
static inline cm31 cadd(cm31 x, cm31 y) { return (cm31){ add(x.a, y.a), add(x.b, y.b) }; }
static inline cm31 cmul(cm31 x, cm31 y) {
  return (cm31){ sub(mul(x.a, y.a), mul(x.b, y.b)), add(mul(x.a, y.b), mul(x.b, y.a)) };
}
static inline cm31 cmulR(cm31 x) { return (cm31){ sub(add(x.a, x.a), x.b), add(x.a, add(x.b, x.b)) }; }

bool jd_qm31_mul(frameItem* dst, frameItem src, const txEnv* env) {
  (void)env;
  uint32_t w[8];
  for (int i = 0; i < 8; ++i) w[i] = (uint32_t)simplicity_read32(&src);
  cm31 x0 = { w[0], w[1] }, x1 = { w[2], w[3] }, y0 = { w[4], w[5] }, y1 = { w[6], w[7] };
  cm31 r0 = cadd(cmul(x0, y0), cmulR(cmul(x1, y1)));
  cm31 r1 = cadd(cmul(x0, y1), cmul(x1, y0));
  simplicity_write32(dst, r0.a); simplicity_write32(dst, r0.b);
  simplicity_write32(dst, r1.a); simplicity_write32(dst, r1.b);
  return true;
}
