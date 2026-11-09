/* multiply_128 : TWO^128 * TWO^128 |- TWO^256   (standalone sketch, not consensus code)
 * Full product, as Simplicity.Programs.Arith.multiply word128.  Schoolbook on 64-bit limbs. */
#include "sketch.h"
#include "limbs.h"
JD_SKETCH(multiply_128, 256, 256)

bool jd_multiply_128(frameItem* dst, frameItem src, const txEnv* env) {
  (void)env;
  uint64_t a[2], b[2], r[4];
  jd_read_le(a, 2, &src);
  jd_read_le(b, 2, &src);
  jd_mul(r, a, 2, b, 2);
  jd_write_le(dst, r, 4);
  return true;
}
