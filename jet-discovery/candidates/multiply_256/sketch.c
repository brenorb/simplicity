/* multiply_256 : TWO^256 * TWO^256 |- TWO^512   (standalone sketch, not consensus code)
 * Full product, as Simplicity.Programs.Arith.multiply word256.  Schoolbook on 64-bit limbs. */
#include "sketch.h"
#include "limbs.h"
JD_SKETCH(multiply_256, 512, 512)

bool jd_multiply_256(frameItem* dst, frameItem src, const txEnv* env) {
  (void)env;
  uint64_t a[4], b[4], r[8];
  jd_read_le(a, 4, &src);
  jd_read_le(b, 4, &src);
  jd_mul(r, a, 4, b, 4);
  jd_write_le(dst, r, 8);
  return true;
}
