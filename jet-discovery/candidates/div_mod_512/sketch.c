/* div_mod_512 : TWO^512 * TWO^512 |- TWO^512 * TWO^512   (standalone sketch, not consensus code)
 * (x div y, x mod y), and (0, x) when y = 0, as Simplicity.Programs.Arith.div_mod.
 * Knuth algorithm D on 64-bit limbs. */
#include "sketch.h"
#include "limbs.h"
JD_SKETCH(div_mod_512, 1024, 1024)

bool jd_div_mod_512(frameItem* dst, frameItem src, const txEnv* env) {
  (void)env;
  uint64_t x[8], y[8], q[8], r[8];
  jd_read_le(x, 8, &src);
  jd_read_le(y, 8, &src);
  jd_divmod(q, r, x, y, 8);
  jd_write_le(dst, q, 8);
  jd_write_le(dst, r, 8);
  return true;
}
