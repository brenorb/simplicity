/* div_mod_256 : TWO^256 * TWO^256 |- TWO^256 * TWO^256   (standalone sketch, not consensus code)
 * (x div y, x mod y), and (0, x) when y = 0, as Simplicity.Programs.Arith.div_mod.
 * Knuth algorithm D on 64-bit limbs. */
#include "sketch.h"
#include "limbs.h"
JD_SKETCH(div_mod_256, 512, 512)

bool jd_div_mod_256(frameItem* dst, frameItem src, const txEnv* env) {
  (void)env;
  uint64_t x[4], y[4], q[4], r[4];
  jd_read_le(x, 4, &src);
  jd_read_le(y, 4, &src);
  jd_divmod(q, r, x, y, 4);
  jd_write_le(dst, q, 4);
  jd_write_le(dst, r, 4);
  return true;
}
