/* koalabear_add : TWO^32 * TWO^32 |- TWO^32   (standalone sketch, not consensus code)
 * Mirrors JetDiscovery.Lib.KoalaBear.addRef on every input word:
 *   u = a + b mod 2^32; result = u < q ? u : u - q, q = 2130706433.
 */
#include "sketch.h"
JD_SKETCH(koalabear_add, 64, 32)

bool jd_koalabear_add(frameItem* dst, frameItem src, const txEnv* env) {
  (void)env;
  const uint32_t q = 2130706433u;
  uint32_t a = (uint32_t)simplicity_read32(&src);
  uint32_t u = a + (uint32_t)simplicity_read32(&src);
  simplicity_write32(dst, u < q ? u : u - q);
  return true;
}
