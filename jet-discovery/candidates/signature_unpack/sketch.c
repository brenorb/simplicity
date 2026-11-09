/* signature_unpack : TWO^256 * TWO^256 |- S (TWO^256 * TWO^256)   (standalone sketch, not consensus code)
 * r < p and s < n give Right (r, s), otherwise Left (), as
 * Simplicity.Programs.LibSecp256k1.Lib.signature_unpack. */
#include "sketch.h"
#include "limbs.h"
JD_SKETCH(signature_unpack, 512, 513)

static const uint64_t P[4] = { 0xfffffffefffffc2fu, 0xffffffffffffffffu, 0xffffffffffffffffu, 0xffffffffffffffffu };
static const uint64_t N[4] = { 0xbfd25e8cd0364141u, 0xbaaedce6af48a03bu, 0xfffffffffffffffeu, 0xffffffffffffffffu };

bool jd_signature_unpack(frameItem* dst, frameItem src, const txEnv* env) {
  (void)env;
  uint64_t r[4], s[4];
  jd_read_le(r, 4, &src);
  jd_read_le(s, 4, &src);
  if (writeBit(dst, jd_lt4(r, P) && jd_lt4(s, N))) { jd_write_le(dst, r, 4); jd_write_le(dst, s, 4); }
  else skipBits(dst, 512);
  return true;
}
