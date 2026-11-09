/* pubkey_unpack_neg : TWO^256 |- S (TWO * TWO^256)   (standalone sketch, not consensus code)
 * x < p (secp256k1 field order) gives Right (true, x), otherwise Left (), as
 * Simplicity.Programs.LibSecp256k1.Lib.pubkey_unpack_neg. */
#include "sketch.h"
#include "limbs.h"
JD_SKETCH(pubkey_unpack_neg, 256, 258)

static const uint64_t P[4] = { 0xfffffffefffffc2fu, 0xffffffffffffffffu, 0xffffffffffffffffu, 0xffffffffffffffffu };

bool jd_pubkey_unpack_neg(frameItem* dst, frameItem src, const txEnv* env) {
  (void)env;
  uint64_t x[4];
  jd_read_le(x, 4, &src);
  if (writeBit(dst, jd_lt4(x, P))) { writeBit(dst, true); jd_write_le(dst, x, 4); }
  else skipBits(dst, 257);
  return true;
}
