/* sha256_pair : TWO^512 |- TWO^256   (standalone sketch, not consensus code)
 * SHA-256 of a 64-byte message (two compressions), as JetDiscovery.Lib.Kernels.sha256Pair. */
#include "sketch.h"
#include "sha256.h"
JD_SKETCH(sha256_pair, 512, 256)

bool jd_sha256_pair(frameItem* dst, frameItem src, const txEnv* env) {
  (void)env;
  unsigned char msg[64];
  sha256_midstate out;
  read8s(msg, 64, &src);
  sha256_context ctx = sha256_init(out.s);
  sha256_uchars(&ctx, msg, 64);
  sha256_finalize(&ctx);
  write32s(dst, out.s, 8);
  return true;
}
