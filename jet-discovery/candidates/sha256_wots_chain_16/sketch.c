/* sha256_wots_chain_16 : CTX8 * (TWO^4 * TWO^128) |- TWO^128   (standalone sketch, not consensus code)
 * For j = start..14: node := first 16 bytes of SHA-256-finalize(ctx || BE32(j) || node), with
 * the same context reused every step, as JetDiscovery.Lib.Kernels.wotsChain.  Mirrors the
 * existing ctx8_add_4 / ctx8_add_16 / ctx8_finalize jets: an executed step fails on an
 * overflowing context; start = 15 returns the node without reading the context. */
#include <string.h>
#include "sketch.h"
#include "sha256.h"
JD_SKETCH(sha256_wots_chain_16, 962, 128)

bool jd_sha256_wots_chain_16(frameItem* dst, frameItem src, const txEnv* env) {
  (void)env;
  uint32_t base_ms[8];
  sha256_context base = { .output = base_ms };
  bool valid = simplicity_read_sha256_context(&base, &src);
  unsigned start = (unsigned)simplicity_read4(&src);
  unsigned char node[16];
  read8s(node, 16, &src);
  for (unsigned j = start; j < 15; ++j) {
    if (!valid) return false;
    uint32_t ms[8];
    memcpy(ms, base_ms, sizeof ms);
    sha256_context c = { .output = ms, .counter = base.counter, .overflow = base.overflow };
    memcpy(c.block, base.block, sizeof c.block);
    const unsigned char jb[4] = { 0, 0, 0, (unsigned char)j };
    sha256_uchars(&c, jb, 4);
    if (c.overflow) return false;
    sha256_uchars(&c, node, 16);
    if (c.overflow) return false;
    sha256_finalize(&c);
    unsigned char full[32];
    sha256_fromMidstate(full, ms);
    memcpy(node, full, 16);
  }
  write8s(dst, node, 16);
  return true;
}
