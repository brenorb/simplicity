/* sha256_wots_chain_16_fixed : TWO^256 * (((TWO^8 * TWO^64) * (TWO^8 * TWO^64)) * (TWO^4 * TWO^128)) |- TWO^128
 * (standalone sketch, not consensus code).  For j = start..14,
 * node := first 16 bytes of SHA256_compress(state, prefix18 || 0,0,0,j || node || padding),
 * with the padding length fixed at 816 bits, as JetDiscovery.Lib.ShrincsHash.chainRef. */
#include <string.h>
#include "sketch.h"
#include "sha256.h"
JD_SKETCH(sha256_wots_chain_16_fixed, 532, 128)

bool jd_sha256_wots_chain_16_fixed(frameItem* dst, frameItem src, const txEnv* env) {
  (void)env;
  uint32_t state[8];
  unsigned char block[64] = { 0 };
  read32s(state, 8, &src);
  read8s(block, 18, &src);           /* b0, 8 bytes, b1, 8 bytes */
  unsigned start = (unsigned)simplicity_read4(&src);
  unsigned char node[16];
  read8s(node, 16, &src);
  block[38] = 0x80;
  block[62] = 0x03; block[63] = 0x30; /* 816 bits */
  for (unsigned j = start; j < 15; ++j) {
    uint32_t s[8], w[16];
    block[21] = (unsigned char)j;
    memcpy(block + 22, node, 16);
    memcpy(s, state, sizeof s);
    for (int i = 0; i < 16; ++i)
      w[i] = (uint32_t)block[4*i] << 24 | (uint32_t)block[4*i+1] << 16 | (uint32_t)block[4*i+2] << 8 | block[4*i+3];
    simplicity_sha256_compression(s, w);
    unsigned char full[32];
    sha256_fromMidstate(full, s);
    memcpy(node, full, 16);
  }
  write8s(dst, node, 16);
  return true;
}
