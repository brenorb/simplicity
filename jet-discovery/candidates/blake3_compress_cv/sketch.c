/* blake3_compress_cv : CV * (BLOCK * (TWO^64 * (TWO^32 * TWO^32))) |- CV,
 * CV = (TWO^32)^8, BLOCK = (TWO^32)^16   (standalone sketch, not consensus code).
 * BLAKE3 compression returning the first 8 output words (v[i] xor v[i+8]), as
 * JetDiscovery.Corpus.Blake3.compressChainingSpec.  v[12] is the low counter word. */
#include "sketch.h"
JD_SKETCH(blake3_compress_cv, 896, 256)

static inline uint32_t rotr(uint32_t v, unsigned n) { return (v >> n) | (v << (32 - n)); }
static inline void g(uint32_t* v, int a, int b, int c, int d, uint32_t x, uint32_t y) {
  v[a] += v[b] + x; v[d] = rotr(v[d] ^ v[a], 16); v[c] += v[d]; v[b] = rotr(v[b] ^ v[c], 12);
  v[a] += v[b] + y; v[d] = rotr(v[d] ^ v[a], 8);  v[c] += v[d]; v[b] = rotr(v[b] ^ v[c], 7);
}

bool jd_blake3_compress_cv(frameItem* dst, frameItem src, const txEnv* env) {
  (void)env;
  static const uint32_t iv[4] = { 0x6A09E667u, 0xBB67AE85u, 0x3C6EF372u, 0xA54FF53Au };
  static const unsigned char perm[16] = { 2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8 };
  uint32_t v[16], m[16], t[16];
  for (int i = 0; i < 8; ++i) v[i] = (uint32_t)simplicity_read32(&src);
  for (int i = 0; i < 16; ++i) m[i] = (uint32_t)simplicity_read32(&src);
  uint64_t counter = simplicity_read64(&src);
  for (int i = 0; i < 4; ++i) v[8 + i] = iv[i];
  v[12] = (uint32_t)counter; v[13] = (uint32_t)(counter >> 32);
  v[14] = (uint32_t)simplicity_read32(&src); v[15] = (uint32_t)simplicity_read32(&src);
  for (int r = 0; r < 7; ++r) {
    g(v, 0, 4, 8, 12, m[0], m[1]);  g(v, 1, 5, 9, 13, m[2], m[3]);
    g(v, 2, 6, 10, 14, m[4], m[5]); g(v, 3, 7, 11, 15, m[6], m[7]);
    g(v, 0, 5, 10, 15, m[8], m[9]); g(v, 1, 6, 11, 12, m[10], m[11]);
    g(v, 2, 7, 8, 13, m[12], m[13]); g(v, 3, 4, 9, 14, m[14], m[15]);
    for (int i = 0; i < 16; ++i) t[i] = m[perm[i]];
    for (int i = 0; i < 16; ++i) m[i] = t[i];
  }
  for (int i = 0; i < 8; ++i) simplicity_write32(dst, v[i] ^ v[i + 8]);
  return true;
}
