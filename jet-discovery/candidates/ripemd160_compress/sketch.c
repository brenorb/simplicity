/* ripemd160_compress : (TWO^32)^5 * (TWO^32)^16 |- (TWO^32)^5   (standalone sketch, not consensus code)
 * RIPEMD-160 compression on the state h0..h4 and 16 message words already decoded from
 * little-endian bytes, as JetDiscovery.Lib.Ripemd160.ripemd160Compress. */
#include "sketch.h"
JD_SKETCH(ripemd160_compress, 672, 160)

static const unsigned char RL[80] = {
  0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15, 7,4,13,1,10,6,15,3,12,0,9,5,2,14,11,8,
  3,10,14,4,9,15,8,1,2,7,0,6,13,11,5,12, 1,9,11,10,0,8,12,4,13,3,7,15,14,5,6,2,
  4,0,5,9,7,12,2,10,14,1,3,8,11,6,15,13 };
static const unsigned char RR[80] = {
  5,14,7,0,9,2,11,4,13,6,15,8,1,10,3,12, 6,11,3,7,0,13,5,10,14,15,8,12,4,9,1,2,
  15,5,1,3,7,14,6,9,11,8,12,2,10,0,4,13, 8,6,4,1,3,11,15,0,5,12,2,13,9,7,10,14,
  12,15,10,4,1,5,8,7,6,2,13,14,0,3,9,11 };
static const unsigned char SL[80] = {
  11,14,15,12,5,8,7,9,11,13,14,15,6,7,9,8, 7,6,8,13,11,9,7,15,7,12,15,9,11,7,13,12,
  11,13,6,7,14,9,13,15,14,8,13,6,5,12,7,5, 11,12,14,15,14,15,9,8,9,14,5,6,8,6,5,12,
  9,15,5,11,6,8,13,12,5,12,13,14,11,8,5,6 };
static const unsigned char SR[80] = {
  8,9,9,11,13,15,15,5,7,7,8,11,14,14,12,6, 9,13,15,7,12,8,9,11,7,7,12,7,6,15,13,11,
  9,7,15,11,8,6,6,14,12,13,5,14,13,13,7,5, 15,5,8,11,14,14,6,14,6,9,12,9,12,5,15,8,
  8,5,12,9,12,5,14,6,8,13,6,5,15,13,11,11 };
static const uint32_t KL[5] = { 0x00000000u, 0x5A827999u, 0x6ED9EBA1u, 0x8F1BBCDCu, 0xA953FD4Eu };
static const uint32_t KR[5] = { 0x50A28BE6u, 0x5C4DD124u, 0x6D703EF3u, 0x7A6D76E9u, 0x00000000u };
static inline uint32_t rol(uint32_t v, unsigned n) { return (v << n) | (v >> (32 - n)); }
static inline uint32_t f(int j, uint32_t x, uint32_t y, uint32_t z) {
  switch (j) {
    case 0: return x ^ y ^ z;
    case 1: return (x & y) | (~x & z);
    case 2: return (x | ~y) ^ z;
    case 3: return (x & z) | (y & ~z);
    default: return x ^ (y | ~z);
  }
}

bool jd_ripemd160_compress(frameItem* dst, frameItem src, const txEnv* env) {
  (void)env;
  uint32_t h[5], x[16];
  for (int i = 0; i < 5; ++i) h[i] = (uint32_t)simplicity_read32(&src);
  for (int i = 0; i < 16; ++i) x[i] = (uint32_t)simplicity_read32(&src);
  uint32_t al = h[0], bl = h[1], cl = h[2], dl = h[3], el = h[4];
  uint32_t ar = h[0], br = h[1], cr = h[2], dr = h[3], er = h[4];
  for (int j = 0; j < 80; ++j) {
    int g = j / 16;
    uint32_t t = rol(al + f(g, bl, cl, dl) + x[RL[j]] + KL[g], SL[j]) + el;
    al = el; el = dl; dl = rol(cl, 10); cl = bl; bl = t;
    t = rol(ar + f(4 - g, br, cr, dr) + x[RR[j]] + KR[g], SR[j]) + er;
    ar = er; er = dr; dr = rol(cr, 10); cr = br; br = t;
  }
  uint32_t t = h[1] + cl + dr;
  h[1] = h[2] + dl + er; h[2] = h[3] + el + ar; h[3] = h[4] + al + br; h[4] = h[0] + bl + cr; h[0] = t;
  for (int i = 0; i < 5; ++i) simplicity_write32(dst, h[i]);
  return true;
}
