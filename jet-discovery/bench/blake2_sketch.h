/* BLAKE2 compression F shared by the blake2s/blake2b sketches.  The final-block flag
 * is always set (v[14] = IV[6] xor all-ones), matching the Simplicity reference. */
#ifndef JD_BLAKE2_SKETCH_H
#define JD_BLAKE2_SKETCH_H
static const unsigned char jd_blake2_sigma[10][16] = {
  { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,10,11,12,13,14,15}, {14,10, 4, 8, 9,15,13, 6, 1,12, 0, 2,11, 7, 5, 3},
  {11, 8,12, 0, 5, 2,15,13,10,14, 3, 6, 7, 1, 9, 4}, { 7, 9, 3, 1,13,12,11,14, 2, 6, 5,10, 4, 0,15, 8},
  { 9, 0, 5, 7, 2, 4,10,15,14, 1,11,12, 6, 8, 3,13}, { 2,12, 6,10, 0,11, 8, 3, 4,13, 7, 5,15,14, 1, 9},
  {12, 5, 1,15,14,13, 4,10, 0, 7, 6, 3, 9, 2, 8,11}, {13,11, 7,14,12, 1, 3, 9, 5, 0,15, 4, 8, 6, 2,10},
  { 6,15,14, 9,11, 3, 0, 8,12, 2,13, 7, 1, 4,10, 5}, {10, 2, 8, 4, 7, 6, 1, 5,15,11, 9,14, 3,12,13, 0} };
#define BLAKE2_F(NAME, W, BITS, ROUNDS, R1, R2, R3, R4, I0, I1, I2, I3, I4, I5, I6, I7)        \
static inline W NAME##_rotr(W v, unsigned n) { return (W)((v >> n) | (v << (BITS - n))); }     \
static inline W NAME##_rd(frameItem* f) { return (W)simplicity_read##BITS(f); }                \
bool jd_##NAME(frameItem* dst, frameItem src, const txEnv* env) {                              \
  (void)env;                                                                                    \
  static const W iv[8] = { I0, I1, I2, I3, I4, I5, I6, I7 };                                    \
  W h[8], m[16], v[16];                                                                         \
  for (int i = 0; i < 8; ++i) h[i] = NAME##_rd(&src);                                           \
  for (int i = 0; i < 16; ++i) m[i] = NAME##_rd(&src);                                          \
  W t0 = NAME##_rd(&src), t1 = NAME##_rd(&src);                                                 \
  for (int i = 0; i < 8; ++i) { v[i] = h[i]; v[i + 8] = iv[i]; }                                \
  v[12] ^= t0; v[13] ^= t1; v[14] = (W)~v[14];                                                  \
  static const unsigned char lanes[8][4] = { {0,4,8,12},{1,5,9,13},{2,6,10,14},{3,7,11,15},     \
                                             {0,5,10,15},{1,6,11,12},{2,7,8,13},{3,4,9,14} };   \
  for (int r = 0; r < ROUNDS; ++r) {                                                            \
    const unsigned char* s = jd_blake2_sigma[r % 10];                                           \
    for (int g = 0; g < 8; ++g) {                                                               \
      W* a = &v[lanes[g][0]]; W* b = &v[lanes[g][1]]; W* c = &v[lanes[g][2]]; W* d = &v[lanes[g][3]]; \
      *a = (W)(*a + *b + m[s[2 * g]]);     *d = NAME##_rotr(*d ^ *a, R1);                       \
      *c = (W)(*c + *d);                   *b = NAME##_rotr(*b ^ *c, R2);                       \
      *a = (W)(*a + *b + m[s[2 * g + 1]]); *d = NAME##_rotr(*d ^ *a, R3);                       \
      *c = (W)(*c + *d);                   *b = NAME##_rotr(*b ^ *c, R4);                       \
    }                                                                                           \
  }                                                                                             \
  for (int i = 0; i < 8; ++i) simplicity_write##BITS(dst, h[i] ^ v[i] ^ v[i + 8]);              \
  return true;                                                                                  \
}
#endif
