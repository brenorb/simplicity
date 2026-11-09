/* keccak_f1600 : (TWO^64)^32 |- (TWO^64)^32   (standalone sketch, not consensus code)
 * Keccak-f[1600] on lanes A[x + 5y] = word x + 5y, as JetDiscovery.Corpus.Hashes.keccakF.
 * Input words 25..31 are ignored; output words 25..31 are zero. */
#include "sketch.h"
JD_SKETCH(keccak_f1600, 2048, 2048)

static const uint64_t RC[24] = {
  0x0000000000000001u, 0x0000000000008082u, 0x800000000000808Au, 0x8000000080008000u,
  0x000000000000808Bu, 0x0000000080000001u, 0x8000000080008081u, 0x8000000000008009u,
  0x000000000000008Au, 0x0000000000000088u, 0x0000000080008009u, 0x000000008000000Au,
  0x000000008000808Bu, 0x800000000000008Bu, 0x8000000000008089u, 0x8000000000008003u,
  0x8000000000008002u, 0x8000000000000080u, 0x000000000000800Au, 0x800000008000000Au,
  0x8000000080008081u, 0x8000000000008080u, 0x0000000080000001u, 0x8000000080008008u };
/* rotation offset of lane x + 5y */
static const unsigned ROT[25] = { 0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
                                  41, 45, 15, 21, 8, 18, 2, 61, 56, 14 };
static inline uint64_t rotl(uint64_t v, unsigned n) { return n ? (v << n) | (v >> (64 - n)) : v; }

bool jd_keccak_f1600(frameItem* dst, frameItem src, const txEnv* env) {
  (void)env;
  uint64_t a[25], b[25], c[5], d[5];
  for (int i = 0; i < 25; ++i) a[i] = simplicity_read64(&src);
  for (int r = 0; r < 24; ++r) {
    for (int x = 0; x < 5; ++x) c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
    for (int x = 0; x < 5; ++x) d[x] = c[(x + 4) % 5] ^ rotl(c[(x + 1) % 5], 1);
    for (int i = 0; i < 25; ++i) a[i] ^= d[i % 5];
    for (int x = 0; x < 5; ++x)
      for (int y = 0; y < 5; ++y) b[y + 5 * ((2 * x + 3 * y) % 5)] = rotl(a[x + 5 * y], ROT[x + 5 * y]);
    for (int y = 0; y < 5; ++y)
      for (int x = 0; x < 5; ++x) a[x + 5 * y] = b[x + 5 * y] ^ (~b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]);
    a[0] ^= RC[r];
  }
  for (int i = 0; i < 25; ++i) simplicity_write64(dst, a[i]);
  for (int i = 25; i < 32; ++i) simplicity_write64(dst, 0);
  return true;
}
