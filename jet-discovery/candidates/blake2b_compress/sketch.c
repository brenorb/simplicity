/* blake2b_compress : ((TWO^64)^8 * (TWO^64)^16) * (TWO^64 * TWO^64) |- (TWO^64)^8
 * (standalone sketch, not consensus code).  BLAKE2b F(h, m, t, f = final) with words
 * taken as given, as JetDiscovery.Corpus.Hashes.blake2F blake2b. */
#include "sketch.h"
#include "blake2_sketch.h"
JD_SKETCH(blake2b_compress, 1664, 512)
BLAKE2_F(blake2b_compress, uint64_t, 64, 12, 32, 24, 16, 63,
  0x6A09E667F3BCC908u, 0xBB67AE8584CAA73Bu, 0x3C6EF372FE94F82Bu, 0xA54FF53A5F1D36F1u,
  0x510E527FADE682D1u, 0x9B05688C2B3E6C1Fu, 0x1F83D9ABFB41BD6Bu, 0x5BE0CD19137E2179u)
