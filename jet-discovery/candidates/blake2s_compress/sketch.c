/* blake2s_compress : ((TWO^32)^8 * (TWO^32)^16) * (TWO^32 * TWO^32) |- (TWO^32)^8
 * (standalone sketch, not consensus code).  BLAKE2s F(h, m, t, f = final) with words
 * taken as given, as JetDiscovery.Corpus.Hashes.blake2F blake2s. */
#include "sketch.h"
#include "blake2_sketch.h"
JD_SKETCH(blake2s_compress, 832, 256)
BLAKE2_F(blake2s_compress, uint32_t, 32, 10, 16, 12, 8, 7,
  0x6A09E667u, 0xBB67AE85u, 0x3C6EF372u, 0xA54FF53Au, 0x510E527Fu, 0x9B05688Cu, 0x1F83D9ABu, 0x5BE0CD19u)
