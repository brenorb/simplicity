/* Core jets together with the portable SHA-256 compression function and its
 * dispatch pointer, so that the SHA jets' indirect call resolves to an actual
 * C body in this program, and the Bitcoin jets and tap-hash operations, whose
 * hashing jets call that same code. No C bodies or headers are substituted. */
#include "../../C/frame.c"
#include "../../C/jets.c"
#include "../../C/sha256.c"
#include "../../C/bitcoin/ops.c"
#include "../../C/bitcoin/bitcoinJets.c"
