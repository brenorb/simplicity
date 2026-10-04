/* The SHA translation unit (core jets, SHA-256, Bitcoin jets and tap-hash
 * operations) together with the secp256k1 jets and the libsecp256k1 code they
 * call, in the production configuration. No C bodies or headers are
 * substituted. */
#include "../../C/frame.c"
#include "../../C/jets.c"
#include "../../C/sha256.c"
#include "../../C/bitcoin/ops.c"
#include "../../C/bitcoin/bitcoinJets.c"
#include "../../C/jets-secp256k1.c"
