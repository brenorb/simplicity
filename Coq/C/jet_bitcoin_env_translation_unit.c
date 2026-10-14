/* The SHA translation unit (jet_sha_translation_unit.c) followed by the
 * actual construction of the Bitcoin transaction and taproot environments,
 * so that proofs about the callers that build the environment can use the
 * same hashing code as the jets. No C bodies or headers are substituted. */
#include "../../C/frame.c"
#include "../../C/jets.c"
#include "../../C/sha256.c"
#include "../../C/bitcoin/ops.c"
#include "../../C/bitcoin/bitcoinJets.c"
#include "../../C/bitcoin/env.c"
#include "../../C/bitcoin/txEnv.c"
