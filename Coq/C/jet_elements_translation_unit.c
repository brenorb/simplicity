/* Keep actual core/frame helpers in this program so application proofs can
 * establish their concrete linkage. No C bodies or headers are substituted.
 * The SHA-256 implementation and the Elements operations are included so
 * that the hash and issuance helpers called by the Elements jets are
 * internal functions of the same program rather than external declarations
 * (as in jet_sha_translation_unit.c for Bitcoin). */
#include "../../C/frame.c"
#include "../../C/jets.c"
#include "../../C/sha256.c"
#include "../../C/elements/ops.c"
#include "../../C/elements/elementsJets.c"
