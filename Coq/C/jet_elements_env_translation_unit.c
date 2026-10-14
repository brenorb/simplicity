/* The core jets, the portable SHA-256 code and the Elements tap-hash
 * operations, followed by the actual construction of the Elements
 * transaction and taproot environments.  elements/elementsJets.c is not part
 * of this unit: it and elements/env.c each define a static function named
 * isFee with a different type, so the two files cannot share a translation
 * unit.  No C bodies or headers are substituted. */
#include "../../C/frame.c"
#include "../../C/jets.c"
#include "../../C/sha256.c"
#include "../../C/elements/ops.c"
#include "../../C/elements/env.c"
#include "../../C/elements/txEnv.c"
