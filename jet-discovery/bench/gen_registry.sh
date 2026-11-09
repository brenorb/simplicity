#!/bin/sh
# Emit the sketch registry from the JD_SKETCH(name, in, out) markers.
set -eu
echo '#include "sketch.h"'
echo '#include "harness.h"'
for f in "$@"; do
  sed -n 's/^JD_SKETCH(\([a-z0-9_]*\), *\([0-9]*\), *\([0-9]*\)).*/bool jd_\1(frameItem*, frameItem, const txEnv*);/p' "$f"
done
echo 'const jet_entry jd_sketches[] = {'
for f in "$@"; do
  sed -n 's/^JD_SKETCH(\([a-z0-9_]*\), *\([0-9]*\), *\([0-9]*\)).*/  { "\1", jd_\1, \2, \3, NULL },/p' "$f"
done
echo '  { NULL, NULL, 0, 0, NULL }'
echo '};'
