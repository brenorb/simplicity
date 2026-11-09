/* Shared declarations for standalone candidate jet sketches.
 *
 * Each ../candidates/<name>/sketch.c defines
 *
 *   bool jd_<name>(frameItem* dst, frameItem src, const txEnv* env);
 *
 * with the calling convention of a libsimplicity jet: read the input value from
 * the 'src' read frame, write the output to the 'dst' write frame, return false
 * where the Simplicity reference expression fails.  A sketch also declares its
 * frame sizes with JD_SKETCH(name, input_bits, output_bits).
 *
 * Sketches are experiments for pricing; they are not linked into libsimplicity
 * and carry no consensus meaning.
 */
#ifndef JD_SKETCH_H
#define JD_SKETCH_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include "frame.h"

typedef struct txEnv txEnv;

/* Marker parsed by gen_registry.sh; expands to nothing. */
#define JD_SKETCH(name, in_bits, out_bits)

/* Read/write an n-bit big-endian word held as 64-bit limbs, most significant
 * limb first (x[0] holds the top bits).  n must be a multiple of 64. */
static inline void jd_read_limbs(uint64_t* x, size_t limbs, frameItem* f) {
  for (size_t i = 0; i < limbs; ++i) x[i] = simplicity_read64(f);
}
static inline void jd_write_limbs(frameItem* f, const uint64_t* x, size_t limbs) {
  for (size_t i = 0; i < limbs; ++i) simplicity_write64(f, x[i]);
}

#endif
