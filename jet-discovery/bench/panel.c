/* Calibration panel: existing libsimplicity jets with an in-tree rawBenchmark
 * value (Haskell/Simplicity/Bitcoin/Benchmarks.hs).  Each is timed by the same
 * loop as the sketches, on uniform random inputs of its input width.
 * Only total jets whose work does not depend on rejecting random inputs are
 * included.
 */
#include "harness.h"
#include "jets.h"

/* secp256k1 generator G, big-endian affine coordinates. */
static const unsigned char gx[32] = {
  0x79,0xbe,0x66,0x7e,0xf9,0xdc,0xbb,0xac,0x55,0xa0,0x62,0x95,0xce,0x87,0x0b,0x07,
  0x02,0x9b,0xfc,0xdb,0x2d,0xce,0x28,0xd9,0x59,0xf2,0x81,0x5b,0x16,0xf8,0x17,0x98 };
static const unsigned char gy[32] = {
  0x48,0x3a,0xda,0x77,0x26,0xa3,0xc4,0x65,0x5d,0xa4,0xfb,0xfc,0x0e,0x11,0x08,0xa8,
  0xfd,0x17,0xb4,0x48,0xa6,0x85,0x54,0x19,0x9c,0x47,0xd0,0x8f,0xfb,0x10,0xd4,0xb8 };

/* LinearCombination1 rejects invalid points before multiplying, so put the
 * valid point (G, z = 1) between its two random scalars. */
static void prep_linear_combination(unsigned char* in) {
  for (int i = 0; i < 32; ++i) { in[32 + i] = gx[i]; in[64 + i] = gy[i]; in[96 + i] = 0; }
  in[127] = 1;
}

/* Decompress input is a parity bit followed by x; use x(G), which is on the curve. */
static void prep_decompress(unsigned char* in) {
  /* bit 0 is the parity; x occupies cells 1..256, i.e. shifted by one bit. */
  unsigned char parity = in[0] & 0x80;
  for (int i = 0; i < 33; ++i) in[i] = 0;
  in[0] = parity;
  for (int i = 0; i < 32; ++i) { in[i] |= (unsigned char)(gx[i] >> 1); in[i + 1] = (unsigned char)(gx[i] << 7); }
}

const jet_entry jd_panel[] = {
  { "Add32",              simplicity_add_32,               64,   33, NULL },
  { "Subtract32",         simplicity_subtract_32,          64,   33, NULL },
  { "FullAdd32",          simplicity_full_add_32,          65,   33, NULL },
  { "Add64",              simplicity_add_64,              128,   65, NULL },
  { "FullMultiply32",     simplicity_full_multiply_32,    128,   64, NULL },
  { "Multiply64",         simplicity_multiply_64,         128,  128, NULL },
  { "FullMultiply64",     simplicity_full_multiply_64,    256,  128, NULL },
  { "DivMod128_64",       simplicity_div_mod_128_64,      192,  128, NULL },
  { "Sha256Block",        simplicity_sha_256_block,       768,  256, NULL },
  { "FeNormalize",        simplicity_fe_normalize,        256,  256, NULL },
  { "FeMultiply",         simplicity_fe_multiply,         512,  256, NULL },
  { "FeSquare",           simplicity_fe_square,           256,  256, NULL },
  { "FeInvert",           simplicity_fe_invert,           256,  256, NULL },
  { "ScalarNormalize",    simplicity_scalar_normalize,    256,  256, NULL },
  { "ScalarMultiply",     simplicity_scalar_multiply,     512,  256, NULL },
  { "ScalarInvert",       simplicity_scalar_invert,       256,  256, NULL },
  { "GejNormalize",       simplicity_gej_normalize,       768,  513, NULL },
  { "GejDouble",          simplicity_gej_double,          768,  768, NULL },
  { "GejAdd",             simplicity_gej_add,            1536,  768, NULL },
  { "LinearCombination1", simplicity_linear_combination_1, 1280, 768, prep_linear_combination },
  { "Decompress",         simplicity_decompress,          257,  513, prep_decompress },
  { NULL, NULL, 0, 0, NULL }
};
