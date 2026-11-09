#ifndef JD_HARNESS_H
#define JD_HARNESS_H

#include <stdbool.h>
#include <stddef.h>
#include "frame.h"

typedef struct txEnv txEnv;
typedef bool (*jd_jet)(frameItem* dst, frameItem src, const txEnv* env);

typedef struct jet_entry {
  const char* name;      /* candidate name, or rawBenchmark name for the panel */
  jd_jet fn;
  size_t in_bits, out_bits;
  /* Optional: adjust a random input so the jet does its full work (panel only). */
  void (*prep)(unsigned char* in);
} jet_entry;

extern const jet_entry jd_sketches[];
extern const jet_entry jd_panel[];

#endif
