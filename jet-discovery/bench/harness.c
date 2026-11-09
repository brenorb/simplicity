/* Verify and time candidate jet sketches and the calibration panel.
 *
 *   bench verify VECTORS.tsv       compare every sketch with the reference vectors
 *   bench bench  VECTORS.tsv [NAME...]
 *                                  time sketches (on their OK vectors) and the panel
 *
 * VECTORS.tsv comes from tools/CandidateCVectors.hs:
 *   name  input-hex  OK|FAIL  output-hex  output-mask-hex
 * with Bit Machine cells MSB-first.
 *
 * Timing: every input is called through the same function-pointer loop.  For
 * each input the loop runs 7 repetitions of a call count sized to take at least
 * 2 ms each; the per-input figure is the median repetition.  An entry reports
 * the mean, median and maximum per-input figure in nanoseconds per call.
 */
#if defined(__APPLE__)
#define _DARWIN_C_SOURCE
#else
#define _POSIX_C_SOURCE 200809L
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "harness.h"

#define MAX_BITS 4096
#define MAX_WORDS (MAX_BITS / 8)

typedef struct vec {
  unsigned char in[MAX_BITS / 8], out[MAX_BITS / 8], mask[MAX_BITS / 8];
  bool ok;
} vec;

static int hexval(char c) {
  if ('0' <= c && c <= '9') return c - '0';
  if ('a' <= c && c <= 'f') return c - 'a' + 10;
  if ('A' <= c && c <= 'F') return c - 'A' + 10;
  return -1;
}

static bool unhex(unsigned char* dst, size_t bytes, const char* s) {
  if (strlen(s) != 2 * bytes) return false;
  for (size_t i = 0; i < bytes; ++i) {
    int hi = hexval(s[2*i]), lo = hexval(s[2*i+1]);
    if (hi < 0 || lo < 0) return false;
    dst[i] = (unsigned char)(16 * hi + lo);
  }
  return true;
}

static bool bit_at(const unsigned char* b, size_t i) { return 1 & (b[i / 8] >> (7 - i % 8)); }

/* Load the input cells into a read frame backed by 'buf'. */
static frameItem load_input(UWORD* buf, const unsigned char* in, size_t n) {
  memset(buf, 0, sizeof(UWORD) * ROUND_UWORD(n ? n : 1));
  frameItem w = initWriteFrame(n, buf + ROUND_UWORD(n));
  for (size_t i = 0; i < n; ++i) writeBit(&w, bit_at(in, i));
  return initReadFrame(n, buf);
}

static UWORD inbuf[MAX_WORDS], outbuf[MAX_WORDS];

/* Run once; return the jet's result and compare its output cells. */
static bool run_check(const jet_entry* e, const vec* v, bool* match) {
  frameItem src = load_input(inbuf, v->in, e->in_bits);
  memset(outbuf, 0, sizeof outbuf);
  frameItem dst = initWriteFrame(e->out_bits, outbuf + ROUND_UWORD(e->out_bits));
  bool result = e->fn(&dst, src, NULL);
  *match = true;
  if (result && v->ok) {
    frameItem r = initReadFrame(e->out_bits, outbuf);
    for (size_t i = 0; i < e->out_bits; ++i) {
      bool got = readBit(&r);
      if (bit_at(v->mask, i) && got != bit_at(v->out, i)) { *match = false; break; }
    }
  }
  return result;
}

typedef struct counts { const jet_entry* e; size_t pass, fail, ok_vectors, fail_vectors; } counts;

static char line[1 << 14];

static vec* read_vectors(const char* path, const char* only, const jet_entry* e, size_t* nvec) {
  FILE* f = fopen(path, "r");
  if (!f) { perror(path); exit(2); }
  size_t cap = 64, n = 0;
  vec* vs = malloc(cap * sizeof *vs);
  while (fgets(line, sizeof line, f)) {
    char* fields[5]; size_t k = 0;
    for (char* tok = strtok(line, "\t\n"); tok && k < 5; tok = strtok(NULL, "\t\n")) fields[k++] = tok;
    if (k != 5 || strcmp(fields[0], only)) continue;
    if (n == cap) { cap *= 2; vs = realloc(vs, cap * sizeof *vs); }
    vec* v = &vs[n];
    memset(v, 0, sizeof *v);
    v->ok = 0 == strcmp(fields[2], "OK");
    size_t ib = (e->in_bits + 7) / 8, ob = (e->out_bits + 7) / 8;
    if (!unhex(v->in, ib, fields[1]) || (v->ok && (!unhex(v->out, ob, fields[3]) || !unhex(v->mask, ob, fields[4])))) {
      fprintf(stderr, "%s: malformed vector for %s (frame sizes %zu/%zu)\n", path, only, e->in_bits, e->out_bits);
      exit(2);
    }
    ++n;
  }
  fclose(f);
  *nvec = n;
  return vs;
}

static int verify(const char* path) {
  int bad = 0;
  for (const jet_entry* e = jd_sketches; e->name; ++e) {
    size_t n; vec* vs = read_vectors(path, e->name, e, &n);
    size_t fail = 0, okv = 0, shown = 0;
    for (size_t i = 0; i < n; ++i) {
      bool match; bool r = run_check(e, &vs[i], &match);
      okv += vs[i].ok;
      if (r != vs[i].ok || !match) {
        ++fail;
        if (shown++ < 3) {
          fprintf(stderr, "  %s vector %zu: reference %s, sketch %s%s\n", e->name, i,
                  vs[i].ok ? "OK" : "FAIL", r ? "OK" : "FAIL", r && vs[i].ok && !match ? " (output differs)" : "");
        }
      }
    }
    printf("%s\t%zu vectors (%zu OK, %zu FAIL)\t%s\n", e->name, n, okv, n - okv,
           n == 0 ? "NO VECTORS" : fail ? "MISMATCH" : "PASS");
    if (fail || n == 0) bad = 1;
    free(vs);
  }
  return bad;
}

static double now_ns(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return 1e9 * (double)t.tv_sec + (double)t.tv_nsec;
}

static volatile UWORD sink;

static double time_calls(const jet_entry* e, frameItem src, size_t calls) {
  double t0 = now_ns();
  for (size_t c = 0; c < calls; ++c) {
    frameItem dst = initWriteFrame(e->out_bits, outbuf + ROUND_UWORD(e->out_bits));
    sink ^= (UWORD)e->fn(&dst, src, NULL);
    sink ^= outbuf[0];
  }
  return (now_ns() - t0) / (double)calls;
}

static int cmpd(const void* a, const void* b) {
  double x = *(const double*)a, y = *(const double*)b;
  return (x > y) - (x < y);
}

/* Per-input median of 7 repetitions. */
static double time_input(const jet_entry* e, const unsigned char* in) {
  frameItem src = load_input(inbuf, in, e->in_bits);
  size_t calls = 16;
  time_calls(e, src, 1000);
  while (time_calls(e, src, calls) * (double)calls < 2e6 && calls < (1u << 30)) calls *= 2;
  double reps[7];
  for (int r = 0; r < 7; ++r) reps[r] = time_calls(e, src, calls);
  qsort(reps, 7, sizeof reps[0], cmpd);
  return reps[3];
}

static void report(const char* kind, const jet_entry* e, double* t, size_t n) {
  double sum = 0;
  for (size_t i = 0; i < n; ++i) sum += t[i];
  qsort(t, n, sizeof t[0], cmpd);
  printf("%s\t%s\t%zu\t%zu\t%zu\t%.3f\t%.3f\t%.3f\n", kind, e->name, e->in_bits, e->out_bits, n,
         sum / (double)n, t[n / 2], t[n - 1]);
  fflush(stdout);
}

static uint64_t rng = 0x243f6a8885a308d3u;
static unsigned char next_byte(void) {
  rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
  return (unsigned char)(rng >> 32);
}

static bool selected(const char* name, int argc, char** argv) {
  if (argc == 0) return true;
  for (int i = 0; i < argc; ++i) if (0 == strcmp(argv[i], name)) return true;
  return false;
}

static int bench(const char* path, int argc, char** argv) {
  printf("kind\tname\tin_bits\tout_bits\tinputs\tmean_ns\tmedian_ns\tmax_ns\n");
  for (const jet_entry* e = jd_panel; e->name; ++e) {
    if (!selected(e->name, argc, argv)) continue;
    enum { N = 32 };
    double t[N];
    unsigned char in[MAX_BITS / 8];
    for (size_t i = 0; i < N; ++i) {
      for (size_t b = 0; b < sizeof in; ++b) in[b] = next_byte();
      if (e->prep) e->prep(in);
      t[i] = time_input(e, in);
    }
    report("panel", e, t, N);
  }
  for (const jet_entry* e = jd_sketches; e->name; ++e) {
    if (!selected(e->name, argc, argv)) continue;
    size_t n; vec* vs = read_vectors(path, e->name, e, &n);
    double* t = malloc((n ? n : 1) * sizeof *t);
    size_t k = 0;
    for (size_t i = 0; i < n; ++i) if (vs[i].ok) t[k++] = time_input(e, vs[i].in);
    if (k) report("sketch", e, t, k);
    free(t); free(vs);
  }
  return 0;
}

int main(int argc, char** argv) {
  if (argc >= 3 && 0 == strcmp(argv[1], "verify")) return verify(argv[2]);
  if (argc >= 3 && 0 == strcmp(argv[1], "bench")) return bench(argv[2], argc - 3, argv + 3);
  fprintf(stderr, "usage: %s verify|bench VECTORS.tsv [NAME...]\n", argv[0]);
  return 2;
}
