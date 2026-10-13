/* Reference byte-loop implementation of memcmp with the libc ABI.
 * It is not part of the production library: it exists so that the libc
 * contract the proofs need for the callers of memcmp (memcmp_model) has a
 * checked Clight implementation that can be linked in place of the external
 * declaration. */
#include <stddef.h>

int memcmp(const void *a, const void *b, size_t n) {
  const unsigned char *p = a;
  const unsigned char *q = b;
  size_t i;
  for (i = 0; i < n; i++) {
    if (p[i] != q[i]) return p[i] < q[i] ? -1 : 1;
  }
  return 0;
}
