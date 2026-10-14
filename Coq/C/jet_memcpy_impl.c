/* Reference byte-loop implementation of memcpy with the libc ABI.
 * It is not part of the production library: it exists so that the libc
 * contract assumed by the jet proofs (memcpy_model) has a checked Clight
 * implementation that can be linked in place of the external declaration. */
#include <stddef.h>

void *memcpy(void *dest, const void *src, size_t n) {
  unsigned char *d = dest;
  const unsigned char *s = src;
  size_t i;
  for (i = 0; i < n; i++) d[i] = s[i];
  return dest;
}
