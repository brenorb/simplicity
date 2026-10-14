/* Reference memcpy with the libc ABI that moves every byte with CompCert's
 * defined one-byte block copy, so that the representation of each byte is
 * preserved exactly (including uninitialized bytes and pointer fragments).
 * Not part of the production library: it is the concrete definition linked
 * in place of the external declaration by the linked-program proofs. */
#include <stddef.h>

void *memcpy(void *dest, const void *src, size_t n) {
  unsigned char *d = dest;
  const unsigned char *s = src;
  size_t i;
  for (i = 0; i < n; i++) __builtin_memcpy_aligned(d + i, s + i, 1, 1);
  return dest;
}
