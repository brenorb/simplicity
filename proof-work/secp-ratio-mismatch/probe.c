#include <stdio.h>
#include <string.h>
#include "jets.h"
#include "frame.h"

static int run(int noncanonical) {
  UWORD input[ROUND_UWORD(1280)] = {0};
  UWORD output[ROUND_UWORD(1024)] = {0};
  unsigned char p[32], zero[32] = {0}, one[32] = {0}, actual[32];
  memset(p, 255, sizeof p);
  p[27] = 254; p[30] = 252; p[31] = 47;
  one[31] = 1;
  frameItem fill = initWriteFrame(1280, input + ROUND_UWORD(1280));
  write8s(&fill, zero, 32);
  write8s(&fill, noncanonical ? p : zero, 32);
  write8s(&fill, one, 32);
  write8s(&fill, zero, 32);
  write8s(&fill, zero, 32);
  frameItem dst = initWriteFrame(1024, output + ROUND_UWORD(1024));
  const int ok = simplicity_gej_ge_add_ex(&dst, initReadFrame(1280, input), NULL);
  frameItem readback = initReadFrame(1024, output);
  read8s(actual, 32, &readback);
  printf("AY=%s; returned=%d; remaining=%zu; C ratio=", noncanonical ? "p" : "0", ok, dst.offset);
  for (size_t i=0; i<32; ++i) printf("%02x", actual[i]);
  putchar('\n');
  return !ok || dst.offset != 0 || memcmp(actual, zero, 32) != 0;
}
int main(void) { return run(0) || run(1); }
