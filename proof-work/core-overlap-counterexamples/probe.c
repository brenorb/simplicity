/* Native overlap diagnostics only; no Coq execution or evaluator reachability
 * is claimed. Link the original production sources. The copy adapter's true
 * return is supplied by this test, not by the void simplicity_copyBits. */
#include <inttypes.h>
#include <stdio.h>
#include "jets.h"
typedef struct { const char* name; jet_ptr jet; unsigned in, out; bool high; } test_case;
#define PAD(kind,n,m,h) {"left_pad_" #kind "_" #n "_" #m, simplicity_left_pad_##kind##_##n##_##m,n,m,h}
static bool copy8(frameItem* dst, frameItem src, const txEnv* env) {
  (void)env; simplicity_copyBits(dst, &src, 8); return true;
}
static const test_case cases[] = {
  {"copyBits_8",copy8,8,8,false},
  PAD(low,8,16,false), PAD(low,8,32,false), PAD(low,8,64,false),
  PAD(low,16,32,false), PAD(low,16,64,false), PAD(low,32,64,false),
  PAD(high,8,16,true), PAD(high,8,32,true), PAD(high,8,64,true),
  PAD(high,16,32,true), PAD(high,16,64,true), PAD(high,32,64,true),
  PAD(high,1,8,true), PAD(high,1,16,true), PAD(high,1,32,true), PAD(high,1,64,true)
};
static uint64_t mask(unsigned n) { return n==64 ? UINT64_MAX : (UINT64_C(1)<<n)-1; }
static void put(UWORD* words, unsigned n, uint64_t value) {
  frameItem f=initWriteFrame(n,words+ROUND_UWORD(n));
  for(unsigned k=n;k;--k) writeBit(&f,(value>>(k-1))&1);
}
static uint64_t get(UWORD* words,unsigned n) {
  frameItem f=initReadFrame(n,words); uint64_t value=0;
  for(unsigned k=0;k<n;++k) value=(value<<1)|readBit(&f);
  return value;
}
int main(void) {
  unsigned failures=0,controls=0;
  for(size_t k=0;k<sizeof(cases)/sizeof(cases[0]);++k) {
    const test_case* c=&cases[k];
    for(unsigned layout=0;layout<3;++layout) {
      UWORD cells[16]={0}, separate[ROUND_UWORD(64)]={0};
      UWORD* input=layout==0 ? separate : layout==1
        ? cells+ROUND_UWORD(c->out)-ROUND_UWORD(c->in) : cells+ROUND_UWORD(c->out);
      const uint64_t value=c->in==1 ? c->out<=UWORD_BIT : UINT64_C(0xa5a5a5a5)&mask(c->in);
      put(input,c->in,value);
      frameItem src=initReadFrame(c->in,input), dst=initWriteFrame(c->out,cells+ROUND_UWORD(c->out));
      const uint64_t expected=value|(c->high ? mask(c->out)^mask(c->in) : 0);
      const bool ok=c->jet(&dst,src,NULL);
      const uint64_t actual=get(cells,c->out);
      const bool match=ok && dst.offset==0 && actual==expected;
      printf("%s layout=%u input=%" PRIx64 " expected=%" PRIx64 " actual=%" PRIx64 " success=%d remaining=%zu match=%d\n",
        c->name,layout,value,expected,actual,ok,dst.offset,match);
      if(layout==1) { if(match || !ok || dst.offset) return 1; ++failures; }
      else { if(!match) return 2; ++controls; }
    }
  }
  printf("wrong_overlap_results=%u passing_disjoint_controls=%u\n",failures,controls);
  return 0;
}
