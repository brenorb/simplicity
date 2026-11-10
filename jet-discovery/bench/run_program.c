/* Run a serialized Bitcoin Simplicity program with libsimplicity's own evaluator.
 *
 *   run_program PROGRAM.bin WITNESS.bin
 *
 * Follows simplicity_bitcoin_execSimplicity (C/bitcoin/exec.c): decode,
 * type inference, witness fill, duplicate-IHR check, static analysis and
 * evaluation, in a one-input/one-output transaction environment.  It differs
 * in two ways, both so that unpruned research programs above BUDGET_MAX can be
 * checked for correctness:
 *   - no budget is passed to the evaluator (static analysis is still run and
 *     its cost bound printed, in milliWU, for comparison with the Haskell
 *     analysis);
 *   - the anti-DoS execution checks (every node / every case branch executed)
 *     are off, because unpruned programs keep both branches of every case.
 * The script-CMR check is skipped; the program's CMR is printed instead.
 *
 * Prints "OK cost_mwu=N cmr=HEX" or "ERR code cost_mwu=N cmr=HEX".
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "simplicity/bitcoin/env.h"
#include "bitcoin/primitive.h"
#include "bitcoin/txEnv.h"
#include "bitstream.h"
#include "dag.h"
#include "deserialize.h"
#include "eval.h"
#include "limitations.h"
#include "simplicity_alloc.h"
#include "typeInference.h"

static unsigned char* slurp(const char* path, size_t* len) {
  FILE* f = fopen(path, "rb");
  if (!f) { perror(path); exit(2); }
  fseek(f, 0, SEEK_END);
  long n = ftell(f);
  fseek(f, 0, SEEK_SET);
  unsigned char* buf = malloc(n ? (size_t)n : 1);
  if (n && fread(buf, 1, (size_t)n, f) != (size_t)n) { perror(path); exit(2); }
  fclose(f);
  *len = (size_t)n;
  return buf;
}

int main(int argc, char** argv) {
  if (argc != 3) { fprintf(stderr, "usage: %s PROGRAM.bin WITNESS.bin\n", argv[0]); return 2; }
  size_t plen, wlen;
  unsigned char* program = slurp(argv[1], &plen);
  unsigned char* witness = slurp(argv[2], &wlen);

  unsigned char txid[32] = {0}, prev[32] = {0x11}, cb[33] = {0xc0}, cmrbuf[32] = {0};
  rawBitcoinInput in = { .annex = NULL, .prevTxid = prev, .txo = { .value = 1000, .scriptPubKey = { NULL, 0 } },
                         .scriptSig = { NULL, 0 }, .prevIx = 0, .sequence = 0 };
  rawBitcoinOutput out = { .value = 900, .scriptPubKey = { NULL, 0 } };
  rawBitcoinTransaction raw = { .txid = txid, .input = &in, .output = &out, .numInputs = 1, .numOutputs = 1,
                                .version = 2, .lockTime = 0 };
  bitcoinTransaction* tx = simplicity_bitcoin_mallocTransaction(&raw);
  rawBitcoinTapEnv rawTap = { .controlBlock = cb, .scriptCMR = cmrbuf, .pathLen = 0 };
  bitcoinTapEnv* tap = simplicity_bitcoin_mallocTapEnv(&rawTap);
  if (!tx || !tap) { fprintf(stderr, "environment allocation failed\n"); return 2; }

  combinator_counters census;
  dag_node* dag = NULL;
  bitstream stream = initializeBitstream(program, plen);
  int_fast32_t len = simplicity_decodeMallocDag(&dag, simplicity_bitcoin_decodeJet, &census, &stream);
  if (len <= 0) { printf("ERR decode %d\n", (int)len); return 1; }
  simplicity_err err = simplicity_closeBitstream(&stream);
  char cmr[65] = {0};
  for (int i = 0; i < 8; ++i) sprintf(cmr + 8 * i, "%08x", (unsigned)dag[len - 1].cmr.s[i]);

  type* type_dag = NULL;
  if (IS_OK(err)) err = simplicity_mallocTypeInference(&type_dag, simplicity_bitcoin_mallocBoundVars, dag, (uint_fast32_t)len, &census);
  if (IS_OK(err) && (0 != dag[len - 1].sourceType || 0 != dag[len - 1].targetType)) err = SIMPLICITY_ERR_TYPE_INFERENCE_NOT_PROGRAM;
  if (IS_OK(err)) {
    bitstream ws = initializeBitstream(witness, wlen);
    err = simplicity_fillWitnessData(dag, type_dag, (uint_fast32_t)len, &ws);
    if (IS_OK(err)) err = simplicity_closeBitstream(&ws);
  }
  if (IS_OK(err)) {
    sha256_midstate ihr;
    err = simplicity_verifyNoDuplicateIdentityHashes(&ihr, dag, type_dag, (uint_fast32_t)len);
  }
  ubounded cells = 0, uwords = 0, frames = 0, cost = 0;
  if (IS_OK(err)) err = simplicity_analyseBounds(&cells, &uwords, &frames, &cost, CELLS_MAX, 0, UBOUNDED_MAX, dag, type_dag, (size_t)len);
  if (IS_OK(err)) {
    txEnv env = simplicity_bitcoin_build_txEnv(tx, tap, 0);
    err = simplicity_evalTCOExpression(CHECK_NONE, NULL, NULL, dag, type_dag, (size_t)len, 0, NULL, &env);
  }
  if (IS_OK(err)) printf("OK cost_mwu=%llu cmr=%s\n", (unsigned long long)cost, cmr);
  else printf("ERR %d cost_mwu=%llu cmr=%s\n", (int)err, (unsigned long long)cost, cmr);
  simplicity_free(type_dag);
  simplicity_free(dag);
  simplicity_bitcoin_freeTransaction(tx);
  simplicity_bitcoin_freeTapEnv(tap);
  free(program);
  free(witness);
  return IS_OK(err) ? 0 : 1;
}
