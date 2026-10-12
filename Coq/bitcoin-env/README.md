# The Bitcoin environment builders (`C/bitcoin/env.c`)

The accepted environment-reading jets take the C environment as given: their
relations say, for example, that the cached `tapLeafHash` field holds the
canonical tagged hash. Those are facts the *caller* establishes. This
directory proves them from the code that actually builds the environment.

Unregistered; accepted sources are only read.

## Program

`C/jets_bitcoin_env.v` is clightgen's output (`C/regenerate-bitcoin-env.sh`)
for `C/jet_bitcoin_env_translation_unit.c`: the SHA translation unit followed
by `bitcoin/env.c`. `check-definitions.py` checks that all 495 functions and
globals of the SHA unit have identical generated text in it and that the SHA
unit's composites are a prefix of its composites. New functions:
`sha256_toMidstate`, `hashBuffer`, `copyOutput`, `copyInput`,
`simplicity_bitcoin_mallocTransaction`, `…freeTransaction`,
`simplicity_bitcoin_mallocTapEnv`, `…freeTapEnv`.

`build-bitcoin-env.sh` builds the derived tree `tree/` (ignored by git) in
which `C.jets_sha` is a copy of that program, so every accepted SHA-unit
proof module is recompiled for it unchanged and `sha_ge` is the environment
unit's global environment.

## Proved so far (six inherited assumptions; `memcpy_model` explicit where the SHA code needs it)

| Module | Result |
|---|---|
| `C/jet_env_store_words.v` | consecutive 32-bit stores as one operation (contents, permissions, unchanged memory) |
| `C/jet_bitcoin_env_field_eval.v` (generated) | struct-field evaluation and checked field offsets for the builder structures |
| `C/jet_bitcoin_env_tomidstate.v` | `eval_sha256_toMidstate`: stores the eight big-endian words of 32 bytes |
| `C/jet_bitcoin_env_hashbuffer.v` | `eval_hashBuffer`: writes the SHA-256 state of a raw buffer to any writable midstate |

## Plan for `simplicity_bitcoin_mallocTapEnv`

Structure of the generated body (offsets: `bitcoinTapEnv` is 176 bytes,
`path` 0, `tapLeafHash` 8, `tappathHash` 40, `tapEnvHash` 72, `internalKey`
104, `scriptCMR` 136, `pathLen` 168, `leafVersion` 169; `rawBitcoinTapEnv`:
`controlBlock` 0, `scriptCMR` 8, `pathLen` 16):

1. guards and size arithmetic, `malloc` (CompCert's `EF_malloc`, concrete semantics);
2. `sha256_toMidstate(internalKey.s, &controlBlock[1])`;
3. compound literal into the local `__compound`, struct copy to `*env`;
4. `sha256_toMidstate(env->scriptCMR.s, rawEnv->scriptCMR)`;
5. `tappathHash`: `sha256_init`, loop of `sha256_toMidstate`/`sha256_hash`, `sha256_finalize`;
6. `tapLeafHash = simplicity_bitcoin_make_tapleaf(...)` (accepted `eval_make_tapleaf`);
7. `tapEnvHash`: `sha256_init`, three `sha256_hash`, `sha256_finalize`.

Target statement: for a well-formed raw environment the returned block holds
the fields that the accepted relations (`hash_getter_rep tapleaf_hash_of 8 8
176`, `… words_hash_of 5 3 (tappath_of e) … 8 40 176`, `… tap_env_hash_of 8
72 176`, and the scalar getters) require of the taproot structure.

Legitimate input requirements that stay premises: the raw structure is
readable, `pathLen <= 128`, the control block has `33 + 32 * pathLen`
readable bytes, the script CMR has 32. Composite lookups of late structures
must not be normalised with `vm_compute` (the composite records carry large
proof terms); use `envu_field_at`.

## Build

```bash
bash Coq/build-bitcoin-env.sh -j4
```
