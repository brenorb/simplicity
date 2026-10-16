# Elements tapleaf_hash: compiled literal-tag C-to-program checkpoint

Private tree: `/private/tmp/jet-elements-tapleaf.XHgO5wjf`.
Seed: completed seven-jet Elements proof tree
`/private/tmp/jet-elements-stream.1zVQb2CU`; no live audit objects copied.
Main Coq inputs and the original staged patch remain unchanged.

`source/jet_elements_tapleaf_hash_program.v.source` contains the original
Elements `f_simplicity_tapleaf_hash` execution contract against the literal
tagged-hash Simplicity program using `TapleafVersion` and `ScriptCMR`.
The usual explicit separated frame/cache relation remains. The cached field
is the taproot hash at offset8; this result does not establish caller setup.

The tag prefix is constructed from the sixteen ASCII bytes of
`TapLeaf/elements`, SHA-256 of those bytes and compression of the repeated tag
digest. The word uses the checked Haskell/native-hash converter. There is no
unconnected assumed numeric midstate. The exact string and word/leaf-size
bridges are proved; the actual tagged-context absorption/finalization proof
is reused from the Bitcoin development with this different prefix.

The complete fresh compiler/report phase passed:

```sh
python3 -B proof-work/elements-tapleaf/check.py /private/tmp/jet-elements-tapleaf.XHgO5wjf
```

`RUN.json` and the exact logs bind six results, eight definitions, four closed
results, the pure semantic theorem's inherited functional extensionality, and
exactly the six inherited assumptions of the C endpoint. Source fingerprint:
`cbbfd7c397e1ba21f74f0fcad2e7e4116f52219111adbdd5763fcd2a4cf25048`.

The once-only recursive-kernel/Elements-AST phase completed with exit zero
under handle19181:

```sh
python3 -B proof-work/elements-tapleaf/kernel.py /private/tmp/jet-elements-tapleaf.XHgO5wjf
```

`CHECKED.json`, `KERNEL-RUN.json`, `ast.log` and `kernel.log` bind the actual
recursive kernel and Elements AST-regeneration success. The canonical-source
review and61 mutation tests also passed, recorded in
`../elements-tapleaf-source/`. Independent evidence review is running.

Main420 and the private443 full audit remain frozen and separate. Normal
registration/admission remains; no additional accepted coverage or full normal
acceptance is claimed here. Host-library equivalence and actual caller cache
establishment remain separate.
