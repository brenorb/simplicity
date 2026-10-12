#!/usr/bin/env python3
"""Generate the start-up invariant modules of the Elements unit from
startup/proofs/jet_sha_startup_{state,jets}.v.

Differences from the SHA unit, all made explicit here:
  * the tag arrays of elements/ops.c hold "TapLeaf/elements" (17 bytes with
    the terminator) and "TapBranch/elements" (19 bytes);
  * both are writable objects that are large enough to hold a 16-byte frame
    record, so the separation of the destination frame *record* from them
    cannot be derived from extents as in the SHA unit: it is the explicit
    premise [el_frame_record_sep].  The word buffer is still separated
    automatically, for outputs wider than two words (128 bits);
  * the contracts are stated for [elements_ge].

Usage: gen-elements-startup.py OUTDIR   (run from Coq/)"""
import re, sys
out = sys.argv[1]
state = open("startup/proofs/jet_sha_startup_state.v").read()
jets = open("startup/proofs/jet_sha_startup_jets.v").read()

def sub(text, old, new, count=1):
    assert text.count(old) == count, (old, text.count(old))
    return text.replace(old, new)

# ---- state ----
a = state.index("(** ** Separation derived from the frame's own extent *)")
b = state.index("(** ** Contracts over the invariant *)")
head, tail = state[:a], state[b:]
head = head[head.index("From Coq Require"):]
head = sub(head, "C.jet_bitcoin_make_tapleaf_exec C.jet_bitcoin_make_tapbranch_exec",
           "C.jet_elements_make_tapleaf_exec C.jet_elements_make_tapbranch_exec")
head = sub(head, "Require Import JetStartup.jet_sha_startup_globals.",
           "Require Import JetStartup.jet_sha_startup_globals.\nRequire C.jets_elements.\n"
           "Require Import C.jet_elements_linkage C.jet_elements_sha_program.")
head = sub(head, "_tagName__1) ofs Max p -> 0 <= ofs < 8)", "_tagName__1) ofs Max p -> 0 <= ofs < 17)")
head = sub(head, "_tagName__2) ofs Max p -> 0 <= ofs < 10)", "_tagName__2) ofs Max p -> 0 <= ofs < 19)")
def init_proof(n):
    return ("  intros i Hi.\n  do %d (destruct i as [|i]; [exact (proj1 HLoad)|apply proj2 in HLoad]).\n  lia.\nQed." % n)
for thm, n in (("sha_tapleaf_tag_initialized", 16), ("sha_tapbranch_tag_initialized", 18)):
    m = re.search(r"(Theorem %s m :.*?specialize \(HLoad eq_refl\)\.\n).*?Qed\." % thm, head, re.S)
    head = head[:m.start()] + m.group(1) + init_proof(n) + head[m.end():]
head = head.replace("sha_tapleaf_tag_ok", "el_sha_tapleaf_tag_ok").replace("sha_tapbranch_tag_ok", "el_sha_tapbranch_tag_ok")

middle = r'''(** ** Separation from the output frame *)

(** The constant "TapData" array (8 bytes) cannot hold a frame record. *)
Lemma small_object_not_frame_record m b bound bf base bw edge cursor count :
  (forall ofs p, Mem.perm m b ofs Max p -> 0 <= ofs < bound) -> bound <= 10 ->
  write_frame_at m bf base bw edge cursor count -> bf <> b.
Proof.
  intros HBounds HSmall (HBase & _ & _ & _ & _ & HRecord & HCells) HSame; subst b.
  destruct HRecord as [HRange _].
  assert (HP : Mem.perm m bf (base + 8 + 7) Cur Writable).
  { apply HRange. cbn. lia. }
  pose proof (HBounds _ _ (Mem.perm_cur_max _ _ _ _ HP)) as HIn.
  destruct HBase as [HBase _]. lia.
Qed.

(** An object of at most 19 bytes is not the word buffer of an output frame
    of more than 128 cells (three 8-byte words). *)
Lemma small_object_not_wide_frame m b bound bf base bw edge cursor count :
  (forall ofs p, Mem.perm m b ofs Max p -> 0 <= ofs < bound) -> bound <= 19 ->
  128 < count -> write_frame_at m bf base bw edge cursor count ->
  bw <> b.
Proof.
  intros HBounds HSmall HCount (HBase & _ & _ & _ & _ & HRecord & HCells) HSame; subst b.
  destruct (HCells 0 ltac:(lia)) as (_ & _ & _ & [HRange0 _] & _).
  destruct (HCells 128 ltac:(lia)) as (HLow & _ & _ & _ & _).
  unfold write_cell_address in HRange0, HLow.
  assert (HDiv : (cursor - 1 - 128) / 64 = (cursor - 1 - 0) / 64 - 2).
  { replace (cursor - 1 - 128) with (cursor - 1 - 0 + (-2) * 64) by lia.
    rewrite Z.div_add by lia. lia. }
  rewrite HDiv in HLow.
  assert (HP : Mem.perm m bw (edge + 8 * ((cursor - 1 - 0) / 64) + 7) Cur Writable).
  { apply HRange0. cbn. lia. }
  pose proof (HBounds _ _ (Mem.perm_cur_max _ _ _ _ HP)) as HIn.
  lia.
Qed.

(** The two writable tag arrays of elements/ops.c are 17 and 19 bytes long:
    large enough for a frame record.  That the destination frame record is
    not one of them is therefore a premise the caller establishes (it holds
    for every separately allocated frame). *)
Definition frame_record_sep (bf : block) : Prop :=
  bf <> sha_symbol_block _tagName__1 /\ bf <> sha_symbol_block _tagName__2.

Lemma tag_block_valid m b ofs v :
  Mem.load Mint8unsigned m b ofs = Some v -> Mem.valid_block m b.
Proof.
  intros HL. eapply Mem.perm_valid_block with (ofs := ofs) (k := Cur) (p := Readable).
  eapply (Mem.valid_access_perm m Mint8unsigned b ofs Cur Readable).
  eapply Mem.load_valid_access; exact HL.
Qed.

Section FrameCall.
Variables (m mf : mem) (bf : block) (base : Z) (bw : block) (edge cursor count : Z).
Hypothesis HForward : mem_forward m mf.
Hypothesis HCount : 128 < count.
Hypothesis HFrame : write_frame_at m bf base bw edge cursor count.
Hypothesis HLoads : forall chunk b ofs, Mem.valid_block m b ->
  (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
  (b <> bw \/ ofs + size_chunk chunk <= edge + 8 * ((cursor - count) / 64) \/
    write_word_address edge cursor + 8 <= ofs) ->
  Mem.load chunk mf b ofs = Mem.load chunk m b ofs.
Hypothesis HRecordSep : frame_record_sep bf.

Lemma small_object_loads_preserved b bound ofs v :
  (forall o p, Mem.perm m b o Max p -> 0 <= o < bound) -> bound <= 19 ->
  bf <> b ->
  Mem.load Mint8unsigned m b ofs = Some v ->
  Mem.load Mint8unsigned mf b ofs = Some v.
Proof.
  intros HBounds HSmall HF HL.
  pose proof (small_object_not_wide_frame m b bound bf base bw edge cursor count
    HBounds HSmall HCount HFrame) as HW.
  rewrite HLoads; [exact HL| |left; congruence|left; congruence].
  eapply tag_block_valid; exact HL.
Qed.

Lemma small_object_extent_preserved b bound v :
  Mem.load Mint8unsigned m b 0 = Some v ->
  (forall o p, Mem.perm m b o Max p -> 0 <= o < bound) ->
  (forall o p, Mem.perm mf b o Max p -> 0 <= o < bound).
Proof.
  intros HL HBounds o p HP. apply (HBounds o p).
  exact (proj2 (HForward b (tag_block_valid m b 0 v HL)) o p HP).
Qed.

Theorem sha_tags_state_frame_call : sha_tags_state m -> sha_tags_state mf.
Proof.
  intros (HT & HL & HB & HE1 & HE2 & HE3).
  destruct HRecordSep as [HR1 HR2].
  split; [|split; [|split; [|split; [|split]]]].
  - intros i Hi. eapply small_object_loads_preserved; [exact HE1|lia| |exact (HT i Hi)].
    eapply small_object_not_frame_record; [exact HE1|lia|exact HFrame].
  - intros i Hi. eapply small_object_loads_preserved; [exact HE2|lia|exact HR1|exact (HL i Hi)].
  - intros i Hi. eapply small_object_loads_preserved; [exact HE3|lia|exact HR2|exact (HB i Hi)].
  - eapply small_object_extent_preserved; [exact (HT 0%nat ltac:(lia))|exact HE1].
  - eapply small_object_extent_preserved; [exact (HL 0%nat ltac:(lia))|exact HE2].
  - eapply small_object_extent_preserved; [exact (HB 0%nat ltac:(lia))|exact HE3].
Qed.

Theorem sha_startup_state_frame_call : sha_startup_state m -> sha_startup_state mf.
Proof.
  intros [HGlobals HTags]. split.
  - eapply sha_persistent_globals_forward; [exact HGlobals|exact HForward|].
    eapply sha_globals_from_public_frame_observations;
      [apply sha_persistent_globals_original; exact HGlobals| |exact HFrame|exact HLoads].
    lia.
  - exact (sha_tags_state_frame_call HTags).
Qed.
End FrameCall.

'''
tail = sub(tail, "    sha_startup_state m ->\n", "    sha_startup_state m ->\n    frame_record_sep bd ->\n", 3)
tail = sub(tail, "  64 < Z.of_nat (bitSize B) ->", "  128 < Z.of_nat (bitSize B) ->", 4)
tail = sub(tail, "\n    HState HBase", "\n    HState HRecSep HBase", 3)
tail = sub(tail, "    HState HRep HSep HBase", "    HState HRecSep HRep HSep HBase", 1)
tail = sub(tail, "[|exact HWide|exact HOutput|exact HLoads|exact HState]",
           "[|exact HWide|exact HOutput|exact HLoads|exact HRecSep|exact HState]", 4)
tail = sub(tail, "Clight2.eval_funcall sha_ge", "Clight2.eval_funcall elements_ge", 3)
tail = sub(tail, "application_jet_local_spec_sep f sha_ge", "application_jet_local_spec_sep f elements_ge", 1)
i = tail.rindex("clight_exec_forward sha_ge")
tail = tail[:i] + "clight_exec_forward elements_ge" + tail[i + len("clight_exec_forward sha_ge"):]
for thm, spec in (("sha_startup_total_from_pre", "sha_startup_total_spec"),
                  ("sha_startup_total_from_local", "sha_startup_total_spec"),
                  ("sha_startup_partial_from_local", "sha_startup_partial_spec")):
    m = re.search(r"Theorem %s .*?\nProof\.\n" % thm, tail, re.S)
    tail = tail[:m.end()] + "  unfold %s. rewrite <- elements_sha_genv.\n" % spec + tail[m.end():]
text = head + middle + tail
defined = set(re.findall(r"^(?:Definition|Lemma|Theorem)\s+([A-Za-z_][A-Za-z_0-9']*)", text, re.M))
rename = re.compile(r"(?<![A-Za-z_0-9'.])(%s)(?![A-Za-z_0-9'])" % "|".join(sorted(map(re.escape, defined), key=len, reverse=True)))
text = rename.sub(lambda mo: "el_" + mo.group(1), text)
text = '''(** GENERATED by elements-sha/gen-elements-startup.py from
    startup/proofs/jet_sha_startup_state.v; do not edit.

    The start-up invariant of the Elements translation unit: the dispatch
    pointer, the maximum counter (the accepted [sha_persistent_global_state],
    read in the Elements program) and the three tag arrays, derived from
    [Genv.init_mem jets_elements.prog] and preserved by every call whose
    effect is the public frame contract with an output wider than 128 bits.

    Unlike the SHA unit, the two writable tag arrays here ("TapLeaf/elements",
    "TapBranch/elements": 17 and 19 bytes) could hold a 16-byte frame record,
    so [el_frame_record_sep] -- the destination frame record is not one of
    them -- is a premise for the caller; everything else is derived. *)
''' + text
text += '''
(** The invariant holds in the initial memory of the Elements program. *)
Theorem elements_startup_state_initialized m :
  Genv.init_mem jets_elements.prog = Some m -> el_sha_startup_state m.
Proof. rewrite <- elements_sha_program. exact (el_sha_startup_state_initialized m). Qed.
'''
open(out + "/jet_elements_startup_state.v", "w").write(text)

# ---- jets ----
j = jets[jets.index("From Coq Require"):]
m = re.search(r"Theorem bitcoin_outpoint_hash_startup_spec.*?Qed\.\n", j, re.S)
j = j[:m.start()] + j[m.end():]
j = sub(j, "C.jet_bitcoin_ctx_hash_spec C.jet_bitcoin_build_tapleaf_spec C.jet_bitcoin_build_tapbranch_spec",
        "C.jet_bitcoin_ctx_hash_spec C.jet_elements_build_tapleaf_spec C.jet_elements_build_tapbranch_spec")
j = sub(j, "C.jet_bitcoin_annex_hash_jet C.jet_bitcoin_outpoint_hash_jet", "C.jet_elements_annex_hash_jet")
j = sub(j, "C.jet_bitcoin_make_tapleaf_exec C.jet_bitcoin_make_tapbranch_exec", "C.jet_elements_make_tapleaf_exec C.jet_elements_make_tapbranch_exec")
j = sub(j, "C.jet_bitcoin_build_tapleaf_jet C.jet_bitcoin_build_tapbranch_jet", "C.jet_elements_build_tapleaf_jet C.jet_elements_build_tapbranch_jet")
j = sub(j, "Require Import JetStartup.jet_sha_startup_state.", "Require C.jets_elements.\nRequire Import ElementsStartup.jet_elements_startup_state.")
j = j.replace("f_simplicity_bitcoin_", "f_simplicity_")
j = re.sub(r"\bbitcoin_(annex_hash|build_tapleaf_simplicity|build_tapbranch)_(startup_spec|local_spec)\b", r"elements_\1_\2", j)
j = re.sub(r"\b(build_tapleaf_spec|build_tapbranch_spec)\b", r"el_\1", j)
j = rename.sub(lambda mo: "el_" + mo.group(1), j)
j = re.sub(r"\b(f_simplicity_\w+)", r"jets_elements.\1", j)
n = len(re.findall(r"^Theorem \w+_startup_spec", j, re.M))
assert n == 17 and "bitcoin" not in j.replace("jet_bitcoin_ctx_hash_spec", ""), n
j = '''(** GENERATED by elements-sha/gen-elements-startup.py from
    startup/proofs/jet_sha_startup_jets.v; do not edit.

    Seventeen jets of the Elements translation unit over the single start-up
    invariant [el_sha_startup_state] (established by [Genv.init_mem] of the
    Elements program) and re-establishing it; executions are in
    [elements_ge].  State premises left to the caller: none.  Frame premise
    specific to this unit: [el_frame_record_sep]. *)
''' + j
open(out + "/jet_elements_startup_jets.v", "w").write(j)
print("generated state and %d jet theorems" % n)

# ---- caller setup and executability on fresh frames ----
def names(t):
    return set(re.findall(r"^(?:Definition|Lemma|Theorem|Inductive)\s+([A-Za-z_][A-Za-z_0-9']*)", t, re.M)) | \
           set(re.findall(r"^\| ([A-Za-z_][A-Za-z_0-9']*) :", t, re.M))
def renamer(ns):
    rx = re.compile(r"(?<![A-Za-z_0-9'.])(%s)(?![A-Za-z_0-9'])" % "|".join(sorted(map(re.escape, ns), key=len, reverse=True)))
    return lambda t: rx.sub(lambda mo: "el_" + mo.group(1), t)
def common(t):
    t = t[t.index("From Coq Require"):]
    t = t.replace("sha_tapleaf_tag_ok", "el_sha_tapleaf_tag_ok").replace("sha_tapbranch_tag_ok", "el_sha_tapbranch_tag_ok")
    t = t.replace("C.jet_bitcoin_make_tapleaf_exec C.jet_bitcoin_make_tapbranch_exec",
                  "C.jet_elements_make_tapleaf_exec C.jet_elements_make_tapbranch_exec")
    t = t.replace("JetStartup.jet_sha_startup_state", "ElementsStartup.jet_elements_startup_state")
    t = t.replace("JetStartup.jet_sha_startup_setup", "ElementsStartup.jet_elements_startup_setup")
    return t
setup = common(open("startup/proofs/jet_sha_startup_setup.v").read())
execu = common(open("startup/proofs/jet_sha_startup_executable.v").read())
execu = sub(execu, "Definition sha_total_runs_on_fresh_frames", '''(** A block distinct from every block of the memory in which the invariant
    holds is not a tag array: the frame-record premise holds for fresh frames. *)
Lemma fresh_record_sep (m0 : mem) (bd : block) :
  sha_startup_state m0 -> (forall b, Mem.valid_block m0 b -> b <> bd) -> frame_record_sep bd.
Proof.
  intros HS H.
  split; intro E; (eapply H; [|symmetry; exact E]); (eapply sha_state_blocks_valid; [exact HS|cbn; tauto]).
Qed.

Definition sha_total_runs_on_fresh_frames''')
execu = sub(execu, "\n    HState' HBase HAlign",
            "\n    HState' (fresh_record_sep m0 bd HState (fun b Hb => proj1 (proj2 (HOld b Hb)))) HBase HAlign", 2)
execu = sub(execu, "Clight2.eval_funcall sha_ge", "Clight2.eval_funcall elements_ge", 2)
execu = sub(execu, "Import Values Mem ListNotations.", "Require C.jets_elements.\nRequire Import C.jet_elements_linkage.\nImport Values Mem ListNotations.")
ren = renamer(defined | names(setup) | names(execu))
banner = "(** GENERATED by elements-sha/gen-elements-startup.py from\n    startup/proofs/%s.v; do not edit.\n\n    %s *)\n"
open(out + "/jet_elements_startup_setup.v", "w").write(banner % ("jet_sha_startup_setup",
    "The Elements start-up invariant through the memory operations of a\n    caller; a setup that only allocates and writes its own blocks keeps it\n    and its blocks satisfy [el_frame_record_sep] (they are not state blocks).") + ren(setup) + '''
Theorem el_owned_record_sep m owned b :
  el_sha_owned_setup m owned -> In b owned -> el_frame_record_sep b.
Proof.
  intros HSetup HIn. destruct (el_sha_owned_setup_state m owned HSetup) as [_ HOwners].
  split; intro E; apply (HOwners b HIn); rewrite E; cbn; tauto.
Qed.
''')
open(out + "/jet_elements_startup_executable.v", "w").write(banner % ("jet_sha_startup_executable",
    "Jets of the Elements unit run on freshly constructed frames in any memory\n    satisfying the start-up invariant, for every input; the frame-record\n    premise is discharged because the frames are fresh blocks.") + ren(execu))

runs = ['''(** GENERATED by elements-sha/gen-elements-startup.py; do not edit.

    Each of the seventeen jets runs on freshly constructed frames, for every
    input, in any memory satisfying the Elements start-up invariant -- in
    particular the initial memory of the Elements program
    ([elements_startup_state_initialized]) -- and re-establishes it.  No
    premise about global objects, frames or inputs remains. *)
From Coq Require Import ZArith.
From compcert Require Import Integers.
Require Import C.jet_memcpy_model.
Require Import ElementsStartup.jet_elements_startup_state ElementsStartup.jet_elements_startup_executable.
Require ElementsStartup.jet_elements_startup_jets.

Local Ltac bound := vm_compute; discriminate.
Local Ltac runs_type T :=
  lazymatch T with
  | memcpy_model -> ?S => let R := runs_type S in constr:(memcpy_model -> R)
  | el_sha_startup_total_spec ?f ?A ?B ?s => constr:(el_sha_total_runs_on_fresh_frames f A B s)
  | el_sha_startup_partial_spec ?f ?A ?B ?s => constr:(el_sha_partial_runs_on_fresh_frames f A B s)
  end.
Local Ltac run :=
  first [apply el_sha_startup_total_executable | apply el_sha_startup_partial_executable];
  [|bound|bound].
''']
for name, cond in re.findall(r"^Theorem (\w+)_startup_spec :( memcpy_model ->)?", j, re.M):
    full = "ElementsStartup.jet_elements_startup_jets.%s_startup_spec" % name
    proof = ("  intros Hmodel. run. exact (%s Hmodel)." % full) if cond else ("  run. exact %s." % full)
    runs.append("Theorem %s_startup_runs :\n  ltac:(let T := type of %s in let R := runs_type T in exact R).\nProof.\n%s\nQed.\n" % (name, full, proof))
assert len(runs) == 18
open(out + "/jet_elements_startup_runs.v", "w").write("\n".join(runs))
print("generated setup, executable and %d run theorems" % (len(runs) - 1))
