(** Full initialized local contract and its all-input constructibility.
    The original memset steps are explicit parameters, not new axioms or
    an external-call model. This conditional result is not a coverage row. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Integers
  Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout
  C.jet_frame_inv C.jet_encoding C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp
  C.jet_secp_initialized_contract C.jet_secp_generate_program C.jet_secp_generate_lifecycle
  C.jet_secp_generator_startup C.jet_secp_generator_zero_global C.jet_secp_generator_globals
  C.jet_clight_forward C.jet_clight_readonly_frame C.jet_frame_constructible
  C.jet_secp_wnaf_digit C.jet_secp_wnaf_entry15 C.jet_secp_wnaf_loop.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_generate encode generator_zero_block generator_table_block.

Theorem generate_initialized_local_spec_from_memset_steps :
  (forall ma mi local ba b,Mem.alloc ma 0 32=(mi,local) ->
    Mem.range_perm ma b 0 516 Cur Freeable -> exists mz,
    Clight2.exec_stmt secp_ge (wnaf_env local)
      (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba Ptrofs.zero))) mi wnaf_memset_call E0
      (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba Ptrofs.zero))) mz Out_normal /\
    (forall i,0<=i<129 -> Mem.load Mint32 mz b (4*i)=Some (Vint Int.zero)) /\
    wnaf_memory_effect b mi mz) ->
  secp_jet_initialized_local_spec generator_startup f_simplicity_generate Word256
    (Ty.Prod (Ty.Prod Word256 Word256) Word256) (@literal_generate Alg.CoreFunSem).
Proof.
  intros ZeroSteps env m bd base bs sbase bi bw edge outedge cursor rc value
    Ready Base Align Source RC Max Input Output.
  change (rc+256<=Int64.max_unsigned) in Max.
  change (write_frame_at m bd base bw outedge cursor 768) in Output.
  rewrite encode_word in Input.
  destruct (eval_generate_initialized env m bd base bs sbase bw outedge cursor 768 bi edge rc value
    ZeroSteps Ready Output ltac:(clear;lia) Base Align Source Input RC Max)
    as (mf & Call & Final & Frame & ReadyF).
  destruct Final as [Valid [FinFrame [Capacity [[Cells [Prefix [Fields [Loads Perms]]]] Written]]]].
  rewrite encode_length in Fields,Loads.
  exists mf;split;[exact Call|];split;[exact Cells|];split;[exact Prefix|];split;[exact Fields|];split;[|exact ReadyF].
  intros chunk b ofs V FrameOther OutputOther.
  destruct (Pos.eq_dec b bd) as [D|D];
    [apply Loads;[split;[left;exact D|exact V]|exact FrameOther|exact OutputOther]|].
  destruct (Pos.eq_dec b bw) as [W|W];
    [apply Loads;[split;[right;left;exact W|exact V]|exact FrameOther|exact OutputOther]|].
  destruct (Pos.eq_dec b bi) as [I|I];
    [apply Loads;[split;[right;right;exact I|exact V]|exact FrameOther|exact OutputOther]|].
  apply (proj1 Frame);[exact V|];intros pos Range;unfold extA,fext;intros [[E|[E|E]] _];contradiction.
Qed.

(** The shared frame constructor preserves old loads and does not increase
    old permissions. Recover readonly-byte access from those very loads,
    rather than assuming that initialized global state survived it. *)
Lemma generate_startup_old_blocks m mf : generator_startup m ->
  (forall b,Mem.valid_block m b -> Mem.valid_block mf b /\
    (forall chunk ofs,Mem.load chunk mf b ofs=Mem.load chunk m b ofs) /\
    (forall ofs k p,Mem.perm mf b ofs k p -> Mem.perm m b ofs k p)) -> generator_startup mf.
Proof.
  intros Ready Old.
  assert (Forward:mem_forward m mf).
  { intros b Valid;destruct (Old b Valid) as (VF & Loads & Perms);split;[exact VF|intros;apply Perms;assumption]. }
  set (P:=fun b (_:Z)=>b=generator_zero_block \/ exists h,b=generator_table_block h).
  assert (Frame:lframe P m mf).
  { split.
    - intros chunk b ofs Valid Cover;exact (proj1 (proj2 (Old b Valid)) chunk ofs).
    - split;[|intros b Valid;exact (proj1 (Old b Valid))].
      intros b pos k p Valid At Perm.
      assert (Bounds:exists hi,readonly_region_bounds m b 0 hi).
      { destruct At as [At|[h At]];subst b;
          [exists 32;exact (proj2 (proj1 Ready))|exists 524288;exact (proj2 (proj2 Ready h))]. }
      destruct Bounds as (hi & Bounds);destruct (proj1 (Bounds pos k p) Perm) as (Range & Order).
      assert (Access:Mem.valid_access m Mint8unsigned b pos Readable).
      { split.
        + intros i R;change (pos<=i<pos+1) in R;assert (i=pos) by lia;subst i;
            apply (proj2 (Bounds pos Cur Readable));split;[exact Range|constructor].
        + change (1|pos);exists pos;lia. }
      destruct (Mem.valid_access_load _ _ _ _ Access) as (v & Load).
      assert (LoadF:Mem.load Mint8unsigned mf b pos=Some v).
      { rewrite (proj1 (proj2 (Old b Valid)));exact Load. }
      pose proof (proj1 (Mem.load_valid_access _ _ _ _ _ LoadF) pos
        ltac:(change (pos<=pos<pos+1);lia)) as Read.
      eapply Mem.perm_implies;[|exact Order];destruct k;[apply Mem.perm_cur_max;exact Read|exact Read]. }
  eapply generator_startup_lframe;[exact Ready|exact Forward|exact Frame|
    intros;left;reflexivity|intros;right;eexists;reflexivity].
Qed.

Theorem generate_runs_from_actual_init (value:Ty.tySem Word256) envv :
  (forall ma mi local ba b,Mem.alloc ma 0 32=(mi,local) ->
    Mem.range_perm ma b 0 516 Cur Freeable -> exists mz,
    Clight2.exec_stmt secp_ge (wnaf_env local)
      (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba Ptrofs.zero))) mi wnaf_memset_call E0
      (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba Ptrofs.zero))) mz Out_normal /\
    (forall i,0<=i<129 -> Mem.load Mint32 mz b (4*i)=Some (Vint Int.zero)) /\
    wnaf_memory_effect b mi mz) ->
  exists mi m bd bs bi bw edge mf,
    Genv.init_mem jets_secp.prog=Some mi /\ generator_startup mi /\ generator_startup m /\
    frame_fields_at m bs 0 bi edge 0 /\ frame_input_cells_at m bi edge 0 (encode value) /\
    write_frame_at m bd 0 bw 0 768 768 /\
    Clight2.eval_funcall secp_ge m (Internal f_simplicity_generate)
      [Vptr bd Ptrofs.zero;Vptr bs Ptrofs.zero;envv] E0 mf (Vint Int.one) /\
    finv m bd 0 bw 0 768 768 bi mf true (encode (@literal_generate Alg.CoreFunSem value)) /\
    generator_startup mf /\
    (forall b chunk ofs,Mem.valid_block mi b -> Mem.load chunk mf b ofs=Mem.load chunk mi b ofs).
Proof.
  intro ZeroSteps;destruct generator_startup_exists as (mi & Init & Ready).
  destruct (jet_frames_constructible mi (encode value) 768)
    as (m & bd & bs & bi & bw & edge & Base & Align & Fields & Input & Output & Sep & Old).
  - rewrite encode_length;change (256<=18446744073709551615);lia.
  - change (0<=768<=18446744073709551615);lia.
  - assert (ReadyM:generator_startup m).
    { apply (generate_startup_old_blocks mi m Ready);intros b Valid;
        destruct (Old b Valid) as (VF & _ & _ & _ & _ & Loads & Perms);exact (conj VF (conj Loads Perms)). }
    pose proof Input as ReaderInput;rewrite encode_word in ReaderInput.
    destruct (eval_generate_initialized envv m bd 0 bs 0 bw 0 768 768 bi edge 0 value ZeroSteps ReadyM Output
      ltac:(clear;lia) Base Align Fields ReaderInput ltac:(clear;lia)
      ltac:(change (256<=18446744073709551615);clear;lia)) as (mf & Call & Final & Frame & ReadyF).
    exists mi,m,bd,bs,bi,bw,edge,mf;split;[exact Init|];split;[exact Ready|];split;[exact ReadyM|];
      split;[exact Fields|];split;[exact Input|];split;[exact Output|];split;[exact Call|];
      split;[exact Final|];split;[exact ReadyF|].
    intros b chunk ofs V;destruct (Old b V) as (VF & ND & _ & NI & NW & Loads & _).
    rewrite (proj1 Frame);[exact (Loads chunk ofs)|exact VF|].
    intros pos Range;unfold extA,fext;intros [[E|[E|E]] _];contradiction.
Qed.
