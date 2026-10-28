From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Integers Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit Simplicity.Translate.
Require Import C.jets_secp C.jet_secp_linkage C.jet_sx_mem C.jet_clight_forward C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Require Import C.jet_partial C.jet_secp_frame C.jet_frame_inv C.jet_output_layout C.jet_write_layout.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_encoding.
Require Import Simplicity.Ty Simplicity.Translate Simplicity.Util.Option.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition secp_jet_initialized_partial_local_spec (Ready:Mem.mem->Prop)
 (f:function) (A B:Ty.Ty) (spec:Ty.tySem A->option (Ty.tySem B)) : Prop :=
 forall env m bd base bs sbase bi bw edge outedge cursor rc (a:Ty.tySem A),
 Ready m -> frame_base_valid sbase -> (8|sbase) ->
 frame_fields_at m bs sbase bi edge rc ->
 0<=rc -> rc+Z.of_nat (bitSize A)<=Int64.max_unsigned ->
 frame_input_cells_at m bi edge rc (encode a) ->
 write_frame_at m bd base bw outedge cursor (Z.of_nat (bitSize B)) ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f)
  [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);env] E0 mf (jet_partial_return (spec a)) /\
 (match spec a with
  | Some value=>frame_output_cells_at mf bw outedge cursor (encode value) /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd base bw outedge (cursor-Z.of_nat (bitSize B))
  | None=>True end) /\
 (forall chunk b ofs,Mem.valid_block m b ->
  (b<>bd \/ ofs+size_chunk chunk<=base+8 \/ base+16<=ofs) ->
  (b<>bw \/ ofs+size_chunk chunk<=outedge+8*((cursor-Z.of_nat (bitSize B))/64) \/
   write_word_address outedge cursor+8<=ofs) ->
  Mem.load chunk mf b ofs=Mem.load chunk m b ofs) /\ Ready mf.

Lemma partial_frame_observations B m bd base bw edge cursor N bi mf (result:option (Ty.tySem B)) :
 finv m bd base bw edge cursor N bi mf
  (match result with Some _=>true|None=>false end)
  (match result with Some value=>encode value|None=>[] end) ->
 lframe (fun b _=>~extA m bd bw bi b) m mf ->
 (match result with
  | Some value=>frame_output_cells_at mf bw edge cursor (encode value) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bd base bw edge (cursor-Z.of_nat (bitSize B))
  | None=>True end) /\
 (forall chunk b ofs,Mem.valid_block m b ->
  (b<>bd \/ ofs+size_chunk chunk<=base+8 \/ base+16<=ofs) ->
  (b<>bw \/ ofs+size_chunk chunk<=edge+8*((cursor-Z.of_nat (bitSize B))/64) \/
   write_word_address edge cursor+8<=ofs) ->
  Mem.load chunk mf b ofs=Mem.load chunk m b ofs).
Proof.
 intros Final Frame;destruct result as [value|].
 - destruct Final as (Valid & Output & Cap & (Cells & Prefix & Fields & Loads & Perms) & Written).
   rewrite encode_length in Fields,Loads.
   split;[exact (conj Cells (conj Prefix Fields))|].
   intros chunk b ofs V FrameOther OutputOther.
   destruct (Pos.eq_dec b bd) as [D|D];
    [apply Loads;[split;[left;exact D|exact V]|exact FrameOther|exact OutputOther]|].
   destruct (Pos.eq_dec b bw) as [W|W];
    [apply Loads;[split;[right;left;exact W|exact V]|exact FrameOther|exact OutputOther]|].
   destruct (Pos.eq_dec b bi) as [I|I];
    [apply Loads;[split;[right;right;exact I|exact V]|exact FrameOther|exact OutputOther]|].
   apply (proj1 Frame);[exact V|intros pos Range;unfold extA,fext;intros [[Same|[Same|Same]] _];contradiction].
 - destruct Final as (Valid & Output & Cap & Effects & Written).
   destruct (Written eq_refl) as (_ & ExactFrame).
   split;[exact I|].
   intros chunk b ofs V FrameOther OutputOther.
   destruct (Pos.eq_dec b bd) as [D|D];
    [apply (proj1 ExactFrame);[exact V|intros;split;[left;exact D|exact V]]|].
   destruct (Pos.eq_dec b bw) as [W|W];
    [apply (proj1 ExactFrame);[exact V|intros;split;[right;left;exact W|exact V]]|].
   destruct (Pos.eq_dec b bi) as [I|I];
    [apply (proj1 ExactFrame);[exact V|intros;split;[right;right;exact I|exact V]]|].
   apply (proj1 Frame);[exact V|intros pos Range;unfold extA,fext;intros [[Same|[Same|Same]] _];contradiction].
Qed.
