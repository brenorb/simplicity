(** Literal canonical TransactionVersion program (primitive Version), with the
    actual Bitcoin Clight jet and Translate.encode output. The definition follows
    Haskell/Simplicity/Bitcoin/Jets.hs; it is not a replacement numeric function. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.Util.Option.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition bitcoin_transaction_version_spec {alg : Primitive.Algebra} : alg Ty.Unit Word32 :=
  Primitive.Combinators.prim Bitcoin.Version.

Lemma bitcoin_transaction_version_spec_parametric :
  Primitive.Parametric (@bitcoin_transaction_version_spec).
Proof. intros alg1 alg2 R. apply prim_Parametric. Qed.

Lemma bitcoin_transaction_version_spec_sem (environment : Bitcoin.env) :
  @bitcoin_transaction_version_spec (PrimitivePrimSem option_Monad_Zero) tt environment =
    Bitcoin.sem Bitcoin.Version tt environment.
Proof. reflexivity. Qed.

Theorem bitcoin_transaction_version_canonical_spec (environment : Bitcoin.env)
    m bd dbase bs sbase bw edge cursor be ebase bt txbase version bytes :
  frame_base_valid sbase -> (8 | sbase) ->
  Mem.loadbytes m bs sbase 16 = Some bytes ->
  0 <= ebase <= Ptrofs.max_unsigned -> 0 <= txbase -> txbase + 488 <= Ptrofs.max_unsigned ->
  Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mint64 m bt (txbase + 464) = Some (Vlong version) ->
  Int64.unsigned version = Int.unsigned (sigTxVersion (Bitcoin.envTx environment)) ->
  write_frame_at m bd dbase bw edge cursor 32 ->
  exists mf value,
    @bitcoin_transaction_version_spec (PrimitivePrimSem option_Monad_Zero) tt environment = Some value /\
    Clight2.eval_funcall bitcoin_ge m (Internal f_simplicity_bitcoin_version)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); Vptr be (Ptrofs.repr ebase)]
      E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw edge cursor (encode value) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bd dbase bw edge (cursor - 32) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= slice_write_low 32 edge cursor \/
        write_word_address edge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HS HA HB HE HT HM HEnv HVersion HR HFrame.
  destruct (eval_bitcoin_version_layout_matches_primitive environment m bd dbase bs sbase bw edge cursor
      be ebase bt txbase version bytes HS HA HB HE HT HM HEnv HVersion HR HFrame)
    as (mf & value & HSpec & HCall & HOutput & HPrefix & HFields & HMemory).
  exists mf, value. split.
  - rewrite bitcoin_transaction_version_spec_sem; exact HSpec.
  - split; [exact HCall|]. split.
    + apply (wide_output_at_encode W32); [|exact HOutput].
      destruct HFrame as (_ & _ & _ & HC & _). change (32 <= cursor); lia.
    + split; [exact HPrefix|]. split; [exact HFields|exact HMemory].
Qed.
