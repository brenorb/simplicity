(** Initialized-memory extension of the existing full local jet contract.
    Outputs/framing are unchanged; startup state is additionally preserved. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Ty Simplicity.Translate.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout
  C.jet_encoding C.jet_secp_linkage.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition secp_jet_initialized_local_spec (Ready : Mem.mem -> Prop) (f : function) (A B : Ty) (spec : A -> B) : Prop :=
  forall env m bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A),
    Ready m -> frame_base_valid sbase -> (8 | sbase) ->
    frame_fields_at m bs sbase bi edge read_cursor ->
    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge read_cursor (encode a) ->
    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->
    exists mf,
      Clight2.eval_funcall secp_ge m (Internal f)
        [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
        E0 mf (Vint Int.one) /\
      frame_output_cells_at mf bw outedge cursor (encode (spec a)) /\
      write_prefix_at m mf bw outedge cursor /\
      frame_fields_at mf bd dbase bw outedge (cursor - Z.of_nat (bitSize B)) /\
      (forall chunk b ofs, Mem.valid_block m b ->
        (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
        (b <> bw \/
          ofs + size_chunk chunk <= outedge + 8 * ((cursor - Z.of_nat (bitSize B)) / 64) \/
          write_word_address outedge cursor + 8 <= ofs) ->
        Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\ Ready mf.
