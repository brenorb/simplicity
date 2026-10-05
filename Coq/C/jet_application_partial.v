(** Application-jet contract for jets with assertion/failure semantics: the
    return value is fixed by the option semantics on every input.  Successful
    calls have the canonical output/prefix/cursor observations; the memory
    footprint is bounded by the destination cursor and output-word interval in
    both cases.  This is [jet_partial_local_spec] with a logical environment. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Memory Values Events Ctypes Clight ClightBigstep.
Require Import Simplicity.Ty Simplicity.Translate.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_encoding C.jet_partial.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition application_jet_partial_spec (f : function) (ge : Clight.genv) (E : Set)
    (A B : Ty) (env_rep : mem -> val -> E -> Prop) (spec : A -> E -> option B) : Prop :=
  forall logical_env env m bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A),
    env_rep m env logical_env ->
    frame_base_valid sbase -> (8 | sbase) ->
    frame_fields_at m bs sbase bi edge read_cursor ->
    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge read_cursor (encode a) ->
    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->
    exists mf,
      Clight2.eval_funcall ge m (Internal f)
        [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
        E0 mf (jet_partial_return (spec a logical_env)) /\
      (match spec a logical_env with
       | Some b => frame_output_cells_at mf bw outedge cursor (encode b) /\
           write_prefix_at m mf bw outedge cursor /\
           frame_fields_at mf bd dbase bw outedge (cursor - Z.of_nat (bitSize B))
       | None => True
       end) /\
      (forall chunk b ofs, Mem.valid_block m b ->
        (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
        (b <> bw \/
          ofs + size_chunk chunk <= outedge + 8 * ((cursor - Z.of_nat (bitSize B)) / 64) \/
          write_word_address outedge cursor + 8 <= ofs) ->
        Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
