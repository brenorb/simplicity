(** Initial-only contracts for jets with assertion/failure semantics.
    The return value is fixed by option semantics on EVERY input. Successful
    calls have the existing canonical output/prefix/cursor observations.
    Failed calls need not produce an output, but the memory footprint is still
    bounded by the destination cursor and output-word interval. Individual
    jets can prove stronger failure preservation, as verify does. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Memory Values Events Ctypes Clight ClightBigstep.
Require Import Simplicity.Ty Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_bitmachine_rep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition jet_partial_return {B : Type} (result : option B) : val :=
  match result with Some _ => Vint Int.one | None => Vint Int.zero end.

Definition jet_partial_local_spec (f : function) (A B : Ty)
    (spec : A -> option B) : Prop :=
  forall env m bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A),
    frame_base_valid sbase -> (8 | sbase) ->
    frame_fields_at m bs sbase bi edge read_cursor ->
    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge read_cursor (encode a) ->
    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->
    exists mf,
      Clight2.eval_funcall ge0 m (Internal f)
        [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
        E0 mf (jet_partial_return (spec a)) /\
      (match spec a with
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

Lemma jet_total_to_partial f (A B : Ty) (spec : A -> B) :
  jet_local_spec f A B spec ->
  jet_partial_local_spec f A B (fun a => Some (spec a)).
Proof.
  intros Hspec env m bd dbase bs sbase bi bw edge outedge cursor rc a HB HA HF H0 Hmax Hin Hout.
  destruct (Hspec env m bd dbase bs sbase bi bw edge outedge cursor rc a
    HB HA HF H0 Hmax Hin Hout) as (mf & Hcall & Hobs & Hpre & Hfields & Hpres).
  exists mf. split; [exact Hcall|]. split; [exact (conj Hobs (conj Hpre Hfields))|exact Hpres].
Qed.
