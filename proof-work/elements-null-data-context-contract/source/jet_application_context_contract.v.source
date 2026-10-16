(** Application jets on represented evaluator frames.
    Unlike a broad value-only local contract, this contract explicitly includes
    the Bit Machine separation discipline and preserves represented frames.
    Environment representation/footprints remain independent of the input. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Ty Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_application_sep.
Import Values Mem ListNotations.
Local Open Scope Z_scope.

Definition application_jet_bitmachine_spec (f : function) (ge : Clight.genv) (E : Set)
    (A B : Ty) (env_rep : mem -> val -> E -> list (block * Z * Z) -> Prop)
    (spec : A -> E -> option B) : Prop :=
  forall logical_env env m L s (a : A) tail fp,
    env_rep m env logical_env fp ->
    Forall (fun '(b, lo, hi) => out_sep (frames_blk L) (item_ofs (active_write_loc L))
      (cells_blk L) (edge_ofs (active_write_loc L)) (Z.of_nat (writeEmpty (activeWriteFrame s)))
      (Z.of_nat (bitSize B)) b lo hi) fp ->
    bm_rep m L s -> bm_separated L s -> active_write_writable m L s ->
    nextData (activeReadFrame s) = @encode A a ++ tail ->
    (bitSize B <= writeEmpty (activeWriteFrame s))%nat ->
    exists mf (value : B),
      spec a logical_env = Some value /\
      Clight2.eval_funcall ge m (Internal f) (jet_args env L) E0 mf (Vint Int.one) /\
      bm_rep mf L
        {| inactiveReadFrames := inactiveReadFrames s;
           activeReadFrame := activeReadFrame s;
           activeWriteFrame :=
             {| writeData := rev (@encode B value) ++ writeData (activeWriteFrame s);
                writeEmpty := (writeEmpty (activeWriteFrame s) - length (@encode B value))%nat |};
           inactiveWriteFrames := inactiveWriteFrames s |}.
