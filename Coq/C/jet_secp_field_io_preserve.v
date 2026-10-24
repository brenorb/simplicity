(** Original field reader/writer preserve initially readonly memory. Extend
    the existing checked internal helper table, not the external-call model. *)
From Coq Require Import List Bool.
From compcert Require Import AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jets_secp C.jet_secp_linkage C.jet_sx_pure C.jet_secp_scalar_io_preserve
 C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition field_io_helpers :=
 (_read_fe,f_read_fe)::(_write_fe,f_write_fe)::scalar_io_helpers.
Lemma field_io_helpers_checked : forallb(fun it=>
 closed_stmtb field_io_helpers(fn_body(snd it)) &&
 forallb(fun local=>nonfunction_type(snd local))(fn_vars(snd it)))field_io_helpers=true.
Proof. vm_compute;reflexivity. Qed.
Lemma field_io_helpers_lookup : map(symbol_lookup secp_ge)field_io_helpers=
 map(fun p=>Some(Internal(snd p)))field_io_helpers.
Proof. vm_compute;reflexivity. Qed.
Lemma field_io_allowed : allowed_call field_io_helpers(Internal f_read_fe) /\
 allowed_call field_io_helpers(Internal f_write_fe).
Proof.
 split;[exists _read_fe,f_read_fe|exists _write_fe,f_write_fe];split;reflexivity.
Qed.
Local Opaque field_io_helpers.
Lemma field_io_helpers_ok : internal_table_ok secp_ge field_io_helpers.
Proof.
 intros id fd Lookup;pose proof(internal_lookup_in _ _ _ Lookup) as Member.
 pose proof field_io_helpers_checked as Checked;rewrite forallb_forall in Checked.
 specialize(Checked(id,fd)Member);apply andb_true_iff in Checked;destruct Checked as[Body Vars].
 split;[|split;assumption].
 exact(symbol_lookup_table secp_ge field_io_helpers field_io_helpers_lookup id fd Member).
Qed.
Theorem field_reader_preserved m args t mf result :
 Clight2.eval_funcall secp_ge m(Internal f_read_fe)args t mf result -> readonly_preserved m mf.
Proof.
 intro Run;exact(proj2(internal_exec_preserved _ _ field_io_helpers_ok)
  m _ args t mf result Run(proj1 field_io_allowed)).
Qed.
Theorem field_writer_preserved m args t mf result :
 Clight2.eval_funcall secp_ge m(Internal f_write_fe)args t mf result -> readonly_preserved m mf.
Proof.
 intro Run;exact(proj2(internal_exec_preserved _ _ field_io_helpers_ok)
  m _ args t mf result Run(proj2 field_io_allowed)).
Qed.
