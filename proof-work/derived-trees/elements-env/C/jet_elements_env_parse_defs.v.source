(** [parseNullData(result, allocation, allocationLen, scriptPubKey)]
    (elements/env.c): the statement, decomposed into its idioms.  The reads
    of the script are the idioms of [countNullDataCodes]
    (jet_elements_env_nulldata_count.v); every failure is
    [{ result->op = NULL; return; }]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_add_n_init.
Require Import C.jet_elements_env_nulldata_count.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.

Notation PND := (Tstruct _parsedNullData noattr).
Notation OPC := (Tstruct _opcode noattr).
Notation PO := (tptr (Tstruct _opcode noattr)).
Notation PPO := (tptr (tptr (Tstruct _opcode noattr))).
Notation PRBUF := (Tstruct _rawElementsBuffer noattr).
Notation PRES := (Ederef (Etempvar _result (tptr PND)) PND).
Notation PSPK := (Ederef (Etempvar _scriptPubKey (tptr PRBUF)) PRBUF).

Definition pn_fail : statement :=
  Ssequence (Sassign (Efield PRES _op PO) (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))) (Sreturn None).

Definition pn_eof (tl : ident) : statement :=
  Ssequence (Sset tl (Efield PSPK _len tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar tl tuint) (Etempvar _i tulong) tint) pn_fail Sskip).

(** [( *allocation)[result->len].code = rhs] *)
Definition pn_setcode (ta tn : ident) (rhs : expr) : statement :=
  Ssequence (Sset ta (Ederef (Etempvar _allocation PPO) PO))
    (Ssequence (Sset tn (Efield PRES _len tulong))
      (Sassign (Efield (Ederef (Ebinop Oadd (Etempvar ta PO) (Etempvar tn tulong) PO) OPC) _code tint) rhs)).

Definition pn_kind : statement :=
  Sifthenelse (Ebinop Olt (Etempvar _code tuchar) (Econst_int (Int.repr 76) tint) tint)
    (Ssequence (Sset _skip (Ecast (Etempvar _code tuchar) tulong))
       (pn_setcode _t'35 _t'36 (Econst_int (Int.repr 0) tint)))
    (Ssequence (pn_eof _t'34)
      (Ssequence (nd_read_stmt _t'4 _t'32 _t'33 (nd_skip_set1 _t'33))
        (Sifthenelse (Ebinop Olt (Etempvar _code tuchar) (Econst_int (Int.repr 77) tint) tint)
          (pn_setcode _t'30 _t'31 (Econst_int (Int.repr 1) tint))
          (Ssequence (pn_eof _t'29)
            (Ssequence (nd_read_stmt _t'5 _t'27 _t'28 (nd_skip_add _t'28 8))
              (Sifthenelse (Ebinop Olt (Etempvar _code tuchar) (Econst_int (Int.repr 78) tint) tint)
                (pn_setcode _t'25 _t'26 (Econst_int (Int.repr 2) tint))
                (Ssequence (pn_eof _t'24)
                  (Ssequence (nd_read_stmt _t'6 _t'22 _t'23 (nd_skip_add _t'23 16))
                    (Ssequence (pn_eof _t'21)
                      (Ssequence (nd_read_stmt _t'7 _t'19 _t'20 (nd_skip_add _t'20 24))
                        (pn_setcode _t'17 _t'18 (Econst_int (Int.repr 3) tint)))))))))))).

Definition pn_hash : statement :=
  ltac:(let b := eval cbv delta [f_parseNullData fn_body] beta iota in (fn_body f_parseNullData) in
        lazymatch b with
        | Ssequence _ (Ssequence _ (Ssequence (Ssequence _ (Sloop
            (Ssequence _ (Ssequence _ (Ssequence _ (Sifthenelse _ _
               (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?h _)))))))) _)) _)) => exact h
        end).

Definition pn_tail : statement :=
  Ssequence
    (Ssequence (Sset _t'16 (Efield PSPK _len tuint))
       (Sifthenelse
          (Ebinop Olt (Ebinop Osub (Etempvar _t'16 tuint) (Etempvar _i tulong) tulong)
             (Etempvar _skip tulong) tint) pn_fail Sskip))
    (Ssequence pn_hash (Sset _i (Ebinop Oadd (Etempvar _i tulong) (Etempvar _skip tulong) tulong))).

Definition pn_check : statement :=
  Ssequence
    (Ssequence (Sset _t'39 (Ederef (Etempvar _allocationLen (tptr tulong)) tulong))
      (Ssequence (Sset _t'40 (Efield PRES _len tulong))
        (Sifthenelse (Ebinop Ole (Etempvar _t'39 tulong) (Etempvar _t'40 tulong) tint)
          (Sset _t'3 (Econst_int (Int.repr 1) tint))
          (Sset _t'3 (Ecast (Ebinop Olt (Econst_int (Int.repr 96) tint) (Etempvar _code tuchar) tint) tbool)))))
    (Sifthenelse (Etempvar _t'3 tint) pn_fail Sskip).

Definition pn_s1 : statement :=
  Ssequence
    (Ssequence (Sset _t'43 (Efield PSPK _len tuint))
       (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _t'43 tuint) tint) Sskip Sbreak))
    (Ssequence
      (nd_read_stmt _t'2 _t'41 _t'42 (Sset _code (Ecast (Etempvar _t'42 tuchar) tuchar)))
      (Ssequence pn_check
        (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 79) tint) (Etempvar _code tuchar) tint)
          (pn_setcode _t'37 _t'38
             (Ebinop Oadd (Econst_int (Int.repr 4) tint)
                (Ebinop Osub (Etempvar _code tuchar) (Econst_int (Int.repr 79) tint) tint) tint))
          (Ssequence (Sset _skip (Ecast (Econst_int (Int.repr 0) tint) tulong))
            (Ssequence pn_kind pn_tail))))).

Definition pn_s2 : statement :=
  Ssequence (Sset _t'12 (Efield PRES _len tulong))
    (Sassign (Efield PRES _len tulong)
       (Ebinop Oadd (Etempvar _t'12 tulong) (Econst_int (Int.repr 1) tint) tulong)).

Definition pn_init : statement :=
  Ssequence
    (Ssequence
      (Ssequence (Sset _t'47 (Ederef (Etempvar _allocation PPO) PO))
         (Sassign (Efield (Evar ___compound PND) _op PO) (Etempvar _t'47 PO)))
      (Sassign (Efield (Evar ___compound PND) _len tulong) (Econst_int (Int.repr 0) tint)))
    (Sassign PRES (Evar ___compound PND)).

Definition pn_head : statement :=
  Ssequence
    (Ssequence (Sset _t'44 (Efield PSPK _len tuint))
       (Sifthenelse (Ebinop Oeq (Econst_int (Int.repr 0) tint) (Etempvar _t'44 tuint) tint)
          (Sset _t'1 (Econst_int (Int.repr 1) tint))
          (Ssequence (Sset _t'45 (Efield PSPK _buf (tptr tuchar)))
             (Ssequence
                (Sset _t'46
                   (Ederef (Ebinop Oadd (Etempvar _t'45 (tptr tuchar)) (Econst_int (Int.repr 0) tint)
                              (tptr tuchar)) tuchar))
                (Sset _t'1
                   (Ecast (Ebinop One (Econst_int (Int.repr 106) tint) (Etempvar _t'46 tuchar) tint)
                      tbool))))))
    (Sifthenelse (Etempvar _t'1 tint) pn_fail Sskip).

Definition pn_finish : statement :=
  Ssequence
    (Ssequence (Sset _t'10 (Ederef (Etempvar _allocation PPO) PO))
      (Ssequence (Sset _t'11 (Efield PRES _len tulong))
        (Sassign (Ederef (Etempvar _allocation PPO) PO)
           (Ebinop Oadd (Etempvar _t'10 PO) (Etempvar _t'11 tulong) PO))))
    (Ssequence (Sset _t'8 (Ederef (Etempvar _allocationLen (tptr tulong)) tulong))
      (Ssequence (Sset _t'9 (Efield PRES _len tulong))
        (Sassign (Ederef (Etempvar _allocationLen (tptr tulong)) tulong)
           (Ebinop Osub (Etempvar _t'8 tulong) (Etempvar _t'9 tulong) tulong)))).

Lemma parseNullData_body_shape :
  fn_body f_parseNullData =
    Ssequence pn_init
      (Ssequence pn_head
        (Ssequence
          (Ssequence (Sset _i (Ecast (Econst_int (Int.repr 1) tint) tulong)) (Sloop pn_s1 pn_s2))
          pn_finish)).
Proof. reflexivity. Qed.
