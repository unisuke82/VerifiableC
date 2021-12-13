Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VC.stack.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Require Import VC.hints. (* Import special hints for this tutorial. *)

Definition malloc_spec_example :=
 DECLARE _malloc
 WITH t:type, gv: globals
 PRE [ tuint ]
    PROP (0 <= sizeof t <= Int.max_unsigned;
          complete_legal_cosu_type t = true;
          natural_aligned natural_alignment t = true)
    PARAMS (Vint (Int.repr (sizeof t)))
    SEP (mem_mgr gv)
 POST [ tptr tvoid ] EX p:_,
    PROP ()
    RETURN (p)
    SEP (mem_mgr gv;
            if eq_dec p nullval then emp
            else (malloc_token Ews t p * data_at_ Ews t p)).
Definition free_spec_example :=
 DECLARE _free
 WITH t: type, p:val, gv: globals
 PRE [ tptr tvoid ]
     PROP ()
     PARAMS (p)
     SEP (mem_mgr gv; malloc_token Ews t p; data_at_ Ews t p)
 POST [ Tvoid ]
     PROP () RETURN () SEP (mem_mgr gv).

Fixpoint listrep (il: list Z) (p: val) : mpred :=
 match il with
 | i::il' => EX y: val,
        malloc_token Ews (Tstruct _cons noattr) p *
        data_at Ews (Tstruct _cons noattr) (Vint (Int.repr i),y) p *
        listrep il' y
 | nil => !! (p = nullval) && emp
 end.

Arguments listrep il p : simpl never.

(*standard (stack_listrep_properties)*)
Lemma listrep_local_prop: forall il p, listrep il p |--
        !! (is_pointer_or_null p /\ (p=nullval <-> il=nil)).
Proof.
  intros. unfold listrep. induction il. 
  - entailer!.
    split; auto.
  - fold listrep. Intros y. entailer!. split. 
    + intro. 
      eapply field_compatible_nullval. subst p. eapply H0.  
    + intro. inversion H2. 
Qed.   
      
#[export] Hint Resolve listrep_local_prop : saturate_local.

Lemma listrep_valid_pointer:
  forall il p,
    listrep il p |-- valid_pointer p.
Proof.
  intros. unfold listrep. destruct il.
  - entailer!.
  - Intro y. hint.  auto with valid_pointer.
Qed.    

#[export] Hint Resolve listrep_valid_pointer : valid_pointer.
(*/standard (stack_listrep_properties)*)

Definition stack (il: list Z) (p: val) :=
 EX q: val,
  malloc_token Ews (Tstruct _stack noattr) p *
  data_at Ews (Tstruct _stack noattr) q p *
  listrep il q.
Arguments stack il p : simpl never.

(*standard (stack_properties)*)
Lemma stack_local_prop: forall il p, stack il p |-- !! (isptr p).
Proof.
  intros. unfold stack. entailer. hint. entailer!.
Qed.
    
#[export] Hint Resolve stack_local_prop : saturate_local.

Lemma stack_valid_pointer:
  forall il p,
   stack il p |-- valid_pointer p.
Proof.
  intros. unfold stack. hint. entailer!. auto with valid_pointer.
Qed.
#[export] Hint Resolve stack_valid_pointer : valid_pointer.
(*/standard (stack_properties)*)

Definition newstack_spec : ident * funspec :=
 DECLARE _newstack
 WITH gv: globals
 PRE [ ]
    PROP () PARAMS() GLOBALS(gv) SEP (mem_mgr gv)
 POST [ tptr (Tstruct _stack noattr) ]
 EX p: val, PROP ( ) RETURN (p) SEP (stack nil p; mem_mgr gv).

Definition push_spec : ident * funspec :=
 DECLARE _push
 WITH p: val, i: Z, il: list Z, gv: globals
 PRE [ tptr (Tstruct _stack noattr), tint ]
    PROP (Int.min_signed <= i <= Int.max_signed)
    PARAMS (p; Vint (Int.repr i)) GLOBALS(gv)
    SEP (stack il p; mem_mgr gv)
 POST [ tvoid ]
 PROP ( ) RETURN () SEP (stack (i::il) p; mem_mgr gv).

Definition pop_spec : ident * funspec :=
 DECLARE _pop
 WITH p: val, i: Z, il: list Z, gv: globals
 PRE [ tptr (Tstruct _stack noattr) ]
    PROP ()
    PARAMS (p) GLOBALS(gv)
    SEP (stack (i::il) p; mem_mgr gv)
 POST [ tint ]
 PROP ( ) RETURN (Vint (Int.repr i)) SEP (stack il p; mem_mgr gv).


Definition Gprog : funspecs :=
        ltac:(with_library prog [
                   newstack_spec; push_spec; pop_spec
             ]).

(*standard (body_pop)*)

Lemma body_pop: semax_body Vprog Gprog f_pop pop_spec.
Proof.
  start_function.
  unfold stack.
  Intros q.
  Print listrep.

  unfold listrep.
  fold listrep.
  Intros y.
  forward.
  forward.
  forward.
  forward.
  hint.
  Print free_spec'.
  hint.
  assert_PROP(q<>nullval) by entailer!.
  forward_call(Tstruct _cons noattr, q, gv).
  - hint.
    Print eq_dec.
    destruct (eq_dec q nullval).
    + contradiction.
    + hint. entailer!.
  - forward. hint. unfold stack. hint. Exists y. hint. entailer!.
Qed. 

Lemma body_push: semax_body Vprog Gprog f_push push_spec.
Proof.
  start_function.
  forward_call (Tstruct _cons noattr, gv).
  unfold stack.
  Intros q x.
  destruct (eq_dec q nullval).
  - hint. forward_if(q<>nullval). 
    + Print exit_spec'. forward_call(1). entailer!.
    + contradiction.
    + Intros. contradiction.
  - hint. forward_if(q<>nullval).
    + forward_call(1). entailer!.
    + hint. forward. hint. entailer!.
    + Intros. forward. forward. forward. forward. unfold stack. fold stack. hint. Exists q. hint.
      unfold listrep. fold listrep. Exists x.
      entailer!.
Qed.

Lemma body_newstack: semax_body Vprog Gprog f_newstack newstack_spec.
Proof.
  start_function.
  forward_call ((Tstruct _stack noattr) , gv).
  Intro p.
  destruct (eq_dec p nullval).
  - forward_if(p<>nullval).
    + forward_call(1). entailer!.
    + contradiction.
    + Intros. contradiction.
  - forward_if(p<>nullval).
    + forward_call(1). entailer!.
    + forward. entailer!.
    + hint. Intros. forward. forward. unfold stack. hint. Exists p. hint.  entailer!. hint.
      Exists nullval. unfold listrep.  entailer!.
Qed.
