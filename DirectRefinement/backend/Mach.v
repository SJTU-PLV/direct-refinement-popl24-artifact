(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** The Mach intermediate language: abstract syntax.

  Mach is the last intermediate language before generation of assembly
  code.
*)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import LanguageInterface CKLR.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Stacklayout.
Local Opaque Z.add Z.mul.

(** * Abstract syntax *)

(** Like Linear, the Mach language is organized as lists of instructions
  operating over machine registers, with default fall-through behaviour
  and explicit labels and branch instructions.

  The main difference with Linear lies in the instructions used to
  access the activation record.  Mach has three such instructions:
  [Mgetstack] and [Msetstack] to read and write within the activation
  record for the current function, at a given word offset and with a
  given type; and [Mgetparam], to read within the activation record of
  the caller.

  These instructions implement a more concrete view of the activation
  record than the the [Lgetstack] and [Lsetstack] instructions of
  Linear: actual offsets are used instead of abstract stack slots, and the
  distinction between the caller's frame and the callee's frame is
  made explicit. *)

Definition label := positive.

Inductive instruction: Type :=
  | Mgetstack: ptrofs -> typ -> mreg -> instruction
  | Msetstack: mreg -> ptrofs -> typ -> instruction
  | Mgetparam: ptrofs -> typ -> mreg -> instruction
  | Mop: operation -> list mreg -> mreg -> instruction
  | Mload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Mstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Mcall: signature -> mreg + ident -> instruction
  | Mtailcall: signature -> mreg + ident -> instruction
  | Mbuiltin: external_function -> list (builtin_arg mreg) -> builtin_res mreg -> instruction
  | Mlabel: label -> instruction
  | Mgoto: label -> instruction
  | Mcond: condition -> list mreg -> label -> instruction
  | Mjumptable: mreg -> list label -> instruction
  | Mreturn: instruction.

Definition code := list instruction.

Record function: Type := mkfunction
  { fn_sig: signature;
    fn_code: code;
    fn_stacksize: Z;
    fn_link_ofs: ptrofs;
    fn_retaddr_ofs: ptrofs }.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

Definition genv := Genv.t fundef unit.

(** * Operational semantics *)

(** The semantics for Mach is close to that of [Linear]: they differ only
  on the interpretation of stack slot accesses.  In Mach, these
  accesses are interpreted as memory accesses relative to the
  stack pointer.  More precisely:
- [Mgetstack ofs ty r] is a memory load at offset [ofs * 4] relative
  to the stack pointer.
- [Msetstack r ofs ty] is a memory store at offset [ofs * 4] relative
  to the stack pointer.
- [Mgetparam ofs ty r] is a memory load at offset [ofs * 4]
  relative to the pointer found at offset 0 from the stack pointer.
  The semantics maintain a linked structure of activation records,
  with the current record containing a pointer to the record of the
  caller function at offset 0.

In addition to this linking of activation records, the
semantics also make provisions for storing a back link at offset
[f.(fn_link_ofs)] from the stack pointer, and a return address at
offset [f.(fn_retaddr_ofs)].  The latter stack location will be used
by the Asm code generated by [Asmgen] to save the return address into
the caller at the beginning of a function, then restore it and jump to
it at the end of a function.  The Mach concrete semantics does not
attach any particular meaning to the pointer stored in this reserved
location, but makes sure that it is preserved during execution of a
function.  The [return_address_offset] parameter is used to guess the
value of the return address that the Asm code generated later will
store in the reserved location.
*)

Definition load_stack (m: mem) (sp: val) (ty: typ) (ofs: ptrofs) :=
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr sp ofs).

Definition store_stack (m: mem) (sp: val) (ty: typ) (ofs: ptrofs) (v: val) :=
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr sp ofs) v.

Module RegEq.
  Definition t := mreg.
  Definition eq := mreg_eq.
End RegEq.

Module Regmap := EMap(RegEq).

Definition regset := Regmap.t val.

Notation "a ## b" := (List.map a b) (at level 1).
Notation "a # b <- c" := (Regmap.set b c a) (at level 1, b at next level).

Fixpoint undef_regs (rl: list mreg) (rs: regset) {struct rl} : regset :=
  match rl with
  | nil => rs
  | r1 :: rl' => Regmap.set r1 Vundef (undef_regs rl' rs)
  end.

Lemma undef_regs_other:
  forall r rl rs, ~In r rl -> undef_regs rl rs r = rs r.
Proof.
  induction rl; simpl; intros. auto. rewrite Regmap.gso. apply IHrl. intuition. intuition.
Qed.

Lemma undef_regs_same:
  forall r rl rs, In r rl -> undef_regs rl rs r = Vundef.
Proof.
  induction rl; simpl; intros. tauto.
  destruct H. subst a. apply Regmap.gss.
  unfold Regmap.set. destruct (RegEq.eq r a); auto.
Qed.

Definition undef_caller_save_regs (rs: regset) : regset :=
  fun r => if is_callee_save r then rs r else Vundef.

Definition set_pair (p: rpair mreg) (v: val) (rs: regset) : regset :=
  match p with
  | One r => rs#r <- v
  | Twolong rhi rlo => rs#rhi <- (Val.hiword v) #rlo <- (Val.loword v)
  end.

Definition get_pair (p : rpair mreg) (rs : regset) :=
  match p with
  | One r => rs r
  | Twolong r1 r2 => Val.longofwords (rs r1) (rs r2)
  end.

Fixpoint set_res (res: builtin_res mreg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => Regmap.set r v rs
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Mlabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Mlabel lbl else instr <> Mlabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | i1 :: il => if is_label lbl i1 then Some il else find_label lbl il
  end.

Lemma find_label_tail:
  forall lbl c c', find_label lbl c = Some c' -> is_tail c' c.
Proof.
  induction c; simpl; intros. discriminate.
  destruct (is_label lbl a). inv H. auto with coqlib. eauto with coqlib.
Qed.

Lemma find_label_incl:
  forall lbl c c', find_label lbl c = Some c' -> incl c' c.
Proof.
  intros; red; intros. eapply is_tail_incl; eauto. eapply find_label_tail; eauto.
Qed.

Section RELSEM.

Variable return_address_offset: function -> code -> ptrofs -> Prop.

Variable ge: genv.

Definition ros_address (ge: genv) (ros: mreg + ident) (rs: regset) : val :=
  match ros with
  | inl r => rs r
  | inr symb => Genv.symbol_address ge symb Ptrofs.zero
  end.

(** Extract the values of the arguments to an external call. *)

Inductive extcall_arg (rs: regset) (m: mem) (sp: val): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m sp (R r) (rs r)
  | extcall_arg_stack: forall ofs ty v,
      load_stack m sp ty (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * ofs)) = Some v ->
      extcall_arg rs m sp (S Outgoing ofs ty) v.

Inductive extcall_arg_pair (rs: regset) (m: mem) (sp: val): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m sp l v ->
      extcall_arg_pair rs m sp (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m sp hi vhi ->
      extcall_arg rs m sp lo vlo ->
      extcall_arg_pair rs m sp (Twolong hi lo) (Val.longofwords vhi vlo).

Definition extcall_arguments
    (rs: regset) (m: mem) (sp: val) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg_pair rs m sp) (loc_arguments sg) args.

(** Mach execution states. *)

(** Mach execution states. *)

Inductive stackframe: Type :=
  | Stackframe:
      forall (vf: val)        (**r pointer to calling function *)
             (sp: val)        (**r stack pointer in calling function *)
             (retaddr: val)   (**r Asm return address in calling function *)
             (c: code),       (**r program point in calling function *)
      stackframe
  | Stackbase:
      forall (sp: val)        (**r stack pointer at module entry *)
             (retaddr: val),  (**r Asm return address at module entry *)
      stackframe.

Inductive state: Type :=
  | State:
      forall (stack: list stackframe)  (**r call stack *)
             (vf: val)                 (**r pointer to current function *)
             (sp: val)                 (**r stack pointer *)
             (c: code)                 (**r current program point *)
             (rs: regset)              (**r register state *)
             (m: mem),                 (**r memory state *)
      state
  | Callstate:
      forall (stack: list stackframe)  (**r call stack *)
             (vf: val)                 (**r pointer to function to call *)
             (rs: regset)              (**r register state *)
             (m: mem),                 (**r memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe)  (**r call stack *)
             (rs: regset)              (**r register state *)
             (m: mem),                 (**r memory state *)
      state.

Definition parent_sp (s: list stackframe) : val :=
  match s with
  | nil => Vundef
  | Stackbase sp ra :: s' => sp
  | Stackframe f sp ra c :: s' => sp
  end.

Definition parent_ra (s: list stackframe) : val :=
  match s with
  | nil => Vundef
  | Stackbase sp ra :: s' => ra
  | Stackframe f sp ra c :: s' => ra
  end.

Inductive step: state -> trace -> state -> Prop :=
  | exec_Mlabel:
      forall s f sp lbl c rs m,
      step (State s f sp (Mlabel lbl :: c) rs m)
        E0 (State s f sp c rs m)
  | exec_Mgetstack:
      forall s f sp ofs ty dst c rs m v,
      load_stack m sp ty ofs = Some v ->
      step (State s f sp (Mgetstack ofs ty dst :: c) rs m)
        E0 (State s f sp c (rs#dst <- v) m)
  | exec_Msetstack:
      forall s f sp src ofs ty c rs m m' rs',
      store_stack m sp ty ofs (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_setstack ty) rs ->
      step (State s f sp (Msetstack src ofs ty :: c) rs m)
        E0 (State s f sp c rs' m')
  | exec_Mgetparam:
      forall s vf f sp ofs ty dst c rs m v rs',
      Genv.find_funct ge vf = Some (Internal f) ->
      load_stack m sp Tptr f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (parent_sp s) ty ofs = Some v ->
      rs' = (rs # temp_for_parent_frame <- Vundef # dst <- v) ->
      step (State s vf sp (Mgetparam ofs ty dst :: c) rs m)
        E0 (State s vf sp c rs' m)
  | exec_Mop:
      forall s f sp op args res c rs m v rs',
      eval_operation ge sp op rs##args m = Some v ->
      rs' = ((undef_regs (destroyed_by_op op) rs)#res <- v) ->
      step (State s f sp (Mop op args res :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mload:
      forall s f sp chunk addr args dst c rs m a v rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = ((undef_regs (destroyed_by_load chunk addr) rs)#dst <- v) ->
      step (State s f sp (Mload chunk addr args dst :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mstore:
      forall s f sp chunk addr args src c rs m m' a rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      step (State s f sp (Mstore chunk addr args src :: c) rs m)
        E0 (State s f sp c rs' m')
  | exec_Mcall:
      forall s vf sp sig ros c rs m f ra,
      Genv.find_funct ge vf = Some (Internal f) ->
      return_address_offset f c ra ->
      step (State s vf sp (Mcall sig ros :: c) rs m)
        E0 (Callstate (Stackframe vf sp (Val.offset_ptr vf ra) c :: s)
                      (ros_address ge ros rs) rs m)
  | exec_Mtailcall:
      forall s vf stk soff sig ros c rs m f m',
      Genv.find_funct ge vf = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk (Ptrofs.unsigned soff) (Ptrofs.unsigned soff + f.(fn_stacksize)) = Some m' ->
      step (State s vf (Vptr stk soff) (Mtailcall sig ros :: c) rs m)
        E0 (Callstate s (ros_address ge ros rs) rs m')
  | exec_Mbuiltin:
      forall s f sp rs m ef args res b vargs t vres rs' m',
      eval_builtin_args ge rs sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = set_res res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      step (State s f sp (Mbuiltin ef args res :: b) rs m)
         t (State s f sp b rs' m')
  | exec_Mgoto:
      forall s vf f sp lbl c rs m c',
      Genv.find_funct ge vf = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      step (State s vf sp (Mgoto lbl :: c) rs m)
        E0 (State s vf sp c' rs m)
  | exec_Mcond_true:
      forall s vf f sp cond args lbl c rs m c' rs',
      eval_condition cond rs##args m = Some true ->
      Genv.find_funct ge vf = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (State s vf sp (Mcond cond args lbl :: c) rs m)
        E0 (State s vf sp c' rs' m)
  | exec_Mcond_false:
      forall s f sp cond args lbl c rs m rs',
      eval_condition cond rs##args m = Some false ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (State s f sp (Mcond cond args lbl :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mjumptable:
      forall s vf f sp arg tbl c rs m n lbl c' rs',
      rs arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      Genv.find_funct ge vf = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs destroyed_by_jumptable rs ->
      step (State s vf sp (Mjumptable arg tbl :: c) rs m)
        E0 (State s vf sp c' rs' m)
  | exec_Mreturn:
      forall s vf stk soff c rs m f m',
      Genv.find_funct ge vf = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk (Ptrofs.unsigned soff) (Ptrofs.unsigned soff + f.(fn_stacksize)) = Some m' ->
      step (State s vf (Vptr stk soff) (Mreturn :: c) rs m)
        E0 (Returnstate s rs m')
  | exec_function_internal:
      forall s vf rs m f m1 m2 m3 stk rs',
      Genv.find_funct ge vf = Some (Internal f) ->
      Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) ->
      let sp := Vptr stk Ptrofs.zero in
      store_stack m1 sp Tptr f.(fn_link_ofs) (parent_sp s) = Some m2 ->
      store_stack m2 sp Tptr f.(fn_retaddr_ofs) (parent_ra s) = Some m3 ->
      rs' = undef_regs destroyed_at_function_entry rs ->
      step (Callstate s vf rs m)
        E0 (State s vf sp f.(fn_code) rs' m3)
  | exec_function_external:
      forall s vf rs m t rs' ef args res m',
      Genv.find_funct ge vf = Some (External ef) ->
      extcall_arguments rs m (parent_sp s) (ef_sig ef) args ->
      external_call ef ge args m t res m' ->
      rs' = set_pair (loc_result (ef_sig ef)) res (undef_caller_save_regs rs) ->
      step (Callstate s vf rs m)
         t (Returnstate s rs' m')
  | exec_return:
      forall s f sp ra c rs m,
      step (Returnstate (Stackframe f sp ra c :: s) rs m)
        E0 (State s f sp c rs m).

End RELSEM.

(** * Language interface *)

(** Mach interactions are similar to the [li_locset] ones, but the
  register state contains only machine registers, whereas the stack
  slots are now stored in memory. *)

Record mach_query :=
  mq {
    mq_vf: val;
    mq_sp: val;
    mq_ra: val;
    mq_rs: regset;
    mq_mem: mem;
  }.

Record mach_reply :=
  mr {
    mr_rs: regset;
    mr_mem: mem;
  }.

Canonical Structure li_mach: language_interface :=
  {|
    query := mach_query;
    reply := mach_reply;
    entry := mq_vf;
  |}.

(** * Interaction predicates *)

(** We need to constrain [sp] to point at offset zero to avoid
  wrap-around issues with the arguments region. The [cc_mach]
  convention must take this into account and force the injection to
  map the stack block at offset 0. Note that in the original CompCert
  semantics, the stack pointer is initially a zero integer, so we may
  want to relax this condition in cases where there are no arguments
  to be read. *)

Inductive initial_state (ge: genv): query li_mach -> state -> Prop :=
  | initial_state_intro: forall vf f sp ra rs m,
      Genv.find_funct ge vf = Some (Internal f) ->
      initial_state ge
        (mq vf sp ra rs m)
        (Callstate (Stackbase sp ra :: nil) vf rs m).

Inductive at_external (ge: genv): state -> query li_mach -> Prop :=
  | at_external_intro vf name sg s rs m:
      Genv.find_funct ge vf = Some (External (EF_external name sg)) ->
      at_external ge
        (Callstate s vf rs m)
        (mq vf (parent_sp s) (parent_ra s) rs m).

Inductive after_external: state -> mach_reply -> state -> Prop :=
  | after_external_intro vf s rs m rs' m':
      after_external (Callstate s vf rs m) (mr rs' m') (Returnstate s rs' m').

Inductive final_state: state -> mach_reply -> Prop :=
  | final_state_intro: forall sp ra s rs m,
      final_state (Returnstate (Stackbase sp ra :: s) rs m) (mr rs m).

Definition semantics (rao: function -> code -> ptrofs -> Prop) (p: program) :=
  Semantics (step rao) initial_state at_external after_external final_state p.

(** * Simulation conventions *)

(** ** CKLR simulation convention *)

Inductive cc_mach_mq R w: mach_query -> mach_query -> Prop :=
  cc_mach_mq_intro vf1 vf2 sp1 sp2 ra1 ra2 rs1 rs2 m1 m2:
    vf1 <> Vundef -> Val.inject (mi R w) vf1 vf2 ->
    sp1 <> Vundef -> Val.inject (mi R w) sp1 sp2 ->
    ra1 <> Vundef -> Val.inject (mi R w) ra1 ra2 ->
    (forall r, Val.inject (mi R w) (rs1 r) (rs2 r)) ->
    match_mem R w m1 m2 ->
    cc_mach_mq R w
      (mq vf1 sp1 ra1 rs1 m1)
      (mq vf2 sp2 ra2 rs2 m2).

Inductive cc_mach_mr R w: mach_reply -> mach_reply -> Prop :=
  cc_mach_mr_intro rs1 rs2 m1 m2:
    (forall r, Val.inject (mi R w) (rs1 r) (rs2 r)) ->
    match_mem R w m1 m2 ->
    cc_mach_mr R w (mr rs1 m1) (mr rs2 m2).

Program Definition cc_mach R: callconv li_mach li_mach :=
  {|
    match_senv := match_stbls R;
    match_query := cc_mach_mq R;
    match_reply := (<> cc_mach_mr R)%klr;
  |}.
Next Obligation.
  eapply match_stbls_proj in H. eapply Genv.mge_public; eauto.
Qed.
Next Obligation.
  eapply match_stbls_proj in H. erewrite <- Genv.valid_for_match; eauto.
Qed.

(** ** Calling convention from [li_locset] *)

(** A key aspect concerns the encoding of arguments in the memory.
  Arguments may be found in assembly stack frames, but the source
  program must not have access to them. So we assert that the source
  memory is equal to the target memory, but in the source the
  permissions for the stack's arguments area has been removed. *)

Require Import Stacklayout.

(** One complication occurs for compatibility with CKLRs. When the
  arguments region is non-empty, success of the source-level
  [Mem.free] ensures that the corresponding pointer [sp + fe_ofs_arg]
  is valid, hence injects into the target-level one. But if the
  argument region is empty, we do not have a similar guarantee.
  For example, for the initial invocation of [main()] with empty
  arguments, the stack pointer is not even of the form [Vptr b ofs]
  but is instead a zero integer.

  In addition to addressing this, we must make sure that accesses to
  the arguments region formulated in terms of concrete binary pointers
  correspond to the range freed in terms of abstract integer addresses.

  This is handled by the following construction. *)

Require Import Separation.
Local Open Scope sep_scope.

Definition offset_sarg sofs ofs :=
  Ptrofs.unsigned (Ptrofs.add sofs (Ptrofs.repr fe_ofs_arg)) + 4 * ofs.

Definition offset_fits sofs ofs :=
  offset_sarg sofs ofs =
  Ptrofs.unsigned (Ptrofs.add sofs (Ptrofs.repr (fe_ofs_arg + 4 * ofs))).

(*
  ofs >= 0 /\ offset_sarg sofs ofs <= Ptrofs.max_unsigned.
*)

Lemma access_fits sofs ofs:
  offset_fits sofs ofs ->
  offset_sarg sofs ofs =
  Ptrofs.unsigned (Ptrofs.add sofs (Ptrofs.repr (fe_ofs_arg + 4 * ofs))).
Proof.
  auto.
(*
  unfold offset_fits, offset_sarg.
  set (base := Ptrofs.unsigned _).
  eassert (0 <= base <= _) by eapply Ptrofs.unsigned_range_2.
  intros [OPOS FITS].
  rewrite add_repr, <- Ptrofs.add_assoc.
  rewrite Ptrofs.add_unsigned.
  rewrite (Ptrofs.unsigned_repr (4 * ofs)) by extlia. fold base.
  rewrite Ptrofs.unsigned_repr by extlia.
  reflexivity.
*)
Qed.


Inductive loc_init_args sz : val -> block -> Z -> Prop :=
  loc_init_args_intro sb sofs ofs:
    offset_sarg sofs 0 <= ofs < offset_sarg sofs sz ->
    loc_init_args sz (Vptr sb sofs) sb ofs.

Program Definition contains_init_args sg j ls m0 sp : massert :=
  let sz := size_arguments sg in
  {|
    m_pred m :=
      Mem.unchanged_on (loc_init_args sz sp) m0 m /\
      (sz > 0 -> exists sb sofs, sp = Vptr sb sofs /\
         Mem.range_perm m sb (offset_sarg sofs 0) (offset_sarg sofs sz) Cur Freeable /\
         forall ofs, 0 <= ofs < sz -> offset_fits sofs ofs) /\
      (forall ofs ty,
          In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) ->
          exists v,
            load_stack m sp ty (Ptrofs.repr (fe_ofs_arg + 4 * ofs)) = Some v /\
            Val.inject j (ls (S Outgoing ofs ty)) v);
    m_footprint := loc_init_args sz sp;
  |}.
Next Obligation.
  repeat apply conj.
  - eapply Mem.unchanged_on_trans; eauto.
  - intros Hsz. edestruct H1 as (sb & sofs & Hsp & PERM & FITS); eauto.
    exists sb, sofs. intuition auto.
    intros ofs Hofs. erewrite <- Mem.unchanged_on_perm; eauto.
    + subst. constructor; auto.
    + eapply Mem.perm_valid_block; eauto.
  - intros ofs ty REG. edestruct H2 as (? & ? & ?); eauto.
    destruct sp as [ | | | | | sb sofs]; eauto.
    pose proof (loc_arguments_bounded _ _ _ REG).
    pose proof (loc_arguments_acceptable_2 _ _ REG) as [? _].
    pose proof (typesize_pos ty).
    eexists; split; eauto.
    edestruct H1 as (sb' & sofs' & Hsp & PERM & FITS). extlia. inv Hsp.
    eapply Mem.load_unchanged_on; eauto. intros. constructor.
    rewrite <- access_fits in H8 by (apply FITS; extlia). unfold offset_sarg in *.
    destruct ty; cbn [typesize size_chunk chunk_of_type] in *; extlia.
Qed.
Next Obligation.
  destruct H0.
  edestruct H1 as (sb' & sofs' & Hsp & PERM & FITS); eauto.
  + unfold offset_sarg in *. extlia.
  + inv Hsp. eapply Mem.perm_valid_block; eauto.
Qed.

Record cc_stacking_world {R} :=
  stkw {
    stk_w :> world R;
    stk_sg : signature;
    stk_ls1 : Locmap.t;
    stk_sp2 : val;
    stk_m2 : mem;
  }.

Arguments cc_stacking_world : clear implicits.

Inductive cc_stacking_mq R: cc_stacking_world R -> _ -> _ -> Prop :=
  | cc_stacking_mq_intro w vf1 vf2 sg ls1 m1 sp2 ra2 rs2 m2:
      vf1 <> Vundef -> Val.inject (mi R w) vf1 vf2 ->
      (forall r, Val.inject (mi R w) (ls1 (Locations.R r)) (rs2 r)) ->
      m2 |= contains_init_args sg (mi R w) ls1 m2 sp2 ->
      match_mem R w m1 m2 ->
      (forall b ofs, loc_init_args (size_arguments sg) sp2 b ofs ->
                     loc_out_of_reach (mi R w) m1 b ofs) ->
      Val.has_type sp2 Tptr ->
      Val.has_type ra2 Tptr ->
      cc_stacking_mq R
        (stkw R w sg ls1 sp2 m2)
        (lq vf1 sg ls1 m1)
        (mq vf2 sp2 ra2 rs2 m2).

Inductive cc_stacking_mr R: cc_stacking_world R -> _ -> _ -> Prop :=
  | cc_stacking_mr_intro w w' sg ls1 ls1' m1' sp2 m2 rs2' m2':
    w ~> w' ->
    (forall r,
      In r (regs_of_rpair (loc_result sg)) ->
      Val.inject (mi R w') (ls1' (Locations.R r)) (rs2' r)) ->
    (forall r,
      is_callee_save r = true ->
      Val.inject (mi R w') (ls1 (Locations.R r)) (rs2' r)) ->
    match_mem R w' m1' m2' ->
    Mem.unchanged_on (loc_init_args (size_arguments sg) sp2) m2 m2' ->
    (forall b ofs, loc_init_args (size_arguments sg) sp2 b ofs ->
                   loc_out_of_reach (mi R w') m1' b ofs) ->
    cc_stacking_mr R
      (stkw R w sg ls1 sp2 m2)
      (lr ls1' m1')
      (mr rs2' m2').

Program Definition cc_stacking R: callconv li_locset li_mach :=
  {|
    match_senv := (match_stbls R @@ [stk_w])%klr;
    match_query := cc_stacking_mq R;
    match_reply := cc_stacking_mr R;
  |}.
Next Obligation.
  eapply (LanguageInterface.cc_c_obligation_1 R w se1 se2 H); eauto.
Qed.
Next Obligation.
  eapply (LanguageInterface.cc_c_obligation_2 R w se1 se2 sk H); eauto.
Qed.

(** ** To relocate or remove *)

(** The [valid_blockv] predicate is used to characterize the initial
  value [mq_sp] for the stack pointer. In order to maintain the
  invariant that each new stack frame has a different stack pointer,
  we need to know in particular that the initial stack pointers refers
  to a valid block, so that any block allocated for new stack frames
  will be different.

  This version of [valid_blockv] forces the value to be both defined,
  and a [Vptr] value. We may want to switch back to a characterization
  where non-pointer values are allowed as well, so that [Vnullptr]
  qualifies. [Vnullptr] which is a [Vint]/[Vlong] null value used in
  the original Compcert semantics as the initial stack pointer. *)

Inductive valid_blockv (s: sup): val -> Prop :=
  | valid_blockv_intro b ofs:
      sup_In b s ->
      valid_blockv s (Vptr b ofs).

Lemma valid_blockv_support s s' v:
  valid_blockv s v ->
  Mem.sup_include s s' ->
  valid_blockv s' v.
Proof.
  destruct 1. constructor.
  unfold Mem.valid_block in *. eauto.
Qed.

(** * Leaf functions *)

(** A leaf function is a function that contains no [Mcall] instruction. *)

Definition is_leaf_function (f: function) : bool :=
  List.forallb
    (fun i => match i with Mcall _ _ => false | _ => true end)
    f.(fn_code).  

(** Semantic characterization of leaf functions: 
    functions in the call stack are never leaf functions. *)

Section WF_STATES.

Variable rao: function -> code -> ptrofs -> Prop.

Variable ge: genv.

Inductive wf_frame: stackframe -> Prop :=
  | wf_stackframe_intro: forall vf sp ra c f
        (CODE: Genv.find_funct ge vf = Some (Internal f))
        (LEAF: is_leaf_function f = false)
        (TAIL: is_tail c f.(fn_code)),
      wf_frame (Stackframe vf sp ra c)
  | wf_parent_intro sp ra:
      wf_frame (Stackbase sp ra).

Inductive wf_state: state -> Prop :=
  | wf_normal_state: forall s vf sp c rs m f
        (STACK: Forall wf_frame s)
        (CODE: Genv.find_funct ge vf = Some (Internal f))
        (TAIL: is_tail c f.(fn_code)),
      wf_state (State s vf sp c rs m)
  | wf_call_state: forall s vf rs m
        (STACK: Forall wf_frame s),
      wf_state (Callstate s vf rs m)
  | wf_return_state: forall s rs m
        (STACK: Forall wf_frame s),
      wf_state (Returnstate s rs m).

Lemma wf_step:
  forall S1 t S2, step rao ge S1 t S2 -> wf_state S1 -> wf_state S2.
Proof.
  induction 1; intros WF; inv WF; try (econstructor; now eauto with coqlib).
- (* call *)
  assert (f0 = f) by congruence. subst f0.
  constructor.
  constructor; auto. econstructor; eauto with coqlib.
  destruct (is_leaf_function f) eqn:E; auto.
  unfold is_leaf_function in E; rewrite forallb_forall in E. 
  symmetry. apply (E (Mcall sig ros)). eapply is_tail_in; eauto.
- (* goto *)
  assert (f0 = f) by congruence. subst f0. econstructor; eauto using find_label_tail.  
- (* cond *)
  assert (f0 = f) by congruence. subst f0. econstructor; eauto using find_label_tail.  
- (* jumptable *)
  assert (f0 = f) by congruence. subst f0. econstructor; eauto using find_label_tail.  
- (* return *)
  inv STACK. inv H1. econstructor; eauto.
Qed.

End WF_STATES.

Lemma wf_initial:
  forall ge q S, initial_state ge q S -> wf_state ge S.
Proof.
  intros. inv H. constructor. constructor.
  constructor. constructor.
Qed.
