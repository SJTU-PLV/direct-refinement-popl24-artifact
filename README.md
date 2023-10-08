# Fully Composable and Adequate Verified Compilation with Direct Refinements between Open Modules (Artifact for POPL 2024)

## Overview 

This artifact consists of our development in the [DirectRefinement](DirectRefinement) 
directory and another directory [CompCertOv3.10](CompCertOv3.10) for comparison. 
The artifact accompanies the following paper:

> [*Fully Composable and Adequate Verified Compilation with Direct Refinements between
Open Modules*](paper/direct-refinement.pdf). Ling Zhang, Yuting Wang, Jinhua Wu, Jeremie
Koenig and Zhong Shao

## List of claims

For the claims made in our paper, please refer to the source files in the 
[DirectRefinement](DirectRefinement) directory.

The simulation convention C in Section 2.2 (line 450) of the paper corresponds to
the definition [cc_c_asm_injp](DirectRefinement/driver/CA.v#L184) in the Coq file
[driver/CA.v](DirectRefinement/driver/CA.v).

Lemma 3.1 from Section3.2.1 (line 708) of the paper corresponds to the theorem
[injp_injp2](DirectRefinement/cklr/InjectFootprint.v#L2481) in the Coq file
[cklr/InjectFootprint.v](DirectRefinement/cklr/InjectFootprint.v). Lemma 3.2 from
Section3.2.2 (line 763) corresponds to the theorem 
[injp_injp](DirectRefinement/cklr/InjectFootprint.v#L472) in the same file.

Lemma 4.1 from Section 4.1.2 (line 861) corresponds to the theorem 
[transf_program_correct](DirectRefinement/backend/Constpropproof.v#1097) in the
Coq file [backend/Constpropproof.v](DirectRefinement/backend/Constpropproof.v).

Definition 4.2 from Section 4.1.2 (line 874) can be found in
[backend/ValueAnalysis.v](DirectRefinement/backend/ValueAnalysis.v#L1939).

Lemma 4.3 from Section 4.2.1 (line 919) corresponds to the instances 
[commut_c_locset](DirectRefinement/driver/CallConv.v#L145), 
[commut_locset_mach](DirectRefinement/driver/CallConv.v#L1091) and 
[commut_mach_asm](DirectRefinement/driver/CallConv.v#L247) in 
[driver/CallConv.v](DirectRefinement/driver/CallConv.v)

For Lemma 4.4 from Section 4.2.2 (line 929), the properties 
[(1)](DirectRefinement/cklr/InjectFootprint.v#L2550) 
[(2)](DirectRefinement/cklr/InjectFootprint.v#L2560)
[(3)](DirectRefinement/cklr/InjectFootprint.v#L2606) can be found in
[cklr/InjectFootprint.v](DirectRefinement/cklr/InjectFootprint.v), property 
[(4)](DirectRefinement/cklr/InjectFootprint.v#L500) can be found in 
[cklr/Inject.v](DirectRefinement/cklr/Inject.v) and properties 
[(5)](DirectRefinement/cklr/Extends.v#L261) 
[(6)](DirectRefinement/cklr/Extends.v#L290) 
[(7)](DirectRefinement/cklr/Extends.v#L237) can be found in 
[cklr/Extends.v](DirectRefinement/cklr/Extends.v).

Lemma 4.5 from Section 4.2.3 (line 946) corresponds to the last 
[theorems](DirectRefinement/driver/CallConv.v#L1920) in 
[driver/CallConv.v](DirectRefinement/driver/CallConv.v). 
Lemma 4.6 (line 950) corresponds to the theorem 
[ro_injp_trans](DirectRefinement/driver/CallConv.v#L1779) in the same file. 
Lemma 4.7 (line 956) is an instantiation of theorems 
[inv_commute](DirectRefinement/common/Invariant.v#L380) and 
[inv_commute_ref](DirectRefinement/common/Invariant.v#L370) in 
[common/Invariant.v](DirectRefinement/common/Invariant.v).

Theorem 4.8 from Section 4.3 (line 963) corresponds to the final theorems
in [cklr/Clightrel.v](DirectRefinement/cklr/Clightrel.v#762), 
[cklr/RTLrel.v](DirectRefinement/cklr/RTLrel.v#L271) and 
[x86/Asmrel.v](DirectRefinement/x86/Asmrel.v#L513).
The direct refinement convention (line 973) is defined as 
[cc_compcert](DirectRefinement/driver/Compiler.v#L399) in the Coq file 
[driver/Compiler.v](DirectRefinement/driver/Compiler.v). 
Theorem 4.9 (line 977) corresponds to the theorem 
[c_semantic_preservation](DirectRefinement/driver/Compiler.v#L842) in the same file.

Definition 5.1 from Section 5.1 (line 1028) is defined in Coq file 
[demo/Serverspec.v](DirectRefinement/demo/Serverspec.v). Theorem 5.2 (line 1058)
corresponds to the theorem 
[semantics_preservation_L2](DirectRefinement/demo/Serverproof.v#L1576) in 
[demo/Serverproof.v](DirectRefinement/demo/Serverproof.v).

Lemma 5.3 from Section 5.2 (line 1087) is defined is the vertical composition of theorems
[top2_ro](DirectRefinement/demo/ClientServercspec2.v#L211), 
[top2_wt](DirectRefinement/demo/ClientServercspec2.v#L234) and 
[top_simulation_L2](DirectRefinement/demo/ClientServercspec2.v#L832) in the Coq file 
[demo/ClientServercspec2.v](DirectRefinement/demo/ClientServercspec2.v).

Theorem 5.4 (line 1097) corresponds to the lemma 
[asm_linking](DirectRefinement/x86/Asmlinking.v#L371) in 
[x86/Asmlinking.v](DirectRefinement/x86/Asmlinking.v).

Lemma 5.5 (line 1101), Lemma 5.6 (line 1107) and Theorem 5.7 (line 1111) correspond to
the theorems [compose_Client_Server_correct2](DirectRefinement/demo/ClientServer.v#L42),
[ro_injp_cc_compcert](DirectRefinement/demo/ClientServer.v#L76) and
[spec_sim_2](DirectRefinement/demo/ClientServer.v#146) in the Coq file 
[demo/ClientServer.v](DirectRefinement/demo/ClientServer.v).

## Installation


###  Requirements

This artifact is based on CompCertO and CompCert v3.10. You can find the user manual of 
CompCert [here](http://compcert.inria.fr/man/).

- If you are using the VM, all the required software have already been installed on the 
virtual machiine.

- If you prefer to compile the source code on your own computer, then
We recommend using the `opam` package manager to set up a build environment. 
We have tested the building on Linux with the following shell commands.
```
    # Initialize opam (if you haven't used it before)
    opam init --bare
    
    # Create an "opam switch" dedicated to building the code
    opam switch create direct-refinement ocaml-base-compiler.4.08.1
    
    # Install the necessary packages
    opam repository add coq-released https://coq.inria.fr/opam/released
    opam install coq.8.9.1 camlp5.7.14 menhir.20201216
    
    # Configure the current shell to use the newly created opam switch
    eval $(opam env)
```
### Instructions for compiling

To compile the source code, please enter the `DirectRefinement` directory.
Our implementation relies on the Coqrel library (repo in
[here](https://github.com/CertiKOS/coqrel/tree/38dd003d28c91b1b93c01a160a31cdbc3348916a)),
which must be built first. To build Coqrel, proceed in the following
way:
```
(cd coqrel && ./configure && make)
```
Then, you can then build the compiler as follows:
```
./configure x86_64-linux
make
```
The compilation should start and terminate successfully. 
If appropriate to your setting, we recommend you use a `-j` option
when invoking make so as to enable parallel compilation.
[TODO:Our test environment and compilation time].

If you want to compile the CompCertOv3.10, the same instructions should
work in the other directory.

### Navigating the proofs

After that, you can navigate the source code by using emacs. For example, running

```
emacs cklr/InjectFootprint.v
```

opens the emacs window in proof-general mode for browsing the file
`cklr/InjectFootprint.v`. The commands for navigating the Coq proof
scripts can be found at 
[here](https://proofgeneral.github.io/doc/master/userman/Introducing-Proof-General/).

You can also compile the source code into html files for better
presentation. Simply run the following command (which needs
`coq2html` which has been installed on the VM)

```
make documentation
```

Then, the html versions of source code can be found at `doc/html`.
Note that the [index page](DirectRefinement/doc/index.html) is provided by CompCertO.

## Evaluation instructions

To check soundness of this artifact, enter `DirectRefinement` and run
```
grep "Admitted" */*.v
```
This instruction should return no result.

### Table 3
The following are the instructions for reproducing the lines of code (LOC) in 
Table 3 (line 2255) of the [technical report](paper/technical-report.pdf).

#### Column 2

The results in the second column can be produced by running the following
command in directories `CompCertOv3.10` and adding the numbers in the `spec` and
`proof` for each file.

```
coqwc lib/Maps.v common/Memory.v cklr/InjectFootprint.v cfrontend/SimplLocalsproof.v backend/ValueAnalysis.v backend/Deadcodeproof.v backend/Constpropproof.v backend/CSEproof.v backend/Unusedglobproof.v driver/CallConv.v driver/Compiler.v
```

The last row of result should be 
```
 // CompCertOv3.10
 6054     9871     1357 total // 15925
```

#### Column 3

The numbers in Column 3 can be obtained in a similar way. Run the following commands 
in `DirectRefinement` for the results except for the examples:
```
coqwc lib/Maps.v common/Memory.v cklr/InjectFootprint.v cfrontend/SimplLocalsproof.v backend/ValueAnalysis.v backend/Deadcodeproof.v backend/Constpropproof.v backend/CSEproof.v backend/Unusedglobproof.v driver/CA.v driver/CallConv.v driver/Compiler.v
```

The last row of result should be 
```
7863    15975     1646 total #23838
```

For the Client-Server example, run
```
coqwc demo/Client.v demo/Server.v demo/Serverspec.v demo/Serverproof.v demo/ClientServerCspec.v demo/ClientServerCspec2.v demo/ClientMR.v demo/ClientServerMRCSpec.v demo/ClientServerMRCSpec2.v demo/ClientServer.v 
```
and add the `spec` and `proof` of the last row.
```
2014     5315      770 total # 7327
```

For the Mutual Sum example, run
```
coqwc demo/Demo.v demo/Demospec.v demo/Demoproof.v demo/DemoCspec.v demo/Demotopspec.v
```
and add the `spec` and `proof` of the last row.
```
880     2248      231 total # 3128
```

Finally we get `23838 + 7327 + 3128 = 34293` for the number in row `Total`.

#### Column 4
The numbers in `Additions(+)` column is the submission of column 3 and colume 2.

## Additional artifact description

This artifact is based on CompCertO v3.10, you can browse the structure and
source code of original CompCert [here](http://compcert.inria.fr/doc/index.html).
Note that we use nominal memory model from Nominal CompCert[1] in our implementation
for future extensions, while our result does not rely on it.

We briefly present the framework of CompCertO as described in Section 2.1. We then demonstrate the key definitions and theorems for building direct refinement (Section 3 and 4). Finally we discuss the examples of end-to-end verification using direct refinement (Section 5).

For CompCert's block-based memory model (Section 2.1.1), see 
[common/Values.v](DirectRefinement/common/Values.v) and
[common/Memory.v](DirectRefinement/common/Memory.v).

### CompCertO

#### Open semantics 
The `language interface` is defined in [common/LanguageInterface.v](DirectRefinement/common/LanguageInterface.v) together with the C level interface `li_c`:
```
Structure language_interface :=
  mk_language_interface {
    query: Type;
    reply: Type;
    entry: query -> val;
  }.


Record c_query :=
  cq {
    cq_vf: val;
    cq_sg: signature;
    cq_args: list val;
    cq_mem: mem;
  }.

Record c_reply :=
  cr {
    cr_retval: val;
    cr_mem: mem;
  }.

Canonical Structure li_c :=
  {|
    query := c_query;
    reply := c_reply;
    entry := cq_vf;
  |}.

```

`Open semantics` is essentially a mapping from global 
symbol table to open LTSand a skeleton
of local definitions as defined in 
[common/Smallstep.v](DirectRefinement/common/Smallstep.v):
```
Record lts liA liB state: Type := {
  genvtype: Type;
  step : genvtype -> state -> trace -> state -> Prop;
  valid_query: query liB -> bool;
  initial_state: query liB -> state -> Prop;
  at_external: state -> query liA -> Prop;
  after_external: state -> reply liA -> state -> Prop;
  final_state: state -> reply liB -> Prop;
  globalenv: genvtype;
}.

Record semantics liA liB := {
  skel: AST.program unit unit;
  state: Type;
  activate :> Genv.symtbl -> lts liA liB state;
}.
```
#### Simulation Convention and CKLR

The Kripke relation is defined in [coqrel/KLR.v](DirectRefinement/coqrel/KLR.v):
```
Definition klr W A B: Type :=
  W -> rel A B.
```

The `simulation convention` between interfaces is also defined in [common/LanguageInterface.v](DirectRefinement/common/LanguageInterface.v) with the C-level convention `cc_c`. The `match_senv` matches the global symbol tables of source and target semantics, which is elided in the paper for simplicity:
```
Record callconv {li1 li2} :=
  mk_callconv {
    ccworld : Type;
    match_senv: ccworld -> Genv.symtbl -> Genv.symtbl -> Prop;
    match_query: ccworld -> query li1 -> query li2 -> Prop;
    match_reply: ccworld -> reply li1 -> reply li2 -> Prop;

    ...
  }.

  Program Definition cc_c (R: cklr): callconv li_c li_c :=
  {|
    ccworld := world R;
    match_senv := match_stbls R;
    match_query := cc_c_query R;
    match_reply := (<> cc_c_reply R)%klr;
  |}.
```

Here `cklr` corresponds to the *Kripke Memory Relation* (Definition 2.1) mentioned in the paper (line 411). It is defined in [cklr/CKLR.v](DirectRefinement/cklr/CKLR.v). Different memory relations
 and their properties are in the [cklr](DirectRefinment/cklr) directory.

The symbol `<>` in `match_reply` indicates that there exists an accessibility relation of worlds from queries to replies. See the discussion in line 395-407 of the paper.

#### Open simulation
The `open simulation` and the `vertical composition` are defined in [common/Smallstep.v](DirectRefinement/common/Smallstep.v):
```
  Record fsim_properties (L1: lts liA1 liB1 state1) (L2: lts liA2 liB2 state2) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> state1 -> state2 -> Prop) : Prop := {
    ...
    fsim_match_initial_states:
      forall q1 q2 s1, match_query ccB wB q1 q2 -> initial_state L1 q1 s1 ->
      exists i, exists s2, initial_state L2 q2 s2 /\ match_states i s1 s2;
    ...
  }.

  Record fsim_components {liA1 liA2} (ccA: callconv liA1 liA2) {liB1  liB2} ccB L1 L2 :=
    Forward_simulation {
    ...
    fsim_skel:
      skel L1 = skel L2;
    fsim_lts se1 se2 wB:
      @match_senv liB1 liB2 ccB wB se1 se2 ->
      Genv.valid_for (skel L1) se1 ->
      fsim_properties ccA ccB se1 se2 wB (activate L1 se1) (activate L2 se2)
        fsim_index fsim_order (fsim_match_states se1 se2 wB);
    ...
  }.
  Definition forward_simulation {liA1 liA2} ccA {liB1 liB2} ccB L1 L2 :=
  inhabited (@fsim_components liA1 liA2 ccA liB1 liB2 ccB L1 L2).

  Lemma compose_fsim_components:
  fsim_components ccA12 ccB12 L1 L2 ->
  fsim_components ccA23 ccB23 L2 L3 ->
  fsim_components (ccA12 @ ccA23) (ccB12 @ ccB23) L1 L3.

    
```
The horizontal composition is defined in [common/SmallstepLinking.v](DirectRefinement/common/SmallstepLinking.v):
```
Lemma compose_simulation {li1 li2} (cc: callconv li1 li2) L1a L1b L1 L2a L2b L2:
  forward_simulation cc cc L1a L2a ->
  forward_simulation cc cc L1b L2b ->
  compose L1a L1b = Some L1 ->
  compose L2a L2b = Some L2 ->
  forward_simulation cc cc L1 L2.

```
The refinement of simulation conventions `ccref` and Theorem 2.4 from the Section 2.4 
(line 580) are defined in 
[common/CallconvAlgebra.v](DirectRefinement/common/CallconvAlgebra.v):
```
Definition ccref {li1 li2} (cc cc': callconv li1 li2) :=
  forall w se1 se2 q1 q2,
    match_senv cc w se1 se2 ->
    match_query cc w q1 q2 ->
    exists w',
      match_senv cc' w' se1 se2 /\
      match_query cc' w' q1 q2 /\
      forall r1 r2,
        match_reply cc' w' r1 r2 ->
        match_reply cc w r1 r2.
		
Definition cceqv {li1 li2} (cc cc': callconv li1 li2) :=
  ccref cc cc' /\ ccref cc' cc.

Global Instance open_fsim_ccref:
  Monotonic
    (@forward_simulation)
    (forallr - @ liA1, forallr - @ liA2, ccref ++>
     forallr - @ liB1, forallr - @ liB2, ccref -->
     subrel).
```


You can refer the [CompCertO documentation page](DirectRefinement/doc/index.html) for further detailed description of CompCertO implementation.

### `injp` and its transitivity (Section 3)

The dinifition of `injp` (Definition 2.2, line 417) can be found in
[cklr/InjectFootprint.v](DirectRefinement/cklr/InjectFootprint.v):

```

Program Definition injp: cklr :=
  {|
    world := injp_world;
    wacc := injp_acc;
    mi := injp_mi;
    match_mem := injp_match_mem;
    match_stbls := injp_match_stbls;
  |}.
  
Inductive injp_acc: relation injp_world :=
  injp_acc_intro f m1 m2 Hm f' m1' m2' Hm':
    Mem.ro_unchanged m1 m1' -> Mem.ro_unchanged m2 m2' ->
    injp_max_perm_decrease m1 m1' ->
    injp_max_perm_decrease m2 m2' ->
    Mem.unchanged_on (loc_unmapped f) m1 m1' ->
    Mem.unchanged_on (loc_out_of_reach f m1) m2 m2' ->
    inject_incr f f' ->
    inject_separated f f' m1 m2 ->
    injp_acc (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm').
  
```

Note that `mem-acc m1 m1'` mentioned in the paper (ling 422) corresponds to the 
`ro_acc` defined in [backend/ValueAnalysis.v](DirectRefinement/backend/ValueAnalysis.v):
```
Inductive ro_acc : mem -> mem -> Prop :=
| ro_acc_intro m1 m2:
  Mem.ro_unchanged m1 m2 ->
  Mem.sup_include (Mem.support m1) (Mem.support m2) ->
  injp_max_perm_decrease m1 m2 ->
  ro_acc m1 m2.
                  
```
These properties of memory accessibility is defined by vanilla CompCert in 
[common/Events.v](DirectRefinement/common/Events.v) as `ec_readonly`, `ec_valid_block`
and `ec_perm` for external calls. We use it as a preorder relation for both internal
and external executions.
`Mem_sup_include (Mem.support m1) (Mem.support m2)` means that `m2` have more
valid blocks than `m1`. It is included in `Mem.unchanged_on P m1 m2` which is defined
in [common/Memory.v](DirectRefinement/common/Memory.v):
```
Record unchanged_on (m_before m_after: mem) : Prop := mk_unchanged_on {
  unchanged_on_support:
    sup_include (support m_before) (support m_after);
  unchanged_on_perm:
    forall b ofs k p,
    P b ofs -> valid_block m_before b ->
    (perm m_before b ofs k p <-> perm m_after b ofs k p);
  unchanged_on_contents:
    forall b ofs,
    P b ofs -> perm m_before b ofs Cur Readable ->
    ZMap.get ofs (NMap.get _ b m_after.(mem_contents)) =
    ZMap.get ofs (NMap.get _ b m_before.(mem_contents))
}.

```

The proof of `injp` transivity in 
[cklr/InjectFootprint.v](DirectRefinement/cklr/InjectFootprint.v) is commented according
to the appendix C of our [technical report](paper/technical-report.pdf).
The refinements (Lemma 3.1 and Lemma 3.2) correspond to the following lemmas:
```
Lemma injp_injp2:
  subcklr (injp @ injp) injp.
  
Lemma injp_injp:
  subcklr injp (injp @ injp).
```

Here we briefly persent the construction of intermediate memory state
(as discussed in the paper line 738-753) as following steps. 
We first construct the injections and shape of `m2'`:
```
Fixpoint update_meminj12 (sd1': list block) (j1 j2 j': meminj) (si1: sup) :=
  match sd1' with
    |nil => (j1,j2,si1)
    |hd::tl =>
       match compose_meminj j1 j2 hd, (j' hd) with
       | None , Some (b2,ofs) =>
         let b0 := fresh_block si1 in
         update_meminj12 tl (meminj_add j1 hd (b0,0) )
                         (meminj_add j2 (fresh_block si1) (b2,ofs))
                         j' (sup_incr si1)
       | _,_ => update_meminj12 tl j1 j2 j' si1
       end
  end.
```

We then copy the values and permissions for newly allocated blocks as:

```
Definition m2'1 := Mem.step2 m1 m2 m1' s2' j1'.
```
Finally we update the values and permissions for old blocks according whether they
are protected or read-only using:

```
Definition m2' := Mem.copy_sup m1 m2 m1' j1 j2 j1' INJ12 (Mem.support m2) m2'1.
```

These memory operations are defined in [common/Memory.v](DirectRefinement/common/Memory.v).
For these operations, we changed the type of `mem_access` to be the same structure as
`mem_contents` in order to enumerate the valid (with nonempty permissions)
locations of a memory block.
```
# Our implementation
Record mem' : Type := mkmem {
  mem_contents: NMap.t (ZMap.t memval);
  mem_access: NMap.t (ZMap.t memperm);
  ...
}

# CompCertO v3.10
Record mem' : Type := mkmem {
  mem_contents: NMap.t (ZMap.t memval);
  mem_access: NMap.t (Z -> perm_kind -> option permission);
  ... 
}

```

### Derivation of direct Refinement (Section 4)

#### Proofs of individual passes

Table 1 can be checked accoding to `CompCertO's passes` in 
[driver/Compiler.v](DirectRefinement/driver/Compiler.v). 
The definitions used in the table from CompCertO can be found as follows.
The simulation conventions relate the same language interfaces 
`cc_c`, `cc_locset`, `cc_mach` and `cc_asm` (line 813) are defined in 
in [common/Languageinterface.v](DirectRefinement/common/LanguageInterface.v),
[backend/Conventions](DirectRefinement/backend/Conventions.v),
[backend/Mach.v](DirectRefinement/backend/Mach.v) and
[x86/Asm.v](DirectRefinement/x86/Asm.v).
The structure simulation conventions `cc_c_locset`, `cc_locset_mach` and
`cc_mach_asm` (line 823) are defined in 
[backend/Conventions](DirectRefinement/backend/Conventions.v),
[driver/CallConv.v](DirectRefinement/driver/CallConv.v) and
[x86/Asm.v](DirectRefinement/x86/Asm.v). The definition of semantic invariant
and `wt` are in [common/Invariant.v](DirectRefinement/common/Invairant.v):

```
Record invariant {li: language_interface} :=
  {
    inv_world : Type;
    symtbl_inv : inv_world -> Genv.symtbl -> Prop;
    query_inv : inv_world -> query li -> Prop;
    reply_inv : inv_world -> reply li -> Prop;
  }.

Definition wt_c : invariant li_c :=
  {|
    symtbl_inv :=
      fun '(se, sg) => eq se;
    query_inv :=
      fun '(se, sg) q =>
        sg = cq_sg q /\ Val.has_type_list (cq_args q) (sig_args sg);
    reply_inv :=
      fun '(se, sg) r =>
        Val.has_type (cr_retval r) (proj_sig_res sg);
  |}.

```

For the passes using static analysis, we define the invariant `ro` in
[backend/ValueAnalysis.v](DirectRefinement/backend/ValueAnalysis.v):
```

Inductive sound_query ge m: c_query -> Prop :=
  sound_query_intro vf sg vargs:
    sound_memory_ro ge m ->
    sound_query ge m (cq vf sg vargs m).

Inductive sound_reply m: c_reply -> Prop :=
  sound_reply_intro res tm:
    ro_acc m tm ->
    sound_reply m (cr res tm).

Definition ro : invariant li_c :=
  {|
    symtbl_inv '(row ge m) := eq ge;
    query_inv '(row ge m) := sound_query ge m;
    reply_inv '(row ge m) := sound_reply m;
  |}.

```

The proof which uses `injp` to guarantee the dynamic values of
unreachable local variables (Fig. 14) is carried out in the lemma
 `transf_external_states` in 
[backend/Constpropproof.v](DirectRefinement/bakend/Constpropproof.v).


For [Unusedglob](DirectRefinement/backend/Unusedglobproof.v) pass,
we assume that the global symbol table are the same for source and target
semantics. While some local static definitions are removed. 

Moreover, We use `injp` in the incoming simulation convention in
[cfrontend/SimplLocalsproof.v](DirectRefinement/cfrontend/SimplLocalsproof.v)
as an example to show that `injp` is a reasonable guarantee condition. 
The proofs of remaining passes are unchanged from CompCertO.

#### Unification of the simulation conventions

We have mentioned the corresponding theorems of lemmas in Section 4.2 in the
`List of claims` part. The direct simulation convention $\mathcal{C}$ (line 973)
is defined as `cc_compcert` in [driver/Compiler.v](DirectRefinement/driver/Compiler.v):
```
Definition cc_compcert : callconv li_c li_asm :=
       ro @ wt_c @
       cc_c_asm_injp @
       cc_asm injp.
```

Where `cc_c_asm_injp` (`CAinjp` in the paper) is defined in 
[driver/CA.v](DirectRefinement/driver/CA.v). The proof of merging
`c_injp`, `CL`, `LM` and `MA` into `CAinjp` is also here:

```
Lemma ca_cllmma_equiv :
  cceqv cc_c_asm (cc_c_locset @ cc_locset_mach @ cc_mach_asm).

Lemma cainjp__injp_ca_equiv:
  cceqv cc_c_asm_injp (cc_c injp @ cc_c_asm).
  
```

The unification of simulation convention in 
[driver/Compiler.v](DirectRefinement/driver/Compiler.v) is slightly different
as we presented in the paper. Take the incoming side for example.
We first define extend `cc_compcert` to `cc_compcert_cod` as follows:
```
Definition cc_compcert_cod : callconv li_c li_asm :=
  ro @ wt_c @ cc_c injp @
       cc_c_locset @ cc_locset_mach @ cc_mach_asm @
       @ cc_asm inj.
	   
Theorem cc_compcert_merge:
  forall p tp,
  forward_simulation cc_compcert_dom cc_compcert_cod (Clight.semantics1 p) (Asm.semantics tp) ->
  forward_simulation cc_compcert cc_compcert (Clight.semantics1 p) (Asm.semantics tp).
  
```
Then we define the simulation convention `cc_c_level` for C level and further extend
`cc_compcert_cod` to satisfy the passes after C level:
```
Definition cc_c_level : callconv li_c li_c := ro @ wt_c @ injp.

Lemma cc_compcert_expand:
  ccref
    cc_compcert_cod
    (cc_c_level @                                          (* Passes up to Alloc *)
     cc_c inj @                                            (* to compose the ext downside*)
     (wt_c @ cc_c ext @ cc_c_locset) @                     (* Alloc *)
     cc_locset ext @                                       (* Tunneling *)
     (wt_loc @ cc_locset_mach @ cc_mach inj) @             (* Stacking *)
     (cc_mach ext @ cc_mach_asm) @                         (* Asmgen *)
     cc_asm inj).

```
Finally we expend `cc_c_level` to satisfy the passes at C level:
```
Lemma cc_c_level_expand:
  ccref cc_c_level
        ( ro @ cc_c injp @ 
              cc_c inj@
              (wt_c @ cc_c ext) @ cc_c ext @
              cc_c inj @
              cc_c ext @ cc_c inj @ cc_c injp @
              (ro @ injp) @ (ro @ injp) @ (ro @ injp)).
```
Therefore the simulation conventions can be unificated into our direct simulation 
convention as proved in theorem `clight_semantics_preservation`:
```
Theorem clight_semantic_preservation:
  forall p tp,
  match_prog p tp ->
  forward_simulation cc_compcert cc_compcert (Clight.semantics1 p) (Asm.semantics tp)
  /\ backward_simulation cc_compcert cc_compcert (Clight.semantics1 p) (Asm.semantics tp).
```

### Section 5: End-to-End Verification of Heterogenous Modules

In the section 5 of the paper, we introduce the end-to-end
verification of the client-server example (whose code and proof
structure are shown in Figure 3 and Figure 4, respectively) based on
the direct refinement. 

#### Definitions of the Client-Server Example

The C or assembly code of `client.c`, `server.s` and `server_opt.s`
are shown in Figure 3 in our paper.

* `client.c` is defined in [Client.v](demo/Client.v).
* `server.s` and `server_opt.s` are defined in [Server.v](demo/Server.v).

#### Refinement for the Hand-written Server (Section 5.1)

* (Definition 5.1) The hand-written specification ($L_S$) for the
  optimized server (i.e., `server_opt.s`) is defined by `L2` in [Serverspec.v](demo/Serverspec.v#L116). The hand-written specification (not
  discussed in the paper) for `server.s` is defined by `L1` in [Serverspec.v](demo/Serverspec.v#L98).
* (Theorem 5.2) The theorem of $L_S
  \leqslant_{\mathbb{C}}[\![\texttt{server\_opt.s}]\!]$ is defined by
  `semantics_preservation_L2` in [Serverproof.v](demo/Serverproof.v).
  This proof is decomposed into  $L_S \leqslant_{\texttt{wt}} L_S$ and
  $L_S \leqslant_{\texttt{ro}\cdot\texttt{CAinjp}}
  [\![\texttt{server\_opt.s}]\!]$, which are stated in
  `self_simulation_wt'` and `CAinjp_simulation_L2`, respectively. More specifically, for the verification of $L_S \leqslant_{\texttt{ro}\cdot\texttt{CAinjp}} [\![\texttt{server\_opt.s}]\!]$, the simulation relation is defined by `match_state_c_asm` in [Serverproof.v](demo/Serverproof.v).

#### End-to-End Correctness Theorem (Section 5.2)

* Definition of the top-level specification (optimized version) $L_{\texttt{CS}}$ is by `top_spec2` in [ClientServerCspec2.v](demo/ClientServerCspec2.v). The unoptimized top-level specification is defined by `top_spec1` in [ClientServerCspec1.v](demo/ClientServerCspec2.v).
* (Lemma 5.3) $L_{\texttt{CS}} \leqslant_{\texttt{ro}\cdot\texttt{wt}\cdot \texttt{c}_{\texttt{injp}}} [\![\texttt{client.c}]\!] \oplus L_S$ is defined by `top_simulation_L2` in [ClientServerCspec2.v](demo/ClientServerCspec2.v). The simulation relation is defined by `match_state` in the same file. Note that `top_simulation_L1` is the refinement theorem for the unoptimized server, i.e., $L_S$ and $L_{\texttt{CS}}$ in $L_{\texttt{CS}} \leqslant_{\texttt{ro}\cdot\texttt{wt}\cdot \texttt{c}_{\texttt{injp}}} [\![\texttt{client.c}]\!] \oplus L_S$ are replaced by `L1` and `top_spec1`, respectively.
* (Theorem 5.4) `compose_simulation` in [Smallstep.v](common/Smallstep.v) and `asm_linking` in [AsmLinking.v](x86/AsmLinking.v).
* (Lemma 5.5) `compose_Client_Server_correct2` in [ClientServer.v](demo/ClientServer.v).
* (Lemma 5.6) `ro_injp_cc_compcert` in [ClientServer.v](demo/ClientServer.v).
* (Theorem 5.7) `spec_sim_2` in [ClientServer.v](demo/ClientServer.v).
  
#### Other Examples

The following examples are not discussed in our paper, because they
are more complicated than the client-server example introduced in our
paper. However, we implement and verify them to show the effectiveness of our framework.

##### Mutual Recursive Client-Server Example

We define a mutual recursive client-server example where the server
code is the same as `server.s` in [Server.v](demo/Server.v) and the
client code can repeatedly invoke the server to encrypt a list of
data. The C code of the new client (denoted by `client_mr.c`) is shown
below:

```c
/* client_mr.c */
int input[N], result[N];
int index;

void request (int *r){
  if (index == 0) {
    index += 1;
    encrypt(input[index - 1], request);
  }
  else if (0 < index < N){
    result[index - 1] = *r;
    index += 1;
    encrypt(input[index - 1], request);
  }
  else {
    result[index - 1] = *r;
    return;
  }
}
```

* `client_mr.c` is defined by the Coq definition `client` in
  [ClientMR.v](demo/ClientMR.v).
* The definition of server is the same as the example (`server.s`)
  introduced in our paper, i.e., it is defined by  `L1` in
  [Server.v](demo/Server.v). Note that we implement the repeated
  invocation by directly passing the `request` function in `client` to
  the server. Thereby the server can jump to the call-back function
  (the `request` function in client) to encrypt the subsequent data.
* The top level specification is defined by `top_spec1` in
  [ClientServerMRCSpec.v](demo/ClientServerMRCSpec.v).
* The refinement $\texttt{top\_spec1} \leqslant_{\texttt{ro}\cdot\texttt{wt}\cdot \texttt{c}_{\texttt{injp}}} [\![\texttt{client\_mr.c}]\!] \oplus \texttt{L1}$ is defined by `top_simulation_L1`, `top1_ro` and `top1_wt` in [ClientServerMRCspec.v](demo/ClientServerMRCSpec.v).
* The final theorem $\texttt{top\_spec1} \leqslant_{\mathbb{C}} [\![\texttt{CompCert}(\texttt{client\_mr.c}) + \texttt{server.s}]\!]$ is defined by `spec_sim_mr` in [ClientServer.v](demo/ClientServer.v).

##### Mutual Summation Example

We present the application of our method to an example borrowed from
CompCertM[^1] — two programs that mutually invoke each other to finish
a summation task. One program (denoted by `M_C`) is implemented in C
and the other (denoted by `M_A`) is implemented in assembly. Their code are shown below:

```C {.line-numbers}
/* C implementation of M_C */
  static int memoized[1000] = {0};
  int f(int i) {
    int sum;
    if (i == 0) return 0;
    sum = memoized[i];
    if (sum == 0) 
    { sum = g(i-1) + i;
      memoized[i] = sum; }
    return sum;
  }
  /* C code corresponding to M_A */
  static int s[2] = {0,0};
  int g(int i){
    int sum;
    if (i == 0) return 0;
    if (i == s[0]) 
      { sum = s[1]; } 
    else 
      { sum = f(i-1) + i;
        s[0] = i;
        s[1] = sum; }
    return sum;
  }
```

```x86asm
/* Assembly implementation of M_A */  
g:  Pallocframe 24 16 0 
    Pmov RBX 8(RSP) // save RBX
    /* begin */
    Pmov RDI RBX 
    Ptestl RBX RBX  // i==0
    Pjne l0  
    Pxorl_r RAX     // rv=0
    Pjmp l1
l0: Pmov s[0] RAX 
    Pcmpl RAX RBX  // i==s[0]
    Pje l2
    Pleal -1(RBX) RDI 
    Pcall f        // f(i-1)
    Pleal (RAX,RBX) RAX//sum=f(i-1)+i
    Pmov RBX s[0]  // s[0] = i
    Pmov RAX s[1]  // s[1] = sum
    Pjmp l1 
l2: Pmov s[1] RAX  // rv=s[1]
    /* return */
l1: Pmov 8(RSP) RBX 
    Pfreeframe 24 16 0 
    Pret
```

The procedure of the refinement is shown below:
* First, like what we do for the server in the above example, we define a high-level specification (called `L_A`) for `M_A`. The definition of `L_A` is in [Demospec.v](demo/Demospec.v) with the same name. The refinement $\texttt{L\_A} \leqslant_\mathbb{C} [\![\texttt{M\_A}]\!]$ is defined by `M_A_semantics_preservation` in [Demoproof](demo/Demoproof.v). The simulation relation of this proof is defined by `match_state_c_asm` in the same file.
* Second, for `M_C`, we also define a specification `L_C` and show that $\texttt{L\_C} \leqslant_{\texttt{ro}\cdot\texttt{wt}\cdot \texttt{c}_{\texttt{injp}}}[\![\texttt{M\_C}]\!]$. `L_C` is defined by `L_C` in [DemoCspec.v](demo/DemoCspec.v) and the refinement is defined by `cspec_simulation`, `cspec_ro` and `cspec_self_simulation_wt` in [DemoCspec.v](demo/DemoCspec.v).
* With the above definitions, we define a top-level specification called `top_spec` in [Demotopspec.v](demo/Demotopspec.v). We prove that $\texttt{top\_spec}  \leqslant_{\texttt{ro}\cdot\texttt{wt}\cdot \texttt{c}_{\texttt{injp}}} \texttt{L\_C} \oplus \texttt{L\_A}$ in [Demotopspec.v](demo/Demotopspec.v) by `top_simulation`, `top_ro` and `topspec_self_simulation_wt`.
* Finally, with the above refinements and the correctness of CompCert(O), we show $\texttt{top\_spec} \leqslant_\mathbb{C} \texttt{CompCert}(\texttt{M\_C}) \oplus [\![\texttt{M\_A}]\!]$ in `topspec_correct` in [Demotopspec.v](demo/Demotopspec.v).

## Reference

[^1]: Youngju Song, Minki Cho, Dongjoo Kim, Yonghyun Kim, Jeehoon Kang, and Chung-Kil Hur. 2020. CompCertM: CompCert with C-Assembly Linking and Lightweight Modular Verification. Proc. ACM Program. Lang. 4, POPL, Article 23 (Jan. 2020),31pages. https://doi.org/10.1145/3371091
