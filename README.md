# Fully Composable and Adequate Verified Compilation with Direct Refinements between Open Modules (Artifact for POPL 2024)

## 1. Overview 

This artifact contains an extension of CompCertO that provides a
direct refinement between the source C modules and the target assembly
modules while retaining the support of both horizontal and vertical
compositionality and compilation to native assembly interfaces. The
extended CompCertO is based on CompCert version 3.10.  It is located
in the [`DirectRefinement`](DirectRefinement) directory along with
several examples that demonstrate the effectiveness of the extension
in end-to-end program verification. For comparison, we also upload a
copy of CompCertO in the directory
[`CompCertOv3.10`](CompCertOv3.10). This artifact accompanies the following paper:

> [*Fully Composable and Adequate Verified Compilation with Direct Refinements between
Open Modules*](paper/direct-refinement.pdf). Ling Zhang, Yuting Wang, Jinhua Wu, Jeremie
Koenig and Zhong Shao


## 2. List of Claims

Since our paper is about compiler verification, the claims we make are
mainly in the form of definitions, lemmas and theorems. We list the
claims made in each section of the paper below along with the
references to their corresponding Coq formalization in the artifact. A
more organized and complete explanation of the Coq formalization is
located in the section "Structure of the Formal Proofs" below.

### Section 2
- The simulation convention `\mathbb{C}` for the direct refinement in
  Section 2.2 (line 450) corresponds to the definition
  [cc_c_asm_injp](DirectRefinement/driver/CA.v#L184) in the Coq file
  [driver/CA.v](DirectRefinement/driver/CA.v).

- Theorem 2.3 in Section 2.4 (line 557) corresponds to the theorem
  [compose_fsim_components](DirectRefinement/common/Smallstep.v#L896) in the Coq file
  [common/Smallstep.v](DirectRefinement/common/Smallstep.v). 
  Note that this theorem is part of the background and has already been proved in CompCertO.
  
- Theorem 2.4 from Section 2.4 (line 580) corresponds to the theorem
  [open_fsim_ccref](./DirectRefinement/common/CallconvAlgebra.v#L76) in the Coq file
  [common/CallconvAlgebra.v](./DirectRefinement/common/CallconvAlgebra.v).
  Note that this theorem is part of the background and has already been proved in CompCertO.
  
### Section 3

- Lemma 3.1 from Section3.2.1 (line 708) of the paper corresponds to the theorem
  [injp_injp2](DirectRefinement/cklr/InjectFootprint.v#L2481) in the Coq file
  [cklr/InjectFootprint.v](DirectRefinement/cklr/InjectFootprint.v). 
  
- Lemma 3.2 from Section3.2.2 (line 763) corresponds to the theorem 
  [injp_injp](DirectRefinement/cklr/InjectFootprint.v#L472) in the same file.

### Section 4
- Lemma 4.1 from Section 4.1.2 (line 861) corresponds to the theorem 
  [transf_program_correct](DirectRefinement/backend/Constpropproof.v#L1097) in the
  Coq file [backend/Constpropproof.v](DirectRefinement/backend/Constpropproof.v).
  Similar correctness theorems for other changed passes in Table 1 
  (`CSE`, `DeadCode` and `Unusedglob`) have the same name.
  They can be found in [backend/CSEproof.v](DirectRefinement/backend/CSEproof.v),
  [backend/Deadcodeproof.v](DirectRefinement/backend/Deadcodeproof.v) and
  [backend/Unusedglobproof.v](DirectRefinement/backend/Unusedglobproof.v).
  Note that the correctness of `Deadcode` pass need further refinement
  as described in [driver/CallConv.v](DirectRefinement/driver/CallConv.v#L1783).

- Definition 4.2 from Section 4.1.2 (line 874) can be found in
  [backend/ValueAnalysis.v](DirectRefinement/backend/ValueAnalysis.v#L1939).

- Lemma 4.3 *provided by CompCertO* from Section 4.2.1 (line 919) corresponds to the instances 
  [commut_c_locset](DirectRefinement/driver/CallConv.v#L145), 
  [commut_locset_mach](DirectRefinement/driver/CallConv.v#L1091) and 
  [commut_mach_asm](DirectRefinement/driver/CallConv.v#L247) in 
  [driver/CallConv.v](DirectRefinement/driver/CallConv.v)

- For Lemma 4.4 from Section 4.2.2 (line 929),
  + property (1) is [injp_injp_eq](DirectRefinement/cklr/InjectFootprint.v#L2550) in
    the Coq file [cklr/InjectFootprint.v](DirectRefinement/cklr/InjectFootprint.v). 
  + property (2) is [sub_inj_injp](DirectRefinement/cklr/InjectFootprint.v#L2560) in
    the same file.
  + property (3) is [injp__injp_inj_injp](DirectRefinement/cklr/InjectFootprint.v#L2606)
	in the same file.
  + property (4) is [inj_inj](DirectRefinement/cklr/Inject.v#L500) in the Coq file
  [cklr/Inject.v](DirectRefinement/cklr/Inject.v).
  + property (5) is [ext_inj](DirectRefinement/cklr/Extends.v#L261) in the Coq file
  [cklr/Extends.v](DirectRefinement/cklr/Extends.v).
  + property (6) is [inj_ext](DirectRefinement/cklr/Extends.v#L290) in the same file.
  + property (7) is [ext_ext](DirectRefinement/cklr/Extends.v#L237) in the same file.
  

- Lemma 4.5 from Section 4.2.3 (line 946) corresponds to the last 
  [theorems](DirectRefinement/driver/CallConv.v#L1920) in 
  [driver/CallConv.v](DirectRefinement/driver/CallConv.v). 

- Lemma 4.6 (line 950) corresponds to the theorem 
  [ro_injp_trans](DirectRefinement/driver/CallConv.v#L1779) in the same file. 

- Lemma 4.7 (line 956) is an instantiation of theorem 
  [inv_commute](DirectRefinement/common/Invariant.v#L380) in 
  [common/Invariant.v](DirectRefinement/common/Invariant.v).

- Theorem 4.8 from Section 4.3 (line 963) corresponds to the final theorems
  in [cklr/Clightrel.v](DirectRefinement/cklr/Clightrel.v#L762), 
  [cklr/RTLrel.v](DirectRefinement/cklr/RTLrel.v#L271) and 
  [x86/Asmrel.v](DirectRefinement/x86/Asmrel.v#L513).
  
- The direct refinement convention (line 973) is defined as 
  [cc_compcert](DirectRefinement/driver/Compiler.v#L399) in the Coq file 
  [driver/Compiler.v](DirectRefinement/driver/Compiler.v). 
  
- Theorem 4.9 (line 977) corresponds to the theorem 
  [c_semantic_preservation](DirectRefinement/driver/Compiler.v#L842) in the same file.

- The unification of simulation conventions at the outgoing side (line 993-1005)
  is carried out by theorems in the Coq file [driver/Compiler.v](DirectRefinement/driver/Compiler.v).
  We will discuss this later in the `Structure of formal proofs` section.

### Section 5

- Definition 5.1 from Section 5.1 (line 1028) is defined in Coq file 
  [demo/Serverspec.v](DirectRefinement/demo/Serverspec.v). 

- Theorem 5.2 (line 1058) corresponds to the theorem 
  [semantics_preservation_L2](DirectRefinement/demo/Serverproof.v#L1581) in 
  [demo/Serverproof.v](DirectRefinement/demo/Serverproof.v).

- Lemma 5.3 from Section 5.2 (line 1088) is defined is the vertical composition of theorems
  [top2_ro](DirectRefinement/demo/ClientServerCspec2.v#L211), 
  [top2_wt](DirectRefinement/demo/ClientServerCspec2.v#L234) and 
  [top_simulation_L2](DirectRefinement/demo/ClientServerCspec2.v#L832) in the Coq file 
  [demo/ClientServerCspec2.v](DirectRefinement/demo/ClientServerCspec2.v).

- Theorem 5.4 (line 1097) corresponds to the lemmas
  [compose_simulation](DirectRefinement/common/SmallstepLinking.v#L338) in
  [common/SmallstepLinking.v](DirectRefinement/common/SmallstepLinking.v) and
  [asm_linking](DirectRefinement/x86/AsmLinking.v#L371) in 
  [x86/AsmLinking.v](DirectRefinement/x86/AsmLinking.v).

- Lemma 5.5 (line 1101) corresponds to the theorem 
  [compose_Client_Server_correct2](DirectRefinement/demo/ClientServer.v#L42) in the Coq 
  file [demo/ClientServer.v](DirectRefinement/demo/ClientServer.v).
  
- Lemma 5.6 (line 1107) corresponds to the theorem 
  [ro_injp_cc_compcert](DirectRefinement/demo/ClientServer.v#L76) in the same file.
  
-  Theorem 5.7 (line 1111) corresponds to the theorem
  [spec_sim_2](DirectRefinement/demo/ClientServer.v#L146) in the same file.
  
### Section 6

- The claim "We added 15k lines of code on top of CompCertO" form Section 6 (line 1114)
  is checked by `coqwc`. We add some theorems for readability after the submission.
  See the `Evaluation of soundness and proof effort` section.
  

## 3. Installation


###  Requirements

This artifact is based on the most recent version of CompCertO which
is in turn based on CompCert v3.10. You can find the user manual of
CompCert [here](http://compcert.inria.fr/man/).

- If you are using the VM, all the required software have already been installed on the 
virtual machine.

- If you prefer to compile the source code on your own computer, then
we recommend using the `opam` package manager to set up a build environment in Linux. 
We have tested the following building commands in the Linux shell (Ubuntu 22.04).
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
### Instructions for compiling the Coq code

The Coq code is located in the `DirectRefinement` directory.
First, you need to build a library named [Coqrel](https://github.com/CertiKOS/coqrel/tree/38dd003d28c91b1b93c01a160a31cdbc3348916a)),
```
(cd coqrel && ./configure && make)
```
Then, you can build the whole extension of CompCertO along with all the examples, as follows:
```
./configure x86_64-linux
make
```
You are all set if the compilation finishes successfully.  You may
also speed up the process by using `-jN` argument to run the Coq
compiler in parallel.
We have tested running `make -j4` in
the VM with 4GB virtual memory and 4 CPU cores, which in turn runs
on a host machine with Intel i9-12900H and 64 GB memory. The whole compilation takes about 8
minutes. When using `make` command without any parallel compilation,
it takes about 20 minutes.

The same instructions should be followed if you also want to compile
the original CompCert in the directory `CompCertOv3.10`.


### Navigating the proofs

After that, you can navigate the source code by using
[emacs](https://www.gnu.org/software/emacs/) with [proof-general](https://proofgeneral.github.io/doc/master/userman/Introducing-Proof-General/)
installed.

For example, running

```
emacs cklr/InjectFootprint.v
```

opens the emacs window in 
proof-general
mode for browsing the file `cklr/InjectFootprint.v`. 

You can also compile the source code into html files for better
readability. Simply run the following command (needs
`coq2html` which has already been installed in the VM)

```
make documentation
```

Then, the html versions of source code can be found at `doc/html`.
Note that the [index page](DirectRefinement/doc/index.html) is provided by CompCertO.

Note that if you compile the code in your own machine (without
`coq2html` installed), you need to install `coq2html` using the
following commands:

```
git clone https://github.com/xavierleroy/coq2html.git
cd coq2html
make
sudo make install
```

## 4. Evaluation of Soundness and Proof Effort

### Soundness 
To check that there is no admit in the artifact, enter `DirectRefinement` and run
```
find . -name "*.v" | xargs grep "Admitted"
```
which should show no admit.

### Proof effort

The following are the instructions for reproducing the lines of code (LOC) in 
Table 3 (line 2255) of the [technical report](paper/technical-report.pdf).

#### Column 2

The results in the second column can be produced by running the following
command in directory `CompCertOv3.10` and adding the numbers in the `spec` and
`proof` for each file.

```
coqwc lib/Maps.v common/Memory.v cklr/InjectFootprint.v cfrontend/SimplLocalsproof.v backend/ValueAnalysis.v backend/Deadcodeproof.v backend/Constpropproof.v backend/CSEproof.v backend/Unusedglobproof.v driver/CallConv.v driver/Compiler.v
```

The last row of result should be 
```
 6054     9871     1357 total #15925
```

#### Column 3

The numbers in Column 3 can be obtained in a similar way. Run the following command 
in `DirectRefinement` for the results except for the examples:
```
coqwc lib/Maps.v common/Memory.v cklr/InjectFootprint.v cfrontend/SimplLocalsproof.v backend/ValueAnalysis.v backend/Deadcodeproof.v backend/Constpropproof.v backend/CSEproof.v backend/Unusedglobproof.v driver/CA.v driver/CallConv.v driver/Compiler.v
```

The last row of result should be 
```
7863    15975     1647 total #23838
```

For the Client-Server example, run
```
coqwc demo/Client.v demo/Server.v demo/Serverspec.v demo/Serverproof.v demo/ClientServerCspec.v demo/ClientServerCspec2.v demo/ClientMR.v demo/ClientServerMRCSpec.v demo/ClientServerMRCSpec2.v demo/ClientServer.v 
```
and add the `spec` and `proof` of the last row.
```
2014     5315      770 total # 7329
```

For the Mutual Sum example, run
```
coqwc demo/Demo.v demo/Demospec.v demo/Demoproof.v demo/DemoCspec.v demo/Demotopspec.v
```
and add the `spec` and `proof` of the last row.
```
880     2248      231 total # 3128
```

Finally we get `23838 + 7329 + 3128 = 34295` for the number in row `Total`.

#### Column 4
The numbers in `Additions(+)` column is the result of subtracting column 2 from column 3.


## 5. Structure of the Formal Proofs

This artifact is based on CompCertO v3.10, you can browse the structure and
source code of original CompCert [here](http://compcert.inria.fr/doc/index.html).
Note that we use nominal memory model from Nominal CompCert[^1] in our implementation
for future extensions, while our result does not rely on it.

We demonstrate the formal proofs following the structure of our paper.
We first briefly present the background from CompCertO as described in Section 2.1.
We then demonstrate the key definitions and theorems for building direct refinement (Section 3 and 4).
Finally we discuss the examples of end-to-end verification using direct refinement (Section 5).

For CompCert's block-based memory model (Section 2.1.1), see 
[common/Values.v](DirectRefinement/common/Values.v) and
[common/Memory.v](DirectRefinement/common/Memory.v).

### CompCertO

#### Open semantics 

- The *language interface* (line 358) is defined in 
[common/LanguageInterface.v](DirectRefinement/common/LanguageInterface.v):

```
Structure language_interface :=
  mk_language_interface {
    query: Type;
    reply: Type;
    entry: query -> val;
  }.
```
- The interfaces of C and Asm (line 363-364) are defined as `li_c` in
[common/LanguageInterface.v](DirectRefinement/common/LanguageInterface.v) and
`li_asm` in [x86/Asm.v](DirectRefinement/x86/Asm.v).

- *Open semantics* corresponds to `semantics` in
[common/Smallstep.v](DirectRefinement/common/Smallstep.v),
The *Open LTS* (line 369-377) is defined by `lts` in the same file.

#### Open simulation

- The *simulation convention* between interfaces is defined as `callconv` in 
[common/LanguageInterface.v](DirectRefinement/common/LanguageInterface.v).


- The *open simulation* is defined as `forward_simulation` in 
  [common/Smallstep.v](DirectRefinement/common/Smallstep.v). The core of it
  is `fsim_properties` which corresponds to Figure 5 (line 344) in the paper.

#### Kripke Memory Relations

- (Definition 2.1, line 411) *Kripke Memory Relation* is defined as `cklr` in 
  [cklr/CKLR.v](DirectRefinement/cklr/CKLR.v). Different memory relations
  and their properties are in the [cklr](DirectRefinment/cklr) directory.

- For the *world accessibility* (line 395-407), see the C-level simulation convention
  `cc_c`  defined in [common/LanguageInterface.v](DirectRefinement/common/LanguageInterface.v)
  as an example. It defines the simulation convention between C interfaces
  parameterized over memory relation `R` as:
  :
  ```
  Program Definition cc_c (R: cklr): callconv li_c li_c :=
  {|
    ccworld := world R;
    match_senv := match_stbls R;
    match_query := cc_c_query R;
    match_reply := (<> cc_c_reply R)%klr;
  |}.
  ```
  If we use the same world `w` for `match_query` and `match_reply`, the symbol `<>` in
  `match_reply` indicates that there exists an accessibility relation of worlds from 
  queries to replies. `<>` is the notation of `klr_diam` in 
  [coqrel/KLR.v](DirectRefinement/coqrel/KLR.v)


#### Vertical Composition of simulations

- Theorem 2.3 from Section 2.4 (line 557) corresponds to the theorem `compose_forward_simulations`
  in the Coq file [common/Smallstep.v](DirectRefinement/common/Smallstep.v).
  
- The composition of simulation conventions (line 561) is defined as `cc_compose` in
  [common/LanguageInterface.v](DirectRefinement/common/LanguageInterface.v).
  
#### Refinement of calling conventions

-  The refinement of simulation conventions (line 571-572) is defined as `ccref` 
   in [common/CallconvAlgebra.v](DirectRefinement/common/CallconvAlgebra.v).
   Note that `\mathbb{R} \sqsubseteq \mathbb{S}` corresponds to `ccref S R`.
   The equivalence is defined as `cceqv` in the same file.

-  Theorem 2.4 (line 580) is defined as `open_fsim_ccref` in 
   [common/CallconvAlgebra.v](DirectRefinement/common/CallconvAlgebra.v).

#### Kripke Relation with Memory Protection (`injp`)

- (Definition 2.2, line 417) The definition of `injp` can be found in 
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
	```

- The `injp` accessibility is defined as `injp_acc` in the same file:
	```
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
	Note that *mem-acc(m,m')* mentioned in the paper (line 422) is summarized as definition
	`ro_acc` in [backend/ValueAnalysis.v](DirectRefinement/backend/ValueAnalysis.v):
   ```
   Inductive ro_acc : mem -> mem -> Prop :=
   | ro_acc_intro m1 m2:
      Mem.ro_unchanged m1 m2 -> (*ec_readonly*)
      Mem.sup_include (Mem.support m1) (Mem.support m2) -> (*ec_valid_block*)
      injp_max_perm_decrease m1 m2 -> (*ec_perm*)
	  ro_acc m1 m2.
  ```
  These properties of are defined by vanilla CompCert in 
  [common/Events.v](DirectRefinement/common/Events.v) as `ec_readonly`, `ec_valid_block`
  and `ec_perm` for external calls. We use them together as a
  preorder relation for memory transformation during both internal and external executions.
  
  The *unchanged-on* (line 424) is defined as `unchanged_on` in
  [common/Memory.v](DirectRefinement/common/Memory.v).
  Note that `Mem_sup_include (Mem.support m1) (Mem.support m2)` which means that
  `m2` have more valid blocks than `m1` is included in 
  `Mem.unchanged_on P m1 m2`. Therefore all three properties of `ro_acc m1 m1'` are
  included in `injp_acc` as we defined in the paper.


### `injp` transitivity (Section 3)
The proof of `injp` transitivity in 
[cklr/InjectFootprint.v](DirectRefinement/cklr/InjectFootprint.v) is commented according
to the appendix C of our [technical report](paper/technical-report.pdf).
The refinements (Lemma 3.1 and Lemma 3.2) correspond to the following lemmas:
```
Lemma injp_injp2:
  subcklr (injp @ injp) injp.
Lemma injp_injp:
  subcklr injp (injp @ injp).
```

Here `subcklr` is the refinement of kripke memory relations. The lemma
`cc_c_ref` in [cklr/CKLRAlgebra.v](DirectRefinement/cklr/CKLRAlgebra.v)
can turn `subcklr R S` into the refinement of simulation conventions
`ccref (cc_c R) (cc_c S)`. Similar lemma `cc_asm_ref` for `cc_asm` is defined
in [x86/Asm.v](DirectRefinement/x86/Asm.v).

Here we briefly present the construction of intermediate memory state
(as discussed in the paper line 738-753) as following steps. 
We first construct the injections and shape of `m2'` using
the operation `update_meminj12` defined in 
[cklr/InjectFootprint.v](DirectRefinement/cklr/InjectFootprint.v).

We then copy the values and permissions for newly allocated blocks as:

```
Definition m2'1 := Mem.step2 m1 m2 m1' s2' j1'.
```
Finally we update the values and permissions for old blocks:

```
Definition m2' := Mem.copy_sup m1 m2 m1' j1 j2 j1' INJ12 (Mem.support m2) m2'1.
```

These memory operations are defined in [common/Memory.v](DirectRefinement/common/Memory.v).
For these operations, we changed the type of `mem_access` to be the same structure as
`mem_contents` in order to enumerate the valid (with nonempty permissions)
locations of a memory block.
```
Record mem' : Type := mkmem {
  ...
  (* old implementation *)
  (* mem_access: NMap.t (Z -> perm_kind -> option permission); *)
  mem_access: NMap.t (ZMap.t memperm);
  ...
}
```
Given the transivity of `injp` as depicted in Figure 10 (line 599), we are able to
achieve the "real" vertical composition of open simulations as depicted in Figure 9 (line 589).

### Derivation of direct Refinement (Section 4)

#### Proofs of individual passes

- Table 1 can be checked according to `CompCertO's_passes` in 
  [driver/Compiler.v](DirectRefinement/driver/Compiler.v). 
  The definitions used in the table from CompCertO can be found as follows.
  The simulation conventions between the same language interfaces 
  `cc_c`, `cc_locset`, `cc_mach` and `cc_asm` (line 813) are defined in 
  in [common/Languageinterface.v](DirectRefinement/common/LanguageInterface.v),
  [backend/Conventions](DirectRefinement/backend/Conventions.v),
  [backend/Mach.v](DirectRefinement/backend/Mach.v) and
  [x86/Asm.v](DirectRefinement/x86/Asm.v).
  The structure simulation conventions `cc_c_locset`, `cc_locset_mach` and
  `cc_mach_asm` (line 823) are defined in 
  [backend/Conventions](DirectRefinement/backend/Conventions.v),
  [driver/CallConv.v](DirectRefinement/driver/CallConv.v) and
  [x86/Asm.v](DirectRefinement/x86/Asm.v). 
  
- The *semantic invariant* is defined as `invariant` in
  [common/Invariant.v](DirectRefinement/common/Invairant.v):

```
Record invariant {li: language_interface} :=
  {
    inv_world : Type;
    symtbl_inv : inv_world -> Genv.symtbl -> Prop;
    query_inv : inv_world -> query li -> Prop;
    reply_inv : inv_world -> reply li -> Prop;
  }.
```

For the passes using static analysis, we define the invariant `ro` in
[backend/ValueAnalysis.v](DirectRefinement/backend/ValueAnalysis.v):
```
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
[backend/Constpropproof.v](DirectRefinement/backend/Constpropproof.v).
The same theorems and similar proofs can be found in
[backend/CSEproof.v](DirectRefinement/backend/CSEproof.v) and
[backend/Deadcodeproof.v](DirectRefinement/backend/Deadcodeproof.v).


For [Unusedglob](DirectRefinement/backend/Unusedglobproof.v) pass,
we assume that the global symbol table are the same for source and target
semantics. While some local static definitions are removed. 

Moreover, We use `injp` in the incoming simulation convention in
[cfrontend/SimplLocalsproof.v](DirectRefinement/cfrontend/SimplLocalsproof.v)
as an example to show that `injp` is a reasonable guarantee condition. 
The proofs of remaining passes are unchanged from CompCertO.

#### Unification of the simulation conventions

We have mentioned the corresponding theorems of the properties for refining
simulation conventions in Section 4.2 in the `List of technical claims` part.
The direct simulation convention `\mathbb{C}` (line 973)
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
as we presented in the paper. As in the paper, we take the outgoing side for example.
We first extend `cc_compcert` to `cc_compcert_dom` as follows:
```
Definition cc_compcert_dom : callconv li_c li_asm :=
  ro @ wt_c @  cc_c injp @
       cc_c_locset @ cc_locset_mach @ cc_mach_asm.
	   
Theorem cc_compcert_merge:
  forall p tp,
  forward_simulation cc_compcert_dom cc_compcert_cod (Clight.semantics1 p) (Asm.semantics tp) ->
  forward_simulation cc_compcert cc_compcert (Clight.semantics1 p) (Asm.semantics tp).  
```

Then we define the simulation convention `cc_c_level` for the frontend of C level
passes. Thus we partially extend `cc_compcert_dom` to satisfy the passes after
`Deadcode`:

```
Definition cc_c_level : callconv li_c li_c := ro @ wt_c @ injp.

Lemma cc_compcert_collapse:
  ccref
    (cc_c_level @                                 (* Passes up to Unusedglob *)
     cc_c inj @                                   (* Unusedglob *)
     (wt_c @ cc_c ext @ cc_c_locset) @            (* Alloc *)
     cc_locset ext @                              (* Tunneling *)
     (wt_loc @ cc_locset injp @ cc_locset_mach) @ (* Stacking *)
     (cc_mach ext @ cc_mach_asm) @                (* Asmgen *)
    cc_asm inj)                                   (* Self-Sim *)
    cc_compcert_dom.
```

Finally we extend `cc_c_level` to satisfy the passes at C level:

```
Lemma cc_c_level_collapse:
  ccref (ro @ cc_c injp @ cc_c injp @             (* Up to Cminorgen *)
         (wt_c @ cc_c ext) @ cc_c ext @           (* Up to RTLgen *)
         cc_c inj @                               (* Self-Sim *)
         cc_c ext @                               (* Tailcall *)
         cc_c injp @                              (* Inlining *)
         cc_c injp @                              (* Self-Sim *)
         (ro @ injp) @ (ro @ injp) @ (ro @ injp)  (* VA passes *)
        )
        cc_c_level.
```
Therefore the simulation conventions can be refined into our direct simulation 
convention as proved in the theorem `clight_semantics_preservation` (Theorem 4.9):
```
Theorem clight_semantic_preservation:
  forall p tp,
  match_prog p tp ->
  forward_simulation cc_compcert cc_compcert (Clight.semantics1 p) (Asm.semantics tp)
  /\ backward_simulation cc_compcert cc_compcert (Clight.semantics1 p) (Asm.semantics tp).
```
### End-to-End Verification of Heterogeneous Modules (Section 5)

In the section 5 of the paper, we introduce the end-to-end
verification of the client-server example based on the direct
refinement. We first give the definitions of the C and assembly code
of our example, and then follow the Figure 4 to give the overview of
the refinement proof.

#### Definitions of the Client-Server Example

The C or assembly code of `client.c`, `server.s` and `server_opt.s`
are shown in Figure 3 in our paper.

* `client.c` is defined in [demo/Client.v](DirectRefinement/demo/Client.v).
* `server.s` and `server_opt.s` are defined in [demo/Server.v](DirectRefinement/demo/Server.v).

#### Refinement for the Hand-written Server (Section 5.1)

First, we show the refinement between the specification of
`server_opt.s` (i.e., `L_s` in our paper) and the semantics of
`server_opts`.

* (Definition 5.1) The hand-written specification (`L_s`) for the
  optimized server (i.e., `server_opt.s`) is defined by `L2` in [demo/Serverspec.v](DirectRefinement/demo/Serverspec.v#L116). The hand-written specification (not
  discussed in the paper) for `server.s` is defined by `L1` in [demo/Serverspec.v](DirectRefinement/demo/Serverspec.v#L98).
* (Theorem 5.2) It corresponds to `semantics_preservation_L2` in
  [demo/Serverproof.v](DirectRefinement/demo/Serverproof.v#L1581).
  ```
  Lemma semantics_preservation_L2:
    forward_simulation cc_compcert cc_compcert L2 (Asm.semantics b2).
  ```
  This proof is decomposed into
  [self_simulation_wt](DirectRefinement/demo/Serverproof.v#L1533) and
  [CAinjp_simulation_L2](DirectRefinement/demo/Serverproof.v#L1089) in the same file.
  For the proof of `CAinjp_simulation_L2`, the simulation relation is defined by [match_state_c_asm](DirectRefinement/demo/Serverproof.v#L42).
  

#### End-to-End Correctness Theorem (Section 5.2)

In this section, we first show the refinement between the top-level
specification (`L_cs`) and the composition of `client.c` and
`L_s`. And then we use the correctness of the compiler and vertical
compositionality to establish the end-to-end refinement.

* Definition of the top-level specification (for optimized server `server_opt.s`) `L_cs` is `top_spec2` in [demo/ClientServerCspec2.v](DirectRefinement/demo/ClientServerCspec2.v#L138). The top-level specification for `server.s` is defined by `top_spec1` in [demo/ClientServerCspec.v](DirectRefinement/demo/ClientServerCspec.v#L136).
* (Lemma 5.3) It is defined by `top_simulation_L2` in [demo/ClientServerCspec2.v](DirectRefinement/demo/ClientServerCspec2.v#L832). 
  ```
  Lemma top_simulation_L2:
    forward_simulation (cc_c injp) (cc_c injp) top_spec2 composed_spec2.
  ```
  The simulation relation is defined by
  [match_state](DirectRefinement/demo/ClientServerCspec2.v#L254) in the same file. For
  the same theorem for unoptimized server, we define it in
  [top_simulation_L1](DirectRefinement/demo/ClientServerCspec.v#L136).

* (Theorem 5.4) The theorem of horizontal composition corresponds to
  `compose_simulation` in
  [common/SmallstepLinking.v](DirectRefinement/common/SmallstepLinking.v#L338). The
  adequacy theorem corresponds to `asm_linking` in
  [x86/AsmLinking.v](DirectRefinement/x86/AsmLinking.v#L371).
  ```
  Lemma compose_simulation {li1 li2} (cc: callconv li1 li2) L1a L1b L1 L2a L2b L2:
    forward_simulation cc cc L1a L2a ->
    forward_simulation cc cc L1b L2b ->
    compose L1a L1b = Some L1 ->
    compose L2a L2b = Some L2 ->
    forward_simulation cc cc L1 L2.
  ```
  ```
  Lemma asm_linking:
  forward_simulation cc_id cc_id
    (SmallstepLinking.semantics L (erase_program p))
    (semantics p).
  ```
* (Lemma 5.5) It corresponds to `compose_Client_Server_correct2` in [demo/ClientServer.v](DirectRefinement/demo/ClientServer.v#L42).
* (Lemma 5.6) It corresponds to `ro_injp_cc_compcert` in [demo/ClientServer.v](DirectRefinement/demo/ClientServer.v#L76).
  ```
  Lemma ro_injp_cc_compcert:
    cceqv cc_compcert (wt_c @ ro @ cc_c injp @ cc_compcert).
  ```
* (Theorem 5.7) It corresponds to `spec_sim_2` in [ClientServer.v](DirectRefinement/demo/ClientServer.v#L146).
  ```
  Theorem spec_sim_2 : forward_simulation cc_compcert cc_compcert top_spec2 (Asm.semantics tp2).
  ```
  
#### Other Examples

The following examples are not discussed in our paper, because they
are more complicated than the client-server example introduced in our
paper. However, we implement and verify them to show the effectiveness of our framework.

##### Mutual Recursive Client-Server Example

We define a mutual recursive client-server example where the server
code is the same as `server.s` in [demo/Server.v](DirectRefinement/demo/Server.v) and the
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
  [demo/ClientMR.v](DirectRefinement/demo/ClientMR.v#L157).
* The definition of servers are the same as the examples (`server.s`
  and `server_opt.s`) introduced in our paper, i.e., it is defined by
  `b1` and `b2` in [demo/Server.v](DirectRefinement/demo/Server.v). Note that we
  implement the repeated invocation by directly passing the `request`
  function in `client` to the server. Thereby the server can jump to
  the call-back function (the `request` function in client) to encrypt
  the subsequent data.
* The top level specification is defined by `top_spec1` in
  [demo/ClientServerMRCSpec.v](DirectRefinement/demo/ClientServerMRCSpec.v#L150).
* The refinement between the top-level specification and composition of `client_mr.c` and `L1` is defined by `top_simulation_L1` in [demo/ClientServerMRCspec.v](DirectRefinement/demo/ClientServerMRCSpec.v#L844).
  ```
  Lemma top_simulation_L1:
  forward_simulation (cc_c injp) (cc_c injp) top_spec1 composed_spec1.
  ```
  To compose with the direct refinement, we show that the top-level
  specification is self-simulated by `ro` and `wt`. They are defined
  by `top1_ro` and `top1_wt` in [demo/ClientServerMRCspec.v](DirectRefinement/demo/ClientServerMRCSpec.v).
* The direct refinement of this example is defined by `spec_sim_mr` in
  [demo/ClientServer.v](DirectRefinement/demo/ClientServer.v#L233).
  ```
  Theorem spec_sim_mr : forward_simulation cc_compcert cc_compcert (top_spec1 N) (Asm.semantics tp1).
  ```


##### Mutual Summation Example

We present the application of our method to an example borrowed from
CompCertM[^2] — two programs that mutually invoke each other to finish
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
* First, like what we do for the server in the above example, we define a high-level specification (called `L_A`) for `M_A`. The definition of `L_A` is in [demo/Demospec.v](DirectRefinement/demo/Demospec.v#L88) with the same name. The refinement is defined by `M_A_semantics_preservation` in [demo/Demoproof](DirectRefinement/demo/Demoproof.v). 
  ```
  Lemma M_A_semantics_preservation:
  forward_simulation cc_compcert cc_compcert L_A (Asm.semantics M_A).
  ```
  The simulation relation of this proof is defined by [match_state_c_asm](DirectRefinement/demo/Demoproof.v#L44) in the same file.
* Second, for `M_C`, we define its specification `L_C` in
  [demo/DemoCspec.v](DirectRefinement/demo/DemoCspec.v#L90). Therefore, the refinement
  between `L_C` and the semantics of `M_C` is defined by
  [cspec_simulation](DirectRefinement/demo/DemoCspec.v#L423),
  [cspec_ro](DirectRefinement/demo/DemoCspec.v#L901) and
  [cspec_self_simulation_wt](DirectRefinement/demo/DemoCspec.v#L908).
  ```
  Lemma cspec_simulation:
  forward_simulation (cc_c injp) (cc_c injp) L_C (Clight.semantics1 M_C).

  Theorem cspec_ro :
  forward_simulation ro ro L_C L_C.

  Theorem cspec_self_simulation_wt :
  forward_simulation wt_c wt_c L_C L_C.
  ```

* With the above definitions, we define a top-level specification
  called `top_spec` in [demo/Demotopspec.v](DirectRefinement/demo/Demotopspec.v#L171).
  The refinement between `top_spec` and the composition of `L_C` and
  `L_A` corresponds to [top_simulation](DirectRefinement/demo/Demotopspec.v#L592),
  [top_ro](DirectRefinement/demo/Demotopspec.v#L933) and
  [topspec_self_simulation_wt](DirectRefinement/demo/Demotopspec.v#L940).
* Finally, with the above refinements and the correctness of CompCert(O), we show the end-to-end refinement theorem in  `topspec_correct` in [Demotopspec.v](DirectRefinement/demo/Demotopspec.v#L1011).
  ```
  Theorem topspec_correct:
    forall tp M_C',
      transf_clight_program M_C = OK M_C' ->
      link M_C' M_A = Some tp ->
      forward_simulation cc_compcert cc_compcert top_spec (Asm.semantics tp).
  ```

## References
[^1]: Yuting Wang, Ling Zhang, Zhong Shao, and Jérémie Koenig. 2022. Verified compilation of C programs with a nominal memory model. Proc. ACM Program. Lang. 6, POPL, Article 25 (January 2022), 31 pages. https://doi.org/10.1145/3498686

[^2]: Youngju Song, Minki Cho, Dongjoo Kim, Yonghyun Kim, Jeehoon Kang, and Chung-Kil Hur. 2020. CompCertM: CompCert with C-Assembly Linking and Lightweight Modular Verification. Proc. ACM Program. Lang. 4, POPL, Article 23 (Jan. 2020), 31 pages. https://doi.org/10.1145/3371091
    
