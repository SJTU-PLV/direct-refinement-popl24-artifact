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
Note that the [index page](doc/index.html) is provided by CompCertO.

## Evaluation instructions



## Additional artifact description

For reference, you can browse the original CompCert source code [here]
(http://compcert.inria.fr/doc/index.html). We also export our code as
[browsable HTML files](./doc/). Note that we use nominal memory model from
[Nominal CompCert](https://dl.acm.org/doi/10.1145/3498686) in our implementation
for future extensions, while our result does not rely on it.

[TODO: make documentation and leave the html folder in the archive.]

We briefly present the contents of CompCertO, then introduce our implementation of direct
refinement and the examples of end-to-end verification using direct refinement.

### CompCertO

[CompCertO](https://flint.cs.yale.edu/flint/publications/compcerto.html) is a version of CompCert
developed by the Yale FLINT group. The semantic model of CompCert is extended to describe the behavior
of individual compilation units and enable compositional verification.


The language interfaces and simulation conventions are defined in [common/LanguageInterface.v]
(doc/LanguageInterface.html). This file also contains the "concatenation" of simulation conventions
[cc_compose](doc/LanguageInterface.html#cc_compose), C level interface [li_c](doc/LanguageInterface.html#li_c)
and C level simulation convention [cc_c](doc/LanguageInterface.html#cc_c) parameterized over
[CompCert Kripke Logical Relation](doc/CKLR.html#cklr) (which we call Kripke Memory Relation in the paper).
The definition of different memory relations and their properties are in the `cklr` directory.

The open semantics and open simulations are defined in [common/Smallstep.v](doc/Smallstep.html).
[Open semantics](doc/Smallstep.html#semantics) is essentially a mapping from global 
[symbol table](doc/Globalenvs.html#Genv.symtbl) to [open LTS](doc/Smallstep.html#lts) and a skeleton
of local definitions.
The [forward simulation](doc/Smallstep.html#forward_simulation) and the
[vertical composition](doc/Smallstep.html#compose_forward_simulations) are also defined here.
The horizontal composition is defined in [SmallstepLinking.v](doc/SmallstepLinking.html).

You can refer the [CompCertO documentation page](doc/index.html) for further detailed description of CompCertO implementation.

### Direct Refinement 

* `injp` transitivity

    The [definition](doc/InjectFootprint.html#injp) and [transitivity](doc/InjectFootprint.html#injp_injp_eq) of
	`injp` are in [cklr/InjectFootprint.v](doc/InjectFootprint.html). Note that the properties 
	[Mem.ro_unchanged](doc/Memory.html#Mem.ro_unchanged) and [injp_max_perm_decrease](doc/InjectFootprint.html) 
	in `injp_acc` are the same as the assumptions [ec_readonly](doc/Event.html#ec_readonly) and
	[ec_max_perm](doc/Event.html#ec_max_perm) of external functions defined in original CompCert.

    The proof of `injp` transitivity is commented according to the appendix C of our [technical report](popl24-technical-report.pdf).
	We update the memory injections using [update_meminj12](doc/InjectFootprint.html#update_meminj12) and construct
	the intermediate memory state [m2'](doc/InjectFootprint.html#m2') using the memory operations 
	[Mem.step2](doc/Memory.html#Mem.step2) and [Mem.copy_sup](doc/Memory.html#Mem.copy_sup) 
	defined in [common/Memory.v](doc/Memory.html).

* Proofs of individual passes

    For the passes using static analysis, we define the invariant [ro](doc/ValueAnalysis.html#ro) in 
	[backend/ValueAnalysis.v](doc/ValueAnalysis.html). The proof which uses `injp` to guarantee the dynamic values of
	unreachable local variables for these passes can be found in the lemmas `transf_external_states` in 
	[Constpropproof](doc/Constpropproof.html#transf_external_states), [CSEproof](doc/CSEproof.html#transf_external_states) 
	and [Deadcodeproof](doc/Deadcodeproof.html#transf_external_states).

    For [Unusedglob](doc/Unusedglob.html) pass, we assume that the global symbol table are the same for source and target
	semantics. While some local static definitions are removed. We use `injp` in the incoming simulation convention in
	[backend/SimplLocalsproof.v](doc/SimplLocalsproof.html#transf_program_correct') as an example to show that `injp` is a
	reasonable guarantee condition to provide by the compilation passes. The proofs of remaining passes are unchanged from CompCertO.

* Unification of the simulation conventions.
   
  The basic simulation convention between C and assembly [$\mathit{CA}$](doc/CA.html#cc_c_asm) and [$\mathit{CAinjp}$](doc/CA.html#cc_c_asm_injp)
  are defined in [driver/CA.v](doc/CA.html). The proof of
  [$\mathit{c}_{\mathit{injp}} \cdot \mathit{CA} \equiv \mathit{CAinjp}$](doc/CA.html#ccinjp__injp_ca_equiv) 
  can also be found here. We add some refinements about `wt` and `ro` in the end of [driver/CallConv.v](doc/CallConv.v).
  Some new refinement properties about `injp` can be found in the end of [cklr/InjectFootprint.v].

  The direct simulation convention $\mathit{ro} \cdot \mathit{wt} \cdot \mathit{CAinjp} \cdot \mathit{asm}_{\mathit{injp}}$
  is defined as [cc_compcert](doc/Compiler.html#cc_compcert) in [driver/Compiler.v](doc/Compiler.html). 
  
  The unification of simulation convention at the incoming and outgoing side is also carried out here. The implementation is
  actually "expanding" the [cc_compcert](doc/Compiler.html#cc_compcert) step by step to satisty the requirement of all compilation
  passes. For examples, the lemmas [cc_expand](doc/Compiler.html#cc_expand) and [cc_collapse](doc/Compiler.html#cc_collapse) describe
  the main result of the incoming and outgoing side.

### Examples of end-to-end verification

* The Client-Server example:
    The definitions of client and server can be found in [demo/Client.v](doc/Client.html) and [demo/Server.v](doc/Server.html). The C-level specification of the server is defined in
    [demo/Serverspec.v](doc/Serverspec.html), the refinement
    between the server and its specification can be found in
    [demo/Serverproof.v](doc/Serverproof.html)
    [TODO:two versions?]

    + Top-level specification and its refinement proof (Lemma 5.3 in Section 5.2): [demo/ClientServerCspec.v](demo/ClientServerCspec.v)(unoptimized) and [demo/ClientServerCspec2.v](demo/ClientServerCspec2.v)(optimized)
    + Final theorem (Theorem 5.7 in Section 5.2): [demo/ClientServer.v](demo/ClientServer.v)

* The Mutual Sum example from CompCertM:

    We take the mutual summation example from CompCertM to test our framework. The open modules $M_C$ and $M_A$ are defined in [demo/Demo.v](doc/Demo.html). The definition of specification $L_A$ and its refinement with $M_A$ can be found in [demo/Demospec.v](doc/Demospec.html) and [demo/Demoproof.v](doc/Demoproof.html) The Top-level specification of composed semantics and the refinement proof are in [demo/DemoCspec.v](doc/DemoCspec.html) and [demo/Demotopspec.v](doc/Demotopspec.html).

    The final theorem [topspec_correct] is also in [demo/Demotopspec.v](doc/Demotopspec.html#topspec_correct).
    Note that our verification result of this example is slightly different from CompCertM. We build an open simulation which can take arbitrary incoming memories while
    CompCertM establish the RUSC relation (and behavior refinement) based on source-level module-local invariants about the memory.

    
* Client-Server with multiple mutual recursion:
    + Definition of client: [demo/ClientMR.v](demo/ClientMR.v)
    + Top-level specification and its refinement proof: [demo/ClientServerMRCSpec.v](demo/ClientServerMRCSpec.v)
    + Final theorem: [demo/ClientServer.v](demo/ClientServer.v) -- [`spec_sim_mr`](demo/ClientServer.v#L202)
