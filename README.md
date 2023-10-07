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
Note that the [index page](DirectRefinement/doc/index.html) is provided by CompCertO.

## Evaluation instructions

To check soundness of this artifact, enter `DirectRefinement` and run
```
grep "Admitted" */*.v
```
This instruction should return no result.

[TODO: compare the Lines of code with CompCertOv3.10, change the table in TR according to 
modification of the code]

## Additional artifact description

This artifact is based on CompCertO v3.10, you can browse the structure and
source code of original CompCert [here](http://compcert.inria.fr/doc/index.html).
Note that we use nominal memory model from Nominal CompCert[1] in our implementation
for future extensions, while our result does not rely on it.

We briefly present the framework of CompCertO, then introduce our implementation of direct
refinement and the examples of end-to-end verification using direct refinement.
For CompCert's block-based memory model (Section 2.1.1), see 
[common/Values.v](DirectRefinement/common/Values.v) and
[common/Memory.v](DirectRefinement/common/Memory.v).

### CompCertO

The language interfaces and simulation conventions are defined in 
[common/LanguageInterface.v](DirectRefinement/common/LanguageInterface.v).
This file also contains the "concatenation" of simulation conventions
[cc_compose](DirectRefinement/common/LanguageInterface.v#),
C level interface [li_c](DirectRefinement/common/LanguageInterface.v#)
and C level simulation convention 
[cc_c](DirectRefinement/common/LanguageInterface.v#cc_c) parameterized over
[CompCert Kripke Logical Relation](DirectRefinement/CKLR.html#cklr) 
(which we call Kripke Memory Relation in the paper).
The definition of different memory relations and their properties are in 
the `cklr` directory.

The open semantics and open simulations are defined in 
[common/Smallstep.v](DirectRefinement/common/Smallstep.v).
[Open semantics](DirectRefinement/common/Smallstep.v#)
is essentially a mapping from global 
[symbol table](DirectRefinement/Globalenvs.html#Genv.symtbl) to [open LTS](DirectRefinement/Smallstep.html#lts) and a skeleton
of local definitions.
The [forward simulation](DirectRefinement/Smallstep.html#forward_simulation) and the
[vertical composition](DirectRefinement/Smallstep.html#compose_forward_simulations) are also defined here.
The horizontal composition is defined in [SmallstepLinking.v](DirectRefinement/SmallstepLinking.html).

You can refer the [CompCertO documentation page](DirectRefinement/index.html) for further detailed description of CompCertO implementation.

### Direct Refinement 

* `injp` transitivity

    The [definition](DirectRefinement/InjectFootprint.html#injp) and [transitivity](DirectRefinement/InjectFootprint.html#injp_injp_eq) of
	`injp` are in [cklr/InjectFootprint.v](DirectRefinement/InjectFootprint.html). Note that the properties 
	[Mem.ro_unchanged](DirectRefinement/Memory.html#Mem.ro_unchanged) and [injp_max_perm_decrease](DirectRefinement/InjectFootprint.html) 
	in `injp_acc` are the same as the assumptions [ec_readonly](DirectRefinement/Event.html#ec_readonly) and
	[ec_max_perm](DirectRefinement/Event.html#ec_max_perm) of external functions defined in original CompCert.

    The proof of `injp` transitivity is commented according to the appendix C of our [technical report](popl24-technical-report.pdf).
	We update the memory injections using [update_meminj12](DirectRefinement/InjectFootprint.html#update_meminj12) and construct
	the intermediate memory state [m2'](DirectRefinement/InjectFootprint.html#m2') using the memory operations 
	[Mem.step2](DirectRefinement/Memory.html#Mem.step2) and [Mem.copy_sup](DirectRefinement/Memory.html#Mem.copy_sup) 
	defined in [common/Memory.v](DirectRefinement/Memory.html).

* Proofs of individual passes

    For the passes using static analysis, we define the invariant [ro](DirectRefinement/ValueAnalysis.html#ro) in 
	[backend/ValueAnalysis.v](DirectRefinement/ValueAnalysis.html). The proof which uses `injp` to guarantee the dynamic values of
	unreachable local variables for these passes can be found in the lemmas `transf_external_states` in 
	[Constpropproof](DirectRefinement/Constpropproof.html#transf_external_states), [CSEproof](DirectRefinement/CSEproof.html#transf_external_states) 
	and [Deadcodeproof](DirectRefinement/Deadcodeproof.html#transf_external_states).

    For [Unusedglob](DirectRefinement/Unusedglob.html) pass, we assume that the global symbol table are the same for source and target
	semantics. While some local static definitions are removed. We use `injp` in the incoming simulation convention in
	[backend/SimplLocalsproof.v](DirectRefinement/SimplLocalsproof.html#transf_program_correct') as an example to show that `injp` is a
	reasonable guarantee condition to provide by the compilation passes. The proofs of remaining passes are unchanged from CompCertO.

* Unification of the simulation conventions.
   
  The basic simulation convention between C and assembly [$\mathit{CA}$](DirectRefinement/CA.html#cc_c_asm) and [$\mathit{CAinjp}$](DirectRefinement/CA.html#cc_c_asm_injp)
  are defined in [driver/CA.v](DirectRefinement/CA.html). The proof of
  [$\mathit{c}_{\mathit{injp}} \cdot \mathit{CA} \equiv \mathit{CAinjp}$](DirectRefinement/CA.html#ccinjp__injp_ca_equiv) 
  can also be found here. We add some refinements about `wt` and `ro` in the end of [driver/CallConv.v](DirectRefinement/CallConv.v).
  Some new refinement properties about `injp` can be found in the end of [cklr/InjectFootprint.v].

  The direct simulation convention $\mathit{ro} \cdot \mathit{wt} \cdot \mathit{CAinjp} \cdot \mathit{asm}_{\mathit{injp}}$
  is defined as [cc_compcert](DirectRefinement/Compiler.html#cc_compcert) in [driver/Compiler.v](DirectRefinement/Compiler.html). 
  
  The unification of simulation convention at the incoming and outgoing side is also carried out here. The implementation is
  actually "expanding" the [cc_compcert](DirectRefinement/Compiler.html#cc_compcert) step by step to satisty the requirement of all compilation
  passes. For examples, the lemmas [cc_expand](DirectRefinement/Compiler.html#cc_expand) and [cc_collapse](DirectRefinement/Compiler.html#cc_collapse) describe
  the main result of the incoming and outgoing side.

### Examples of end-to-end verification

* The Client-Server example:
    The definitions of client and server can be found in [demo/Client.v](DirectRefinement/Client.html) and [demo/Server.v](DirectRefinement/Server.html). The C-level specification of the server is defined in
    [demo/Serverspec.v](DirectRefinement/Serverspec.html), the refinement
    between the server and its specification can be found in
    [demo/Serverproof.v](DirectRefinement/Serverproof.html)
    [TODO:two versions?]

    + Top-level specification and its refinement proof (Lemma 5.3 in Section 5.2): [demo/ClientServerCspec.v](demo/ClientServerCspec.v)(unoptimized) and [demo/ClientServerCspec2.v](demo/ClientServerCspec2.v)(optimized)
    + Final theorem (Theorem 5.7 in Section 5.2): [demo/ClientServer.v](demo/ClientServer.v)

* The Mutual Sum example from CompCertM:

    We take the mutual summation example from CompCertM to test our framework. The open modules $M_C$ and $M_A$ are defined in [demo/Demo.v](DirectRefinement/Demo.html). The definition of specification $L_A$ and its refinement with $M_A$ can be found in [demo/Demospec.v](DirectRefinement/Demospec.html) and [demo/Demoproof.v](DirectRefinement/Demoproof.html) The Top-level specification of composed semantics and the refinement proof are in [demo/DemoCspec.v](DirectRefinement/DemoCspec.html) and [demo/Demotopspec.v](DirectRefinement/Demotopspec.html).

    The final theorem [topspec_correct] is also in [demo/Demotopspec.v](DirectRefinement/Demotopspec.html#topspec_correct).
    Note that our verification result of this example is slightly different from CompCertM. We build an open simulation which can take arbitrary incoming memories while
    CompCertM establish the RUSC relation (and behavior refinement) based on source-level module-local invariants about the memory.

    
* Client-Server with multiple mutual recursion:
    + Definition of client: [demo/ClientMR.v](demo/ClientMR.v)
    + Top-level specification and its refinement proof: [demo/ClientServerMRCSpec.v](demo/ClientServerMRCSpec.v)
    + Final theorem: [demo/ClientServer.v](demo/ClientServer.v) -- [`spec_sim_mr`](demo/ClientServer.v#L202)

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
