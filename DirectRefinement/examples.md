## Section 5: End-to-End Verification of Heterogenous Modules

In the section 5 of the paper, we introduce the end-to-end
verification of the client-server example (whose code and proof
structure are shown in Figure 3 and Figure 4, respectively) based on
the direct refinement. 

### Definitions of the Client-Server Example

The C or assembly code of `client.c`, `server.s` and `server_opt.s`
are shown in Figure 3 in our paper.

* `client.c` is defined in [demo/Client.v](demo/Client.v).
* `server.s` and `server_opt.s` are defined in [demo/Server.v](demo/Server.v).

### Refinement for the Hand-written Server (Section 5.1)

* (Definition 5.1) The hand-written specification ($L_S$) for the
  optimized server (i.e., `server_opt.s`) is defined by `L2` in [demo/Serverspec.v](demo/Serverspec.v#L116). The hand-written specification (not
  discussed in the paper) for `server.s` is defined by `L1` in [demo/Serverspec.v](demo/Serverspec.v#L98).
* (Theorem 5.2) It corresponds to `semantics_preservation_L2` in
  [demo/Serverproof.v](demo/Serverproof.v#L1581).
  ```
  Lemma semantics_preservation_L2:
    forward_simulation cc_compcert cc_compcert L2 (Asm.semantics b2).
  ```
  This proof is decomposed into
  [self_simulation_wt](demo/Serverproof.v#L1533) and
  [CAinjp_simulation_L2](demo/Serverproof.v#L1089) in the same file.
  For the proof of `CAinjp_simulation_L2`, the simulation relation is defined by [match_state_c_asm](demo/Serverproof.v#42).
  


### End-to-End Correctness Theorem (Section 5.2)

* Definition of the top-level specification (for optimized server `server_opt.s`) $L_{CS}$ is `top_spec2` in [demo/ClientServerCspec2.v](demo/ClientServerCspec2.v#138). The top-level specification for `server.s` is defined by `top_spec1` in [demo/ClientServerCspec.v](demo/ClientServerCspec.v#L136).
* (Lemma 5.3) It is defined by `top_simulation_L2` in [demo/ClientServerCspec2.v](demo/ClientServerCspec2.v#L832). 
  ```
  Lemma top_simulation_L2:
    forward_simulation (cc_c injp) (cc_c injp) top_spec2 composed_spec2.
  ```
  The simulation relation is defined by
  [match_state](demo/ClientServerCspec2.v#254) in the same file. For
  the same theorem for unoptimized server, we define it in
  [top_simulation_L1](demo/ClientServerCspec.v#L136).

* (Theorem 5.4) The theorem of horizontal composition corresponds to
  `compose_simulation` in
  [common/SmallstepLinking.v](common/SmallstepLinking.v#L338). The
  adequacy theorem corresponds to `asm_linking` in
  [x86/AsmLinking.v](x86/AsmLinking.v#L371).
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
* (Lemma 5.5) It corresponds to `compose_Client_Server_correct2` in [demo/ClientServer.v](demo/ClientServer.v#L42).
* (Lemma 5.6) It corresponds to `ro_injp_cc_compcert` in [demo/ClientServer.v](demo/ClientServer.v#L76).
  ```
  Lemma ro_injp_cc_compcert:
    cceqv cc_compcert (wt_c @ ro @ cc_c injp @ cc_compcert).
  ```
* (Theorem 5.7) It corresponds to `spec_sim_2` in [ClientServer.v](demo/ClientServer.v#L146).
  ```
  Theorem spec_sim_2 : forward_simulation cc_compcert cc_compcert top_spec2 (Asm.semantics tp2).
  ```
  
### Other Examples

The following examples are not discussed in our paper, because they
are more complicated than the client-server example introduced in our
paper. However, we implement and verify them to show the effectiveness of our framework.

#### Mutual Recursive Client-Server Example

We define a mutual recursive client-server example where the server
code is the same as `server.s` in [demo/Server.v](demo/Server.v) and the
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
  [demo/ClientMR.v](demo/ClientMR.v#L157).
* The definition of servers are the same as the examples (`server.s`
  and `server_opt.s`) introduced in our paper, i.e., it is defined by
  `b1` and `b2` in [demo/Server.v](demo/Server.v). Note that we
  implement the repeated invocation by directly passing the `request`
  function in `client` to the server. Thereby the server can jump to
  the call-back function (the `request` function in client) to encrypt
  the subsequent data.
* The top level specification is defined by `top_spec1` in
  [demo/ClientServerMRCSpec.v](demo/ClientServerMRCSpec.v#L150).
* The refinement between the top-level specification and composition of `client_mr.c` and `L1` is defined by `top_simulation_L1` in [demo/ClientServerMRCspec.v](demo/ClientServerMRCSpec.v#L844).
  ```
  Lemma top_simulation_L1:
  forward_simulation (cc_c injp) (cc_c injp) top_spec1 composed_spec1.
  ```
  To compose with the direct refinement, we show that the top-level
  specification is self-simulated by `ro` and `wt`. They are defined
  by `top1_ro` and `top1_wt` in [demo/ClientServerMRCspec.v](demo/ClientServerMRCSpec.v).
* The direct refinement of this example is defined by `spec_sim_mr` in
  [demo/ClientServer.v](demo/ClientServer.v#233).
  ```
  Theorem spec_sim_mr : forward_simulation cc_compcert cc_compcert (top_spec1 N) (Asm.semantics tp1).
  ```


#### Mutual Summation Example

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
* First, like what we do for the server in the above example, we define a high-level specification (called `L_A`) for `M_A`. The definition of `L_A` is in [demo/Demospec.v](demo/Demospec.v#L88) with the same name. The refinement is defined by `M_A_semantics_preservation` in [demo/Demoproof](demo/Demoproof.v). 
  ```
  Lemma M_A_semantics_preservation:
  forward_simulation cc_compcert cc_compcert L_A (Asm.semantics M_A).
  ```
  The simulation relation of this proof is defined by [match_state_c_asm](demo/Demoproof.v#L44) in the same file.
* Second, for `M_C`, we define its specification `L_C` in
  [demo/DemoCspec.v](demo/DemoCspec.v#L90). Therefore, the refinement
  between `L_C` and the semantics of `M_C` is defined by
  [cspec_simulation](demo/DemoCspec.v#L423),
  [cspec_ro](demo/DemoCspec.v#L901) and
  [cspec_self_simulation_wt](demo/DemoCspec.v#L908).
  ```
  Lemma cspec_simulation:
  forward_simulation (cc_c injp) (cc_c injp) L_C (Clight.semantics1 M_C).

  Theorem cspec_ro :
  forward_simulation ro ro L_C L_C.

  Theorem cspec_self_simulation_wt :
  forward_simulation wt_c wt_c L_C L_C.
  ```

* With the above definitions, we define a top-level specification
  called `top_spec` in [demo/Demotopspec.v](demo/Demotopspec.v#L171).
  The refinement between `top_spec` and the composition of `L_C` and
  `L_A` corresponds to [top_simulation](demo/Demotopspec.v#L592),
  [top_ro](demo/Demotopspec.v#L933) and
  [topspec_self_simulation_wt](demo/Demotopspec.v#L940).
* Finally, with the above refinements and the correctness of CompCert(O), we show the end-to-end refinement theorem in  `topspec_correct` in [Demotopspec.v](demo/Demotopspec.v#L1011).
  ```
  Theorem topspec_correct:
    forall tp M_C',
      transf_clight_program M_C = OK M_C' ->
      link M_C' M_A = Some tp ->
      forward_simulation cc_compcert cc_compcert top_spec (Asm.semantics tp).
  ```

## Reference

[^1]: Youngju Song, Minki Cho, Dongjoo Kim, Yonghyun Kim, Jeehoon Kang, and Chung-Kil Hur. 2020. CompCertM: CompCert with C-Assembly Linking and Lightweight Modular Verification. Proc. ACM Program. Lang. 4, POPL, Article 23 (Jan. 2020),31pages. https://doi.org/10.1145/3371091