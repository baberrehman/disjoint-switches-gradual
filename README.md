# Section 3 structural gradual extension (partial metatheory)

Section 3 includes structural unknown types inside arrows and unions, open gradual environments, annotations, higher-order wrapper casts, and explicit evaluation errors. Syntax is in `syntax.v`; judgments, semantics, and proofs are in `typing.v`. Static subsumption and static union introductions now elaborate to `sg_coerce A B target`: erased subtype evidence that preserves the entire runtime value rather than projecting it through a target-only union check. This repairs the closed union regression: the original program and its exhibited exact elaboration both return integer `7`. General static conservativity remains a target, with function and switch boundary casts still requiring further work. See [the implementation and proof guide](code/section3/GRADUAL.md) for exact scope and validation.

General cast compatibility is also proved: `sg_cast_precision` preserves cast success under simultaneous structural target-type and runtime-value weakening, with structurally related results, including closures, wrappers, and left-biased unions. Using this result, `sg_evaluation_simulation` simultaneously proves expression and application success simulation for every target fuel budget at least as large as the precise budget. `sg_dynamic_gradual_guarantee` and `sg_application_dynamic_guarantee` give fuel-independent existential success statements; both can choose the original budget.

Public gradual typing `sgtyping` has no coercion rule. Its original structural static gradual guarantee remains proved, with every existing term-precision case retained. `sg_complete_outcome_gradual_guarantee` packages success precision, error approximation, and divergence approximation for the independent unbounded semantics; it uses explicit `sg_error` and divergence and introduces no blame labels. Fuel monotonicity, operational adequacy, determinism, divergence adequacy, and termination classification remain proved. `sg_public_logical_safety` covers publicly typed programs with the existing arrow-shaped lambda descriptor condition and valid environments; public typing itself excludes coercions. Arbitrary descriptor safety remains open.

`sg_exact_elaboration` covers every original typing rule, including arbitrary subsumption and nested union introductions. `sg_exact_elaboration_source` proves original typing; `sg_exact_elaboration_target` proves the separate `sg_compiler_typing` judgment together with `sg_elaboration_syntax`. Compiler coercions require `A <: B` and an operand certified at exactly `sg_lift A`; there is no unknown-operand precision escape or consistency rule. This is trusted compiler-only evidence, not public gradual typing or a runtime check. `sg_exact_elaboration_complete` retains existence for every original typing derivation and covering indexed context; canonical and closed corollaries remain. Compiler preservation and an SG for compiler certificates are not proved. Completeness includes cofinite and fresh-name binder rules; their equivalence and target independence from fresh-name choice remain open.

`sg_removed_coerce_rule_unsound` formally audits the removed public rule: its premises accept unit annotated with unknown as evidence for `Int <: Int`, while evaluation returns raw unit at the claimed integer type. `sg_public_rejects_coerce` and `sg_compiler_rejects_forged_evidence` reject that use in the separated judgments. `sg_compiler_coercion_preservation` proves the erased-coercion compiler preservation fragment: successful coercion evaluation returns the identical runtime value and descriptor. Preservation for compiler applications and switches remains outside this fragment.

`sg_static_tag_cast_total` proves that a valid value whose tag subtypes a static type can be cast successfully to that lifted type, with logical typing and tag preservation; `sg_static_subsumption_cast_total` composes this with arbitrary static subsumption. `sg_typing_fresh_open` transports source body typing between fresh binder names. For descriptors, `sg_descriptor_entry_contract` proves the contract installed by a successful tested entry cast; `sg_checked_descriptor_application` gives the result type of successful calls; `sg_descriptor_arrow_call_checks` factors a successful wrapped call into argument cast, inner application, and result cast. `sg_subtype_closed_descriptor_contract_total` extends this contract to every `A <: B`, including arrow and union subtyping, while preserving the runtime descriptor. These results do not establish an intrinsic contract for unwrapped closure descriptors.

`sg_source_value_observation` independently relates original and runtime values: integers retain their exact payload, null corresponds to unit, and functions retain their declared arrow descriptor. `sg_source_value_observation_cast` preserves this relation through every successful cast. `sg_source_value_cast_total` proves that, for an original value typed at `A`, a valid runtime value related by this observation casts successfully to every lifted supertype `B`, preserving the observation. `sg_exact_elaboration_value_evaluation` proves that every elaboration of an original value evaluates successfully in every logically valid environment for its indexed context, producing an observed value. It covers repeated subsumption and both fresh-pick and cofinite lambda rules; function observations constrain only descriptors.

The separate compiler `sg_data_compile` has first-order and higher-order correspondence results. Independent `sg_ho_runs` and `sg_ho_applies` evaluate lexical closures, captured environments, computed function positions, arguments/results, switches, and checked source boundaries. `sg_ho_compile_simulation`, `sg_ho_original_simulation`, and `sg_ho_compile_original_correspondence` retain their existing conditional statements. They require successful checked source runs and do not establish their existence for every original execution. Their source checks remain left biased; the exact elaboration repair does not change this separate compiler.

`sg_original_execution_decomposition` decomposes every finite original reduction ending in a value into `sg_original_evaluates`; `sg_original_evaluation_reduction` proves the converse for typed terms. These establish original execution decomposition, not existence of checked higher-order runs. The predicate `sg_ho_shape` excludes boundaries around data but does not establish function boundary contracts.

The boundary lemmas `sg_union_trap_source_boundary`, `sg_union_trap_target_boundary`, and `sg_union_trap_boundary_operational_error` exhibit a limitation of left-biased union checks. Although `Int → Int` subtypes `(Unit → Unit) | (Int → Int)` and the two arms are disjoint, checking an integer identity closure at this union installs a `Unit → Unit` wrapper; calling that wrapper with integer `7` returns an operational error. This proves a boundary-level obstruction to deriving call compatibility from subtype membership and cast success alone.

`sg_union_trap_exact_elaboration` checks the repaired target under empty contexts: switch the integer identity against these arrow descriptors, return `0` on the left, and apply the right binder to `7`. Its union introduction and subsequent subsumption both use erased evidence. `sg_union_trap_source_termination` proves original reduction to `7`; `sg_union_trap_elaborated_success` proves target success at fuel `8`, and `sg_union_trap_elaborated_operational_success` proves unbounded success with the same integer. The obsolete whole-elaboration error/no-success and universal-refutation theorems have been removed. Raw projection obstruction theorems remain true.

The separated development passed direct Docker `make`, `coqchk -silent -R . Top Top.typing`, and assumption audits with a read-only source mount and temporary build copy. Public SG, complete outcome DGG, erased-coercion preservation, subtype-closed descriptor contracts, compiler rejection of forged evidence, and the repaired regression are checked. No new axioms or admitted proofs were added. Full compiler preservation for applications and switches, general exact-elaboration execution correspondence, and intrinsic unwrapped closure contracts remain explicit obligations; the left-biased gradual boundary obstruction is retained and documented.

# Artifact: Union Types with Disjoint Switches, Disjoint Functions, and gradual typing

Title of the ECOOP 2022 paper: Union Types with Disjoint Switches

## Overview: What does the artifact comprise?

This artifact contains the mechanical formalization of the extended
calculi of adding disjoint function types associated with the paper
Union Types with Disjoint Switches.
All of the metatheory has been formalized in Coq theorem prover.
We provide a docker image as well the code archive.

We claim the functional, reusable, and available badges.

## For authors claiming a functional or reusable badge: What are claims about the artifact’s functionality to be evaluated by the committee?

All of the metatheory and theorems stated in paper can be found in the artifact.

**Note:** Please follow the steps under *Getting Started* to
access the artifact and look into the directory hierarchy.

### Code Structure:

There are 5 sub-folders in the artifact in *code* folder:
1) section3
2) section3_domain
3) section4
4) section51
5) section52

Each folder contains Coq formalization for a variant of our calculus discussed in paper.
Organization of folders is:

|  Folder          |   System                                     | Reference in paper       |
| :--------------- | :------------------------------------------- | :----------------------- |
| section3         | Union calculus                               | Discussed in section 3   |
| section3_domain  | Section 3 + domain-based function disjointness | Extension of section 3 |
| section4         | Union calculus with various advance features | Discussed in section 4   |
| section51        | An extension with parametric polymorphism    | Discussed in section 5.1 |
| section52        | An extension with generalized subtyping      | Discussed in section 5.2 |

**Note:** Note that section 5 in extended version of the paper
corresponds to appendix A in ECOOP 2022 publication.

#### section3
1. syntax.v contains syntax and disjointness properties of the union calculus.
2. typing.v contains semantics and properties related to type-safety and determinism.

Important lemmas/theorems in folder *section3* and
reference in *section 3* in the paper:


|  Lemma in Paper  |   Coq file   |     Lemma(s) in Coq File             |
| :--------------- | :----------- | :----------------------------------- |
| Lemma 3          | syntax.v     | BL_soundness and BL_completeness     |
| Theorem 5        | syntax.v     | Disj_soundness and Disj_completeness (*a ⇔ *s1*) |
| Theorem 7        | typing.v     | preservation                         |
| Theorem 8        | typing.v     | progress                             |
| Theorem 10       | typing.v     | determinism                          |
| Lemma 12         | syntax.v     | dropped: *s ⇔ *s1 no longer holds    |
| ad_arrow (new)   | syntax.v     | B1 *a B2 ⇒ (A1→B1) *a (A2→B2)     |


#### section3_domain
Section 3 plus `ad_arrow_dom`: disjoint domains imply disjoint function types.
`*s2` is sound and complete for the algorithm (`*a ⇔ *s2`): arrows overlap
iff domains and ranges both overlap, and inhabitation of `A→B` follows the
range only. `typeof` uses `*s2`. A value can still inhabit both branches
(`⊤→Int` subtypes both `Int→Int` and `Unit→Int`), so the right branch steps
only when the runtime tag is not a subtype of the left.

|  Lemma                 |   Coq file   |     Lemma(s) in Coq File             |
| :--------------------- | :----------- | :----------------------------------- |
| ad_arrow_dom (new)     | syntax.v     | A1 *a A2 ⇒ (A1→B1) *a (A2→B2)     |
| DisjSpec2 / *s2        | syntax.v     | domain+range overlap; *a ⇔ *s2     |
| Disj_equiv2            | syntax.v     | *a ⇔ *s2 (sound + complete)        |
| sub_dec                | syntax.v     | subtyping is decidable               |
| arrow_dom_unsound      | syntax.v     | domain rule is not *s1-sound         |
| s2_common_value        | typing.v     | one value can inhabit both *s2 branches |
| step_typeofr           | typing.v     | right branch only if tag not <: left |
| Disj_completeness      | syntax.v     | *s1 ⇒ *a still holds               |
| Theorem 7 / 8 / 10     | typing.v     | preservation / progress / determinism |


#### section4
1. disjointness.v contains disjointness properties of the
   union calculus with intersection types, nominal types and distributive subtyping.
2. typing.v contains semantics and properties related to type-safety and determinism.
3. equivalence.v contains distributive subtyping.

Important lemmas/theorems in folder *section4* and
reference in *section 4* in the paper:


|  Lemma in Paper  |   Coq file     |   Lemma(s) in Coq File               |
| :--------------- | :------------- | :----------------------------------- |
| Lemma 13         | equivalence.v  | algo_sub_arrow_inv                   |
| Lemma 14         | equivalence.v  | dsub2asub                            |
| Lemma 15         | equivalence.v  | decidability                         |
| Theorem 18       | disjointness.v | Disj_soundness and Disj_completeness (FunRange / range rule) |
| Lemma 19         | disjointness.v | elem_in_findsubtypes_sub             |
| Lemma 20         | disjointness.v | ord_in_findsubtypes                  |
| Theorem 21       | typing.v       | preservation                         |
| Theorem 22       | typing.v       | progress                             |
| Theorem 23       | typing.v       | determinism                          |


**Note:** Note that section 5 in extended version of the paper
corresponds to appendix A in ECOOP 2022 publication.

#### section51
1. syntax.v contains syntax and disjointness properties of the
   union calculus with parametric polymorphism, intersection types
   and nominal types.
2. typing.v contains semantics and properties related to type-safety and determinism.


Important lemmas/theorems in folder *section51* and
reference in *section 5.1* in the paper:


|  Lemma in Paper  |   Coq file     |   Lemma(s) in Coq File  |
| :--------------- | :------------- | :---------------------- |
| Lemma 25         | typing.v       | disj_subst              |
| Lemma 26         | typing.v       | disj_narrowing          |


#### section52
1. syntax.v contains syntax and disjointness properties of the
   union calculus with intersection types, nominal types and general subtyping rule.
2. typing.v contains semantics and properties related to type-safety and determinism.

Important lemmas/theorems in folder *section52* and
reference in *section 5.2* in the paper:


|  Lemma in Paper  |   Coq file     |   Lemma(s) in Coq File  |
| :--------------- | :------------- | :---------------------- |
| Lemma 27         | syntax.v       | bot_sub_all             |
| Lemma 28         | syntax.v       | disj_bot_like           |



## For authors claiming a reusable badge: What are the authors' claims about the artifact's reusability to be evaluated by the committee?

More features can be added in the metatheory. For example, merge operator
and disjoint intersection types. This is also discussed in Section 6
in the paper.

### Extension: disjoint function types

The published development treated every function type as sharing the
ordinary witness `⊤ → ⊥`, so two arrows were never disjoint. This
artifact now uses:

1. Church-style lambdas `e_abs A B e` (`λ(x:A):B. e`) with
   `findtype (e_abs A B e) (A → B)`.
2. Ordinary arrows only when the range is ordinary
   (`Ord (A → B)` requires `Ord B`).
3. The algorithmic rule `B1 * B2 ⇒ (A1 → B1) * (A2 → B2)`,
   implemented by peeling `FunRange` (section 4 / 5.2) and by
   `ArrowRanges` (section 5.1).

Official disjointness is ordinary-type disjointness (`*s1` / `DisjSpec`).
Lemma 12 of the paper (`*s1 ⇔ *s`) no longer holds, because `⊤ → ⊥`
is a common subtype of every pair of arrows but is not ordinary.
Domain-based disjointness is unsound under contravariant arrow
subtyping (`⊤ → Y` inhabits both sides whenever `Y` inhabits both
ranges).

## For authors claiming an available badge

We agree to publish under a Creative Commons license on DARTS.

## Artifact Requirements

We tested all the Coq files using Coq version 8.13.1. Please use same version for the sake
of consistency.

Coq TLC and Coq Metatheory libraries are also required to run the artifact.


## Getting Started

We provide two alternatives to run the artifact:
1) Docker Image
2) Build From Scratch

# 1) Docker Image #

This is the easiest way to run the artifact.
The `Dockerfile` in this repository installs Coq 8.13, TLC, and Metalib.

Build and start the image from the repository root:

1. `$ docker build -t disjoint-switches-functions .`
2. `$ docker run --rm -it disjoint-switches-functions`

**Note:** Please note that **$** symbol appearing in
the beginning is not a part of the command.


The artifact is located in the directory: */home/coq/code*

`$ cd /home/coq/code`

There are 4 folders in the artifact, with make file in each.

1. **section3** → Discussed in section 3 in paper
2. **section4** → Discussed in section 4 in paper
3. **section51** → Discussed in section 5.1 in paper
4. **section52** → Discussed in section 5.2 in paper

Go to each folder and run make:

### section3

1. `$ cd /home/coq/code/section3`
2. `$ make`

### section3_domain

1. `$ cd /home/coq/code/section3_domain`
2. `$ make`

### section4

1. `$ cd /home/coq/code/section4`
2. `$ make`

Note that compilation of equivalence.v takes a few minutes
to complete.

### section51

1. `$ cd /home/coq/code/section51`
2. `$ make`

### section52

1. `$ cd /home/coq/code/section52`
2. `$ make`

Please feel free to go through the code in each section.
**vim** and **cat** commands are available to look into the files.
Recommended way to look into the files is by downloading the
code archive from the given git repo.

This completes the evaluation of artifact following docker image.


# 2) Build from Scratch #

This section explains how to build the artifact from scratch.

### Prerequisites
We tested all the Coq files using Coq version 8.13.1. Please use same version for the sake
of consistency. We recommend installing Coq using the opam package installer.

`$ opam install coq.8.13.1`

Refer to this link for more information and installation
steps: https://coq.inria.fr/opam-using.html

### Required Libraries

Coq TLC and Coq Metatheory libraries are required to compile the code.
Next, we explain briefly how to install each.

TLC library can also be installed using the opam package installer.

Run the following commands one by one to install TLC by opam package installer:

1. `$ opam repo add coq-released http://coq.inria.fr/opam/released`
2. `$ opam install coq-tlc.20210316`

Please refer to this link for detailed compilation and installation of Coq TLC:
https://github.com/charguer/tlc/tree/20210316

Metatheory can be installed by following the instructions at this link:
https://github.com/plclub/metalib. Metatheory library from branch
**coq8.10** must be installed.


### Getting the files
Use the following commands to clone our git repo.
Please note that **$** symbol is not a part of command:

`$ git clone https://github.com/baberrehman/disjoint-switches.git`

You should be able to see all the Coq files inside folder *code*
after cloning the repo. Alternatively you can download the zip file
from repo and you should be able to see all the Coq files after unzipping it.

There are 4 sub-folders in the *code* folder, with make file in each.

1. **section3** → Discussed in section 3 in paper
2. **section4** → Discussed in section 4 in paper
3. **section51** → Discussed in section 5.1 in paper
4. **section52** → Discussed in section 5.2 in paper

**Note:** Please make sure to run `$ eval $(opam env)` if Coq
is installed using opam. This command can be skipped otherwise.

Open the terminal in each folder and run make:

### section3

1. `$ eval $(opam env)` (optional)
2. `$ make`

Similarly, section4, section51 and section52 can be compiled
by opening the terminal in each respective folder and
running the `make` command.

Please feel free to go through the code in each section.
This completes the evaluation of artifact following build from scratch.
