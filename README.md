# Section 3 structural gradual extension (partial metatheory)

Section 3 includes structural unknown types inside arrows and unions, open gradual environments, annotations, higher-order wrapper casts, and explicit evaluation errors. Syntax is in `syntax.v`; judgments, semantics, and proofs are in `typing.v`. The static and successful dynamic gradual guarantees cover all structural source constructors. The development also proves fuel monotonicity for successes and errors, soundness and completeness against independent unbounded operational semantics, operational determinism, divergence adequacy, termination classification, and expression error/divergence approximation. Logical preservation is checked for arrow-shaped lambda descriptors and arbitrary switch descriptors, in both finite-fuel and unbounded semantics. A selected switch branch casts its binder to the lifted descriptor type before evaluating its body. Intrinsic descriptor validity, error-free progress, and full static conservativity remain open. The former closed boundary layer and its safety proofs are retained in these same two files; `gradual.v` has been removed. See [the implementation and proof guide](code/section3/GRADUAL.md) for exact statements, validation, and limitations. This extension is not a complete gradual metatheory.

General cast compatibility is also proved: `sg_cast_precision` preserves cast success under simultaneous structural target-type and runtime-value weakening, with structurally related results, including closures, wrappers, and left-biased unions. Using this result, `sg_evaluation_simulation` simultaneously proves expression and application success simulation for every target fuel budget at least as large as the precise budget. `sg_dynamic_gradual_guarantee` and `sg_application_dynamic_guarantee` give fuel-independent existential success statements; both can choose the original budget.

The logical runtime judgments include mutually inductive value/environment validity: closures carry a typed body and a typed captured environment, and wrappers contain valid callable values. `sg_finite_success_preservation` mutually proves expression logical typing and application validity; `sg_application_logical_preservation` adds the result type for logically typed arrows. Unbounded counterparts follow by operational adequacy. Branch-entry casts justify arbitrary switch bindings; the older `sg_evaluation_descriptor_safety` additionally proves uncast Int/Unit refinement. `sg_logical_safety` classifies evaluation as logically typed success, explicit error, or divergence. `sg_safe_syntax_precision` and `sg_safe_static_gradual_guarantee` show that weakening preserves this fragment. Function descriptors still have no intrinsic domain/result contract; switch binders acquire their contract through runtime casts. The outcome classification permits cast errors and uncovered switches.

`sg_exact_elaboration` relates original locally nameless `exp` terms to structural de Bruijn `sgexp` terms, including literals, null, variables, lambdas, applications, disjoint switches, union introductions, and general static subsumption. Subsumption elaborates to a checked annotation; directed compatibility `sg_con_sub` includes static subtype pairs and their precision weakenings. `sg_exact_elaboration_source` proves original typing; `sg_exact_elaboration_target` proves structural typing at the lifted type together with safe syntax. `sg_exact_elaboration_complete` proves existence of an elaboration from any original typing derivation and `sg_context_covers G Delta`, which requires an indexed slot of the same name and type for every source binding. It assumes no target or elaboration exists. The canonical context is `Delta = G`; `sg_exact_elaboration_closed` supplies a closed elaboration, target typing, and safe syntax. Completeness uses the fresh-name binder rules `sgee_abs_pick` and `sgee_switch_pick`, whose source soundness uses `sg_typing_fresh_open`; equivalence to the cofinite-only relation is not proved. Source/target evaluation correspondence and full static conservativity remain open.

`sg_static_tag_cast_total` proves that a valid value whose tag subtypes a static type can be cast successfully to that lifted type, with logical typing and tag preservation; `sg_static_subsumption_cast_total` composes this with arbitrary static subsumption. `sg_typing_fresh_open` transports source body typing between fresh binder names. For descriptors, `sg_descriptor_entry_contract` proves the contract installed by a successful tested entry cast; `sg_checked_descriptor_application` gives the result type of successful calls; `sg_descriptor_arrow_call_checks` factors a successful wrapped call into argument cast, inner application, and result cast. These results do not establish an intrinsic contract for unwrapped closure descriptors.

`sg_source_value_observation` independently relates original and runtime values: integers retain their exact payload, null corresponds to unit, and functions retain their declared arrow descriptor. `sg_source_value_observation_cast` preserves this relation through every successful cast. `sg_source_value_cast_total` proves that, for an original value typed at `A`, a valid runtime value related by this observation casts successfully to every lifted supertype `B`, preserving the observation. `sg_exact_elaboration_value_evaluation` proves that every elaboration of an original value evaluates successfully in every logically valid environment for its indexed context, producing an observed value. It covers repeated subsumption and both fresh-pick and cofinite lambda rules; function observations constrain only descriptors.

The separate compiler `sg_data_compile` has both a retained first-order correspondence and a higher-order extension. Independent source judgments `sg_ho_runs` and `sg_ho_applies` evaluate lexical closures, captured environments, arbitrary function positions, function arguments/results, switches, and source annotation boundaries. `sg_ho_compile_simulation` mutually proves expression/application simulation under the structural encoding `sg_ho_encode`. With a structurally well-formed source environment and original typing of the substituted quotation, `sg_ho_original_simulation` proves actual original beta/switch reduction to the quoted result. `sg_ho_compile_original_correspondence` pairs this original reduction with the exact unbounded target answer. These are one-way results conditional on successful checked source runs; existence of such runs for every original execution, correspondence for arbitrary exact elaborations, and full static conservativity remain open, as do target independence from fresh binder names and fresh-pick/cofinite equivalence.

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
