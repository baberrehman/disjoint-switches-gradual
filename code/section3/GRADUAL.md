# Section 3 gradual extension

All syntax is in `syntax.v`; typing, evaluation, and proofs are in `typing.v`.
The original static calculus remains available. No new axiom or admitted proof
is introduced by the static evidence repair.

## Static evidence and gradual projection

`sg_coerce A B e` is a trusted compiler-only node. Public `sgtyping` has no
rule for it. The separate `sg_compiler_typing` judgment requires `A <: B`
and compiler typing of the operand at exactly `sg_lift A`, and concludes
compiler typing at `sg_lift B`. Its other rules certify exact variables,
data, source-descriptor lambdas, applications, and switches; there is no
annotation/consistency rule or precision escape to unknown.

`sg_removed_coerce_rule_unsound` proves that the removed public rule's
premises accept `sg_ann sg_null sg_any` as evidence for `Int <: Int`, yet
erasure returns unit, which fails integer runtime typing.
`sg_public_rejects_coerce` excludes every direct public coercion typing;
`sg_compiler_rejects_forged_evidence` rejects this concrete forgery in the
compiler judgment. Compiler typing is a syntactic certificate. The erased-
coercion preservation fragment is proved by
`sg_compiler_coercion_preservation`: successful coercion evaluation returns the
identical runtime value and descriptor. Preservation for compiler applications
and switches remains outside this fragment.

Term precision still fixes both endpoints and recursively relates bodies;
every existing precision case remains available. Arbitrary operand weakening
need not preserve compiler certificates, and no compiler SG is claimed.

Evaluation erases this evidence: at successor fuel, evaluating the coercion
evaluates its body at predecessor fuel and returns exactly the same value.
The independent operational expansion similarly requests evaluation of the
body and returns its result. No union arm is selected and no wrapper is added.

`sg_exact_elaboration` now uses this evidence for arbitrary static subsumption
and both static union introductions. This covers nested unions and general
subtyping endpoints. The runtime equations `sg_static_coercion_erasure`,
`sg_static_coercion_success`, and `sg_nested_union_evidence` establish erasure,
preservation of successful evaluation, and erasure of nested union evidence.
These equations hold independently of typing; compiler typing checks exact
operand types and evidence endpoints separately.

Gradual projection remains implemented by `sg_cast`. Its union case is left
biased, and arrow casts may add delayed wrappers. Explicit gradual annotations
and gradual union introductions still use those casts. Closure domain/range
and switch binder/result boundaries also retain their existing casts. Runtime
descriptors remain immutable, including through successful casts.

## Gradual guarantees and operational results

`sg_static_gradual_guarantee` retains the original structural statement for
public `sgtyping`. Its coercion precision case has no public typing premise
and is discharged by inversion. It is not a guarantee for compiler typing.
`sg_evaluation_simulation`, `sg_dynamic_gradual_guarantee`, and
`sg_application_dynamic_guarantee` retain their general successful-evaluation
statements, now including coercions. `sg_complete_outcome_gradual_guarantee`
combines success precision with `sg_error` and divergence approximation for
all three outcomes. No blame labels are needed because error is an explicit
semantic result. No existing precision case was removed.

The dynamic guarantee relates successful evaluations under precision; it is
not a universal termination or successful-source-execution theorem.
The fuel monotonicity and expansion/evaluation proofs extend to the erased
constructor. Unbounded operational adequacy, determinism, and the existing
error/divergence approximation results remain checked.

## Logical safety scope

`sg_safe_syntax` excludes coercions explicitly. The existing exact-boundary
logical relation uses exact arrow annotations and is not closed under erased
static subtyping. Consequently the checked-syntax finite-success preservation
and logical safety results do not cover every repaired exact elaboration.
Their precision closure remains proved. Public SG excludes compiler nodes
through its typing premise; successful DGG includes them without requiring
typing or claiming preservation of compiler certificates.

`sg_elaboration_syntax` separately describes elaboration targets and permits
coercions recursively. It enforces the existing descriptor shape restrictions
without claiming the checked-boundary logical safety invariant.
`sg_subtype_closed_descriptor_contract_total` proves that a valid value whose
tag is below `A` can be cast to every `B` with `A <: B`, including arrow and
union cases, while retaining logical typing and its descriptor. The contract
is for the successfully installed boundary; it is not an intrinsic claim
about an arbitrary unwrapped closure descriptor.

For publicly typed terms, `sg_public_descriptor_safety` proves that this
descriptor-shape predicate implies `sg_safe_syntax`: there are no typed
coercions to exclude. `sg_public_logical_safety` therefore states logical
safety using public typing, descriptor shape, and valid environments. It allows
explicit runtime errors and divergence. Safety for arbitrary lambda descriptors
and safety for compiler targets remain unproved; this is not full-calculus
typing safety.

## Exact elaboration and source values

`sg_exact_elaboration_source` retains source typing soundness.
`sg_exact_elaboration_target` proves `sg_compiler_typing` at the lifted static type
and `sg_elaboration_syntax`. `sg_exact_elaboration_complete` covers every
original typing rule under a covering context, including arbitrary static
subsumption; its canonical and closed corollaries remain available.

`sg_exact_elaboration_value_evaluation` has no `sg_safe_syntax` premise:
given an exact elaboration, a valid target environment, and a source value,
there exist fuel and a successful target value related by
`sg_source_value_observation`. Static injections and subsumption recurse and
return the same runtime value. Function observation records the descriptor;
it does not establish a relation between function bodies or environments.
The existing cast observation and immediate-totality lemmas remain independent
results about casts.

The relation retains cofinite and fresh-pick binder constructors. This is the
unrestricted exact-elaboration correspondence currently proved for source
values. General beta/switch execution correspondence for arbitrary exact
elaborations is deliberately narrowed to the separately verified `sg_ho_*`
compiler conditions, because the remaining gradual boundary casts are left
biased. Equivalence between binder presentations and independence of the
chosen fresh name remain separate proof obligations.

## Static union regression

The regression combines `Unit -> Unit` and `Int -> Int` in a union, injects an
integer identity function into the right arm, and switches on its descriptor.
The right branch applies the identity to `7`. A left-biased runtime projection
can install the wrong function wrapper even though the immutable descriptor
later selects the right switch branch.

The repaired exact elaboration carries erased evidence for the right injection
and subsequent subsumption. `sg_union_trap_exact_elaboration` witnesses that
elaboration. Original typing and reduction to integer `7` remain proved.
`sg_union_trap_elaborated_success` proves target evaluation at fuel 8 returns
`sg_done (sg_vint 7)`; `sg_union_trap_elaborated_operational_success` proves the
corresponding unbounded operational run.

The retained raw boundary obstruction lemmas describe gradual projection and
the independent checked compiler. They do not refute the repaired exact
elaboration. The obsolete whole-elaboration error and universal-preservation
refutation results were removed.

## Independent compilers and remaining obligations

The data compiler and checked higher-order compiler remain separate
translations. Their conditional correspondences retain explicit successful
source-run premises. Original finite execution decomposition is also retained;
it does not supply unconditional correspondence for repaired exact elaboration.

Full static conservativity remains open. Function and switch boundary casts
can still project static unions and need further analysis or repair. A logical
relation closed under static subtyping, execution correspondence for general
applications and switches, and stronger function observations remain necessary
for a full proof. Intrinsic descriptor validity is also unproved. Neither a
universal success-preservation theorem nor its negation is claimed for the
repaired relation.

## Validation

Validation uses direct `make` and `coqchk -silent -R . Top Top.typing`
with Coq 8.13.2 in `disjoint-switches-functions:latest`, initialized
with `eval "$(opam env)"`, with a read-only source mount and a temporary build
copy. Direct build exit status was checked because the artifact wrapper can
mask failures.

`Print Assumptions` audited public SG/logical safety, successful DGG,
elaboration target/completeness, the removed-rule counterexample, compiler
rejection of forged evidence, and finite/unbounded regression success.
Public SG and compiler rejection are closed under the global context.
The other audited results inherit only the existing TLC assumptions
`LibAxioms.prop_ext`, `LibAxioms.indefinite_description`, and
`LibAxioms.fun_ext_dep`. Original source preservation/substitution and results
depending on them can additionally inherit `JMeq.JMeq_eq`.

<!-- Historical material below is superseded by the repaired scope above.
In particular, older claims refuting the current exact elaboration do not apply.

# Section 3 gradual development: repaired static evidence

All syntax is in `syntax.v`; judgments, evaluators, and proofs are in
`typing.v`. There is no additional gradual module. This is a partial gradual
metatheory: structural SG and successful DGG are proved; full static execution
conservativity remains a target.

## Static evidence and gradual projection

The original obstruction came from conflating static subsumption with gradual
projection. A target-only cast of an `Int -> Int` closure to
`(Unit -> Unit) | (Int -> Int)` chooses the left callable arm and installs a
`Unit -> Unit` wrapper. Although the runtime descriptor remains `Int -> Int`,
calling that wrapper on integer `7` fails. Tag preservation and immediate cast
success do not imply success of future calls.

`sg_coerce A B e` now records static subtype endpoints. Its typing rule requires
`A <: B`, `sgprecision (sg_lift A) X`, and `sgtyping G e X`, and concludes
`sgtyping G (sg_coerce A B e) (sg_lift B)`. The precision premise supports
recursive weakening of the body in structural SG. This is trusted static
evidence, not a dynamically checked boundary or a runtime proof object.

Evaluation consumes one fuel layer and evaluates the body. It preserves the
complete returned value, including closure bodies, captured environments, and
existing wrappers. It does not select a union arm or create a wrapper.
Independent operational expansion makes the corresponding evaluation request.

Exact elaboration uses this node at all three static evidence sites:

- `sgee_sub`: arbitrary `A <: B` becomes `sg_coerce A B target`.
- `sgee_inl`: union introduction becomes `sg_coerce A (t_union A B) target`.
- `sgee_inr`: union introduction becomes `sg_coerce B (t_union A B) target`.

These rules cover general and nested union subsumption, not only reflexive
subsumption or one chosen regression. An injection whose selected arm is itself
a union also preserves the underlying value.

Explicit gradual `sg_ann`, `sg_inl`, and `sg_inr` retain their checked runtime
semantics. `sg_cast` remains left biased for unions and installs delayed arrow
wrappers. Function argument/result checks and switch binder/result checks also
remain. This distinction repairs the static evidence sites without asserting
that every remaining boundary already implements static subtyping correctly.

`sg_static_coercion_erasure` proves, for all endpoints, bodies, environments,
and fuel, that evaluation at successor fuel equals evaluation of the body at
the predecessor fuel. `sg_static_coercion_success` gives the success corollary.
`sg_nested_union_evidence` proves that a right union introduction followed by
arbitrary further static evidence equals evaluation of the original body after
two fuel layers. These operational equations need no subtype premise; typing
separately validates the evidence endpoints. Preserving the identical value
also preserves all subsequent applications of that value.

## Gradual guarantees and operational results

Structural precision permits unknown types inside arrows and unions. Open
environments weaken pointwise. Existing expression precision constructors are
retained. The new `sg_ep_coerce` fixes both static endpoints and recursively
relates the two bodies; the endpoint policy follows the fixed static descriptor
metadata policy. It imposes no restriction on existing precision cases.

- `sg_static_gradual_guarantee`: a precision weakening of a typed expression
  in a precision weakening of its environment has a type less precise than the
  original type. The coercion case composes the body's precision witnesses.
- `sg_cast_precision`: successful casts survive simultaneous structural
  target-type and runtime-value weakening, including closures, wrappers, and
  left-biased unions.
- `sg_evaluation_simulation`: expression and application successes simulate
  under precision for every target fuel budget at least as large as the precise
  budget. The coercion case uses the recursive expression simulation.
- `sg_dynamic_gradual_guarantee` and `sg_application_dynamic_guarantee`:
  successful precise executions have related successful weaker executions;
  the same fuel budget can be chosen. These remain general successful DGGs,
  not only guarantees for exact elaborations or checked-safe syntax.

Fuel monotonicity for successes and errors, independent unbounded semantics
(`sg_runs` / `sg_plan_runs`), operational adequacy, determinism, divergence
adequacy, termination classification, and error/divergence approximation remain
proved. Coercions are covered by evaluator monotonicity and operational
expansion/adequacy. The DGG makes no claim that all typed programs succeed.

## Logical safety: explicit scope change

Runtime logical validity tracks typed closure bodies and captured environments;
wrappers contain valid callable values. `sg_runtime_type` uses exact arrow
annotations, so it cannot directly validate a value whose static supertype
has different arrow endpoints after erased coercion.

Consequently `sg_safe_syntax` explicitly excludes `sg_coerce`. This is a
restriction of the logical-preservation fragment, and is not a weakening of
term precision or of the general SG/DGG statements. Arrow-shaped lambda
descriptors remain required. Arbitrary switch descriptors are supported through
checked branch-entry casts.

`sg_finite_success_preservation`, `sg_application_logical_preservation`, their
unbounded counterparts, and `sg_logical_safety` retain this checked-boundary
scope. `sg_safe_syntax_precision` and `sg_safe_static_gradual_guarantee` preserve
that fragment. Logical safety allows explicit errors and uncovered switches;
function descriptors alone do not establish intrinsic domain/result contracts.

`sg_elaboration_syntax` is a separate recursive descriptor-shape predicate that
permits static coercions. It does not imply checked-boundary logical safety.
Extending preservation to repaired elaborations needs a subtype-closed logical
relation or another semantic argument.

## Exact elaboration and source values

`sg_exact_elaboration G Delta e target A` relates original locally nameless
terms to structural de Bruijn terms. `Delta` supplies indexed positions for free
names. The relation includes literals, null, variables, lambdas, applications,
switches, union introductions, and general subsumption, with both cofinite and
fresh-name binder rules.

- `sg_exact_elaboration_source` proves original `typing G e A`.
- `sg_exact_elaboration_target` proves target typing at `sg_lift A` and
  `sg_elaboration_syntax target`. It no longer claims `sg_safe_syntax target`.
- `sg_context_covers G Delta` requires a slot with the same name and type for
  every original binding. It assumes neither elaboration nor target typing.
- `sg_exact_elaboration_complete` gives an elaboration for every original
  typing derivation and covering indexed context, including every subsumption
  rule. Canonical coverage uses `Delta = G`; the closed corollary gives target
  typing and `sg_elaboration_syntax` under empty contexts.

Fresh-name source soundness uses `sg_typing_fresh_open`, original weakening,
and substitution. Equivalence of fresh-name and cofinite-only elaboration, and
independence of the target from fresh-name choices, remain open.

`sg_source_value_observation` preserves exact integer payloads, null/unit
identity, and a lambda's declared arrow descriptor. Its function case does not
relate bodies or captured environments. Successful casts preserve this
observation. `sg_source_value_cast_total` proves immediate cast success for
already valid observed values at static supertypes; it does not establish future
call success.

`sg_exact_elaboration_value_evaluation` retains its unrestricted statement:
every elaboration of an original value, in every logically valid environment
for its indexed context, has a finite successful evaluation producing an
observed value. It requires no `sg_safe_syntax` premise. Repeated subsumption,
both union introductions, and both lambda binder rules are included. This is
value evaluation, not general beta/switch execution correspondence.

## Regression

The closed source program switches the integer identity between the disjoint
`Unit -> Unit` and `Int -> Int` descriptors, returns `0` on the left, and
applies the right binder to `7` on the right.

`sg_union_trap_exact_elaboration` checks an elaboration whose right union
introduction and following reflexive union subsumption now both carry erased
evidence. Original typing, closedness, and target typing are proved.
`sg_union_trap_source_termination` proves original reduction to integer `7`.
`sg_union_trap_elaborated_success` proves target evaluation at fuel `8` returns
`sg_vint 7`; `sg_union_trap_elaborated_operational_success` proves the same
unbounded answer.

The obsolete whole-elaboration error, no-success, and universal-refutation
theorems have been removed. `sg_union_trap_source_boundary`,
`sg_union_trap_target_boundary`, and
`sg_union_trap_boundary_operational_error` still prove the raw left-biased
projection obstruction. Their statements concern gradual projection and the
independent checked compiler, not the repaired evidence sites.

## Independent compilers and original execution

`sg_source_data_runs` supplies independent first-order source semantics;
`sg_data_compile_evaluation` and `sg_data_compile_operational` preserve its
successful answers exactly. `sg_data_instantiate_open` bridges indexed source
environments to original opening. `sg_source_data_runs_original` and
`sg_data_compile_original_correspondence` pair target success with actual
original reduction under data-environment and original-typing premises.

The higher-order extension has lexical source closures, captured environments,
computed function positions, function arguments/results, switches, and delayed
source boundaries. `sg_ho_check` retains left-biased source checks.
`sg_ho_check_encoding` proves check agreement; `sg_ho_compile_simulation` and
its operational corollary preserve successful `sg_ho_runs` / `sg_ho_applies`
derivations under `sg_ho_encode`. Quotation erases source boundaries.
`sg_ho_original_simulation` and `sg_ho_compile_original_correspondence` require
well-formed environments/arguments and original typing of quotations, and prove
original reduction together with target execution.

These compiler results are conditional on successful checked source runs.
Existence of such runs for every original successful execution is unproved.
They concern a separate compiler, not arbitrary exact elaborations.
`sg_original_execution_decomposition` and `sg_original_evaluation_reduction`
connect finite original reductions and independent original big-step evaluation;
they do not supply the missing checked runs. `sg_ho_shape` excludes data
boundaries but does not prove function domain/result contracts.

`sg_descriptor_entry_contract`, `sg_checked_descriptor_application`, and
`sg_descriptor_arrow_call_checks` certify installed checked boundaries.
`sg_static_tag_cast_total` and `sg_static_subsumption_cast_total` establish
immediate cast totality with explicit tag/subtype premises. None supplies
intrinsic closure descriptor contracts or general future-call nonfailure.

The retained closed `gtyp` / `gexp` layer includes `g_embed`, `g_inject`,
`g_project`, `g_pack`, and `g_error`. Its original preservation, progress,
safety, determinism, embedding, tag-preservation, and roundtrip results remain.
Those results concern `gtyping`, not structural `sgtyping`.

## Remaining obligations

Full static conservativity requires execution correspondence for every relevant
static elaboration, with related function bodies and environments. Function
argument/result and switch binder/result boundaries still invoke target-only
casts; nested unions at these boundaries require analysis and possibly further
repair. The current success regression and erased-evidence equations do not
settle those sites. A subtype-closed logical relation must also replace or
extend exact-boundary preservation for coercions. Fresh-name independence,
fresh-pick/cofinite equivalence, and existence of general checked compiler runs
remain separate obligations. No universal success-preservation theorem is
claimed for the repaired relation, nor is its negation claimed.

## Validation

The repair passed two direct `make` runs with zero failed proof-repair builds
in this round. The second run included both static union introduction changes
and unrestricted source-value evaluation. `coqchk -silent -R . Top Top.typing`
passed. Validation used Coq 8.13.2 in
`disjoint-switches-functions:latest`, `eval "$(opam env)"`, a read-only source
mount, and a temporary copy containing the `.v` files and Makefile. No build
products were written into the source directory. Direct `make` exit status is
used because the artifact's wrapper script can mask failures.

`Print Assumptions` audited SG, successful DGG, elaboration completeness,
unrestricted source-value evaluation, evidence erasure, nested union evidence,
and finite/unbounded repaired regression success. SG is closed under the global
context. The other audited results inherit only the existing TLC assumptions
`LibAxioms.prop_ext`, `LibAxioms.indefinite_description`, and
`LibAxioms.fun_ext_dep`. The original source metatheory and results depending
on its preservation/substitution can additionally inherit `JMeq.JMeq_eq`.
No axiom, parameter, or admitted proof was introduced by this repair.# Section 3 structural gradual extension

This is a checked structural extension with static and successful dynamic gradual-guarantee proofs for every source constructor, unbounded operational adequacy, error/divergence approximation, and logical preservation for arrow-shaped lambda descriptors and arbitrary switch descriptors. It is not a full gradual metatheory: intrinsic descriptor validity remains unproved, and the closed counterexample below refutes preservation of original successful execution by arbitrary exact elaborations. Full static conservativity in that form is false under the current definitions. All syntax is in `syntax.v`; all typing, evaluation, and proofs are in `typing.v`. The original static calculus and its proofs remain available. The former `gradual.v` definitions, proofs, and examples have been integrated into these two files.

## Structural language

`sgtyp` has unknown (`sg_any`), Top, Int, Bottom, Unit, arrows, and unions. Unknown may occur at any depth. `sg_any` and `sg_top` are distinct constructors. The relation named `sgconsistent` is directed compatibility: it includes unknown compatibility, structural arrow/union compatibility, and `sg_con_sub`. The latter accepts `X` as compatible with `Y` whenever static types `A <: B` satisfy `sgprecision (sg_lift A) X` and `sgprecision (sg_lift B) Y`. In particular, Int is compatible with Top. This precision-closed extension supports checked annotations for arbitrary static subsumption; it is not asserted to be symmetric.

`sgexp` includes de Bruijn variables, literals, unit, annotated lambdas, applications, explicit annotations, explicit left/right union introductions, and disjoint switches. `sgtyping` uses arbitrary lists of gradual types, including unknown entries. Closures capture runtime environments. The examples `sg_open_unknown`, `sg_open_evaluation`, and `sg_nested_unknown` exercise open lookup and nested unknown annotations.

Each lambda carries a separate static descriptor `D`, in addition to gradual domain/result annotations. Switch descriptors are also static. `sgterm_precision` holds these descriptors fixed while allowing structural precision changes to gradual annotations and branch bodies. This choice preserves observable switch tests: erasing an observable function descriptor could change which branch executes. `sg_cast_preserves_descriptor` proves every successful cast retains the descriptor, including through wrappers. The current typing rule does not enforce agreement between a closure's descriptor and its gradual annotations; descriptors must not be interpreted as a proved runtime typing invariant.

## Evaluation and casts

`sg_union_trap_disjoint` proves that `Unit → Unit` and `Int → Int` are
semantically disjoint. `sg_union_trap_source_boundary` proves both the
right arm's subtype membership in their union and the source check's selection
of a `Unit → Unit` boundary around the integer identity closure; checking
integer `7` against that boundary's domain fails. The target counterpart
`sg_union_trap_target_boundary` proves that the lifted union cast installs the
same wrapper and `sg_apply 5` returns `sg_error` on integer `7`.
`sg_union_trap_boundary_operational_error` establishes the corresponding
independent operational application error through adequacy.

The closed typed program below turns these boundary facts into a checked
counterexample to success preservation for arbitrary exact elaborations.
Subtype membership, disjointness, quotation preservation, and immediate cast
totality do not establish compatibility of later calls. Reconstructing checked
source runs from all terminating original executions remains open; universal
success preservation for the current exact-elaboration relation is false.
The source boundary theorem is closed under the global context;
disjointness uses TLC propositional extensionality, and the target boundary
and operational error results inherit TLC propositional extensionality,
indefinite description, and dependent functional extensionality.

`sg_eval` and `sg_apply` are mutually recursive fuel interpreters. Results distinguish successful values, `sg_error`, and `sg_timeout`. Timeout is fuel exhaustion, not a proof of divergence. Missing environment entries and non-callable applications return errors. Errors and timeouts propagate through sequencing.

`sg_cast` checks Int/Unit constructors, rejects Bottom, passes unknown/Top unchanged, and wraps callable values at arrow targets. Applying a wrapper checks its argument against the domain, calls the wrapped value, and checks the result. Function arguments can themselves receive wrappers. Union casts try the left component first and then the right on failure; union introductions check their selected component and erase the injection at runtime. These are target-directed casts without source-type evidence, blame labels, or implicit elaboration.

Switch evaluation uses the underlying value descriptor and the original static subtype relation, choosing the first matching branch, or returning an error when neither matches. `sg_test` uses TLC classical case analysis: evaluation involving switches is not an extracted executable subtype decision procedure. Other interpreter clauses compute directly. Switch typing requires disjoint descriptors but does not require exhaustive coverage of the scrutinee type.

Checked examples include `sg_higher_order_wrapper`, `sg_higher_order_argument` (a function receiving a function), `sg_delayed_domain_error`, `sg_delayed_result_error`, union successes/failures, and `sg_application_precision`. The result-error example exercises raw evaluation and is not claimed to be well typed.

## Exact proved guarantees

Precision is defined independently of typing and evaluation. Its orientation is precise to less precise: every type is below unknown, and arrow/union components vary structurally. Term precision preserves constructors, variables, literal values, and static descriptors. Environment precision is pointwise `Forall2` type precision.

- `sg_precision_refl` and `sg_precision_trans` establish the type precision preorder. `sg_consistent_weaken`, `sg_match_weaken`, and `sg_lookup_precision` provide the structural facts used by typing.
- `sg_static_gradual_guarantee`: for every precision-related pair of source terms and environments, if the precise term has type A, the less precise term has some type A' with A below A'. This covers all source constructors and open environments; it does not define precision through typing or assume the desired target typing.
- `sg_cast_data_gradual_guarantee`: for arbitrary structurally related target types, a successful cast on integer/unit data remains successful at the less precise target and returns exactly the same value. Targets can contain nested arrows/unions; the input value must be first-order data.
- `sg_annotation_dynamic_guarantee`: for arbitrary fuel, runtime environment, and computation e returning integer/unit data, weakening an outer annotation preserves a successful result exactly, at the same fuel. The inner computation may include applications and closures. Only the outer annotation changes; this does not simulate arbitrary term precision.
- `sg_annotation_unknown_guarantee`: any successful outer annotation can be replaced by unknown to expose the underlying successful value; applying the original cast reconstructs the original result. This includes function values, but is a factorization theorem rather than a full dynamic gradual guarantee.
- `sg_cast_preserves_descriptor`: successful casts preserve the observable static descriptor.
- `sgvalue_precision` and `sgvalues_precision` independently relate runtime data,
	closures with precision-related bodies and captured environments, corresponding
	delayed wrappers, and additional wrappers on the precise side. They do not
	mention evaluation or typing. `sg_value_descriptor_precision` and
	`sg_value_callable_precision` preserve descriptors and callability across this
	relation; `sg_values_lookup` preserves related environment lookup.
- `sg_cast_forget`: for arbitrary target types and structurally related runtime
	values, a successful cast on the precise value produces a value related to the
	unchanged less precise input. This includes higher-order values.
- `sg_cast_no_timeout`: casts themselves never exhaust fuel.
- `sg_cast_new_success`: for arbitrary structurally related runtime values and
	precision-related targets, if the precise cast fails and the less precise cast
	succeeds, the latter returns its input unchanged. In particular, a previously
	failing left union alternative cannot become successful by installing a new
	delayed wrapper. This rules out that proposed union counterexample mechanism;
	it does not establish the general evaluation guarantee.

- `sg_cast_precision`: for all `A`, `A'`, `v`, `v'`, and `w`, if
	`sgprecision A A'`, `sgvalue_precision v v'`, and
	`sg_cast A v = sg_done w`, there exists `w'` such that
	`sg_cast A' v' = sg_done w'` and `sgvalue_precision w w'`.
	This is general cast compatibility, including higher-order values and changes
	in left-biased union selection. A newly successful left alternative returns
	its input unchanged; `sg_cast_forget` relates the original right result to it.
- `sg_success_precision` is a one-way success lifting of the independently
	defined structural value relation to results. It imposes no condition on a
	source error or timeout; it is not a definition of term precision or a proved
	evaluation guarantee. `sg_bind_precision` proves compositional sequencing
	for this lifting, and `sg_cast_success_precision` packages cast compatibility.

- `sg_evaluation_simulation`: simultaneously, for every `fuel <= fuel'`,
	precision-related expressions in structurally related runtime environments
	have success-related evaluations, and structurally related functions applied
	to structurally related arguments have success-related applications. Both
	conclusions use `sg_success_precision`; they quantify over arbitrary values,
	terms, and environments without typing assumptions. The expression part
	covers every constructor, including switches with unchanged descriptors.
- `sg_dynamic_gradual_guarantee`: for all `e e' rho rho' v`,
	`sgterm_precision e e'` and `sgvalues_precision rho rho'` imply
	`(exists fuel1, sg_eval fuel1 rho e = sg_done v) ->
	 exists fuel2 v', sg_eval fuel2 rho' e' = sg_done v' /\
		 sgvalue_precision v v'`.
	This is general successful expression simulation, including open terms,
	higher-order values, changes inside applications, and function-valued union
	casts. The proof chooses `fuel2 = fuel1`.
- `sg_application_dynamic_guarantee`: the corresponding fuel-independent
	implication for `sg_apply`, assuming structural precision of both functions
	and arguments, with structurally related successful results. It also chooses
	the original budget.

The mutual proof inducts on the precise fuel and generalizes over all target
budgets at least that large. Corresponding closures and wrappers use the
predecessor budget on each side. An extra precise wrapper casts its argument,
applies its inner function, and casts the result. `sg_cast_forget` relates the
checked argument to the original less precise argument and the checked result
to the simulated result. The application induction hypothesis compares the
inner precise call at predecessor fuel with the less precise call at its full
budget. This handles wrapper erasure without a new value relation or a separate
fuel monotonicity assumption. Switch tests agree by descriptor precision.

## Operational metatheory

General successful expression/application simulation and its fuel correspondence
are proved. The operational results below now justify existential interpreter
fuel against a separate unbounded semantics. A single timeout still establishes
only fuel exhaustion.

- `sg_fuel_monotonicity` simultaneously proves that completed expression and
	application runs, including errors, remain exactly unchanged at larger fuel.
- `sg_command` distinguishes evaluation from application. `sg_expand` describes
	their operational clauses as plans containing answers and subcomputation
	requests. The mutually inductive `sg_runs` / `sg_plan_runs` relations give
	finite big-step derivations without any fuel or reference to the interpreter.
	They reuse the same casts and descriptor tests. Errors propagate explicitly;
	no derivation concludes timeout.
- `sg_fuel_sound`, `sg_unbounded_complete`, and `sg_operational_adequacy` prove
	both directions for arbitrary open evaluations and applications, successes
	and errors: an operational derivation exists exactly when a non-timeout
	interpreter result exists at some fuel. `sg_expand_eval` connects individual
	operational clauses to the interpreter. `sg_operational_determinism` proves
	uniqueness of operational results.
- `sg_diverges c` means every fuel budget returns timeout.
	`sg_divergence_adequacy` equates this with absence of any finite operational
	derivation. This is justified interpreter divergence, not a coinductive
	infinite reduction theorem. `sg_termination_classification` classically
	partitions commands into success, error, or divergence; determinism and
	divergence adequacy exclude overlap.
- `sg_unbounded_dynamic_gradual_guarantee` transfers expression success in the
	independent semantics. `sg_error_approximation` says a less precise error
	implies a precise error or precise divergence. `sg_divergence_approximation`
	says less precise divergence implies a precise error or precise divergence.
	Both use the contrapositive of successful simulation plus classification.
	Neither asserts preservation of precise divergence under erasure, nor that
	less precise errors force precise termination. These corollaries are for
	expressions; application adequacy and the existing application success
	guarantee remain separately available.
- `sg_runtime_type` checks integer/unit shapes, excludes Bottom, interprets
	unions by disjunction, and records arrow boundary annotations on closures
	and callable wrappers. `sg_cast_runtime_type` proves successful casts meet
	their target shape, and `sg_application_runtime_type` proves that successful
	application of an arrow-shaped value meets its result shape. Unknown and
	Top accept all values, but the other clauses are restrictive. This is a
	boundary contract, not captured-environment typing or descriptor validity,
	and is not presented as structural type safety.

The typing rules alone cannot establish intrinsic descriptor validity: for
example `sg_lam t_int sg_unit sg_unit sg_null` is typable as an arrow while its
observable descriptor is Int. Switch coverage is also absent. The interpreter
now casts a selected branch's scrutinee to `sg_lift D` before extending the
environment. A false Int descriptor on a closure therefore fails at entry.
Function descriptors install wrappers whose domain/result checks occur during
application; they do not certify the original closure's annotations.

## Logical runtime typing and restricted safety

`sg_value_valid` and `sg_environment_valid` are mutually inductive judgments.
A valid closure has an arrow-shaped static descriptor, a body satisfying
`sg_safe_syntax`, a derivation `sgtyping (A :: G) body C`, consistency between
`C` and its result annotation, and a captured environment valid at `G`.
A valid wrapper contains a valid callable value. Each environment entry has
both inductive value validity and the boundary shape of its declared type.
`sg_value_typing v A` combines inductive validity with `sg_runtime_type A v`.
Thus the logical judgment checks captured code and environments as well as
outer runtime shape; it does not claim an extensional arrow contract.

`sg_safe_syntax` restricts lambda descriptors to arrows, recursively through
all bodies, and permits arbitrary switch descriptors. It does not enforce a
lambda descriptor's domain/result annotations or exhaustive switch coverage.
Branch-entry casts are part of both `sg_eval` and the independent `sg_expand`
semantics. The general DGG proof uses cast precision at reflexively related
lifted descriptors and extends environments with the related cast results.
Fuel monotonicity and operational adequacy are checked for these semantics.

The checked supporting lemmas are:

- `sg_environment_lookup`: a typed lookup in a valid environment finds a
	runtime value with logical typing at the same type.
- `sg_cast_valid`: a successful cast of a valid value returns a valid value.
- `sg_cast_logical_preservation`: if `sg_value_valid v` and
	`sg_cast A v = sg_done w`, then `sg_value_typing w A`. This covers every
	target type, including arrows and left-biased unions.
- `sg_valid_descriptor_shape`: a valid value is integer data, unit data, or
	callable with an arrow descriptor. This excludes the false Int-tagged closure
	above, without asserting semantic agreement with a whole function type.
- `sg_data_test_refinement`: if a valid value passes its descriptor test
	against Int or Unit, it has logical typing at `sg_lift D`. This justifies
	using an uncast value as a data binding; the interpreter now casts all
	selected switch binders, including data binders.
- `sg_bind_success`: successful sequencing factors into a successful input
	and a successful continuation.

The checked preservation and safety results are:

- `sg_finite_success_preservation`: for every fuel budget, mutually:
	(1) `sgtyping G e A`, `sg_safe_syntax e`, a valid environment `rho` at `G`,
	and `sg_eval fuel rho e = sg_done w` imply `sg_value_typing w A`;
	(2) valid function and argument values and `sg_apply fuel f a = sg_done w`
	imply `sg_value_valid w`. The second clause quantifies over arbitrary valid
	callable boundaries and does not require a matching argument type.
- `sg_evaluation_logical_preservation` exposes the expression clause.
	`sg_application_logical_preservation` strengthens the application conclusion:
	logical typing of `f` at `sg_arrow A B`, validity of `a`, and successful
	application imply logical typing of the result at `B`.
- `sg_operational_logical_preservation` and
	`sg_operational_application_preservation` give the corresponding theorems
	for independent finite operational derivations, with no fuel premise.
- `sg_evaluation_descriptor_safety`: a successful evaluation under the
	expression preservation hypotheses, followed by a successful Int/Unit
	descriptor test, gives logical typing at that descriptor's lifted type.
	The switch cases of preservation instead use `sg_cast_logical_preservation`
	to validate arbitrary descriptor binders before evaluating branch bodies.
- `sg_logical_safety`: a typed expression satisfying `sg_safe_syntax` in a
	valid environment either has an operational success with logical typing at
	its source type, has an explicit operational error, or diverges. This uses
	the existing justified divergence classification and does not claim that
	well-typed programs cannot produce errors. Successful Bottom results are
	excluded by logical typing's shape component.
- `sg_safe_syntax_precision`: precision-related expressions satisfy
	`sg_safe_syntax` equivalently. `sg_safe_static_gradual_guarantee` packages
	the static gradual guarantee with preservation of this fragment.

The mutual preservation proof inducts on fuel. Closure application casts the
argument, extends the captured valid environment, recursively checks the typed
body, and casts its result. Wrapper application recursively proves validity of
the inner call on the checked argument before proving validity of its result
cast. These results retain typed closure bodies and captured environments;
they do not replace logical validity with the weaker runtime shape predicate.

Arbitrary function-descriptor branch bindings are justified by entry casts.
An arrow-shaped descriptor alone still does not establish its domain/result
contract: the independent descriptor can disagree with both closure annotations.
The entry wrapper supplies a checked boundary instead. Partial switches and
failing casts permit runtime errors even in the proved fragment. Arrow-shaped
lambda descriptors remain required by logical validity and `sg_safe_syntax`.

The relation `sg_exact_elaboration G Delta e target A` connects original
locally nameless expressions to structural de Bruijn expressions. `Delta` maps
free names and their static types to de Bruijn positions; cofinite binder
premises open original bodies while keeping one fixed target body. Additional
fresh-name rules `sgee_abs_pick` and `sgee_switch_pick` elaborate one opening
with a name absent from the original body's free variables. Their source
soundness uses `sg_typing_fresh_open` to recover cofinite source typing; their
target soundness uses the selected body's target derivation directly. Its named
fragment covers literals, null, variables, lambdas, applications, and disjoint
switches. Static union introductions elaborate to explicit `sg_inl`/`sg_inr`
terms. General static subsumption uses `sgee_sub`: an elaboration of `e` at
`A`, together with `A <: B`, elaborates `e` at `B` to
`sg_ann target (sg_lift B)`. Target typing uses `sg_con_sub`; the runtime cast
semantics are unchanged.

- `sg_exact_elaboration_source`: an elaboration derivation implies
	`typing G e A`, including static subsumption for the union introductions.
- `sg_exact_elaboration_target`: the same derivation implies
	`sgtyping (sg_elaboration_context Delta) target (sg_lift A)` and
	`sg_safe_syntax target`.

- `sg_context_covers G Delta` requires that every `binds x A G` has an index
	with `nth_error Delta index = Some (x, A)`. It assumes no elaboration or
	target typing. Extra slots and duplicate names are permitted; this is an
	existence theorem, not a deterministic name-resolution algorithm.
- `sg_context_covers_push` preserves coverage when the same binding is pushed
	onto the named environment and the indexed list. `sg_context_covers_canonical`
	proves coverage for `Delta = G`, using TLC's environment representation laws.
- `sg_exact_elaboration_complete`: for every `typing G e A` and every `Delta`
	satisfying `sg_context_covers G Delta`, there exists `target` such that
	`sg_exact_elaboration G Delta e target A`. Induction covers every original
	typing rule, including arbitrary subsumption via `sgee_sub`. Binder cases
	select a fresh name and use the fresh-name elaboration rules.
- `sg_exact_elaboration_canonical` instantiates completeness at `Delta = G`.
- `sg_exact_elaboration_closed`: original `typing empty e A` implies existence
	of a target elaboration under `[]`, `sgtyping [] target (sg_lift A)`, and
	`sg_safe_syntax target`.

These establish full typing completeness for the relation containing both
cofinite and fresh-name binder rules. Equivalence to its cofinite-only subset,
or independence of a fixed target from the chosen fresh name, is not proved.
These typing results do not establish operational conservativity. Universal
success correspondence for this relation is refuted by the closed
counterexample below, which uses only cofinite binder rules.

Additional static-interface results are checked:

- `sg_typing_fresh_open`: if `x` is absent from `fv_exp body` and
	`typing (G & x ~: A) (open_exp_wrt_exp body (e_var_f x)) B`, then for every
	`y` absent from `dom G`, the corresponding opening with `y` has type `B`
	in `G & y ~: A`. The proof uses original source weakening and substitution.
- `sg_valid_tag_union`: validity and `sg_tag v <: t_union A B` imply
	`sg_tag v <: A \/ sg_tag v <: B`.
- `sg_static_tag_cast_total`: for all `A v`, validity and `sg_tag v <: A`
	imply existence of `w` with `sg_cast (sg_lift A) v = sg_done w`,
	`sg_value_typing w (sg_lift A)`, and `sg_tag w = sg_tag v`.
- `sg_static_subsumption_cast_total`: for all `A B v`, validity,
	`sg_tag v <: A`, and `A <: B` imply existence of `w` with
	`sg_cast (sg_lift B) v = sg_done w`, logical typing at `sg_lift B`, and
	the same tag as `v`.

Cast totality assumes tag subtyping explicitly. Logical runtime typing alone
does not supply that premise. Arrow casts install delayed wrappers, so these
theorems do not imply that subsequent function calls cannot fail. Evaluation
correspondence still needs an independent relation between substituted source values and target
closures, captured environments, and inserted wrappers.

The additional `sg_source_value_observation` relation mentions neither typing
nor evaluation. It relates `e_lit n` to exactly `sg_vint n`, null to unit, and
an original lambda to a runtime value with its declared arrow descriptor.
Its function case gives no relation between bodies or captured environments.

- `sg_source_value_observation_tag`: an observation and an original `findtype`
	derivation identify the same runtime descriptor.
- `sg_source_value_observation_cast`: every successful cast preserves the
	observation, including exact integer payloads and null/unit identity.
- `sg_source_value_cast_total`: if `typing G e A`, `value e`, a valid runtime
	value `v` observes `e`, and `A <: B`, then there exists `w` such that
	`sg_cast (sg_lift B) v = sg_done w` and `w` still observes `e`.

The cast theorem derives tag subtyping from original value typing and the
observation premise. It proves cast nonfailure for an already related runtime
value. Function application can still encounter checks delayed by wrappers.

`sg_exact_elaboration_value_evaluation` additionally proves actual termination
of elaborated source values. Its exact statement is:

```coq
forall G Delta e target A,
	sg_exact_elaboration G Delta e target A ->
	forall rho, sg_environment_valid rho (sg_elaboration_context Delta) ->
	value e -> exists fuel w,
		sg_eval fuel rho target = sg_done w /\
		sg_source_value_observation e w.
```

This quantifies over every elaboration derivation, including arbitrary repeated
subsumption, union introductions, and both lambda binder rules. Integers retain
their payload and null evaluates to unit; functions retain their original
arrow descriptor. It gives no relation between lambda bodies, captured source
environments, and delayed wrappers, and does not prove beta/switch simulation.

The separate `sg_source_data_runs` judgment supplies independent first-order
environment semantics on original syntax: integer/null answers, indexed
variables, applications of literal lambdas, and both switch branches. Calls
require source `findtype`/subtyping premises at argument and result boundaries;
right switches explicitly exclude the left descriptor. Its rules mention no
target evaluation or casts. `sg_data_compile` is a separate structural compiler
with Top switch results; its free-name case maps to unit, and the source
judgment has no rule evaluating free names. It is not an elaboration rule.
`sg_data_compile_evaluation` proves recursive evaluation preservation:

```coq
forall sigma e v,
	sg_source_data_runs sigma e v ->
	exists fuel, sg_eval fuel (map sg_data_encode sigma) (sg_data_compile e) =
		sg_done (sg_data_encode v).
```

The proof inducts on the independent source derivation, combining recursive
fuel budgets by their maximum. It covers arbitrary finite nesting of calls
and switches, including argument and result casts, both branch choices, and
extension of indexed environments. Integer payloads and null results are
preserved exactly. `sg_data_compile_operational` derives the corresponding
`sg_runs (sg_evaluate (map sg_data_encode sigma) (sg_data_compile e))
(sg_done (sg_data_encode v))` result using operational adequacy.

`sg_data_instantiate depth sigma e` substitutes the data environment into
original syntax, preserving indices underneath binders. The checked opening law
`sg_data_instantiate_open` equates environment extension with the original
`open_exp_wrt_exp_rec` operation. Using original typing regularity and
preservation, `sg_source_data_runs_original` proves:

```coq
forall sigma e v,
	sg_source_data_runs sigma e v ->
	Forall sg_source_data sigma -> forall G T,
	typing G (sg_data_instantiate 0 sigma e) T ->
	sg_original_steps (sg_data_instantiate 0 sigma e) v.
```

Here `sg_original_steps` is the reflexive transitive closure of the original
Section 3 `step`, including its beta, switch, and evaluation-context rules.
`sg_data_compile_original_correspondence` pairs this original reduction with
the exact unbounded target answer above. Its premises contain no target run.
The opening law requires every environment entry to be data; this additional
restriction applies to the bridge, whereas the compiler evaluation theorem
requires only accessed entries to be data. Missing substitution slots default
to null, but successful data derivations never access missing slots.

These results apply to the restricted compiler and source judgment. They do
not prove a compiler typing theorem, the converse from arbitrary original
reductions to source data derivations, or correspondence for arbitrary
`sg_exact_elaboration` derivations. The source judgment cannot return functions
or evaluate a computed function position. The compiler evaluation theorem only
requires accessed environment entries to be data. The higher-order extension
below removes these restrictions through separate source closure semantics.

Checked supporting lemmas are `sg_source_data_runs_answer` (answers are data),
`sg_data_encode_tag` (source/runtime descriptors agree), `sg_data_encode_cast`
(every lifted static supertype cast of encoded data returns exactly that data),
`sg_data_environment_lookup` (indexed lookup commutes with encoding), and
`sg_eval_success_increase` (successful target evaluation persists at larger
fuel). The recursive compiler theorem uses these lemmas.
Target fresh-name independence and fresh-pick/cofinite equivalence also remain
open; source typing transport alone does not establish either result.

The independent higher-order source values `sg_ho_value` contain integers,
unit, lexical closures with source bodies and captured source environments,
and delayed source function boundaries. `sg_ho_check` checks static source
annotations, including left-biased unions. Mutual judgments `sg_ho_runs` and
`sg_ho_applies` cover indexed lookup, closure capture, computed function
positions, higher-order arguments/results, both switch branches, and delayed
domain/range checking. Boundary rules require source descriptor subtyping and
successful source checks. Neither judgment refers to target evaluation.

`sg_ho_encode` maps source values structurally to runtime values: bodies use
`sg_data_compile`, environments map recursively, and source boundaries become
target wrappers. `sg_ho_check_encoding` proves exact check agreement, including
failure. `sg_ho_compile_simulation` mutually proves that every successful source
expression run and application has a finite target execution with exactly the
encoded answer. `sg_ho_compile_operational` gives unbounded target execution.

`sg_ho_quote` substitutes captured environments into original lambda syntax
and erases source boundary wrappers. `sg_ho_check_quote` proves successful
checks preserve quotation. `sg_instantiate_open_lc` generalizes the opening law
to locally closed environments and arguments. The independent structural
predicate `sg_ho_wf` requires well-formed captured values and locally closed
lambda quotations; it contains no evaluation premise.

`sg_ho_original_simulation` mutually proves that source runs/applications,
with well-formed environments/arguments and original typing of their quotation,
produce well-formed answers and finite sequences of actual original `step`
reductions to those answers' quotations. `sg_ho_compile_original_correspondence`
pairs the expression reduction with exact unbounded target execution. This
covers higher-order closures and captures, while retaining original source
typing and source boundary subtyping premises.

These theorems are conditional on a successful checked source derivation.
They do not establish existence of such derivations for all original typed
executions, their converse, typing of this separate compiler, or operational
correspondence for arbitrary `sg_exact_elaboration` derivations. Universal
success correspondence for the latter is refuted below; the converse for this
separate compiler remains open.

`sg_checked_descriptor v D` means both logical typing at `sg_lift D` and
`sg_tag v <: D`. The descriptor theorems establish the installed boundary:

- `sg_descriptor_entry_contract`: validity, a successful descriptor test, and a
	successful cast to `sg_lift D` imply a checked descriptor for the result and
	preservation of the observable tag.
- `sg_checked_descriptor_application`: a checked arrow descriptor, a valid
	argument, and a successful unbounded call imply logical result typing at the
	lifted range.
- `sg_descriptor_arrow_call_checks`: casting to a lifted arrow and successfully
	calling the resulting wrapper at `S fuel` factors into a successful domain
	cast, an inner call at `fuel`, and a successful range cast. This theorem needs
	no intrinsic tag-soundness assumption.

The raw closure descriptor still need not agree with its annotations; these
theorems certify explicit runtime boundaries. Adequacy is proved against
independent big-step semantics; no separate small-step semantics or coinductive
infinite reduction relation is provided.

## Original finite-execution decomposition

`sg_original_evaluates` is an independent big-step judgment over original
expressions. Its rules evaluate values, applications, and both switch branches
using original opening, descriptor lookup, and subtyping. They mention neither
target evaluation nor checked source runs. The checked theorems are:

```coq
sg_original_execution_decomposition : forall e v,
	sg_original_steps e v -> value v -> sg_original_evaluates e v.

sg_original_evaluation_reduction : forall e v,
	sg_original_evaluates e v -> forall G T, typing G e T ->
	sg_original_steps e v.
```

The first theorem covers every terminating original execution, including
untyped ones. It assumes no desired big-step run. A finite prefix ending in
a nonvalue does not satisfy its value premise; infinite executions are not
covered. Neither theorem asserts universal termination. The right-switch rule
retains the original descriptor premise, without imposing the left-failure
premise of checked source semantics.

`sg_ho_shape` independently requires structurally shaped captured values and
callable contents of boundaries. `sg_ho_shape_descriptor` classifies them as
integers, unit, or callable values with arrow tags. `sg_ho_check_shape` proves
that successful source checks preserve this predicate. These statements do
not use evaluation premises. Shape alone does not constrain boundary domains
or ranges relative to the wrapped closure.

The reverse bridge to `sg_ho_runs` remains open. It needs indexed scope/lookup
coverage (missing quotation slots currently default to null), a relation
between substitution and closure environments, boundary domain/result
contracts preserved through calls, and typed disjointness to justify a right
branch's left-test failure. Universal success correspondence for arbitrary
exact elaborations is refuted below. The value observation tracks function tags only,
whereas application correspondence needs a relation between bodies, captured
environments, and inserted wrappers. Exact syntactic equality of function
values would not account for those wrappers.

The attempted check-totality proof was removed after the third unsuccessful
proof build, following the requested repair limit. No unfinished theorem or
admitted proof is retained. The retained modules passed isolated Docker
`make` and `coqchk -silent -R . Top Top.typing` with a read-only source mount
and a temporary build copy. `Print Assumptions` reports the three existing TLC
assumptions for execution decomposition, those assumptions plus
`JMeq.JMeq_eq` for evaluation reduction, and no assumptions for the two shape
lemmas. No new axiom was introduced.

## Retained closed boundary layer

### Checked closed exact-elaboration counterexample

`sg_union_trap_program` switches the closed integer identity against
`Unit → Unit` and `Int → Int`, with branch bodies `0` and `f 7`.
`sg_union_trap_exact_elaboration` proves:

```coq
sg_exact_elaboration empty nil sg_union_trap_program
	sg_union_trap_elaborated t_int.
```

The derivation uses the cofinite binder rules. Its scrutinee target is a
right union injection followed by `sgee_sub` using reflexivity at the full
union. Thus the problematic union check is an allowed exact elaboration
choice. Applying source soundness yields original typing under `empty`;
applying target soundness yields structural typing under `nil` and safe
syntax. The source expression has no free-variable occurrences.

`sg_union_trap_closed` proves the free-variable set is empty;
`sg_union_trap_source_typing` and `sg_union_trap_target_typing` instantiate
source typing and target typing with safe syntax.
`sg_union_trap_source_termination` proves that the original execution selects
right and beta-reduces to `7`, using `sg_original_steps` over actual original
`step` reductions.
The target union check installs the left Unit-domain wrapper while retaining
the integer-arrow tag; right-branch entry wraps it again, and applying the
binder to `7` reaches the failing inner Unit-domain check. The checked results
are:

- `sg_union_trap_switch_tests`: the preserved integer-arrow descriptor fails
	the left test and passes its own right test. The proof uses semantic static
	disjointness and reflexive subtyping, then unfolds `sg_test` and reasons by
	classical cases; it does not assume the opaque classical decision computes.
- `sg_union_trap_elaborated_error`:
	`sg_eval 8 nil sg_union_trap_elaborated = sg_error`.
- `sg_union_trap_elaborated_operational_error`:
	`sg_runs (sg_evaluate nil sg_union_trap_elaborated) sg_error`, by adequacy.
- `sg_union_trap_elaborated_no_success`: no value `v` has a successful
	operational run of this target, by operational determinism.
- `sg_exact_elaboration_success_preservation_refuted`: the universal claim
	that every closed exact elaboration of an original successful execution
	has some successful target answer is false. No particular observation
	relation for the target answer is required, so stronger preservation
	claims implying target success are also excluded.

Together with closedness, both typing results, and original termination at
`7`, these results formally refute arbitrary exact-elaboration success
preservation under the current definitions. The full requested metatheory
cannot be proved unchanged. The separate `sg_ho_runs` compiler converse is
not settled by this exact-elaboration counterexample.

The completed additions passed isolated read-only/temp-copy `make` and
`coqchk -silent -R . Top Top.typing`. An assumption audit of
the whole-target fuel error, unbounded error, and no-success theorems reports
exactly the existing TLC assumptions `prop_ext`, `indefinite_description`,
and `fun_ext_dep`. The universal refutation additionally inherits
`JMeq.JMeq_eq` through original elaboration source soundness. Source and target
soundness are instantiated at the concrete elaboration. No new axiom or
admitted proof was introduced.
The structural dynamic gradual guarantee compares precision-related target
programs and is unchanged by this obstruction to static correspondence.

### Union-cast repair options

Avoiding the reflexive union annotation in this elaboration would remove the
specific wrapper that causes this execution to fail. A compiler that omits
such checks would need its own elaboration relation, typing/completeness
proofs, and operational correspondence. Selecting a better target does not
establish a theorem quantified over every derivation of the existing relation.

A broader repair could use source subtype evidence or retain union-injection
provenance when choosing a cast arm. Descriptor-directed selection is another
candidate, but requires a policy for unknown descriptors and for descriptors
that do not characterize delayed wrapper contracts. None of these proposals
is implemented or proved here. These are design options with explicit proof
obligations, not established sound replacements.

Changing runtime union selection requires revisiting `sg_cast_precision` and
`sg_cast_forget`, their evaluation/application simulations and structural DGG,
logical preservation, and operational adequacy. Changing the source boundary
policy also affects `sg_ho_check_encoding` and compiler simulation. In
particular, a selection policy must behave coherently when descriptors and
types lose precision; tag selection alone is not a proof of that property.
The existing precision relation and DGG are retained. A repaired semantics
would need to reprove them, rather than exclude this case by weakening the
precision theorem's scope.

The `gtyp`/`gexp` API remains available: `g_embed`, `g_inject`, `g_project`, `g_pack`, and `g_error`. Injection retains the original `findtype` tag even under static subsumption to Top; projection checks tag subtyping and returns the unchanged value or an error. This closed boundary layer has no structural function wrappers.

All original general results are retained: `gradual_preservation`, `gradual_preservation_many`, `gradual_progress`, `gradual_safety`, `gradual_determinism`, `successful_projection_typing`, `static_embedding`, `static_step_embedding`, `packed_tag_preserved`, `injection_retains_tag`, `unknown_not_top`, and `boundary_roundtrip`. Its integer/unit and static-switch examples are retained too. These safety results apply to the boundary judgment `gtyping`, not the structural judgment `sgtyping`.

## Validation

The two modules are checked using Coq 8.13.2 and the libraries in `disjoint-switches-functions:latest`, with a read-only source mount copied into a temporary container directory. Build with `make`, then check with `coqchk -silent -R . Top Top.typing`. `_CoqProject` lists only `syntax.v` and `typing.v`; the Makefile also discovers `.v` files automatically. The repository-wide `compile.sh` can mask build failures, so validation uses direct build exit codes.

There are no new axioms or admitted proofs. The development inherits TLC logical assumptions and `JMeq_eq` from the original static preservation proof. Classical descriptor testing additionally uses the existing TLC machinery. This is not an axiom-free formalization.

On 2026-10-27, the completed elaboration batch passed isolated `make` and
`coqchk -silent -R . Top Top.typing`. The fresh build retains all existing
checked results. `Print Assumptions` was run for context coverage (push and
canonical), `sg_typing_fresh_open`, elaboration completeness, source and target
soundness, canonical and closed completeness, the static and dynamic gradual
guarantees, logical safety, and operational adequacy.

- Coverage lemmas, elaboration completeness, target soundness, canonical and
	closed completeness, the dynamic guarantee, logical safety, and operational
	adequacy report exactly `LibAxioms.prop_ext`,
	`LibAxioms.indefinite_description`, and `LibAxioms.fun_ext_dep`.
- `sg_typing_fresh_open` and elaboration source soundness additionally inherit
	`JMeq.JMeq_eq` through original source substitution. The fresh-name binder
	rules introduce this dependency into source soundness; completeness and
	target soundness do not depend on that proof.
- The static gradual guarantee is closed under the global context.

Earlier audits of `sg_consistent_weaken`, `sg_valid_tag_union`,
`sg_static_tag_cast_total`, and `sg_static_subsumption_cast_total` found them
closed under the global context. Earlier descriptor, evaluation-simulation,
and finite-success-preservation audits found only the three TLC assumptions.
No new axiom, parameter, or admitted proof is used by this extension.

The value-observation and elaborated-value evaluation results passed isolated
`make` and `coqchk -silent -R . Top Top.typing`. The assumption audit found
`sg_source_value_observation_cast` closed under the global context;
`sg_source_value_observation_tag` and `sg_source_value_cast_total` inherit
exactly the three TLC assumptions listed above. Elaboration completeness was
audited again with the same three assumptions.

The 2026-10-28 retained source passed the same isolated build and kernel check.
`sg_exact_elaboration_value_evaluation` inherits the three TLC assumptions and
`JMeq.JMeq_eq` through source elaboration soundness. `sg_data_encode_cast`,
`sg_data_encode_tag`, `sg_source_data_runs_answer`, and
`sg_eval_success_increase` report exactly the three TLC assumptions;
`sg_data_environment_lookup` is closed under the global context. No new axiom
or admitted proof was introduced.

The recursive compiler theorem `sg_data_compile_evaluation` and its unbounded
corollary `sg_data_compile_operational` also passed a clean Docker `make` and
`coqchk -silent -R . Top Top.typing`, with the source mounted read-only and
build products confined to a temporary copy. `Print Assumptions` for each
reports exactly `LibAxioms.prop_ext`, `LibAxioms.indefinite_description`, and
`LibAxioms.fun_ext_dep`. Neither introduces a new axiom or admitted proof.

The original-step bridge and paired correspondence also passed isolated
`make` and `coqchk -silent -R . Top Top.typing`. An assumption audit of
`sg_data_instantiate_open` reports the three TLC assumptions above.
`sg_source_data_runs_original` and `sg_data_compile_original_correspondence`
additionally inherit `JMeq.JMeq_eq` through original preservation. They introduce
no new axiom or admitted proof. These compiler results do not establish
universal exact-elaboration success preservation, which is refuted above.

The higher-order compiler simulation, original-step simulation, and paired
correspondence passed the same isolated read-only/temp-copy `make` and
`coqchk` checks. The compiler simulation and operational corollary use exactly
the three TLC assumptions above. The original-step simulation and paired
correspondence additionally inherit `JMeq.JMeq_eq` through original
preservation. No axiom or admitted proof was added.

On 2026-10-28, the completed closed counterexample passed isolated `make` and
`coqchk -silent -R . Top Top.typing` with a read-only source mount and a
temporary build copy. `Print Assumptions` on
`sg_union_trap_elaborated_error`,
`sg_union_trap_elaborated_operational_error`, and
`sg_union_trap_elaborated_no_success` reports the three TLC assumptions above.
`sg_exact_elaboration_success_preservation_refuted` additionally inherits
`JMeq.JMeq_eq`. No semantics, precision relation, or DGG theorem was changed.

-->