# Section 3 structural gradual extension

This is a checked structural extension with static and successful dynamic gradual-guarantee proofs for every source constructor, unbounded operational adequacy, error/divergence approximation, and logical preservation for arrow-shaped lambda descriptors and arbitrary switch descriptors. It is not a full gradual metatheory: intrinsic descriptor validity, error-free progress, and full static conservativity remain open. All syntax is in `syntax.v`; all typing, evaluation, and proofs are in `typing.v`. The original static calculus and its proofs remain available. The former `gradual.v` definitions, proofs, and examples have been integrated into these two files.

## Structural language

`sgtyp` has unknown (`sg_any`), Top, Int, Bottom, Unit, arrows, and unions. Unknown may occur at any depth. `sg_any` and `sg_top` are distinct constructors. The relation named `sgconsistent` is directed compatibility: it includes unknown compatibility, structural arrow/union compatibility, and `sg_con_sub`. The latter accepts `X` as compatible with `Y` whenever static types `A <: B` satisfy `sgprecision (sg_lift A) X` and `sgprecision (sg_lift B) Y`. In particular, Int is compatible with Top. This precision-closed extension supports checked annotations for arbitrary static subsumption; it is not asserted to be symmetric.

`sgexp` includes de Bruijn variables, literals, unit, annotated lambdas, applications, explicit annotations, explicit left/right union introductions, and disjoint switches. `sgtyping` uses arbitrary lists of gradual types, including unknown entries. Closures capture runtime environments. The examples `sg_open_unknown`, `sg_open_evaluation`, and `sg_nested_unknown` exercise open lookup and nested unknown annotations.

Each lambda carries a separate static descriptor `D`, in addition to gradual domain/result annotations. Switch descriptors are also static. `sgterm_precision` holds these descriptors fixed while allowing structural precision changes to gradual annotations and branch bodies. This choice preserves observable switch tests: erasing an observable function descriptor could change which branch executes. `sg_cast_preserves_descriptor` proves every successful cast retains the descriptor, including through wrappers. The current typing rule does not enforce agreement between a closure's descriptor and its gradual annotations; descriptors must not be interpreted as a proved runtime typing invariant.

## Evaluation and casts

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
Source/target evaluation correspondence remains open, so this is not full
structural conservativity.

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
correspondence for arbitrary `sg_exact_elaboration` derivations. In particular,
full static conservativity remains open.

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

## Retained closed boundary layer

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
no new axiom or admitted proof. Full static conservativity remains open.

The higher-order compiler simulation, original-step simulation, and paired
correspondence passed the same isolated read-only/temp-copy `make` and
`coqchk` checks. The compiler simulation and operational corollary use exactly
the three TLC assumptions above. The original-step simulation and paired
correspondence additionally inherit `JMeq.JMeq_eq` through original
preservation. No axiom or admitted proof was added.