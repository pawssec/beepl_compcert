#!/bin/sh
# Isolated fixtures; no Coq installation or Python required.
set -eu
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
checker=$script_dir/check_proof_assumptions.sh
fixture_dir=$(mktemp -d "${TMPDIR:-/tmp}/beepl-assumptions.XXXXXX")
trap 'rm -rf -- "$fixture_dir"' EXIT HUP INT TERM

expect_pass() {
    if ! "$checker" "$fixture_dir/$1.log" > "$fixture_dir/output" 2>&1; then
        cat "$fixture_dir/output" >&2
        echo "FAIL: expected $1 to pass" >&2
        exit 1
    fi
}
expect_fail() {
    if "$checker" "$fixture_dir/$1.log" > "$fixture_dir/output" 2>&1; then
        echo "FAIL: expected $1 to fail" >&2
        exit 1
    fi
    if ! grep -F -- "$2" "$fixture_dir/output" > /dev/null; then
        cat "$fixture_dir/output" >&2
        echo "FAIL: $1 did not report expected diagnostic: $2" >&2
        exit 1
    fi
}

cat > "$fixture_dir/allowed.log" <<'LOG'
Fetching opaque proofs from disk for compcert.lib.Integers
Axioms:
ClassicalDedekindReals.sig_not_dec : forall P : Prop, {~ ~ P} + {~ P}
ClassicalDedekindReals.sig_forall_dec
  : forall P : nat -> Prop,
    (forall n : nat, {P n} + {~ P n}) ->
    {n : nat | ~ P n} + {forall n : nat, P n}
FunctionalExtensionality.functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
Classical_Prop.classic : forall P : Prop, P \/ ~ P
Closed under the global context
Axioms:
Classical_Prop.classic : forall P : Prop, P \/ ~ P
LOG
expect_pass allowed
printf '%s\n' 'Closed under the global context' > "$fixture_dir/closed.log"
expect_pass closed
# Windows line endings are harmless, including a final line without newline.
printf 'Closed under the global context\r' > "$fixture_dir/crlf.log"
expect_pass crlf

cat > "$fixture_dir/admitted.log" <<'LOG'
Axioms:
BeePL_auxlemmas.sub_effect_trans
  : forall e1 e2 e3, sub_effect e1 e2 -> sub_effect e2 e3 -> sub_effect e1 e3
LOG
expect_fail admitted 'unexpected axiom: BeePL_auxlemmas.sub_effect_trans'
cat > "$fixture_dir/extra.log" <<'LOG'
Closed under the global context
Axioms:
Classical_Prop.classic : forall P : Prop, P \/ ~ P
  extra_axiom : False
LOG
expect_fail extra 'unexpected axiom: extra_axiom'
: > "$fixture_dir/empty.log"
expect_fail empty 'no Print Assumptions result'
printf '%s\n' 'Fetching opaque proofs from disk for compcert.lib.Integers' > "$fixture_dir/no_result.log"
expect_fail no_result 'no Print Assumptions result'
printf '%s\n' 'Axioms:' > "$fixture_dir/empty_block.log"
expect_fail empty_block 'empty Axioms block'
printf '%s\n' 'Axioms:' 'Classical_Prop.classic' > "$fixture_dir/missing_type.log"
expect_fail missing_type 'missing type for axiom Classical_Prop.classic'
printf '%s\n' 'Axioms:' 'Classical_Prop.classic :' > "$fixture_dir/empty_type.log"
expect_fail empty_type 'empty type for axiom Classical_Prop.classic'
printf '%s\n' 'Closed under the global context' 'Error: Missing theorem.' > "$fixture_dir/error.log"
expect_fail error 'unexpected output: Error: Missing theorem.'
printf '%s\n' 'Axioms:' 'Classical_Prop.classic' '  Error: Failed output.' > "$fixture_dir/malformed.log"
expect_fail malformed 'expected type after axiom Classical_Prop.classic'
printf '%s\n' 'Axioms:' 'Classical_Prop.classic : Prop' '  Error: Failed output.' > "$fixture_dir/indented_error.log"
expect_fail indented_error 'unexpected axiom: Error'

printf '%s\n' 'Axioms:' 'Classical_Prop.classic : forall (P : Prop,' > "$fixture_dir/truncated.log"
expect_fail truncated 'unterminated axiom type'
printf '%s\n' 'Axioms:' 'Classical_Prop.classic : forall P : Prop,' > "$fixture_dir/dangling.log"
expect_fail dangling 'incomplete axiom type'
printf '%s\n' 'Axioms:' 'Classical_Prop.classic : (Prop]' > "$fixture_dir/unbalanced.log"
expect_fail unbalanced 'unbalanced type delimiters'

if "$checker" > "$fixture_dir/output" 2>&1; then
    echo 'FAIL: missing log argument accepted' >&2
    exit 1
fi
if "$checker" "$fixture_dir/missing.log" > "$fixture_dir/output" 2>&1; then
    echo 'FAIL: nonexistent log accepted' >&2
    exit 1
fi
printf '%s\n' 'Assumption-checker fixtures passed (3 positive, 13 negative, 2 invocation checks).'
