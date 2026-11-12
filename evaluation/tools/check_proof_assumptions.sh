#!/bin/sh
# Check fresh `coqtop -batch` Print Assumptions output. This checks dependencies,
# not whether the requested theorem set was complete; the caller chooses it.
set -eu

if [ "$#" -ne 1 ]; then
    echo "Usage: $0 PRINT_ASSUMPTIONS_LOG" >&2
    exit 2
fi
if [ ! -f "$1" ] || [ ! -r "$1" ]; then
    echo "Assumption audit: cannot read log: $1" >&2
    exit 2
fi

# Read on stdin so a path beginning with '-' cannot become an awk option.
LC_ALL=C awk '
function reject(message) {
    print "Assumption audit: line " NR ": " message > "/dev/stderr"
    failed = 1
}
function type_line(line,    i, character) {
    last_type_line = line
    for (i = 1; i <= length(line); i++) {
        character = substr(line, i, 1)
        if (character == "(" || character == "[" || character == "{") {
            delimiter[++depth] = character
        } else if (character == ")" || character == "]" || character == "}") {
            if (depth == 0 ||
                (character == ")" && delimiter[depth] != "(") ||
                (character == "]" && delimiter[depth] != "[") ||
                (character == "}" && delimiter[depth] != "{")) {
                reject("unbalanced type delimiters")
            } else {
                delete delimiter[depth--]
            }
        }
    }
}
function end_type() {
    if (in_type) {
        if (depth != 0) reject("unterminated axiom type")
        if (last_type_line ~ /([,:]|->|=>|forall|fun)[ \t]*$/)
            reject("incomplete axiom type")
    }
    while (depth > 0) delete delimiter[depth--]
    in_type = 0
    last_type_line = ""
}
function end_block() {
    end_type()
    if (pending != "") reject("missing type for axiom " pending)
    if (in_axioms && declarations == 0) reject("empty Axioms block")
    pending = ""
    in_axioms = 0
    in_type = 0
}
function register_axiom(name) {
    declarations++
    total_axioms++
    if (!(name in allowed) && !(name in unknown)) {
        unknown[name] = 1
        reject("unexpected axiom: " name)
    }
}
BEGIN {
    allowed["ClassicalDedekindReals.sig_not_dec"] = 1
    allowed["ClassicalDedekindReals.sig_forall_dec"] = 1
    allowed["FunctionalExtensionality.functional_extensionality_dep"] = 1
    allowed["Classical_Prop.classic"] = 1
    identifier = "[[:alpha:]_][[:alnum:]_.\047]*"
}
{
    sub(/\r$/, "")
    if ($0 ~ /^[ \t]*$/) next
    if ($0 == "Closed under the global context") {
        end_block()
        outputs++
        closed++
        next
    }
    if ($0 == "Axioms:") {
        end_block()
        outputs++
        in_axioms = 1
        declarations = 0
        next
    }
    # Coq may print these when Print Assumptions forces an opaque dependency.
    if ($0 ~ /^Fetching opaque proofs from disk for [[:alnum:]_.\047]+$/) next

    if (!in_axioms) {
        reject("unexpected output: " $0)
        next
    }
    if (pending != "") {
        if ($0 !~ /^[ \t]+:[ \t]*[^ \t]/) {
            reject("expected type after axiom " pending ": " $0)
            pending = ""
            next
        }
        register_axiom(pending)
        pending = ""
        in_type = 1
        type_line($0)
        next
    }
    # A declaration can put its type on this line or on the next indented line.
    # Also recognize indented declarations, rather than hiding unknown axioms
    # in what would otherwise look like a type continuation.
    if ($0 ~ ("^[ \t]*" identifier "[ \t]*:")) {
        end_type()
        name = $0
        sub(/^[ \t]*/, "", name)
        sub(/[ \t]*:.*/, "", name)
        type_text = $0
        sub(/^[^:]*:[ \t]*/, "", type_text)
        if (type_text == "") reject("empty type for axiom " name)
        register_axiom(name)
        in_type = 1
        type_line(type_text)
        next
    }
    if ($0 ~ ("^" identifier "$")) {
        end_type()
        pending = $0
        in_type = 0
        next
    }
    if ($0 ~ /^[ \t]+/ && in_type) {
        # Never swallow diagnostics merely because they were indented.
        if ($0 ~ /(^|[ \t])(Error|Anomaly|Exception|Warning):/)
            reject("diagnostic in assumptions output: " $0)
        type_line($0)
        next
    }
    reject("malformed assumptions output: " $0)
}
END {
    end_block()
    if (outputs == 0) reject("no Print Assumptions result (empty or unrelated log)")
    if (failed) exit 1
    print "Assumption audit passed: " outputs " result(s), " closed+0 " closed, " total_axioms+0 " allowed axiom declaration(s)."
}
' < "$1"
