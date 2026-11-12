/* Diagnostic harness for ref_output_escape.bpl; not an automated pass check.
 * Run from the repository root after make:
 * ./ccomp -typecheck -S evaluation/tests/known-failures/ref_output_escape.bpl -o /tmp/beepl-ref-output-escape.s
 * gcc -no-pie /tmp/beepl-ref-output-escape.s evaluation/tests/known-failures/ref_output_escape_harness.c -o /tmp/beepl-ref-output-escape
 * /tmp/beepl-ref-output-escape
 *
 * Source fresh-block semantics expects test to return 0. The current generated
 * code accesses an expired automatic local: native behavior is undefined, so
 * neither 7 nor any other result is an expected native-test oracle. A result
 * of 0 does not mean this known compiler correctness defect has been fixed.
 */
#include <stdint.h>
#include <stdio.h>

struct holder { int32_t *saved; };
extern int32_t test(struct holder *, struct holder *);

int main(void)
{
    struct holder first = {0}, second = {0};
    int32_t result = test(&first, &second);
    printf("Observed native result: %d; source semantics expects 0.\n",
           (int)result);
    puts("Known dangling-reference defect: native behavior is undefined; "
         "this observation is not a pass/fail oracle.");
    return (int)result;
}
