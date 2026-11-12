(* Guarded binary operations evaluate both operands once, left to right.
   From the repository root:
     make -C evaluation/tests binary-guards-native
   Or compile and run this test directly after building the native compiler:
     ./ccomp -typecheck -S evaluation/tests/accept/binary_guard_once.bpl -o /tmp/beepl-binary-guard-once.s
     gcc -no-pie /tmp/beepl-binary-guard-once.s -o /tmp/beepl-binary-guard-once
     /tmp/beepl-binary-guard-once; echo $?
   Expected exit status: 0. Native test, not a kernel-verifier test.
   The decimal trace checks ordering as well as the number of evaluations.
*)
fun mark(long* trace, int32 digit, int32 value) : int32, read, write {
 let _ : unit = trace := (!trace * (long)10 + (long)digit) in value
}
fun mark_wide(long* trace, int32 digit, long value) : long, read, write {
 let _ : unit = trace := (!trace * (long)10 + (long)digit) in value
}
fun direct_mod(int32 left, int32 right) : int32, [] { left % right }
fun main() : int32, alloc, read, write, read, write, read, write, read, write, read, write, read, write, read, write, read, write, read, write, read, write, read, write, read, write, read, write, read, write, read, write, read, write, read {
 let trace : long* = ref (long)0 in
 let quotient : int32 = mark(trace, 1, 8) / mark(trace, 2, 2) in
 let remainder : int32 = mark(trace, 3, 8) % mark(trace, 4, 3) in
 let shifted_left : int32 = mark(trace, 5, 3) << mark(trace, 6, 2) in
 let shifted_right : int32 = mark(trace, 7, 16) >> mark(trace, 8, 2) in
 let wide_quotient : long = mark_wide(trace, 1, (long)8) / mark_wide(trace, 2, (long)2) in
 let wide_remainder : long = mark_wide(trace, 3, (long)8) % mark_wide(trace, 4, (long)3) in
 let wide_left : long = mark_wide(trace, 5, (long)3) << mark_wide(trace, 6, (long)2) in
 let wide_right : long = mark_wide(trace, 7, (long)16) >> mark_wide(trace, 8, (long)2) in
 if (wide_quotient == (long)4) then
 if (wide_remainder == (long)2) then
 if (wide_left == (long)12) then
 if (wide_right == (long)4) then
 if (quotient == 4) then
 if (remainder == 2) then
 if (shifted_left == 12) then
 if (shifted_right == 4) then
 if (direct_mod(8, 3) == 2) then
 if (!trace == ((long)12345678 * (long)100000000 + (long)12345678)) then 0 else 6
 else 5 else 4 else 3 else 2 else 1 else 10 else 9 else 8 else 7
}
