(* Native binary guard edge cases; source unsafe operations return zero.
   From the repository root:
     make -C evaluation/tests binary-guards-native
   Or compile and run this test directly after building the native compiler:
     ./ccomp -typecheck -S evaluation/tests/accept/binary_guard_edges.bpl -o /tmp/beepl-binary-guard-edges.s
     gcc -no-pie /tmp/beepl-binary-guard-edges.s -o /tmp/beepl-binary-guard-edges
     /tmp/beepl-binary-guard-edges; echo $?
   Expected exit status: 0. Covers 32/64-bit signed zero divisors,
   min/-1 overflow, negative and width-sized counts, and valid counts.
*)
fun main() : int32, [] {
 let minimum : int32 = -2147483647 - 1 in
 let wide_minimum : long = (long)minimum * (long)65536 * (long)65536 in
 if ((8 / 0) == 0) then
 if ((8 % 0) == 0) then
 if ((minimum / -1) == 0) then
 if ((minimum % -1) == 0) then
 if ((1 << -1) == 0) then
 if ((1 >> -1) == 0) then
 if ((1 << 32) == 0) then
 if ((1 >> 32) == 0) then
 if (((long)8 / (long)0) == (long)0) then
 if (((long)8 % (long)0) == (long)0) then
 if ((wide_minimum / (long)(-1)) == (long)0) then
 if ((wide_minimum % (long)(-1)) == (long)0) then
 if (((long)1 << (long)(-1)) == (long)0) then
 if (((long)1 >> (long)(-1)) == (long)0) then
 if (((long)1 << (long)64) == (long)0) then
 if (((long)1 >> (long)64) == (long)0) then
 if (((long)3 << (long)2) == (long)12) then
 if (((long)16 >> (long)2) == (long)4) then 0
 else 18 else 17 else 16 else 15 else 14 else 13 else 12 else 11
 else 10 else 9 else 8 else 7 else 6 else 5 else 4 else 3 else 2 else 1
}
