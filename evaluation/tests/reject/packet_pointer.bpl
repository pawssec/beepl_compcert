struct Header { ptr : int32* }
fun main (bytes p) : int32, [] { match p with | Pbytes h : struct Header [ ptr : int32* ] -> !ptr | Pbytes r : bytes [] -> 0 }
