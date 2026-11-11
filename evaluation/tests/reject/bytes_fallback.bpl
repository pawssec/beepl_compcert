struct Header { kind : uint16 }
fun main (bytes p) : int32, [] { match p with | Pbytes h : struct Header [ kind : uint16 ] -> 1 }
