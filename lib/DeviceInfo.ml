open! Base

type t =
  { maxThreadsPerBlock : int
  ; maxRegistersPerBlock : int
  ; maxThreadsPerMultiprocessor : int
  ; multiprocessors : int
  ; globalMemoryBytes : int
  }

let maxThreads device = device.maxThreadsPerMultiprocessor * device.multiprocessors

let grid_m10_8q =
  { maxThreadsPerBlock = 1024
  ; maxRegistersPerBlock = 65536
  ; maxThreadsPerMultiprocessor = 65530 (* a little under, experimenting right now *)
  ; multiprocessors = 5
  ; globalMemoryBytes = 8589934592
  }
;;
