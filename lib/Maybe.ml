open! Base

type doesExist = DoesExist [@@deriving sexp_of]
type doesNotExist = DoesNotExist [@@deriving sexp_of]

(* The reason for using this instead of Option, is that you can force *)
(* 'subtypes' to have/not have the optional value by using the 'e part of the type. *)
(* Maybe it would be possible to use Some/None for the same extent but it is *)
(* probably not nearly as nice. *)
(* See example in Corn, where LoopKernels *need* to have a consumer *)
(* While LoopBlock can either have or not have it. *)

type ('a, 'e) t =
  | Just : 'a -> ('a, doesExist) t
  | Nothing : (_, doesNotExist) t
[@@deriving sexp_of]

let map : type a b e. (a, e) t -> f:(a -> b) -> (b, e) t =
  fun m ~f ->
  match m with
  | Just v -> Just (f v)
  | Nothing -> Nothing
;;
