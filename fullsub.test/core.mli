(* module Core

   Core typechecking and evaluation functions
*)

open Syntax
open Support.Error

exception SubtypeFaliure of ty * ty

val eval : context -> term -> term 
val typeof : context -> term -> ty
val subtype : context -> ty -> ty -> unit
val tyeqv : context -> ty -> ty -> bool
val simplifyty : context -> ty -> ty
val evalbinding : context -> binding -> binding 
