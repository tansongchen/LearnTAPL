(* module Core

   Core typechecking and evaluation functions
*)

open Syntax
open Support.Error

val eval : context -> term -> term 
val typeof : context -> term -> ty
val ctypeof : context -> term -> uvargenerator -> (ty * constr * uvargenerator)
val occur : ty -> ty -> bool
val isId : ty -> bool
val subty : subst -> ty -> ty
val sub : subst -> constr -> constr
val compos : subst -> subst -> subst
val unify : constr -> subst
