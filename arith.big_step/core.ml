open Format
open Syntax
open Support.Error
open Support.Pervasive

(* ------------------------   EVALUATION  ------------------------ *)

exception NoRuleApplies

let rec isnumericval t = match t with
    TmZero(_) -> true
  | TmSucc(_,t1) -> isnumericval t1
  | _ -> false

let rec isval t = match t with
    TmTrue(_)  -> true
  | TmFalse(_) -> true
  | t when isnumericval t  -> true
  | _ -> false

let rec eval1 t = match t with
    TmIf(_,TmTrue(_),t2,t3) ->
      t2
  | TmIf(_,TmFalse(_),t2,t3) ->
      t3
  | TmIf(fi,t1,t2,t3) ->
      let t1' = eval1 t1 in
      TmIf(fi, t1', t2, t3)
  | TmSucc(fi,t1) ->
      let t1' = eval1 t1 in
      TmSucc(fi, t1')
  | TmPred(_,TmZero(_)) ->
      TmZero(dummyinfo)
  | TmPred(_,TmSucc(_,nv1)) when (isnumericval nv1) ->
      nv1
  | TmPred(fi,t1) ->
      let t1' = eval1 t1 in
      TmPred(fi, t1')
  | TmIsZero(_,TmZero(_)) ->
      TmTrue(dummyinfo)
  | TmIsZero(_,TmSucc(_,nv1)) when (isnumericval nv1) ->
      TmFalse(dummyinfo)
  | TmIsZero(fi,t1) ->
      let t1' = eval1 t1 in
      TmIsZero(fi, t1')
  | _ -> 
      raise NoRuleApplies

let rec eval t =
  try let t' = eval1 t
      in eval t'
  with NoRuleApplies -> t

let rec evalbig t = match t with
    TmIf(fi,t1,t2,t3) -> (match evalbig t1 with
      | TmTrue(_) when isval (evalbig t2) -> evalbig t2
      | TmFalse(_) when isval (evalbig t3) -> evalbig t3
      | _ -> t)
  | TmSucc(fi,t1) when isnumericval (evalbig t1) ->
      TmSucc(fi, evalbig t1)
  | TmPred(fi,t1) -> (match evalbig t1 with
      | TmZero(fi) -> TmZero(fi)
      | TmSucc(fi, nv1) when isnumericval nv1 -> nv1
      | _ -> t)
  | TmIsZero(fi,t1) -> (match evalbig t1 with
      | TmZero(fi) -> TmTrue(dummyinfo)
      | TmSucc(fi, nv1) when isnumericval nv1 -> TmFalse(dummyinfo)
      | _ -> t)
  | _ -> t
