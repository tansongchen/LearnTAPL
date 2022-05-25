open Format
open Syntax
open Support.Error
open Support.Pervasive
open List

(* ------------------------   EVALUATION  ------------------------ *)

exception NoRuleApplies

let rec isnumericval ctx t = match t with
    TmZero(_) -> true
  | TmSucc(_,t1) -> isnumericval ctx t1
  | _ -> false

let rec isval ctx t = match t with
    TmTrue(_)  -> true
  | TmFalse(_) -> true
  | t when isnumericval ctx t  -> true
  | TmAbs(_,_,_,_) -> true
  | _ -> false

let rec eval1 ctx t = match t with
    TmApp(fi,TmAbs(_,x,tyT11,t12),v2) when isval ctx v2 ->
      termSubstTop v2 t12
  | TmApp(fi,v1,t2) when isval ctx v1 ->
      let t2' = eval1 ctx t2 in
      TmApp(fi, v1, t2')
  | TmApp(fi,t1,t2) ->
      let t1' = eval1 ctx t1 in
      TmApp(fi, t1', t2)
  | TmIf(_,TmTrue(_),t2,t3) ->
      t2
  | TmIf(_,TmFalse(_),t2,t3) ->
      t3
  | TmIf(fi,t1,t2,t3) ->
      let t1' = eval1 ctx t1 in
      TmIf(fi, t1', t2, t3)
  | TmSucc(fi,t1) ->
      let t1' = eval1 ctx t1 in
      TmSucc(fi, t1')
  | TmPred(_,TmZero(_)) ->
      TmZero(dummyinfo)
  | TmPred(_,TmSucc(_,nv1)) when (isnumericval ctx nv1) ->
      nv1
  | TmPred(fi,t1) ->
      let t1' = eval1 ctx t1 in
      TmPred(fi, t1')
  | TmIsZero(_,TmZero(_)) ->
      TmTrue(dummyinfo)
  | TmIsZero(_,TmSucc(_,nv1)) when (isnumericval ctx nv1) ->
      TmFalse(dummyinfo)
  | TmIsZero(fi,t1) ->
      let t1' = eval1 ctx t1 in
      TmIsZero(fi, t1')
  | _ -> 
      raise NoRuleApplies

let rec eval ctx t =
  try let t' = eval1 ctx t
      in eval ctx t'
  with NoRuleApplies -> t

(* ------------------------   TYPING  ------------------------ *)

let rec typeof ctx t =
  match t with
    TmVar(fi,i,_) -> getTypeFromContext fi ctx i
  | TmAbs(fi,x,tyT1,t2) ->
      let ctx' = addbinding ctx x (VarBind(tyT1)) in
      let tyT2 = typeof ctx' t2 in
      TyArr(tyT1, tyT2)
  | TmApp(fi,t1,t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      (match tyT1 with
          TyArr(tyT11,tyT12) ->
            if (=) tyT2 tyT11 then tyT12
            else error fi "parameter type mismatch"
        | _ -> error fi "arrow type expected")
  | TmTrue(fi) -> 
      TyBool
  | TmFalse(fi) -> 
      TyBool
  | TmIf(fi,t1,t2,t3) ->
     if (=) (typeof ctx t1) TyBool then
       let tyT2 = typeof ctx t2 in
       if (=) tyT2 (typeof ctx t3) then tyT2
       else error fi "arms of conditional have different types"
     else error fi "guard of conditional not a boolean"
  | TmZero(fi) ->
      TyNat
  | TmSucc(fi,t1) ->
      if (=) (typeof ctx t1) TyNat then TyNat
      else error fi "argument of succ is not a number"
  | TmPred(fi,t1) ->
      if (=) (typeof ctx t1) TyNat then TyNat
      else error fi "argument of pred is not a number"
  | TmIsZero(fi,t1) ->
      if (=) (typeof ctx t1) TyNat then TyBool
      else error fi "argument of iszero is not a number"

let rec ctypeof ctx t f =
  match t with
    TmVar(fi,i,_) -> getTypeFromContext fi ctx i, [], f
  | TmAbs(fi,x,tyT1,t2) ->
      let ctx' = addbinding ctx x (VarBind(tyT1)) in
      let tyT2, cst, f' = ctypeof ctx' t2 f in
      TyArr(tyT1, tyT2), cst, f'
  | TmApp(fi,t1,t2) ->
      let tyT1, cst1, f1 = ctypeof ctx t1 f in
      let tyT2, cst2, f2 = ctypeof ctx t2 f1 in
      let cst12 = List.append cst1 cst2 in
      let nuv = f2 () in
      (match nuv with
          NextUVar(id,f3) ->
            let tyX = TyId(id) in
            let tyT2X = TyArr(tyT2, tyX) in
            let newcst = (tyT1, tyT2X) in
            let cst = List.cons newcst cst12 in
            tyX, cst, f3)
  | TmTrue(fi) -> 
      TyBool, [], f
  | TmFalse(fi) -> 
      TyBool, [], f
  | TmIf(fi,t1,t2,t3) ->
     let tyT1, cst1, f1 = ctypeof ctx t1 f in
     let tyT2, cst2, f2 = ctypeof ctx t2 f1 in
     let tyT3, cst3, f3 = ctypeof ctx t3 f2 in
     let cst123 = List.append (List.append cst1 cst2) cst3 in
     let newcst1 = (tyT1, TyBool) in
     let newcst2 = (tyT2, tyT3) in
     let cst = List.cons newcst2 (List.cons newcst1 cst123) in
     tyT2, cst, f3
  | TmZero(fi) ->
      TyNat, [], f
  | TmSucc(fi,t1) ->
      let tyT1, cst, f' = ctypeof ctx t1 f in
      let newcst = (tyT1, TyNat) in
      let cst' = List.cons newcst cst in
      TyNat, cst', f'
  | TmPred(fi,t1) ->
      let tyT1, cst, f' = ctypeof ctx t1 f in
      let newcst = (tyT1, TyNat) in
      let cst' = List.cons newcst cst in
      TyNat, cst', f'
  | TmIsZero(fi,t1) ->
      let tyT1, cst, f' = ctypeof ctx t1 f in
      let newcst = (tyT1, TyNat) in
      let cst' = List.cons newcst cst in
      TyBool, cst', f'

let rec occur tyId tyT =
  match tyT with
    TyBool -> false
  | TyNat -> false
  | TyId(_) -> (=) tyId tyT
  | TyArr(tyT1, tyT2) -> (occur tyId tyT1) || (occur tyId tyT2)

let isId tyT = match tyT with TyId(_) -> true | _ -> false

let rec subty sigma tyT =
  match tyT with
    TyBool -> TyBool
  | TyNat -> TyNat
  | TyId(_) -> (try List.assoc tyT sigma with Not_found -> tyT)
  | TyArr(tyT1, tyT2) -> TyArr(subty sigma tyT1, subty sigma tyT2)

let rec sub sigma cst =
  match cst with
    [] -> []
  | (tyT1, tyT2) :: cst' -> (subty sigma tyT1, subty sigma tyT2) :: (sub sigma cst')

let rec compos sigma gamma =
  let component1 = List.map (fun (tyX, tyT) -> (tyX, subty sigma tyT)) gamma in
  let component2 = List.filter (fun (tyX, tyT) -> try let _ = List.assoc tyX gamma in false with Not_found -> true) sigma in
  List.append component1 component2

let rec unify cst =
  match cst with
    [] -> []
  | (tyS, tyT) :: cst' ->
      if (=) tyS tyT then unify cst'
      else if isId tyS && not (occur tyS tyT) then
        let cst'' = sub [(tyS, tyT)] cst' in
        compos (unify cst'') [(tyS, tyT)]
      else if isId tyT && not (occur tyT tyS) then
        let cst'' = sub [(tyT, tyS)] cst' in
        compos (unify cst'') [(tyT, tyS)]
      else (match tyS with
      TyArr(tyS1, tyS2) -> (match tyT with
        TyArr(tyT1, tyT2) ->
          let cst'' = (tyS1, tyT1) :: (tyS2, tyT2) :: cst' in
          unify cst''
      | _ -> error dummyinfo "unify fail!")
    | _ -> error dummyinfo "unify fail!")
