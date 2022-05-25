open Format
open Syntax
open Support.Error
open Support.Pervasive

(* ------------------------   EVALUATION  ------------------------ *)

let rec isval ctx t = match t with
    TmTrue(_)  -> true
  | TmFalse(_) -> true
  | TmAbs(_,_,_,_) -> true
  | TmRecord(_,fields) -> List.for_all (fun (l,ti) -> isval ctx ti) fields
  | _ -> false

exception NoRuleApplies

let rec eval1 ctx t = match t with
    TmApp(fi,TmAbs(_,x,tyT11,t12),v2) when isval ctx v2 ->
      termSubstTop v2 t12
  | TmApp(fi,v1,t2) when isval ctx v1 ->
      let t2' = eval1 ctx t2 in
      TmApp(fi, v1, t2')
  | TmApp(fi,t1,t2) ->
      let t1' = eval1 ctx t1 in
      TmApp(fi, t1', t2)
  | TmRecord(fi,fields) ->
      let rec evalafield l = match l with 
        [] -> raise NoRuleApplies
      | (l,vi)::rest when isval ctx vi -> 
          let rest' = evalafield rest in
          (l,vi)::rest'
      | (l,ti)::rest -> 
          let ti' = eval1 ctx ti in
          (l, ti')::rest
      in let fields' = evalafield fields in
      TmRecord(fi, fields')
  | TmProj(fi, (TmRecord(_, fields) as v1), l) when isval ctx v1 ->
      (try List.assoc l fields
       with Not_found -> raise NoRuleApplies)
  | TmProj(fi, t1, l) ->
      let t1' = eval1 ctx t1 in
      TmProj(fi, t1', l)
  | TmIf(_,TmTrue(_),t2,t3) ->
      t2
  | TmIf(_,TmFalse(_),t2,t3) ->
      t3
  | TmIf(fi,t1,t2,t3) ->
      let t1' = eval1 ctx t1 in
      TmIf(fi, t1', t2, t3)
  | _ -> 
      raise NoRuleApplies

let rec eval ctx t =
  try let t' = eval1 ctx t
      in eval ctx t'
  with NoRuleApplies -> t

(* ------------------------   SUBTYPING  ------------------------ *)
(* join v meet ^ *)
let rec subtype tyS tyT =
   (=) tyS tyT ||
   match (tyS,tyT) with
     (_,TyTop) -> 
       true
   | (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
       (subtype tyT1 tyS1) && (subtype tyS2 tyT2)
   | (TyRecord(fS), TyRecord(fT)) ->
       List.for_all
         (fun (li,tyTi) -> 
            try let tySi = List.assoc li fS in
                subtype tySi tyTi
            with Not_found -> false)
         fT
   | (_,_) -> 
       false

let rec join tyS tyT =
   match (tyS,tyT) with
     (TyBool,TyBool) -> TyBool
   | (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
     TyArr(meet tyS1 tyT1, join tyS2 tyT2)
   | (TyRecord(fS), TyRecord(fT)) ->
       let fJ =
       let tmp = List.filter
         (fun (li,tyTi) -> 
            try let tySi = List.assoc li fS in true
            with Not_found -> false)
         fT in List.map (fun (li,tyTi) ->
         let tySj = List.assoc li fS in (li, join tySj  tyTi)) tmp in TyRecord(fJ)
   | (_,_) -> TyTop
  (* Write me assert false *)

and meet tyS tyT =
   match (tyS,tyT) with
     (_,TyTop) -> tyS
   | (TyTop,_) -> tyT
   | (TyBool,TyBool) -> TyBool
   | (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
     TyArr(join tyS1 tyT1, meet tyS2 tyT2)
   | (TyRecord(fS), TyRecord(fT)) ->
       let fJ =
       let tmp = List.map
         (fun (li,tyTi) -> 
            try let tySj = List.assoc li fS in (li,meet tySj tyTi)
            with Not_found -> (li,tyTi))
         fT in 
       let tmp2 = List.filter (fun (kj,tySj) -> try let tyTi = List.assoc kj fT in false with Not_found -> true) fS in List.append tmp tmp2
        in TyRecord(fJ)
   | (_,_) -> assert false
  (* Write me assert false *)

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
            if subtype tyT2 tyT11 then tyT12
            else error fi "parameter type mismatch"
        | _ -> error fi "arrow type expected")
  | TmRecord(fi, fields) ->
      let fieldtys = 
        List.map (fun (li,ti) -> (li, typeof ctx ti)) fields in
      TyRecord(fieldtys)
  | TmProj(fi, t1, l) ->
      (match (typeof ctx t1) with
          TyRecord(fieldtys) ->
            (try List.assoc l fieldtys
             with Not_found -> error fi ("label "^l^" not found"))
        | _ -> error fi "Expected record type")
  | TmTrue(fi) -> 
      TyBool
  | TmFalse(fi) -> 
      TyBool
  | TmIf(fi,t1,t2,t3) ->
      join (typeof ctx t2) (typeof ctx t3)
      (* write me assert false *)
