type info = unit
let (dummyinfo : info) = ()

type term =
  | TmTrue of info
  | TmFalse of info
  | TmIf of info * term * term * term
  | TmZero of info
  | TmSucc of info * term
  | TmPred of info * term
  | TmIsZero of info * term

let rec isnumericval t =
  match t with
  | TmZero(_) -> true
  | TmSucc(_,t1) -> isnumericval t1
  | _ -> false

let rec isval t =
  match t with
  | TmTrue(_) -> true
  | TmFalse(_) -> true
  | t when isnumericval t -> true
  | _ -> false

exception NoRuleApplies

(* The single-step evaluator. *)
let rec eval1 (t : term) : term =
  match t with
  | TmIf(_,TmTrue(_),tt,_) -> tt  (* E-IfTrue *)
  | TmIf(_,TmFalse(_),_,tf) -> tf  (* E-IfFalse *)
  | TmIf(fi,t1,t2,t3) -> let t1' = eval1 t1 in TmIf(fi,t1',t2,t3)  (* E-If *)
  | TmSucc(fi,t1) -> let t1' = eval1 t1 in TmSucc(fi,t1')  (* E-Succ *)
  | TmPred(_,TmZero(_)) -> TmZero(dummyinfo)  (* E-PredZero *)
  | TmPred(_,TmSucc(_,nv1)) when (isnumericval nv1) -> nv1  (* E-PredSucc *)
  | TmPred(fi,t1) -> let t1' = eval1 t1 in TmPred(fi,t1')  (* E-Pred *)
  | TmIsZero(_,TmZero(_)) -> TmTrue(dummyinfo)  (* E-IsZeroZero *)
  | TmIsZero(_,TmSucc(_,nv1)) when (isnumericval nv1) -> TmFalse(dummyinfo)  (* E-IsZeroSucc *)
  | TmIsZero(fi,t1) -> let t1' = eval1 t1 in TmIsZero(fi,t1')  (* E-IsZero *)
  | _ -> raise NoRuleApplies

(* Its closure. *)
let rec eval (t : term) : term =
  try let t' = eval1 t in eval t'
  with NoRuleApplies -> t

(* The big-step evaluator. *)
let rec bigeval (t : term) : term =
  match t with
  | v when isval v -> v  (* B-Value *)
  | TmIf(_,c,tt,tf) ->
    match bigeval c with
    | TmTrue(_) -> bigeval tt  (* B-IfTrue *)
    | TmFalse(_) -> bigeval tf  (* B-IfFalse *)
    | _ -> raise NoRuleApplies
  | TmSucc(fi,t1) ->
    match bigeval t1 with
    | nv1 when isnumericval nv1 -> TmSucc(fi,nv1)  (* B-Succ *)
    | _ -> raise NoRuleApplies
  | TmPred(fi,t1) ->
    match bigeval t1 with
    | TmZero(_) -> TmZero(dummyinfo)  (* B-PredZero *)
    | TmSucc(_,nv1) when isnumericval nv1 -> nv1  (* B-PredSucc *)
    | _ -> raise NoRuleApplies
  | TmIsZero(fi,t1) ->
    match bigeval t1 with
    | TmZero(_) -> TmTrue(dummyinfo)  (* B-IsZeroZero *)
    | TmSucc(_,nv1) when isnumericval nv1 -> TmFalse(dummyinfo)  (* B-IsZeroSucc *)
    | _ -> raise NoRuleApplies
  | _ -> raise NoRuleApplies
