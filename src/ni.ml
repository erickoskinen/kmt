open Kat
open Syntax
open Common
open Hashcons
open Range

(* Notes: 
     * Need to implement pushback
     * Must use different var names for left and right program or else Z3 will treat them as the same program.
       (this could be fixed by a global refactor of crease_z3_var)
*)
type a =
   | Lgt of string * int 
   | Rgt of string * int 
   | Bieq of string
   [@@deriving eq]

type p =
   | Lassign of string * int  |  Lincr of string
   | Rassign of string * int  |  Rincr of string
   [@@deriving eq]

let compare_k x n y m =
  let cmp = StrType.compare x y in
  if cmp <> 0 then cmp
  else n - m

let compare_a a1 a2 =
  match (a1,a2) with
  | Lgt(x,n),Lgt(y,m) | Rgt(x,n),Rgt(y,m) | Lgt(x,n),Rgt(y,m) | Rgt(x,n),Lgt(y,m) -> compare_k x n y m
  | Bieq(s),Bieq(t) -> StrType.compare s t 
  | _,Bieq(_) -> -1
  | Bieq(_),_ -> 1
  | Rgt(_,_),_ -> 1
  | _,Rgt(_,_) -> -1
  | Lgt(_,_),_ -> 1
  | _,Lgt(_,_) -> -1

(* Needed for Z3 var subscripting *)
type side = Lv | Rv
let str_of_side = function Lv -> "L" | Rv -> "R"
let z3_var_nm str (lr:side) : string = str ^ (str_of_side lr)
let lr_of_a a : side = 
  match a with 
  | Lgt(_,_) -> Lv
  | Rgt(_,_) -> Rv
  | Bieq(_) -> failwith "bieq in lr_of_a"

let compare_p p1 p2 =
  match (p1,p2) with 
  | (Lassign(x,_),Lassign(y,_)) 
  | (Rassign(x,_),Rassign(y,_)) 
  | (Lincr(x),Lincr(y)) 
  | (Rincr(x),Rincr(y)) -> StrType.compare x y
  | (Lassign(_,_),_) -> 1
  | (Rassign(_,_),_) -> 1
  | (Lincr(_),_) -> -1
  | (Rincr(_),_) -> 1

module rec NI : THEORY with type A.t = a and type P.t = p = struct
  module K = KAT (NI)
  module Test = K.Test
  module Term = K.Term

  module P : CollectionType with type t = p = struct
    type t = p
    let compare = compare_p
    let hash = Hashtbl.hash
    let equal = equal_p
    let show = function
      | Lincr x -> "incL (" ^ x ^ ")"
      | Rincr x -> "incR (" ^ x ^ ")"
      | Lassign (x,i) -> "setL (" ^ x ^ "," ^ string_of_int i ^ ")"
      | Rassign (x,i) -> "setR (" ^ x ^ "," ^ string_of_int i ^ ")"
  end

  module A : CollectionType with type t = a = struct
    type t = a
    let compare = compare_a
    let hash = Hashtbl.hash
    let equal = equal_a
    let show = function
      | Lgt (x, n) -> x ^ " >L " ^ string_of_int n
      | Rgt (x, n) -> x ^ " >R " ^ string_of_int n
      | Bieq (x) -> x ^ "bieq (" ^ x ^ ")"
  end

  let name () = "ni"
  module Log = (val logger (name ()) : Logs.LOG)
                                            
(* It seems this is used by the library to get the var names. *)

  let variable =  function (* EJK: Should it be different vars? *)
    | Lincr x
    | Lassign (x,_) -> z3_var_nm x Lv
    | Rincr x
    | Rassign (x,_) -> z3_var_nm x Rv

  let variable_test = function (* EJK: Should it be different vars? *)
    | Lgt (x,_) -> x
    | Rgt (x,_) -> x
    | Bieq (x) -> x

  let parse name es =
    match (name, es) with
    | "incL", [(EId s1)] -> Right (Lincr s1)
    | "setL", [(EId s1);EId s2] -> Right (Lassign (s1, int_of_string s2))
    | "incR", [(EId s1)] -> Right (Rincr s1)
    | "setR", [(EId s1);EId s2] -> Right (Rassign (s1, int_of_string s2))
    | ">L",   [(EId s1); (EId s2)] -> Left (Lgt (s1, int_of_string s2))
    | ">R",   [(EId s1); (EId s2)] -> Left (Rgt (s1, int_of_string s2))
    | "bieq", [(EId s1)] -> Left (Bieq (s1))
    | _, _ ->
        failwith ("Cannot create theory object from (" ^ name ^ ") and parameters")

  open BatSet

  let push_back p a = failwith "push_back"
  (*
    match (p,a) with
    | (Increment x, Gt (_, j)) when 1 > j -> PSet.singleton ~cmp:K.Test.compare (K.one ())
    | (Increment x, Gt (y, j)) when x = y ->
       PSet.singleton ~cmp:K.Test.compare (K.theory (Gt (y, j - 1)))
    | (Assign (x,i), Gt (y,j)) when x = y -> PSet.singleton ~cmp:K.Test.compare (if i > j then K.one () else K.zero ())
    | _ -> PSet.singleton ~cmp:K.Test.compare (K.theory a)*)


  let rec subterms x =
    match x with
    | Lgt (_, 0) -> PSet.singleton ~cmp:K.Test.compare (K.theory x)
    | Lgt (v, i) -> PSet.add (K.theory x) (subterms (Lgt (v, i - 1)))
    | Rgt (_, 0) -> PSet.singleton ~cmp:K.Test.compare (K.theory x)
    | Rgt (v, i) -> PSet.add (K.theory x) (subterms (Rgt (v, i - 1)))


  let simplify_and a b =
    match (a, b) with
    | Lgt (x, v1), Lgt (y, v2) when x = y -> Some (K.theory (Lgt (x, max v1 v2)))
    | Rgt (x, v1), Rgt (y, v2) when x = y -> Some (K.theory (Rgt (x, max v1 v2)))
    | _, _ -> None


  let simplify_not a = None

  let simplify_or a b = None

  let merge (p1: P.t) (p2: P.t) : P.t = p2

  let reduce a p = Some p

  let unbounded () = true

  let create_z3_var (str,a) (ctx : Z3.context) (solver : Z3.Solver.solver) : Z3.Expr.expr = 
    let sym = Z3.Symbol.mk_string ctx str in
    let int_sort = Z3.Arithmetic.Integer.mk_sort ctx in
    let xc = Z3.Expr.mk_const ctx sym int_sort in
    let is_nat =
      Z3.Arithmetic.mk_ge ctx xc (Z3.Arithmetic.Integer.mk_numeral_i ctx 0)
    in
    Z3.Solver.add solver [is_nat];
    xc


  let theory_to_z3_expr (a : A.t) (ctx : Z3.context) (map : Z3.Expr.expr StrMap.t) : Z3.Expr.expr = 
    match a with
    | Lgt (x, v)
    | Rgt (x, v) ->
        let var = StrMap.find (z3_var_nm x (lr_of_a a)) map in 
        let value = Z3.Arithmetic.Integer.mk_numeral_i ctx v in
        Z3.Arithmetic.mk_gt ctx var value
    | Bieq x ->
        let varL = StrMap.find (z3_var_nm x Lv) map in 
        let varR = StrMap.find (z3_var_nm x Rv) map in 
        Z3.Boolean.mk_eq ctx varL varR

  module H = Hashtbl.Make (K.Test)

  let tbl = H.create 2048

  let rec can_use_fast_solver (a: K.Test.t) =
    match a.node with
    | One | Zero | Placeholder _ | Theory _ -> true
    | PPar _ -> false
    | PSeq (b, c) -> can_use_fast_solver b && can_use_fast_solver c
    | Not {node= Theory _} -> true
    | Not _ -> false

  let satisfiable (a: K.Test.t) =
    try H.find tbl a with _ ->
      if not (can_use_fast_solver a)
      then
        begin
          Log.debug (fun m -> m "%s taking SLOW path" (K.Test.show a));
          let ret = K.z3_satisfiable a in
          H.add tbl a ret ; ret
        end
      else begin
        Log.debug (fun m -> m "%s taking FAST path" (K.Test.show a)) ;
        let mergeOp map1 map2 op =
          StrMap.merge
            (fun _ v1 v2 ->
              match (v1, v2) with
              | None, _ -> v2
              | _, None -> v1
              | Some x, Some y -> Some (op x y) )
            map1 map2
        in
        let rec aux (a: K.Test.t) : Range.t StrMap.t =
          match a.node with
          | One | Zero | Placeholder _ -> failwith "NI: satisfiability"
          | Not b -> StrMap.map Range.negate (aux b)
          | PPar (b, c) -> mergeOp (aux b) (aux c) Range.union
          | PSeq (b, c) -> mergeOp (aux b) (aux c) Range.inter
          | Theory Lgt (x, v) ->
              StrMap.singleton (z3_var_nm x Lv) (Range.from_range (v + 1, max_int))
          | Theory Rgt (x, v) ->
              StrMap.singleton (z3_var_nm x Rv) (Range.from_range (v + 1, max_int))
          | Theory Bieq (x) ->
              failwith "aux todo"
        in
        match a.node with
        | One -> true
        | Zero -> false
        | _ ->
            let result = aux a in
            let ret =
              StrMap.for_all (fun _ r -> not (Range.is_false r)) result
            in
            (* Printf.printf "Actual Result: %b\n" ret; *)
            H.add tbl a ret ; ret
        end
end
