open Kat
open Common
open Syntax

open String
open Nat
module Coq = struct
  (* Extracted from Coq *)
  (* ****************************************************************** *)

(** val sub : int -> int -> int **)

let rec sub n m =
  (fun zero succ n ->       if n=0 then zero () else succ (n-1))
    (fun _ -> n)
    (fun k ->
    (fun zero succ n ->       if n=0 then zero () else succ (n-1))
      (fun _ -> n)
      (fun l -> sub k l)
      m)
    n

(** val eqb : char list -> char list -> bool **)

let rec eqb s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' ->
    (match s2 with
     | [] -> false
     | c2::s2' -> if (=) c1 c2 then eqb s1' s2' else false)

type 'bp texp =
| Teprim of 'bp
| Tenot of 'bp texp
| Teplus of 'bp texp * 'bp texp
| Teand of 'bp texp * 'bp texp
| Teone
| Tezero

type pTest =
| PTgt of char list * int

type pAct = char list
  (* singleton inductive, whose constructor was pAinc *)

(** val p_pre' : pTest -> pAct -> pTest texp list **)

let p_pre' t a =
  let PTgt (v, i) = t in
  if eqb v a
  then (Teprim (PTgt (v, (sub i ((fun x -> x + 1) 0)))))::[]
  else (Teprim (PTgt (v, i)))::[]

(** val subt_gt : char list -> int -> pTest list **)

let rec subt_gt v i =
  (fun zero succ n ->       if n=0 then zero () else succ (n-1))
    (fun _ -> (PTgt (v, 0))::[])
    (fun n -> (PTgt (v, n))::(subt_gt v n))
    i

(** val subt : pTest -> pTest list **)

let subt = function
| PTgt (v, i) -> subt_gt v i


end


(* A Kat Module, built from the Coq extracted Module *)

(* Mike's a = Dave's pTest. *)
(* Mike's p = Dave's pAct.  *)
let rec compare_p (p:Coq.pAct) = failwith "compare_p"
let rec compare_a (a:Coq.pTest) = failwith "compare_a"
let rec equal_p (p:Coq.pAct) = failwith "equal_p"
let rec equal_a (a:Coq.pTest) = failwith "equal_a"

module rec CoqNat : THEORY with type A.t = Coq.pTest and type P.t = Coq.pAct = struct
  module K = KAT (CoqNat)
  module Test = K.Test
  module Term = K.Term

  module P : CollectionType with type t = Coq.pAct = struct
    type t = Coq.pAct
    let compare = compare_p
    let hash = Hashtbl.hash
    let equal = equal_p
    let show = failwith "TODO:show P"
  end

  module A : CollectionType with type t = Coq.pTest = struct
    type t = Coq.pTest
    let compare = compare_a
    let hash = Hashtbl.hash
    let equal = equal_a
    let show = failwith "TODO:show A"
  end

  let name () = "coqnat"
  module Log = (val logger (name ()) : Logs.LOG)
                                            
(* It seems this is used by the library to get the var names. *)

  let variable =  failwith "variable"
 (* function 
    | Lincr x -> z3_var_nm x Lv
    | Rincr x -> z3_var_nm x Rv*)

  let variable_test = failwith "variable_test"
  (* function (* EJK: Should it be different vars? *)
    | Lgt (x,_) -> [z3_var_nm x Lv]
    | Rgt (x,_) -> [z3_var_nm x Rv]
    | Bdiff (x,_) -> [z3_var_nm x Lv;z3_var_nm x Rv]*)

  let parse name es = failwith "parse"
(*    match (name, es) with
    | "incL", [(EId s1)] -> Right (Lincr s1)
    | "incR", [(EId s1)] -> Right (Rincr s1)
    | "gtL",   [(EId s1); (EId s2)] -> Left (Lgt (s1, int_of_string s2))
    | "gtR",   [(EId s1); (EId s2)] -> Left (Rgt (s1, int_of_string s2))
    | "bdiff", [(EId s1); (EId s2)] -> Left (Bdiff (s1, int_of_string s2))
    | _, _ ->
        failwith ("Cannot create theory object from (" ^ name ^ ") and parameters")
*)

open BatSet

  let push_back p a = failwith "push_back"
(*
  match (p,a) with
    | (Lincr (_), Rgt(y,v)) -> PSet.singleton ~cmp:K.Test.compare (K.theory (Rgt (y, v))) (* followed by Lassign... *)
    | (Rincr (_), Lgt(y,v)) -> PSet.singleton ~cmp:K.Test.compare (K.theory (Lgt (y, v))) (* followed by Rassign... *)
    | (Lincr (x), Lgt (y,v)) when 1 > v -> PSet.singleton ~cmp:K.Test.compare (K.one ())
    | (Lincr (x), Lgt (y,v)) when x = y -> PSet.singleton ~cmp:K.Test.compare (K.theory (Lgt (y, v - 1)))
    | (Rincr (x), Rgt (y,v)) when 1 > v -> PSet.singleton ~cmp:K.Test.compare (K.one ())
    | (Rincr (x), Rgt (y,v)) when x = y -> PSet.singleton ~cmp:K.Test.compare (K.theory (Rgt (y, v - 1)))
    | (Rincr (x), Bdiff(y,v)) when x = y -> 
      PSet.singleton ~cmp:K.Test.compare (K.theory (Bdiff (y, v + 1)))
    | (Lincr (x), Bdiff(y,v)) when x = y -> 
      PSet.singleton ~cmp:K.Test.compare (K.theory (Bdiff (y, v - 1)))
    | _ -> failwith "push_back"
*)

  let rec subterms x =
    PSet.of_list ~cmp:K.Test.compare (List.map K.theory (Coq.subt x))
(*
  match x with
    | Lgt (_, 0) -> PSet.singleton ~cmp:K.Test.compare (K.theory x)
    | Lgt (v, i) -> PSet.add (K.theory x) (subterms (Lgt (v, i - 1)))
    | Rgt (_, 0) -> PSet.singleton ~cmp:K.Test.compare (K.theory x)
    | Rgt (v, i) -> PSet.add (K.theory x) (subterms (Rgt (v, i - 1)))
    | Bdiff (v, _) -> PSet.singleton ~cmp:K.Test.compare (K.theory x)
    (* Since Bdiff is exact, we don't need subterms like this:
    | Bdiff (v, i) -> PSet.add (K.theory x) (subterms (Bdiff (v, i - 1))) *)
    *)

  let simplify_and a b =
    match (a, b) with
    | Coq.PTgt(x, v1), Coq.PTgt(y, v2) when Coq.eqb x y -> Some (K.theory (Coq.PTgt (x, max v1 v2)))
    | _ -> None
(*
    match (a, b) with
    | Lgt (x, v1), Lgt (y, v2) when x = y -> Some (K.theory (Lgt (x, max v1 v2)))
    | Rgt (x, v1), Rgt (y, v2) when x = y -> Some (K.theory (Rgt (x, max v1 v2)))
    | Bdiff (x, v1), Bdiff (y, v2) when x = y && v1 = v2 -> Some (K.theory (Bdiff (x, v1)))
    | _, _ -> None*)

  let simplify_not a = None

  let simplify_or a b = None

  let merge (p1: P.t) (p2: P.t) : P.t = p2

  let reduce a p = Some p

  let unbounded () = true

  let create_z3_var (str,a) (ctx : Z3.context) (solver : Z3.Solver.solver) : Z3.Expr.expr = 
     failwith "create_z3_var"
    (*
    let sym = Z3.Symbol.mk_string ctx str in
    let int_sort = Z3.Arithmetic.Integer.mk_sort ctx in
    let xc = Z3.Expr.mk_const ctx sym int_sort in
    let is_nat =
      Z3.Arithmetic.mk_ge ctx xc (Z3.Arithmetic.Integer.mk_numeral_i ctx 0)
    in
    Z3.Solver.add solver [is_nat];
    xc

*)
  let theory_to_z3_expr (a : A.t) (ctx : Z3.context) (map : Z3.Expr.expr StrMap.t) : Z3.Expr.expr = 
     failwith "theory_to_z3_expr"
    (*
    match a with
    | Lgt (x, v)
    | Rgt (x, v) ->
        let var = StrMap.find (z3_var_nm x (lr_of_a a)) map in 
        let value = Z3.Arithmetic.Integer.mk_numeral_i ctx v in
        Z3.Arithmetic.mk_gt ctx var value
    | Bdiff (x,v) ->
        let varL = StrMap.find (z3_var_nm x Lv) map in 
        let varR = StrMap.find (z3_var_nm x Rv) map in 
        let df = Z3.Arithmetic.mk_sub ctx [varR;varL] in (* exact *)
        let value = Z3.Arithmetic.Integer.mk_numeral_i ctx v in
        Z3.Boolean.mk_eq ctx df value

  module H = Hashtbl.Make (K.Test)

  let tbl = H.create 2048

  let rec can_use_fast_solver (a: K.Test.t) =
    match a.node with
    | One | Zero | Placeholder _ | Theory _ -> true
    | PPar _ -> false
    | PSeq (b, c) -> can_use_fast_solver b && can_use_fast_solver c
    | Not {node= Theory _} -> true
    | Not _ -> false
*)
  let satisfiable (a: K.Test.t) = failwith "sat"
(*
    try H.find tbl a with _ ->
      if true (* not (can_use_fast_solver a) *)
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
          | One | Zero | Placeholder _ -> failwith "IncNat: satisfiability"
          | Not b -> StrMap.map Range.negate (aux b)
          | PPar (b, c) -> mergeOp (aux b) (aux c) Range.union
          | PSeq (b, c) -> mergeOp (aux b) (aux c) Range.inter
          | Theory Gt (x, v) ->
              StrMap.singleton x (Range.from_range (v + 1, max_int))
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
      *)
end

  (* ****************************************************************** *)
(*  let pset_of_ppre_list p = failwith "todo"*)
  (* construct a PSet, with a fold (over the list generated by p_pre') that uses Coq.subt *)
  
(*  Decide.equivalent  *)

(*  PSet.of_list cmp   Coq.subt *)

      (*   [@@deriving eq, ord] *)