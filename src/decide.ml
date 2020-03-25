open Kat
open Complete
open BatSet
open Hashcons
open Common
open SafeSet
open Automata

(* Decision procedure based on rewriting via normalization *)

module Decide (T : THEORY) = struct
  module K = T.K

  (* module C = CompleteTheory(T) *)

  type nf_elt = K.Test.t * K.Term.t

  type nf = nf_elt PSet.t

  (* locally ambiguous... same type, but useful as documentation *)
  type lanf = nf
          
  let compare_test (a: K.Test.t) (b: K.Test.t) = a.tag - b.tag

  let compare_nf_elt (a, b) (c, d) =
    let cmp = a.tag - c.tag in
    if cmp <> 0 then cmp else b.tag - d.tag

  let empty () = PSet.create compare_nf_elt

  let singleton x = PSet.singleton ~cmp:compare_nf_elt x

  let duplicate s i =
    let acc = ref "" in
    for j = 0 to i - 1 do acc := !acc ^ s done ;
    !acc

  let spaces i = duplicate " " (4 * i)

  let show_nf (x: nf) : string =
    let ret =
      PSet.fold
        (fun (test, term) acc ->
          let x = if acc = "" then acc else acc ^ ", " in
          x ^ "(" ^ K.Test.show test ^ "," ^ K.Term.show term ^ ")" )
        x ""
    in
    "{" ^ ret ^ "}"

  let rec flatten (a: K.Test.t) : K.Test.t PSet.t =
    match a.node with
    | Theory _ | PPar _ | One | Not _ -> PSet.singleton ~cmp:compare_test a
    | PSeq (b, c) -> PSet.union (flatten b) (flatten c)
    | Placeholder _ | Zero -> failwith "impossible"

  let rec size (a: K.Test.t) =
    match a.node with
    | Zero | One -> 0
    | Theory _ -> 1
    | PPar (b, c) | PSeq (b, c) -> 1 + size b + size c
    | Not b -> 1 + size b
    | Placeholder _ -> failwith "impossible"

  let seq_all (x: K.Test.t PSet.t) =
    PSet.fold (fun test acc -> K.pseq test acc) x (K.one ())

  let split (a: K.Test.t) (x: nf) : nf * nf =
    if PSet.is_empty x then (empty (), empty ())
    else
      let flat = PSet.map (fun (test, term) -> (flatten test, term)) x in
      let contains, missing =
        PSet.partition (fun (tests, _) -> PSet.mem a tests) flat
      in
      let contains =
        PSet.map
          (fun (tests, term) -> (PSet.remove a tests |> seq_all, term))
          contains
      in
      let missing =
        PSet.map (fun (tests, term) -> (seq_all tests, term)) missing
      in
      (contains, missing)

  let pick_mt (x: nf) : K.Test.t =
    let choices =
      PSet.fold
        (fun (test, _) acc -> PSet.union (flatten test) acc)
        x (PSet.create compare_test)
    in
    let choices = PSet.to_list choices in
    let choices = List.map (fun a -> (a, size a)) choices in
    let pick =
      List.fold_left
        (fun acc (a, size) ->
          match acc with
          | None -> Some (a, size)
          | Some (b, sizeb) -> if size > sizeb then Some (a, size) else acc )
        None choices
    in
    match pick with None -> failwith "impossible" | Some (a, _) -> a

  let zero = K.zero ()

  let one = K.one ()

  let stitch (a: K.Test.t) (x: nf) : nf =
    PSet.map (fun (test, term) -> (K.pseq a test, term)) x
    |> PSet.filter (fun (test, _) -> test.node <> Zero)

  (* nf insert *)
  (* MMG changing to this everywhere severely slows down Boolean-tree-ordering *)
  let nf_add ((a,m) : nf_elt) (x: nf) : nf =
    let (same, rest) = PSet.partition (fun (b, _n) -> a.tag = b.tag) x in
    let ns = PSet.map snd same in
    PSet.add (a, PSet.fold K.par ns m) rest
    
  (* nf union *)
  let nf_union (x: nf) (y: nf) : nf =
    PSet.fold nf_add x y
    
  let rec normalize (p: K.Term.t) : K.Term.t =
    let nf = normalize_term 0 p in
    debug (fun () -> Printf.printf "Full NF: %s\n" (show_nf nf)) ;
    let nf = nf |> PSet.to_list |> List.sort compare_nf_elt in
    let base = K.pred zero in
    List.fold_left
      (fun acc (test, term) -> K.par acc (K.seq (K.pred test) term))
      base nf

  and normalize_term (i: int) (p: K.Term.t) : nf =
    debug (fun () ->
        Printf.printf "%snormalize_term: %s\n" (spaces i) (K.Term.show p) ) ;
    match p.node with
    | Action _ -> singleton (one, p)
    | Pred a -> singleton (a, K.pred one)
    | Par (a, b) ->
        nf_union (normalize_term (i + 1) a) (normalize_term (i + 1) b)
    | Seq (a, b) ->
        push_back_j (i + 1)
          (normalize_term (i + 1) a)
          (normalize_term (i + 1) b)
    | Star a -> push_back_star (i + 1) (normalize_term (i + 1) a)


  and push_back_j (i: int) (x: nf) (y: nf) : nf =
    debug (fun () ->
        Printf.printf "%spush_back_j: %s and %s\n" (spaces i) (show_nf x)
          (show_nf y) ) ;
    let ret =
      PSet.fold
        (fun (test1, term1) acc ->
          PSet.fold
            (fun (test2, term2) acc2 ->
              let elts : nf = push_back_dot (i + 1) term1 test2 in
              let elts : nf =
                PSet.map
                  (fun (test, term) -> (K.pseq test1 test, K.seq term term2))
                  elts
              in
              let elts : nf =
                PSet.filter (fun (test, _) -> test.node <> Zero) elts
              in
              nf_union elts acc2 )
            y acc )
        x (empty ())
    in
    debug (fun () -> Printf.printf "%sresult: %s\n" (spaces i) (show_nf ret)) ;
    ret


  and push_back_dot (i: int) (m: K.Term.t) (a: K.Test.t) : nf =
    debug (fun () ->
        Printf.printf "%spush_back_dot: %s and %s\n" (spaces i) (K.Term.show m)
          (K.Test.show a) ) ;
    let ret =
      match (m.node, a.node) with
      | _, Zero -> singleton (zero, K.pred one)
      | _, One -> singleton (one, m)
      | Action (_, p), Theory a ->
          let x = K.push_back p a in
          PSet.map (fun t -> (t, m)) x
      | Action (_, p), Not a ->
          let nf = push_back_dot (i + 1) m a in
          let sum =
            PSet.fold (fun (test, term) acc -> K.ppar test acc) nf zero
          in
          let b = nnf (K.not sum) in
          singleton (b, m)
      | _, PSeq (a, b) ->
          let y = push_back_dot (i + 1) m a in
          let z = push_back_t (i + 1) y b in
          z
      | Seq (m, n), _ ->
          let x = push_back_dot (i + 1) n a in
          let y = push_back_r (i + 1) m x in
          y
      | _, PPar (a, b) ->
          nf_union (push_back_dot (i + 1) m a) (push_back_dot (i + 1) m b)
      | Par (m, n), _ ->

         nf_union (push_back_dot (i + 1) m a) (push_back_dot (i + 1) n a)
      | Star m', _ ->
          let x = push_back_dot (i + 1) m' a in
          let t, u = split a x in
          if PSet.is_empty t then
            let x = u in
            let y = push_back_r (i + 1) m x in
            PSet.add (a, K.pred one) y
          else
            let x = push_back_r (i + 1) m u in
            let y = push_back_star (i + 1) t in
            let z = push_back_j (i + 1) x y in
            let y = stitch a y in
            nf_union y z
      | _, Placeholder _ -> failwith "impossible"
      | Pred b, _ -> singleton (K.pseq b a, K.pred one)
    in
    debug (fun () -> Printf.printf "%sresult:%s\n" (spaces i) (show_nf ret)) ;
    ret


  and push_back_t (i: int) (x: nf) (a: K.Test.t) : nf =
    debug (fun () ->
        Printf.printf "%spush_back_t: %s and %s\n" (spaces i) (show_nf x)
          (K.Test.show a) ) ;
    let ret =
      PSet.fold
        (fun (test, term) acc ->
          let elts = push_back_dot (i + 1) term a in
          let elts : nf = PSet.map (fun (b, m') -> (K.pseq test b, m')) elts in
          nf_union elts acc )
        x (empty ())
    in
    debug (fun () -> Printf.printf "%sresult: %s\n" (spaces i) (show_nf ret)) ;
    ret


  and push_back_r (i: int) (m: K.Term.t) (x: nf) : nf =
    debug (fun () ->
        Printf.printf "%spush_back_t: %s and %s\n" (spaces i) (K.Term.show m)
          (show_nf x) ) ;
    let ret = PSet.fold
      (fun (test, term) acc ->
        let elts : nf = push_back_dot (i + 1) m test in
        let elts : nf = PSet.map (fun (a, p) -> (a, K.seq p term)) elts in
        nf_union elts acc )
      x (empty ())
    in
    debug (fun () -> Printf.printf "%sresult: %s\n" (spaces i) (show_nf ret)) ;
    ret

  (* and push_back_star_opt (i : int) (x : nf) : nf =
    debug (fun () -> Printf.printf "%spush_back_star_opt: %s\n" (spaces i) (show_nf x) ) ;
    let without_tests : nf = PSet.map (fun (a,p) -> (K.one(), p)) x in
    let total : nf ref = ref (singleton (K.one(), K.pred (K.one()))) in
    let acc = ref x in
    let break = ref false in
    let k = ref 0 in
    while (not !break) && (!k < 10) do 
      debug (fun () -> Printf.printf "%sacc now: %s\n" (spaces i) (show_nf !acc)); 
      let z1 = push_back_j (i+1) !acc x in
      let z2 = push_back_j (i+1) !acc without_tests in 
      if (PSet.equal z1 z2) then begin
        debug (fun () -> Printf.printf "%s[equal]: true\n" (spaces i));
        let stared : K.Term.t = 
          PSet.fold (fun (_,p) acc -> K.par acc p) without_tests (K.pred (K.zero()))
          |> K.star 
        in 
        let the_rest = PSet.map (fun (a,p) -> (a, K.seq p stared)) !acc in
        total := PSet.union !total the_rest;
        break := true
      end else begin
        debug (fun () -> Printf.printf "%s[equal]: false\n" (spaces i)); 
        total := PSet.union !total z1;
        acc := z1
      end;
      incr k
    done;
    if (!break) then begin
      debug (fun () -> Printf.printf "%sresult: %s\n" (spaces i) (show_nf !total)) ;
      !total
    end else failwith "CRAP" *)

  and push_back_star (i: int) (x: nf) : nf =
    debug (fun () -> Printf.printf "%spush_back_star: %s\n" (spaces i) (show_nf x) ) ;
    let ret =
      if PSet.is_empty x then singleton (one, K.pred one) (* StarZero *)
      else
        let a = pick_mt x in
        debug (fun () -> Printf.printf "%sMaximal test:%s\n" (spaces i) (K.Test.show a) ) ;
        let x, y = split a x in
        if PSet.is_empty y then
          if a.node == One then (* some weird optimization? MMG *) begin
              debug (fun () -> Printf.printf "%sHit a.node = One optimization\n" (spaces i));
            (* MMG 2020-03-25 dropping speculative code for non-tracing semantics *)
            (*            if K.unbounded () || true then *)
              let term =
                PSet.fold
                  (fun (test, term) acc -> K.par acc term)
                  x
                  (K.pred (K.zero ()))
              in
              singleton (a, K.star term)
(*            else
              let nf, b, k = fix (i + 1) x in
              let nf_b = repeatSeq (i + 1) x b in
              let nf_k = repeatSeq (i + 1) x k in
              let all = push_back_j (i + 1) nf_b nf_k in
              let all = push_back_j (i + 1) all nf in
              PSet.add (a, K.pred one) all *)
            end
          else
            let y = push_back_t (i + 1) x a in
            let t, u = split a y in
            match PSet.is_empty t with
            | true -> (* Slide *)
                let y = u in
                let y' = push_back_star (i + 1) y in
                let z = push_back_j (i + 1) y' x in
                let z = stitch a z in
                PSet.add (one, K.pred one) z
            | false -> (* Denest *)
                let x' = y in
                let t, u = split a x' in
                let y = push_back_star (i + 1) (nf_union t u) in
                let z = push_back_j (i + 1) y x in
                PSet.add (one, K.pred one) (stitch a z)
        else (* Denest *)
          let y' = push_back_star (i + 1) y in
          let x' = push_back_j (i + 1) x y' in
          let z = push_back_star (i + 1) (stitch a x') in
          push_back_j (i + 1) y' z
    in
    debug (fun () -> Printf.printf "%sresult: %s\n" (spaces i) (show_nf ret)) ;
    ret


  and fix (i: int) (nf: nf) : nf * int * int =
    let eq curr (prev, _) = PSet.equal curr prev in
    let rec aux prevs =
      let prev, i = List.hd prevs in
      let k = i + 1 in
      let curr = push_back_j i prev nf in
      match List.find_opt (eq curr) prevs with
      | None -> aux ((curr, k) :: prevs)
      | Some (_, i) -> (curr, i, k - i)
    in
    aux [(nf, 0)]


  (* returns 1 + x + x;x + x;x;x + ... + x^count *)
  and repeatSeq (i: int) (x: nf) (count: int) : nf =
    let xs : nf ref = ref (singleton (one, K.pred one)) in
    let acc : nf ref = xs in
    for j = 1 to count do
      xs := push_back_j i !xs x ;
      acc := nf_union !xs !acc
    done ;
    !acc


  and nnf (a: K.Test.t) : K.Test.t =
    match a.node with
    | Zero -> zero
    | One -> one
    | Theory _ -> a
    | PSeq (a, b) -> K.pseq (nnf a) (nnf b)
    | PPar (a, b) -> K.ppar (nnf a) (nnf b)
    | Not a -> nnfNeg a
    | Placeholder _ -> failwith ""


  and nnfNeg (a: K.Test.t) : K.Test.t =
    match a.node with
    | Zero -> one
    | One -> zero
    | Theory _ -> K.not a
    | Not a -> a
    | PPar (a, b) -> K.ppar (nnfNeg a) (nnfNeg b)
    | PSeq (a, b) -> K.pseq (nnfNeg a) (nnfNeg b)
    | Placeholder _ -> failwith ""

  (* general outline

       1. explosion into disjoint form (local unambiguity)
          prune obviously impossible cases (no SMT use at present)
       2. cross product (global unambiguity)
          prune impossible cases with SMT
       3. word comparison on like cases
   *)

  module Bits = BatBitSet
                     
  let all_possible_selections (n: int) : Bits.t list =
    let rec go ss i =
      if i = n
      then ss
      else let ss_without_i = List.map Bits.copy ss in
           List.iter (fun s -> Bits.set s i) ss; (* ss_with_i = ss *)
           go (ss_without_i @ ss) (i+1)
    in
    go [Bits.create n] 0 (* |> List.filter (fun s -> Bits.count s > 0) *)

  let array_select (x: nf_elt array) (n: int) (sel: Bits.t) : nf_elt PSet.t =
    let rec go i acc =
      if i = n
      then acc
      else
        let (a,_) as clause =
          if Bits.mem sel i
          then x.(i)
          else let (a,p) = x.(i) in
               (K.not a, K.pred (K.zero ()))
        in
        (* no pruning here---if a=0, leave it in and we'll clear it up in the locally_unambiguous form *)
        go (i+1) (PSet.add clause acc)
    in
    go 0 (empty ())
    
  let locally_unambiguous_form (x: nf) : lanf =
    let summands  = PSet.to_array x in
    let n         = Array.length summands in
    debug (fun () -> Printf.printf "translating %d summands in locally unambiguous form for %s\n" n (show_nf x));
    let sels      = all_possible_selections n |> List.map (array_select summands n) in
    debug (fun () -> Printf.printf "got %d disjunctions\n" (List.length sels));
    List.fold_right (fun (disj: nf) (xhat: nf) ->
        let (preds, acts) = List.split (PSet.to_list disj) in
        debug (fun () -> Printf.printf "disjunction: %s\n" (show_nf disj));
        let a = List.fold_right K.pseq preds (K.one ()) in
        (* if a is contradictory (i.e., 0 or unsat) we must drop it here *)
        if a.node = Zero || not (T.satisfiable a)
        then xhat
        else
          let p = List.fold_right K.par acts (K.pred (K.zero ())) in
          let clause = (a, p) in
          (* match p.node with
          | Pred pa when pa.node = Zero -> xhat
          | _ -> *) PSet.add clause xhat)
      sels (empty ())

  (* deciding equivalence of restricted actions *)

  (* PLAN: given two words of restricted actions, we need to test regex equality

     1. compute alphabets (if different, no way they're equal)
     2. intern each action as a pair of unique id and numeric entry in the alphabet
     3. generate the automata on the fly, using derivatives
     4. run the Hopcroft/Karp union-find algorithm to check equivalence

   *)

  type ra = K.Term.t
  type pi = (int * K.P.t)
          
  type alphabet = pi PSet.t
  let empty_alphabet () : alphabet =
    PSet.create
      (fun (i1,pi1) (i2,pi2) ->
        if i1 = i2
        then K.P.compare pi1 pi2
        else Pervasives.compare i1 i2)
                
  let alphabet_of (m: ra) : alphabet =
    let rec loop (m: ra) (sigma: alphabet) : alphabet =
      match m.node with
      | Action (i, pi) -> PSet.add (i, pi) sigma
      | Pred _ -> sigma
      | Par (n, o) -> loop n (loop o sigma)
      | Seq (n, o) -> loop n (loop o sigma)
      | Star n -> loop n sigma
    in
    loop m (empty_alphabet ())

  type letter = { pi: int; label: int }

  let show_letter l = "pi_" ^ string_of_int l.pi ^ " #" ^ string_of_int l.label
              
  type word = word_hons hash_consed
  and word_hons =
    | Emp
    | Eps
    | Ltr of letter
    | Alt of word * word
    | Cat of word * word
    | Str of word

  let equal_word x y =
    match (x, y) with
    | Emp, Emp | Eps, Eps -> true
    | Ltr l1, Ltr l2 -> l1 = l2
    | Alt (a, b), Alt (c, d) | Cat (a, b), Cat (c, d) ->
        a.tag = c.tag && b.tag = d.tag
    | Str a, Str b -> a.tag = b.tag
    | _, _ -> false

  let hash_word x =
    match x with
    | Emp -> 3
    | Eps -> 5
    | Ltr l -> 7 * (l.label + (11 * l.pi + 3))
    | Alt (a, b) -> 13 * (b.hkey + (17 * a.hkey + 19))
    | Cat (a, b) -> 23 * (b.hkey + (29 * a.hkey + 31))
    | Str a -> 37 * a.hkey + 41
           
  let tbl_word = Hashcons.create 8

  let hashcons_word = Hashcons.hashcons hash_word equal_word tbl_word

  let emp = hashcons_word Emp
  let eps = hashcons_word Eps
  let ltr l = hashcons_word (Ltr l)
  let alt w1 w2 =
    match w1.node, w2.node with
    | Emp, _ -> w2
    | _, Emp -> w1
    | _, _ -> if w1.tag = w2.tag
              then w1
              else hashcons_word (Alt (w1, w2))
  let cat w1 w2 =
    match w1.node, w2.node with
    | Eps, _ -> w2
    | _, Eps -> w1
    | _, _ -> hashcons_word (Cat (w1, w2))
            
  let str w =
    match w.node with
    | Emp -> eps
    | Eps -> eps
    | _ -> hashcons_word (Str w)
    
  module Word : CollectionType with type t = word = struct
    type t = word

    let equal x y = x.tag = y.tag
    let compare x y = x.tag - y.tag
    let hash x = x.hkey
    let show : t -> string =
      let rec alt w =
        match w.node with
        | Alt (w1, w2) -> alt w1 ^ " + " ^ alt w2
        | _ -> cat w

      and cat w =
        match w.node with
        | Cat (w1, w2) -> cat w1 ^ " + " ^ cat w2
        | _ -> str w

      and str w =
        match w.node with
        | Str w -> atom w ^ "*"
        | _ -> atom w

      and atom w =
        match w.node with
        | Ltr l -> show_letter l
        | Emp -> "false"
        | Eps -> "true"
        | _ -> "(" ^ alt w ^ " )"
      in
      alt
  end

  let word_of (m: ra) (sigma: alphabet) : word =
    let next_label = ref 0 in
    let new_label () =
      let lbl = !next_label in
      incr next_label;
      lbl
    in
    let tbl = PSet.to_array sigma in
    let lookup (pi: pi) : int =
      let rec loop (i: int) : int =
        if i = Array.length tbl
        then raise Not_found
        else if tbl.(i) = pi
        then i
        else loop (i + 1)
      in
      loop 0
    in    
    let rec word_of (m: ra) : word =
      match m.node with
      | Action (i, p) -> ltr { pi = lookup (i, p); label = new_label () }
      | Pred a ->
         begin match a.node with
         | Zero -> emp
         | One -> eps
         | _ -> failwith ("Unexpected predicate in word: " ^ K.Test.show a)
         end
      | Par (n, o) ->
         let w1 = word_of n in
         let w2 = word_of o in
         alt w1 w2
      | Seq (n, o) ->
         let w1 = word_of n in
         let w2 = word_of o in
         cat w1 w2
      | Star n ->
         str (word_of n)
    in
    word_of m

  let rec accepting (w: word) : bool =
    match w.node with
    | Eps -> true
    | Str _ -> true
    | Emp | Ltr _ -> false
    | Alt (w1, w2) -> accepting w1 || accepting w2
    | Cat (w1, w2) -> accepting w1 && accepting w2

  let rec derivative (w: word) (l: letter) : word option =
    match w.node with
    | Emp -> None
    | Eps -> None
    | Ltr l' -> if l.pi = l'.pi then Some eps else None
    | Alt (w1, w2) ->
       begin match derivative w1 l, derivative w2 l with
       | Some w1', Some w2' -> Some (alt w1' w2')
       | Some w1', None     -> Some w1'
       | None,     Some w2' -> Some w2'
       | _, _ -> None
       end
    | Cat (w1, w2) ->
       begin match derivative w1 l, derivative w2 l with
       | Some w1', Some w2' -> Some (alt (cat w1' w2) (if accepting w1 then w2' else emp))
       | Some w1', None     -> Some (cat w1' w2)
       | None,     Some w2' -> if accepting w1 then Some w2' else None
       | None,     None     -> None
       end
    | Str w_inner ->
       begin match derivative w_inner l with
       | Some w_inner' -> Some (cat w_inner' w)
       | None -> None
       end

  module UF = BatUref
  module WordMap = Hashtbl.Make(Word)
  type state = word UF.uref

  let find_state (m: state WordMap.t) (w: word) : state =
    match WordMap.find_opt m w with
    | None ->
       let state = UF.uref w in
       WordMap.add m w state;
       state
    | Some state -> state
             
  exception Acceptance_mismatch of word * word
            
  let equivalent_words (w1: word) (w2: word) (sigma: alphabet) : bool =
    let sigma = PSet.to_array sigma in
    let m : state WordMap.t = WordMap.create 16 in
    let start1 = find_state m w1 in
    let start2 = find_state m w2 in
    UF.unite start1 start2;
    let rec loop (l: (word * word) list) : bool =
      match l with
      | [] -> true (* all done! *)
      | (w1, w2)::l' ->
         let rec inner (i: int) : (word * word) list=
           if i = Array.length sigma
           then []
           else begin
               let c = { pi = Array.(i); label = -1 } in
               debug (fun () -> Printf.printf "comparing %s and %s on %s\n"
                                  (Word.show w1) (Word.show w2) (show_letter c));
               let push =
                 match derivative w1 c, derivative w2 c with
                 | None, None -> []
                 | Some w1c, Some w2c ->
                    begin
                      debug (fun () -> Printf.printf "comparing %s and %s on %s\n"
                                         (Word.show w1) (Word.show w2) (show_letter c));

                      let st1 = find_state m w1c in
                      let st2 = find_state m w2c in
                      if accepting w1c <> accepting w2c
                      then raise (Acceptance_mismatch (w1c, w2c))
                      else if not (UF.equal st1 st2)
                      then begin
                          debug (fun () -> Printf.printf "uniting...\n");                          
                          UF.unite st1 st2;
                          [(w1c,w2c)]
                      end
                      else []
                    end
                 | _, _ -> raise (Acceptance_mismatch (w1, w2))
               in
               push @ inner (i+1)
             end
         in
         try
           let app = inner 0 in
           debug (fun () -> Printf.printf "added %s\n" (show_list (fun (w1,w2) -> "(" ^ Word.show w1 ^ ", " ^ Word.show w2 ^ ")") app));
           loop (l' @ app)
         with Acceptance_mismatch (w1, w2) ->
           begin
             debug (fun () -> Printf.printf "%s and %s mismatch\n"
                                (Word.show w1) (Word.show w2));
             false
           end
    in
    loop [(w1, w2)]
                    
  let same_actions (m: K.Term.t) (n: K.Term.t) : bool =
    let sigma_m = alphabet_of m in
    let sigma_n = alphabet_of n in
    if PSet.equal sigma_m sigma_n
    then begin
        let sigma = sigma_m in
        let r = word_of m sigma in
        let s = word_of n sigma in
        debug (fun () -> Printf.printf "%s ~w~> %s\n" (K.Term.show m) (Word.show r));
        debug (fun () -> Printf.printf "%s ~w~> %s\n" (K.Term.show n) (Word.show s));
        if r.tag = s.tag
        then begin
            debug (fun () -> Printf.printf "same_tag = true (same tag)\n");
            true
          end
        else begin
          let same_words = equivalent_words r s sigma in
          debug (fun () -> Printf.printf "same_words = %b\n" same_words);
          same_words
          end
      end
    else begin
        debug (fun () -> Printf.printf "different alphabets, can't be equal\n");
        false
      end

  module A = Automata(K)
    
  let same_actions_automata (m: K.Term.t) (n: K.Term.t) : bool =
    if m.tag = n.tag
    then begin
        debug (fun () -> Printf.printf "same_action = true (same tag)\n");
        true
      end
    else begin
        let a1 = A.of_term m in
        let a2 = A.of_term n in
        let same_actions = A.equivalent a1 a2 in
        debug (fun () -> Printf.printf "same_actions = %b\n" same_actions);
        same_actions
      end
    
  (* ACTUAL EQUIVALENCE ROUTINE STARTS HERE *)
    
  let equivalent_lanf (xhat: lanf) (yhat: lanf) : bool =
    if PSet.equal xhat yhat
    then
      begin
        debug (fun () -> Printf.printf "syntactic equality on locally unambiguous forms\n");
        true
      end
    else if PSet.is_empty xhat || PSet.is_empty yhat (* handle emptiness! *)
    then 
      begin
        debug (fun () -> Printf.printf "empty NF, checking for emptiness of both\n");
        PSet.is_empty xhat && PSet.is_empty yhat
      end
    else
      PSet.fold
        (fun (a1, m1) acc ->
          PSet.fold (fun (a2, m2) acc2 ->
              let adots = K.pseq a1 a2 in
              debug (fun () -> Printf.printf "checking adots=%s (from %s and %s)...%!" (K.Test.show adots) (K.Test.show a1) (K.Test.show a2));
              (* if the conjunction is 0 or unsat, we drop it *)
              if adots.node = Zero || not (T.satisfiable adots)
              then 
                begin
                  debug (fun () -> Printf.printf "skipping unsatisfiable case\n");
                  acc2
                end
              else 
                begin
                  acc2 && same_actions m1 m2
                end) yhat acc)
        xhat true

  let equivalent_nf (nx: nf) (ny: nf) : bool =
    (* optimization: just if syntactically equal first *)
    if PSet.equal nx ny
    then
      begin
        debug (fun () -> Printf.printf "syntactic equality on %s\n" (show_nf nx));
        true
      end
    else begin
        debug (fun () -> Printf.printf
                           "running cross product on %s and %s\n"
                           (show_nf nx) (show_nf ny));
        let xhat = locally_unambiguous_form nx in
        debug (fun () -> Printf.printf "%s is locally unambiguous as %s\n" (show_nf nx) (show_nf xhat));
        let yhat = locally_unambiguous_form ny in
        debug (fun () -> Printf.printf "%s is locally unambiguous as %s\n" (show_nf ny) (show_nf yhat));
        equivalent_lanf xhat yhat
      end
    
  let equivalent (p: K.Term.t) (q: K.Term.t) : bool =
    let nx = normalize_term 0 p in
    let ny = normalize_term 0 q in
    equivalent_nf nx ny

  let equivalence_classes_lanf (l: lanf list) : (lanf list) list =
    let rec add (x: lanf) (eqs: (lanf list) list) : (lanf list) list =
      match eqs with
      | [] -> [[x]]
      | cls::eqs ->
         begin match cls with
         | [] -> add x eqs (* should never happen *)
         | (rep::_) ->
            if equivalent_lanf x rep
            then (x::cls)::eqs
            else cls::add x eqs
         end
    in
    List.fold_right add l []

end
