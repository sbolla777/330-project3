open List
open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma: 's list;
  qs: 'q list;
  q0: 'q;
  fs: 'q list;
  delta: ('q, 's) transition list;
}

(***********)
(* Utility *)
(***********)

(* explode converts a string to a character list *)
let explode (s: string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in
  exp (String.length s - 1) []

(****************)
(* Part 1: NFAs *)
(****************)

let move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list = 
  let rec helper translst state symbol resultlst = match translst with
    | [] -> resultlst
    | (start, transition, dest) :: rest ->
        if (start = state && transition = symbol && not(List.mem dest resultlst)) then
          helper rest state symbol (dest :: resultlst)
        else
          helper rest state symbol resultlst
  in
  List.fold_left (fun lst state -> helper nfa.delta state s lst) [] qs
         

let e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list =
  let rec helper transitionlst state visited = match transitionlst with
    | [] -> visited
    | (start, transition, dest) :: rest ->
      if (Option.is_none transition) && (start = state) && not (List.mem dest visited) then
        let new_visited = helper nfa.delta dest (dest :: visited) in
        helper rest state new_visited
      else
        helper rest state visited
  in
  let closure = List.fold_left (fun acc state -> helper nfa.delta state acc) qs qs in
  List.sort_uniq Stdlib.compare closure

let accept (nfa: ('q,char) nfa_t) (s: string) : bool =
  let rec process states exp = match exp with
    | [] -> List.exists (fun state -> List.mem state nfa.fs) states
    | s :: rest ->
      let aftermove = move nfa states (Some s) in
      let afterclosure = e_closure nfa aftermove in
      process afterclosure rest
  in
  let fstclosure = e_closure nfa [nfa.q0] in
  let charlst = explode s in
  process fstclosure charlst

(*******************************)
(* Part 2: Subset Construction *)
(*******************************)

let new_states (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  List.map (fun s -> e_closure nfa (move nfa qs (Some s))) nfa.sigma

let new_trans (nfa: ('q,'s) nfa_t) (qs: 'q list) : ('q list, 's) transition list =
  List.map (fun s -> (qs, Some s, e_closure nfa (move nfa qs (Some s)))) nfa.sigma

let new_finals (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  if (List.exists (fun state -> List.mem state nfa.fs) qs) then [qs] else []

let rec nfa_to_dfa_step (nfa: ('q,'s) nfa_t) (dfa: ('q list, 's) nfa_t)
    (work: 'q list list) : ('q list, 's) nfa_t = match work with
  | [] -> dfa
  | curr :: rest -> 
    let transitions = new_trans nfa curr in
    let states = List.map (fun (start, trans, dest) -> dest) transitions in
    let newdfa = {sigma = dfa.sigma; qs = insert curr dfa.qs; q0 = dfa.q0; fs = if List.exists (fun state -> List.mem state nfa.fs) curr then insert curr dfa.fs else dfa.fs; delta = insert_all transitions dfa.delta} in
    let newwork = List.fold_left (fun lst state -> if elem state newdfa.qs then lst else state :: lst) rest states in
    nfa_to_dfa_step nfa newdfa newwork

let nfa_to_dfa (nfa: ('q,'s) nfa_t) : ('q list, 's) nfa_t =
  let start = e_closure nfa [nfa.q0] in
  let dfa = {sigma = nfa.sigma; qs = []; q0 = start; fs = []; delta = []} in
  nfa_to_dfa_step nfa dfa [start]
