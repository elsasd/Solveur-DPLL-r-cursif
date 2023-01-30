open List

(* fonctions utilitaires *********************************************)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let dependances = [[1];[-1;2];[-1;3;4;5];[-2;6];[-3;7];[-4;8;9];[-4;9];[-9;-6];[-9;-7];[-4;-5];[-8;-9];[-6;-7]]
let coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]]

(* simplifie : int -> int list list -> int list list
   applique la simplification de l'ensemble des clauses en mettant
   le littéral i à vrai *)

(* Si les clauses se réduisent à la clause vide,
      aucune simplification n'est à faire.
      Sinon on etudie les clauses une à une :
      Si le litteral i est dans la clause,
      elle est vraie, donc on peut l'ignorer, et on applique la
      simplification sur le reste des clauses.
      Si le litteral -i est pas dans la clause, on l'enleve simplement
      de la clause.
*)

let rec simplifie i clauses =
  match clauses with
  | [] -> []
  | l :: t ->
    if mem i l then
      simplifie i t
    else
      (filter (fun y -> y != -i) l) :: simplifie i t

(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* un clause vide est insatisfiable *)
  if mem [] clauses then None else
  (* branchement *)
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* test *)
(*let () = print_modele (solveur_split systeme [])
let () = print_modele (solveur_split dependances [])
let () = print_modele (solveur_split coloriage [])*)

(* solveur dpll récursif *)

(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)

(* On analyse les clauses une à une, si sa taille est egale a 1, elle
est unitaire et on retourne son litteral. *)

let unitaire clauses =
  match find (fun y -> length y = 1) clauses with
  | [x] -> x
  | _ -> raise Not_found


(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)

(* On analyse les clauses une à une:
       Si la clause est vide on appelle pur sur le reste des clauses.
       Sinon, on récupère le premier litteral (stocké dans x), et on cherche
       si dans les clauses il existe un litteral -x.
       Si non, le litteral est pur, on renvoie x.
       Si oui, on rappelle pur sur chaque element de la liste different de x
       ou de -x. *)

let rec pur clauses =
  match clauses with
  | [] -> raise (Failure "pas de littéral pur")
  | h :: t ->
    if h = [] then pur t else
    let x = hd h in
    if exists (mem (-x)) clauses then
      pur (map (filter (fun y -> y <> x && y <> (-x))) clauses)
    else
      x

(* solveur_dpll_rec : int list list -> int list -> int list option *)
    (* On commence par chercher une clause unitaire.
       Si on en trouve une on rappelle la fonction sur les clauses en les
       simplifiant (la valeur unitaire est mise à vrai).
       Sinon (une exception est levee), on cherche un litteral pur.
       Si on en touve on rappelle la fonction sur les clauses en les
       clauses, en les simplifiant (la valeur du litteral pur est mise a
       vrai).
       Sinon (une exception est levee), on applique la fonction split. *)
       
let rec solveur_dpll_rec clauses interpretation =
  match (try Some (unitaire clauses) with Not_found -> None) with
  | Some u ->
     solveur_dpll_rec (simplifie u clauses) (u :: interpretation)
  | _ ->
     match (try Some (pur clauses) with Failure _ -> None) with
     | Some p -> solveur_dpll_rec (simplifie p clauses)(p :: interpretation)
     | _ ->
        (* l'ensemble vide de clauses est satisfiable *)
        if clauses = [] then Some interpretation else
        (* un clause vide est insatisfiable *)
        if mem [] clauses then None else
        (* branchement *)
        let l = hd (hd clauses) in
        let branche = solveur_dpll_rec (simplifie l clauses) (l::interpretation) in
        match branche with
        | None -> solveur_dpll_rec (simplifie (-l) clauses) ((-l)::interpretation)
        | _    -> branche

(* tests *)

(*let () = print_modele (solveur_dpll_rec systeme [])
let () = print_modele (solveur_dpll_rec dependances [])
let () = print_modele (solveur_dpll_rec coloriage [])*)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])
