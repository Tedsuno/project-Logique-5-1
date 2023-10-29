(* MP1 2023/2024 - dpll.ml *)

open List

(* fonctions utilitaires *)
(* ----------------------------------------------------------- *)
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
let coloriage = [
  [1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];
  [19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];
  [-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];
  [-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];
  [-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];
  [-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];
  [-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];
  [-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];
  [-14;-17];[-15;-18]]

(* ----------------------------------------------------------- *)

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai *)
   let simplifie l clauses =
    (* Enlever la clause si le littéral l est à vrai *)
    let clause_supr = List.filter (fun clause -> (List.mem l clause) = false) clauses in
    (* Enlever le littéral l s'il est faux *)
    List.map (fun clause -> List.filter (fun x -> x <> (-l)) clause) clause_supr
  ;;

(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* la clause vide n'est jamais satisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
(* let () = print_modele (solveur_split systeme []) *)
(* let () = print_modele (solveur_split coloriage []) *)

(* solveur dpll récursif *)
(* ----------------------------------------------------------- *)

(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)
    let pur clauses = 
      (* Applatit la liste de liste pour faciliter la recherche.*)
      let flat = List.flatten clauses 
      in 
      let rec chercher memoire list_flat =
        match list_flat with 
        | [] -> failwith "pas de littéral pur"
        | a::r -> 
            if not (List.mem (-a) r) && not ( (List.mem (a) memoire) || (List.mem (-a) memoire) ) then
              a 
            else
              (*Mettre en mémoire les valeurs qui ne sont pas pures*) 
              chercher (a::memoire) r
      in chercher [] flat     
    ;;


(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)
    let unitaire clauses =
      (* On crée ici une fonction auxiliaire récursive (course) qui 
         parcours chaque clause de l'ensemble des clauses et qui vérifie
         si il existe une clause unitaire et la renvoie *)
      let rec course cls =
         match cls with
         | [] -> raise Not_found
         | a::r -> match a with
         (*Si ici [a] est une clause unitaire on renvoie son littéral a
          sinon on continue à chercher dans le reste (r) *)
                   | [a] -> a
                   | _ -> course r
      in course clauses
      
    (* solveur_dpll_rec : int list list -> int list -> int list option *)
    (* solveur dpll récursif *)
    let rec solveur_dpll_rec clauses interpretation =
      (*ON COMMENCE PAR VERIFIER LES CAS DE BASES :*)
      (* l'ensemble vide de clauses est satisfiable *)
      if clauses = [] then Some interpretation else
      (* la clause vide n'est jamais satisfiable *)
      if mem [] clauses then None else
      (* ENSUITE ON SUIT L'ALGORITHME DONNE EN COURS : *) 
        (*On commence par chercher une clause unitaire :*)
        try let unitaires = unitaire clauses in
          (*Si elle a été trouvé on rappelle DPLL en rajoutant le littéral dans l'interpretation :*)
          solveur_dpll_rec (simplifie unitaires clauses) (unitaires::interpretation) 
        with
        | Not_found -> 
          (*Si elle n'a pas été trouvé on cherche un littéral pur :*)
            try let pure = pur clauses in 
              (*Si le littéral pur a été trouvé 
               on rappelle DPLL en rajoutant le littéral dans l'interpretation *)
              solveur_dpll_rec (simplifie pure clauses) (pure::interpretation)
            with
            | Failure _ -> 
              (*Si le pur n'a pas été trouvé on prend le premier littéral qu'on trouve :*)
                let first=List.hd (List.hd clauses) in
                (*On l'étend' ici comme en cours à l'arbre*)
                let extension= solveur_dpll_rec(simplifie first clauses)(first::interpretation) in
                match extension with
                (*Si il ne trouve rien avec le littéral positif on teste avec sa forme négative*)
                | None -> solveur_dpll_rec (simplifie (-first) clauses ) ((-first)::interpretation)
                (*S'il trouve on renvoie finalement cette extension montré comme en cours*)
                | _ -> extension
    ;;





(* tests *)
(* ----------------------------------------------------------- *)
(* let () = print_modele (solveur_dpll_rec systeme []) *)
(* let () = print_modele (solveur_dpll_rec coloriage []) *)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])
