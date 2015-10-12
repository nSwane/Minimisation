(*
Author : Nawaoui Swane & Stahl Gustave
Groupe : MIN International
Subject: Minimisation
*)

open List;;
open Sys;;

(*-----------------------------------------------------------------------*)
(*-------------------------SOME USEFUL FUNCTIONS-------------------------*)
(*-----------------------------------------------------------------------*)

let rec belong_to = fun x seq -> 
	match seq with
	| [] -> false
	| e::s -> (e=x) || belong_to x s
;;
 

let rec prive_de_1 = fun s1 s2 -> 
	match s1 with
	| [] -> []
	|e1::s -> if (belong_to e1 s2) then (prive_de_1 s s2)
			else e1::(prive_de_1 s s2)
;;

let rec prive_de_2 = fun x_list x_list_list ->
	match x_list_list with
	| [] -> []
	| e_list::s_list_list -> (prive_de_1 e_list x_list)::(prive_de_2 x_list s_list_list)
;;


let rec create_doublet_list = fun elt elt_list ->
	match elt_list with
	| [] -> []
	| e::s -> (elt,e)::(create_doublet_list elt s)
;;

let rec create_all_doublet_list = function seq ->
	match seq with
	| [] -> []
	|e::s -> (create_doublet_list e seq)@(create_all_doublet_list s)
;;

 
let rec doublet_to_seq = function doublet_list ->
	match doublet_list with
	| [] -> []
	| (q,p)::s -> q::(doublet_to_seq s)
;;

let rec doublet_to_seq_list = fun doublet_list_list ->
	 match doublet_list_list with
	| [] -> []
	| s1::ss -> (doublet_to_seq s1)::(doublet_to_seq_list ss)
;;


let rec supp_occ = function seq ->
	match seq with
	| [] -> []
	| e::s when (belong_to e s) -> supp_occ s
	| e::s -> e::(supp_occ s)
;;

let rec supp_occ_list = function seq_list_list ->
	match seq_list_list with
	| [] -> []
	| s1::ss -> (supp_occ s1)::(supp_occ_list ss)
;;

(*-------------------------------------------------------------------------------------*)	
(*----------------------------CREATION OF EQUIVALENCE CLASSES--------------------------*)
(*-------------------------------------------------------------------------------------*)

let rec not_same_class = fun auto (q,p) alphabet set_of_set -> 
	match alphabet with
	| [] -> false
	| a::b -> match set_of_set with
		  | [] -> false
		  | s1::ss -> let c1=(read_symbol_state auto q a) and c2=(read_symbol_state auto p a) in
		 	      ( ( (belong_to (c1,c1) s1) )  && ( not(belong_to (c2,c2) s1) ) ||
		   	      ( not_same_class auto (q,p) [a] ss) ||
		   	      ( not_same_class auto (q,p) b set_of_set) ) 
;;


let rec first_elt_of_a_class = fun auto doublet_list set_of_equ_class ->
	let (_,alphabet,_,_,_) = auto in
	
	match doublet_list with
	| [] -> []
	| (p,q)::s when (not_same_class auto (p,q) alphabet set_of_equ_class)-> 
		(p,q)::first_elt_of_a_class auto s set_of_equ_class
	| (p,q)::s -> first_elt_of_a_class auto s set_of_equ_class

;;

let rec create_new_class = fun auto set_R set_of_equ_class_bis ->
	match set_R with
	| [] -> []
	| s1::ss -> (first_elt_of_a_class auto s1 set_of_equ_class_bis)@(create_new_class auto ss set_of_equ_class_bis)
;;

(*-------------------------------------------------------------------------------------*)	
(*--------------------------------------CLEAN CLASS------------------------------------*)
(*-------------------------------------------------------------------------------------*)

let rec clean_class_1 = fun (q,p) doublet_list ->
	match doublet_list with
	| [] -> []
	| (q1,_)::s when (q1=q or q1=p) -> clean_class_1 (q,p) s
	| (_,p1)::s when (p1=q or p1=p) -> clean_class_1 (q,p) s
	| (q1,p1)::s -> (q1,p1)::(clean_class_1 (q,p) s)
;;


let rec clean_class_2 = fun doublet_list_1 doublet_list_2 ->
	match doublet_list_1 with
	| [] -> doublet_list_2
	|(q,p)::s -> let clean_1 =(clean_class_1 (q,p) doublet_list_2) in
		     supp_occ( (clean_class_2 s clean_1) )
;;

let rec clean_class_3 = fun doublet_list doublet_list_list ->
	match doublet_list_list with
	| [] -> []
	| s1::ss -> (clean_class_2 doublet_list s1)::(clean_class_3 doublet_list ss)
;;

(*-------------------------------------------------------------------------------------*)	
(*-------------------------------------FINAL CLASSES-----------------------------------*)
(*-------------------------------------------------------------------------------------*)

(* First Column / Initial equivalence class:
	let class_A = ( create_all_doublet_list(acc_states dfa) );;
	let class_B = ( create_all_doublet_list(prive_de_1 set_of_q (acc_states dfa)) );;
	let class_R = class_A::[class_B] ;; 
*)

(* Next and final Column *)

let rec loop = fun auto class_R ->
	let r_prim=create_all_doublet_list( doublet_to_seq(create_new_class auto class_R class_R) ) in
		if r_prim=[] then class_R
		else
			let r_sec=prive_de_2 r_prim class_R in
				let class_R2=r_prim::(clean_class_3 r_prim r_sec)  in
					loop auto class_R2
;;

let final_class = fun auto ->
	let (set_of_state,_,_,_,_) = auto in
		
	let class_A = ( create_all_doublet_list(acc_states auto) ) in
	let class_B = ( create_all_doublet_list(prive_de_1 set_of_state (acc_states auto)) ) in
	let class_R = class_A::[class_B] in
		supp_occ_list( doublet_to_seq_list( loop auto class_R ) )
;;		

(*-------------------------------------------------------------------------------------*)	
(*--------------------------------------MINIMISATION-----------------------------------*)
(*-------------------------------------------------------------------------------------*)

let rec r = fun st_list m ->
	match st_list with
	| [] -> []
	| e::s -> let ch = "x" ^ (string_of_int m) in (e,ch)::(r s m)
;;

let rec r_2 = fun final_cl m ->
	match final_cl with
	| [] -> []
	| s1::ss -> (r s1 m)@(r_2 ss (m+1))
;;

let rename = function dfa ->
	let m = 1 in
	let final_cl = final_class dfa in
		r_2 final_cl m
;;

(*-------------------------------------------------------------------------------------*)	
(*-------------------------------------NEW SET OF STATE--------------------------------*)
(*-------------------------------------------------------------------------------------*)

let rec s_1 = function state_renamed ->
	match state_renamed with
	| [] -> []
	| (q,q_prim)::s -> (q_prim):: (s_1 s)
;;

let new_set_st = function auto ->
	let state_renamed = rename auto in
		supp_occ( s_1 state_renamed )
;;

(*-------------------------------------------------------------------------------------*)	
(*------------------------------------NEW INITIAL STATE--------------------------------*)
(*-------------------------------------------------------------------------------------*)

let rec i_1 = fun old_st renamed_state ->
	match renamed_state with
	| [] -> old_st
	| (q,q_prim)::s when q=old_st -> q_prim
	| (q,q_prim)::s -> i_1 old_st s
;;

let new_init_state = function auto ->
	let old_st = init_state auto in
	let renamed_state = rename auto in
		i_1 old_st renamed_state
;;
(*-------------------------------------------------------------------------------------*)	
(*---------------------------------NEW TRANSITION RELATION-----------------------------*)
(*-------------------------------------------------------------------------------------*)

let rec t_1 = fun (q,q_prim) seq_trans ->
	match seq_trans with
	| [] -> []
	| (p,a,p_next)::s -> 
			if p=q then
				if p_next=q then
					(q_prim,a,q_prim)::(t_1 (q,q_prim) s )
				else
					(q_prim,a,p_next)::(t_1 (q,q_prim) s )
			else
				if p_next=q then
					(p,a,q_prim)::(t_1 (q,q_prim) s )
				else (p,a,p_next)::(t_1 (q,q_prim) s )
;;

let rec t_2 = fun x_list seq_trans ->
	 match x_list with
	| [] -> seq_trans
	| (q,q_prim)::xs -> (t_2 xs (t_1 (q,q_prim) seq_trans ) )
;;


let new_trans_r = function auto ->
	let (_,_,_,transitions,_) = auto in
	supp_occ( t_2 (rename auto) transitions )
;;


(*-------------------------------------------------------------------------------------*)	
(*------------------------------------NEW ACCEPTING STATE------------------------------*)
(*-------------------------------------------------------------------------------------*)

let rec acc_1 = fun (q,q_prim) old_acc_states ->
	match old_acc_states with
	| [] -> []
	| p::s when p=q -> [q_prim]
	| p::s -> acc_1 (q,q_prim) s
;;	

let rec acc_2 = fun state_renamed old_acc_states ->
	match state_renamed with
	| [] -> []
	| (q,q_prim)::s -> (acc_1 (q,q_prim) old_acc_states)@(acc_2 s old_acc_states)
;;

let new_acc_states = function dfa ->
	let state_renamed = rename dfa in
	let old_acc_states = acc_states dfa in
		supp_occ( acc_2 state_renamed old_acc_states )
;;

(*-------------------------------------------------------------------------------------*)	
(*---------------------------------------MINIMISATION----------------------------------*)
(*-------------------------------------------------------------------------------------*)
let minimisation = function auto ->
	
	let set_of_state = new_set_st auto in
	let (_,alphabet,_,_,_) = auto in
	let i_state = new_init_state auto in
	let trans_r = new_trans_r auto in
	let acc_st = new_acc_states auto in
		(set_of_state, alphabet, i_state, trans_r, acc_st)
;;

