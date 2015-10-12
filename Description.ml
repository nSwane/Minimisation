
Author : Nawaoui Swane & Stahl Gustave
Groupe : MIN International
Subject: Minimisation

(*------------------------------------------------------------Minimisation----------------------------------------------------------------------*)
(* * We work on a DFA
   * During all the exercise we will need to compare each state with the others.
     A way to do all these comparison is to create a list of doublet (q,p) with q and p be states
     This is the reason of defining a function which creates all possible doublet.
*)

(*-----------------------------------------------------------------------*)
(*-------------------------SOME USEFUL FUNCTIONS-------------------------*)
(*-----------------------------------------------------------------------*)

(*1*)
* Header : belong_to arg1 arg2 return res
	with type arg1 = 'a
	     type arg2 = 'a list 
	     type res = 'a list
	     
* Specification: belong_to e1 seq = true if e1 belongs to seq 

* Example: belong_to 2 [1;4;7;2;0] = true ;;
         belong_to (1,2) [(1,1);(1,2);(1,3)] = true ;;
	 belong_to 2 [] = false ;;

(*2.a*)
* Header : prive_de_1 arg1 arg2 return res 
	with type arg1 = type arg2 = type res = 'a list
	 
* Specification: prive_de_1 seq1 seq2 gives us seq1 except for seq2

* Example: prive_de [2;3;4;5] [2;4] = [3;5] ;;
   	    prive_de [] ['a'] = [] ;;	
   	    prive_de ['a';'b';'c'] ['b'] = ['a';'c'] ;;

(*2.b*)
* Header : prive_de_2 arg1 arg2 return res 
	with type arg1 = 'a list
	     type arg2 = type res = ('a list) list 
	     
* Specification: prive_de_2 seq seq_seq applies prive_de_1 for each sequence of seq_seq

* Example: prive_de_2 [(q2,q2)] [ [(q0,q1);(q1,q1)];[(q2,q2);(q1,q2)] ] = [ [("q0", "q1"); ("q1", "q1")]; [("q1", "q2")] ]
           prive_de_2 [1;2;3] [[1;2];[2;3];[0;4];[0;5;6]] = [[]; []; [0; 4]; [0; 5; 6]]

(* Before defining the function which creates all doublet list, we need to define the basis configuration ie
the one which creates a doublet list according to one state : create_doublet_list
*)

(*3.a*)
* Header : create_doublet_list arg1 arg2 return res 
	with type arg1 = 'state
	     type arg2 = 'set_of_state
	     type res = ('state * 'state) list
	     
* Specification: create_doublet_list e [e1;..en] = [(e,e1);..;(e,en)] : 
	This function creates a set of doublet
	
* Example : create_doublet_list q0 [q1;q2] = [("q0", "q1"); ("q0", "q2")] ;;
            create_doublet_list 0 [1;2;3;4] = [(0, 1); (0, 2); (0, 3); (0, 4)]

(*3.b*)
* Header : create_all_doublet_list arg1 return res
	with type arg1 = 'set_of_state
	     type res = ('state * 'state) list
	     
* Specification: create_all_doublet_list [e1;..en] applies the previous function for each element of [e1;..;en]
	       ie the function gives us all possible doublet we can make with e1,e2,... and en
	       
* Example : create_all_doublet_list [q0;q1;q2] = [(q0, q0); (q0, q1); (q0, q2); 
   						 (q1, q1); (q1, q2); (q2, q2)]
(* All comparisons are now represented by the doublet list *)

(* The two next functions are used in the part "FINAL CLASSES" *)
(*4.a*)
* Header : doublet_to_seq arg1 return res 
	with type arg1 = ('state * 'state) list
	     type res = 'set_of_state
	     
* Specification: given an equivalence class represented by a sequence of doublet, doublet_to_seq_list gives us the corresponding sequence

(*4.b*)
* Header : doublet_to_seq_list arg1 return res
	with type arg1=('state * 'state) list list
	     type res='set_of_state list
	
* Specification : This function applies the previous function for each sequence of arg1 

(*5.a*)
* Header : supp_occ arg1 return res
	with type arg1 = 'a list
	     type res = 'a list
	     
* Specification: supp_occ seq removes all repetitions in seq 

* Example: * supp_occ [(1,1);(1,2);(1,1);(2,2);(2,3);(1,1)] = [(1, 2); (2, 2); (2, 3); (1, 1)] ;;
           * supp_occ [(1,1);(1,1);(3,2)] = [(1,1);(3,2)] ;;
           * supp_occ [1;1;1;2;2;1;2;1] = [2; 1]
           
(*5.b*)
* Header : supp_occ arg1 return res 
	with type arg1= type res=('a list) list 
	
* Specification: supp_occ_list arg1 applies the previous function for each sequence of arg1

* Example : * supp_occ_list [["p1"; "p1"]; ["p3"; "p3"; "p5"; "p8"]; ["p2"; "p2"; "p4"; "p6"; "p6"; "p7"]; ["p9"]] = 
			    [["p1"]      ; ["p3"; "p5"; "p8"      ]; ["p2"; "p4"; "p6"; "p7"            ]; ["p9"]]
            * supp_occ_list [[1;1;2];[3;3;4;5];[6]] = [[1; 2]; [3; 4; 5]; [6]]

(*-------------------------------------------------------------------------------------*)	
(*----------------------------CREATION OF EQUIVALENCE CLASSES--------------------------*)
(*-------------------------------------------------------------------------------------*)
(*
Before defining the function which creates a new equivalence class, we need to define 2 functions:
the first one will tell us if 2 states are in the same class and we will use the other to create the first element of a class
*)

(*6*)
* Header : not_same_class arg1 arg2 arg3 arg4 return res
	with type arg1='automaton
	     type arg2=('state*'state)
	     type arg3=('alphabet)
	     type arg4=(('state*'state) list) list : arg4 represents a set of equivalence class (cf TD Minimisation)
	     type res='boolean
	     
* Specification: (not_same_class dfa (q0,q1) sigma set_of_equ_class = true) if q0 and q1 are not in the same class

(*7*)
* Header : first_elt_of_a_class arg1 arg2 arg3 return res
	with type arg1='automaton
	     type arg2=('state*'state)list  (* arg2 represents an equivalence class *)
	     type arg3=(('state*'state) list) list  (* arg3 represents a set of equivalence class *)
	     
* Specification: (first_elt_of_a_class dfa sigma doublet_list set_of_equ_class) creates the first elt of an equivalence class

(*8*)
* Header : create_new_class arg1 arg2 arg3 return res
	with type arg1='automaton
	     type arg2=(('state*'state) list) list : arg2 represents a set of equivalence class
	     type arg3=(('state*'state) list) list : arg3 represents a set of equivalence class
	     type res=('state*'state)list : res represents a new equivalence class
	     
* Specification: create_new_class uses the previous function to create a new equivalence class

(*-------------------------------------------------------------------------------------*)	
(*--------------------------------------CLEAN CLASS------------------------------------*)
(*-------------------------------------------------------------------------------------*)
(*
After creating one equivalence class we must clean the set of equivalence class:
ie remove all doublets which are linked with the class which has been created *)
* Example:

let us consider the set of equivalence class below:
[ [("q0", "q0"); ("q0", "q1"); ("q0", "q2"); ("q1", "q1"); ("q1", "q2"); ("q2", "q2")]; [("q3", "q3")] ]
when we apply the previous function (create_new_class) to the set above we obtain the set below:
[[("q0", "q0"); ("q0", "q1"); ("q1", "q1")]; [("q0", "q0"); ("q0", "q1"); ("q0", "q2"); ("q1", "q1"); ("q1", "q2"); ("q2", "q2")]; [("q3", "q3")] ]

And the goal is to obtain the new set below:
[[("q0", "q0"); ("q0", "q1"); ("q1", "q1")]; [                                                                      ("q2","q2")	]; [("q3", "q3")] ]


(*
Before defining the function which clean a class, we have to define basis configuration:
ie the case which clean a class according to one doublet
*)
(*9.a*)
* Header:  clean_class_1 arg1 arg2 return res 
	with type arg1=('state*'state)
	     type arg2=('state*'state) list
	     type res=('state*'state) list
	
* Specification: clean_class_1 arg1 arg2 cleans the class arg2 according to arg1

* Example: clean_class_1 (q2,q2) [(q0,q1);(q0,q2);(q1,q1);(q1,q2);(q1,q3)] = [("q0", "q1"); ("q1", "q1")]
	   clean_class_1 (q2,q2) [(q0,q1);(q1,q3)] = [("q0", "q1"); ("q1", "q3")]

(*9.b*)
* Header: clean_class_2 arg1 arg2 return res 
	with type arg1=type arg2=type res=('state*'state) list 
	     
* Specification: clean_class_2 arg1 arg2 cleans the class arg2 according to arg1's elements.
 
* Example: clean_class_2 [(q0,q1);(q0,q2)] [(q0,q1);(q0,q2);(q1,q1);(q1,q2);(q3,q3)] = [(q3,q3)]
           clean_class_2 [("q0", "q0"); ("q0", "q1"); ("q1", "q1")]  [("q0", "q2"); ("q1", "q2"); ("q2", "q2")]

(*-------------------------------------------------------------------------------------*)	
(*-------------------------------------FINAL CLASSES-----------------------------------*)
(*-------------------------------------------------------------------------------------*)
(*10.a*)
* Header: loop arg1 arg2 return res
	with type arg1='automaton
	     type arg2=type res=('state*'state)list (* arg2 represents a set of equivalence class *)
	     
* Specification: According to the automaton arg1 and the set of equivalence class arg2, "loop" creates the next set of equivalence class

(*10.b*)
* Header: final_class arg1 return res
	with type arg1='automaton
	     type res=('state*'state)list (* arg2 represents a set of equivalence class *)
	     
* Specification: According to the automaton arg1, final_class creates the corresponding final equivalence class

(*-------------------------------------------------------------------------------------*)	
(*--------------------------------------MINIMISATION-----------------------------------*)
(*-------------------------------------------------------------------------------------*)
(*New Automaton*)

(* Before updating the automaton we need to define a way to link each class with one state *)
* Example: 
	let us consider an automaton A and the cooresponding final set of equivalence class below:
	[["p1"]; ["p3"; "p5"; "p8"]; ["p2"; "p4"; "p6"; "p7"]; ["p9"]]
	The goal is to match :
	["p1"] 		    	 -> s1 (* a state *)
	["p3"; "p5"; "p8"]       -> s2
	["p2"; "p4"; "p6"; "p7"] -> s3
	["p9"] 			 -> s4
	
	We will define the link as a doublet (q,q_prim) with q and q_prim belong to 'state.
	( the left part represents the old state and the right part the new state )
	* Example:
		(p1,s1)
		(p3,s2), (p5,s2), (p8,s2)
		(p2,s3)..(p7,s3)
		(p9,s4)
		
(* But first, let us define the basis configuration, we will use the function:
	* r to rename one class
	Example : when we apply the function to ["p3"; "p5"; "p8"] and the integer 1
		  we obtain [("p3", "X1"); ("p5", "X1"); ("p8", "X1")]
	* r_2 to rename all class
	Example : when we apply the function r_2 to [["p1"]; ["p3"; "p5"; "p8"]; ["p2"; "p4"; "p6"; "p7"]; ["p9"]] and 1
		  we obtain :
		  [("p1", "X1"); ("p3", "X2"); ("p5", "X2"); ("p8", "X2");
		   ("p2", "X3"); ("p4", "X3"); ("p6", "X3"); ("p7", "X3"); ("p9", "X4")]
*)

(*11.a*)
* Header : r arg1 arg2 return res
	with type arg1=('state*'state)list (*represents one class*)
	     type arg2='integer
	     type res=('state*'state) list
	     
* Specification: the function r renames one class

(*11.b*)
* Header : r_2 arg1 arg2 return res
	with type arg1=('state*'state)list list (*respresents set of equivalence class*)
	     type arg2='integer
	     type res =('state*'state) list
	     
* Specification: the function r_2 renames all classes

(*11.c*)
* Header : rename arg1 return res
	with type arg1='automaton
	     type res=('state*'state) list
	     
* Specification: According to the automaton arg1 the function below renames all classes	 	

(* Now we can update the automaton *)
(*-------------------------------------------------------------------------------------*)	
(*-------------------------------------NEW SET OF STATE--------------------------------*)
(*-------------------------------------------------------------------------------------*)

(*12.a*)
* Header : s_1 arg1 return res
	with type arg1=('state*'state) list (* sequence of link *)
	     type res='state
	     
* Specification: the function s_1 creates the new set of state thanks to the sequence of link
   
(*12.b*)
* Header : new_set_st arg1 return res
	with type arg1='automaton
	     type res='set_of_state
	     
* Specification: the function creates the new set of state according to one automaton
	     
(*-------------------------------------------------------------------------------------*)	
(*------------------------------------NEW INITIAL STATE--------------------------------*)
(*-------------------------------------------------------------------------------------*)
(* According to the dfa, new_init_state gives us the minimized corresponding initial state.  
*)
(*13.a*)
* Header : i_1 arg1 arg2 return res
	with type arg1='state
	     type arg2=('state*'state) list (* link list*)
	     type res='state
	     
* Specification: i_1 returns the initial state according to the old state and the sequence of link

(*13.b*)
* Header : new_init_state arg1 return res
	with type arg1='automaton
	     type res='state
	     
* Specification: the function below returns the new initial state according to one automaton	     

(*-------------------------------------------------------------------------------------*)	
(*---------------------------------NEW TRANSITION RELATION-----------------------------*)
(*-------------------------------------------------------------------------------------*)
(* According to the dfa, new_trans_r gives us the minimized corresponding transition relation. 
   Before creating this function we need to define basis case: t_1
*)

(*14.a*)
* Header : t_1 arg1 arg2 return res
	with type arg1=('state*'state) (* link *)
	     type arg2='transition_relation
	     type res='transition_relation
	     
* Specification : t_1 updates the old transition relation according to one link	   

* Example: t_1 (p1,"1") [("p1", 'a', "p2"); ("p1", 'b', "p1");("p2", 'a', "p2")] = [("1", 'a', "p2"); ("1", 'b', "1"); ("p2", 'a', "p2")]

(*14.b*)
* Header : t_2 arg1 arg2 return res
	with type arg1=('state*'state) list (* link list*)
	     type arg2='transition_relation
	     type res='transition_relation

* Specification: t_2 creates the new transition relation according to a	sequence of link

* Example :
t_2 [("p1", "1"); ("p3", "2"); ("p5", "2")] [("p3", 'a', "p4"); ("p3", 'b', "p5"); ("p4", 'a', "p2"); ("p4", 'b', "p3"); ("p5", 'a', "p6")  ]
			      		  = [("2", 'a', "p4");  ("2", 'b', "2");   ("p4", 'a', "p2"); ("p4", 'b', "2");  ("2", 'a', "p6")]

(*14.c*)
* Header : new_trans_r arg1 return res
	with type arg1='automaton
	     type res='transition_relation
	     
* Specification: new_trans_r creates the new transition relation according to one automaton

(*-------------------------------------------------------------------------------------*)	
(*------------------------------------NEW ACCEPTING STATES-----------------------------*)
(*-------------------------------------------------------------------------------------*)
(* According to the dfa, new_acc_states gives us the minimized corresponding accepting state.
   Before creating this function we need to define basis cases : acc_1 *) 

(*15.a*)
* Header : acc_1 arg1 arg2 return res
	with type arg1=('state*'state)
	     type arg2='transition_relation
	     type res='transition_relation
	     
* Specification: According to one link, acc_1 gives us the first element of the new accepting states
	    
* Example: acc_1 ("q0", "1") ["q0"; "q1"; "q2"] = ["1"]

(*15.b*)
* Header : acc_2 arg1 arg2 return res
	with type arg1=('state*'state) (* link *)
	     type arg2='set_of_state 
	     type res='set_of_state
	     
* Specification: acc_2 creates the new accepting states according to the old one and the sequence of link	     

(*15.c*)
* Header : new_acc_states arg1 return res
	with type arg1='automaton
	     type res='set_of_state
	     
* Specification: new_acc_states creates the new accepting states according to the automaton given on parameter	     

(*-------------------------------------------------------------------------------------*)	
(*---------------------------------------MINIMISATION----------------------------------*)
(*-------------------------------------------------------------------------------------*)

(*16*)
* Header : minimisation arg1 return res
	with type arg1='automaton
	     type res='automataon
	     
* Specification: minimisation minimises the automaton passed as on argument	     

