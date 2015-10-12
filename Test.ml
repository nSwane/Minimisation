 
 let a : symbol = 'a' ;;
 let b : symbol = 'b' ;;
 let sigma : alphabet = [a;b] ;;
 
 (* Test1 - Already Minimal *)
 let q0 : state = "q0" ;;
 let q1 : state = "q1" ;;
 let q2 : state = "q2" ;;
 let q3 : state = "q3" ;;
 let  set_of_q: set_of_states = [q0;q1;q2;q3] ;;
 let delta : transition_relation = [(q0,a,q1);(q0,b,q0);(q1,a,q1);(q1,b,q2);(q2,a,q3);(q2,b,q0);(q3,a,q3);(q3,b,q3)] ;;

 let dfa : automaton = (set_of_q,sigma,q0, delta, [q0;q1;q2]) ;;
 
 final_class dfa;; (* We aplly this function to check if the DFA is minimal or not *)
 minimisation dfa;; (* if the DFA is minimal the function "minimisation" renames DFA's states *)
 
(* TEST2 - Not Minimal *)
 let p1 : state = "p1" ;;
 let p2 : state = "p2" ;;
 let p3 : state = "p3" ;;
 let p4 : state = "p4";;
 let p5 : state = "p5";;
 let p6 : state = "p6";;
 let p7 : state = "p7";;
 let p8 : state = "p8";;
 let p9 : state = "p9";;
 let  set_of_p: set_of_states = [p1;p2;p3;p4;p5;p6;p7;p8;p9] ;;
 let delta_2 : transition_relation = [(p1,a,p2);(p1,b,p9);
 				    (p2,a,p2);(p2,b,p3);
 				    (p3,a,p4);(p3,b,p5);
 				    (p4,a,p2);(p4,b,p3);
 				    (p5,a,p6);(p5,b,p5);
 				    (p6,a,p7);(p6,b,p8);
 				    (p7,a,p7);(p7,b,p8);
 				    (p8,a,p6);(p8,b,p8);
 				    (p9,a,p9);(p9,b,p9)];;

 let dfa_2 : automaton = (set_of_p,sigma,p1, delta_2, [p2;p4;p6;p7]) ;;

 final_class dfa_2;; (* We aplly this function to check if the DFA is minimal or not *)
 minimisation dfa_2;; (* if the DFA is not minimal the function "minimisation" minimizes the DFA passed on parameter *)
