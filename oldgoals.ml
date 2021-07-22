(* abandoned attempt at doing ProofPower-style justifications *)

type goal = thm list * form
type goalstate = goal list * thm
type tactic = goal -> goal list * (thm -> thm)

exception QED

let by tac = function
    ([],_) -> raise QED
  | ((h::t),th) -> match tac h with 
        (newgoals,justify) -> 
            (List.append newgoals t,justify th)

let intro_tac = function
    (_ ,Atom _ ) -> failwith "cannot arrive at Atom by intro"
  | (thms,Arrow (a,b)) -> 
          ([(thms,b)]
          ,function curr -> 
          intro_rule a (elim_rule (curr) (intro_rule b (assume b))) )
