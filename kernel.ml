module type Min_lcf_kernel =
    sig
        type form = private
            Atom of string
          | Arrow of form * form

        type thm

        val form_comp : form -> form -> int
        
        val assume : form -> thm
        val intro_rule : form -> thm -> thm
        val elim_rule : thm -> thm -> thm 

        val atom : string -> form
        val (^->) : form -> form -> form
        val show_conclusion : thm -> form
        val has_nil_context : thm -> bool
        val form_tostring : form -> string
        val show_context : thm -> (form list)
        
end;;



module Min_lcf : Min_lcf_kernel = struct
    type form = 
        Atom of string
      | Arrow of form * form

    (* Ordering for use with Set. Orders first on number of arguments, 
     * then on result type, then recursively on arguments, right to left.*)
    let rec form_comp lhs rhs = 
        match lhs with
            Atom(l) -> 
                (match rhs with
                     Atom(r) -> String.compare l r
                   | Arrow(_) -> -1
                   )
          | Arrow(ll,lr) -> 
                  (match rhs with
                       Atom(_) -> 1
                     | Arrow(rl,rr) -> (let pappcomp = form_comp lr rr in
                           if pappcomp = 0 then form_comp ll rl
                           else pappcomp
                           )
                     )

    module Context = Set.Make(struct 
                               type t = form
                               let compare = form_comp
                              end)

    type context = Context.t
                                
    type thm = Sequent of (context * form)

    let assume p = Sequent (Context.singleton p,p)

    let intro_rule p = function 
        Sequent (gamma,seq) -> Sequent (Context.remove p gamma,Arrow (p,seq))

    let rec form_tostring = (function 
        Atom a -> a
      | Arrow(a,b) -> "("^form_tostring a^"->"^form_tostring b^")")
    let tostring = form_tostring

    let elim_rule = function
        Sequent (_,(Atom _ as l)) -> (function Sequent (_,r) -> 
            failwith ("elim_rule: lhs must be Arrow. Got "^
                tostring l^" and "^tostring r))
      | Sequent (gamma,Arrow (a,b)) -> (function 
            Sequent (delta, p) -> if p = a 
                           then Sequent (Context.union gamma delta, b)
                           else failwith "elim_rule (rhs must match lhs antecedent)"
        )
    
    (* While the kernel is nicely delineated by private keywords...
     * We don't actually have any checks to do here. 
     * Still, this seems neater than exposing constructors.*)
    let atom s = Atom (s)

    let (^->) a b = Arrow (a,b)
    (* ^-> is chosen for ^... being right-associative *) 
    
    let show_conclusion = function Sequent(_,s) -> s

    let has_nil_context = function Sequent(gamma,_) -> Context.is_empty gamma

    let show_context = function Sequent(gamma,_) -> Context.elements gamma

end;;

include Min_lcf;; 
(* Undo one layer of nesting, since Min_lcf *is* the kernel. *)

let form_matches_thm f t = has_nil_context t && (show_conclusion t = f)
