

(*open Kernel*)
(* left out due to peculiarities in toplevel module loading *)

module Context = Set.Make(struct 
                           type t = form
                           let compare = form_comp
                          end)

type context = Context.t

type justification = thm list -> thm
type goal = Seq of context * form
type goalstate = goal list * justification
type tactic = goal -> goal list * justification

exception QED

let rec drop n ls = match n with
    0 -> ls
  | n -> (match ls with [] -> [] | (h::t) -> drop (n-1) t)

  (* tail-recursive intermediate for take *)
let rec appendrevtake n xs ys = match n with
    0 -> ys
  | n -> (match xs with 
          [] -> [] 
        | (h::t) -> appendrevtake (n-1) t (h::ys)
         )

let take n ls = List.rev (appendrevtake n ls [])

let listcut n ls = (take n ls,drop n ls)

let by tac = function
    ([],_) -> raise QED
  | ((h::t),justify) -> match tac h with 
        (newgoals,djustify) -> 
            (List.append newgoals t,fun ths ->
            match listcut (List.length newgoals) ths with 
                (newgoalths,t)->justify (try djustify newgoalths :: t with 
                    Failure s -> failwith (s^", dump: ")))


let ftstr = form_tostring 

let ttstr t = ftstr (show_conclusion t) (* "theorem to string" *)


let verbose_proof = ref true

let set_verbose b = verbose_proof := b


let prints s = if !verbose_proof then print_string s else ()


let assumption = function
    Seq(gamma,seq) -> if Context.mem seq gamma 
        then ([],function [] -> (prints ("assuming "^ftstr seq^"\n"); 
                                assume seq)
                         | _ -> failwith "assume takes no thms, got some" )
        else failwith ("assumption: "^ftstr seq^" not in context")

let intro_tac = function 
    Seq(_,Atom _) -> failwith "intro_tac: Intro cannot produce atom"
  | Seq(gamma,Arrow (bind,rest)) -> ([Seq(Context.add bind gamma,rest)],
        (function 
           [h] -> if show_conclusion h = rest 
                  then (prints ("intro "^ ftstr bind^" to "^ttstr h^"\n");
                       intro_rule bind h)
                  else failwith ("intro_tac: Expected "^ftstr rest^", got "^
                                 ftstr (show_conclusion h))
         |  _  -> failwith "intro_tac: need 1 thm to apply intro_rule"))


let elim_tac ante = function
    Seq(gamma,conseq) -> 
        ([Seq(gamma,ante ^-> conseq);Seq(gamma,ante)],function 
            [h1;h2] -> 
                if show_conclusion h1 = (ante ^-> conseq) && 
                    show_conclusion h2 = ante then (prints ("elim "^
                        ftstr ante^" to "^ftstr conseq^"\n"); elim_rule h1 h2)
                else failwith ("elim_tac: expected "^ftstr (ante ^-> conseq)^
                    " and "^ftstr ante^", got "^ttstr h1^" resp. "^ttstr h2)
          | _ -> failwith "elim_tac: need 2 thms to apply elim_rule" )
