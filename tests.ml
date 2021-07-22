#use "minlcf.ml";;

let u = b;;

let a = atom "A";;
let b = atom "B";;
let c = atom "C";;
let s = (a ^-> b ^-> c) ^-> (a ^-> b) ^-> a ^-> c;;
let ass = assumption;;
let intro = intro_tac;;
let elima = elim_tac a;;
let elimb = elim_tac b;;

g s;;
e intro;;
e intro;;
e intro;;
e elimb;;
e elima;;
e ass;;
e ass;;
e elima;;
e ass;;
try ignore (e ass); prints "proof incomplete" with QED -> prints "QED.";;

let proof = top_thm ();;

if form_matches_thm s proof then "type of S proven" else "proof error";;

let b = u;;
