exception QED

let history : goalstate list ref = ref []

let histpeek () = try (List.hd !history) with 
    Failure _ -> failwith "No goal set yet"

let histpush gstate = history := gstate::!history

let histpop () = try history := List.tl !history with Failure _ ->
    failwith "History is empty"

let p () = (function (fst,_) -> try List.hd fst with Failure _ -> raise QED) 
    (histpeek ())

let g newgoal = histpush ([Seq(Context.empty,newgoal)],List.hd); p()

let e tac = histpush (by tac (histpeek ())); p()  

let b () = histpop (); p()

let ignore _ = ()

let top_thm () = try ignore (p ());
                     failwith "Cannot prove goal: open subgoals left!" 
                 with QED -> (function (_,snd) -> snd []) (histpeek ());;


Printexc.register_printer (function QED -> Some "QED." | _ -> None)
