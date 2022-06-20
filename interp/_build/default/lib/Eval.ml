type value =
  {
    as_int : int option ; (** as integer *)
    as_bool : bool option ; (** as boolean *)
    as_func : closure option; (** as function **)
    fields : (Syntax.name * value ref) list (** as object *)
  }

and closure = 
| Closure of value option * (Syntax.name * int * Syntax.expr)


type slot = 
  | Slot of string * int

type link = 
  | Link of string * int

type frame = 
  | Frame of link list * slot list

module Heap = Map.Make(struct type t = int let compare = compare end)
module Store = Map.Make(struct type t = int let compare = compare end)

(* let fTuple (a, _b) = a
let sTuple (_a, b) = b *)
let frameLinks = function
  | Frame(links, _) -> links

let frameSlots = function
  | Frame(_, slots) -> slots

let slotName = function
  | Slot(name, _) -> name

let slotValue = function
  | Slot(_, value) -> value

let linkLabel = function
  | Link(label, _) -> label

let linkID = function
  | Link(_, id) -> id

let containsInt = function
  | None -> -1
  | Some x -> x

let unit_obj = {as_int=None; as_bool=None; as_func=None; fields=[]}

let mk_int i = {as_int=Some i; as_bool=None; as_func=None; fields=[]}

let mk_bool b = {as_int=None; as_bool=Some b; as_func=None; fields=[]}

let mk_func f = {as_int=None; as_bool=None; as_func=Some f; fields=[]}

let mk_obj lst = {as_int=None; as_bool=None; as_func=None; fields=lst}

let copy ob =
  { ob with fields = List.map (fun (x,v) -> (x, ref (!v))) ob.fields }

let get_int = function
  | {as_int = Some i; _} -> i
  | _ -> failwith "integer expected"

let get_bool = function
  | {as_bool = Some b; _} -> b
  | _ -> failwith "boolean expected"

let get_func = function
  | {as_func = Some f; _} -> f
  | _ -> failwith "function expected"

(** [get_attr x ob] returns the value of attribute [x] in object [ob]. *)
let get_attr x {as_int = _; as_bool = _; as_func = _; fields = lst} =
  try
    List.assoc x lst
  with
    Not_found -> failwith "no such field"

(** Mapping from arithmetical operations to corresponding Ocaml functions. *)
let arith = function
  | Syntax.Plus ->  ( + )
  | Syntax.Minus -> ( - )
  | Syntax.Times -> ( * )
  | Syntax.Divide -> ( / )
  | Syntax.Remainder -> ( mod )

(** Mapping from comparisons to corresponding Ocaml functions. *)
let cmp = function
  | Syntax.Equal -> ( = )
  | Syntax.Unequal -> ( <> )
  | Syntax.Less -> ( < )

(** [print_obj ob ppf] pretty-prints the given object. *)
let rec print_value { as_int=i; as_bool=b; as_func=f; fields=lst } ppf =
  let fs =
    (match i with None -> [] | Some i -> [fun ppf -> Format.fprintf ppf "%d" i]) @
    (match b with None -> [] | Some b -> [fun ppf -> Format.fprintf ppf "%b" b]) @
    (match f with None -> [] | Some _ -> [fun ppf -> Format.fprintf ppf "<fun>"])
  and g ppf =
    Format.fprintf ppf "{@[" ;
    Format.pp_print_list
      ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
      (fun ppf (x, v)-> Format.fprintf ppf "%s=@[<hov>%t@]" x (print_value !v))
      ppf
      lst ;
    Format.fprintf ppf "@]}"
  in
  Format.pp_print_list
    ~pp_sep:(fun ppf () -> Format.fprintf ppf " with ")
    (fun ppf f -> f ppf)
    ppf
    (match fs, lst with
     | _::_, [] -> fs
     | _, _ -> fs @ [g])

(* ------------------------------------------- *)
(* ------------ HEAP METHODS ----------------- *)
(* ------------------------------------------- *)

let initFrame heap = 
  let frameID = Heap.cardinal heap in
  let frame = Frame([], []) in
  (Heap.add frameID frame heap, frameID)

let getFrame frameId heap = 
  try Heap.find frameId heap with Not_found -> (Printf.printf "Frame with id %d not found\n" frameId; failwith "NOT FOUND")

let setFrame frameId frame heap = 
    Heap.add frameId frame heap
  
let rec findSlot slots slotName = 
  match slots with 
  | [] -> None
  | Slot(name, value) :: rest -> 
    if name = slotName then Some(value)
    else findSlot rest slotName 

let getSlotValue frameId slotName heap = 
  let frame = getFrame frameId heap in
  let slots = frameSlots frame in
  findSlot slots slotName

let updateSlotValue frameId slotName newValue heap = 
  let frame = getFrame frameId heap in
  let slots = frameSlots frame in
  if (findSlot slots slotName) = None then
    let newSlots = Slot(slotName, newValue) :: slots in
    let newFrame = Frame(frameLinks frame, newSlots) in
    setFrame frameId newFrame heap
  else
    let slots = List.map (function
      | Slot(name, value) -> 
        if name = slotName then Slot(name, newValue) else Slot(name, value)) slots in
    let newFrame = Frame(frameLinks frame, slots) in
    setFrame frameId newFrame heap

let rec findLink links linkLabel = 
  match links with
  | [] -> None
  | Link(label, id) :: rest -> 
    if label = linkLabel then Some(id)
    else findLink rest label

(* let int_of_intoption = function None -> 0 | Some n -> n *)

let getLink frameId linkLabel heap = 
  let frame = getFrame frameId heap in
  let links = frameLinks frame in
  containsInt (findLink links linkLabel)

let createLink childFrameId parentFrameId linkLabel heap = 
  let frame = getFrame childFrameId heap in
  let links = frameLinks frame in
  let link = Link(linkLabel, parentFrameId) in
  let newLinks = link :: links in
  let newFrame = Frame(newLinks, frameSlots frame) in
  setFrame childFrameId newFrame heap

let rec lookup name frameId heap = 
  let frame = getFrame frameId heap in
  let slot = getSlotValue frameId name heap in
  let links = frameLinks frame in

  match slot with
    | None -> 
      if List.length links > 0 then 
        lookup name (getLink frameId "P" heap) heap
      else 
        let _ = Printf.printf "Error: %s not found in frame %d \n" name frameId in
        failwith "lookup: no slot"
    | Some v -> v

(* let rec lookupOrMinusOne name frameId heap = 
  let frame = getFrame frameId heap in
  let slot = getSlotValue frameId name heap in
  let links = frameLinks frame in
  
  match slot with
    | None -> 
      if List.length links > 0 then 
        lookupOrMinusOne name (getLink frameId "P" heap) heap
      else 
        -1 
    | Some v -> v *)

let heap = ref Heap.empty
let store: value Store.t ref = ref Store.empty
    
(* ------------------------------------------- *)
(* ------------ STORE METHODS ---------------- *)
(* ------------------------------------------- *)

(* let initStore =
  let store = Store.empty in
  store *)

let fetch loc sto = 
  try Store.find loc sto with Not_found -> (Printf.printf "Location %d not found\n" loc; failwith "NOT FOUND")
  
let updateCell loc v sto = 
  let newSto = Store.add loc v sto in
  newSto

let newLocation sto = 
  Store.cardinal sto

let extendStore v sto = 
  let newLoc = Store.cardinal sto in 
  let newSto = Store.add newLoc v sto in
  (newSto, newLoc)

(* ------------------------------------------- *)
(* ------------ DEBUGGING HELPERS ------------ *)
(* ------------------------------------------- *)

let rec printFrameLinks = function
  | [] -> Printf.printf "\n"
  | head :: tail -> (
        Printf.printf "\t\t\t%s -> %d\n" (linkLabel head) (linkID head);
        printFrameLinks tail)

let rec printFrameSlots = function
  | [] -> Printf.printf "\n"
  | head :: tail -> (
        Printf.printf "\t\t\t%s -> %d\n " (slotName head) (slotValue head);
        printFrameSlots tail)  

let printCurrentFrame = function
  | Frame(links, slots) -> 
    Printf.printf "\t\tLinks:\n";
    printFrameLinks links;
    Printf.printf "\t\t------\n";
    Printf.printf "\t\tSlots:\n";
    printFrameSlots slots;
    Printf.printf "\n"

let rec printCurrentHeap heap = 
  match heap with
    | (key, frame) :: tail -> 
        Printf.printf "\tKey: %d\n" key;
        Printf.printf "\t\tFrame: \n";
        printCurrentFrame frame;
        printCurrentHeap tail
    | _ -> Printf.printf "\n"

let rec printCurrentStore store = 
  match store with
    | (loc, v) :: tail -> 
        Printf.printf "Loc: %d, Value: " loc;
        Format.printf "%t@." (print_value v);
        Printf.printf "\n";
        printCurrentStore tail
    | _ -> Printf.printf "\n"

let printHeapStore heap store = 
  Printf.printf "Heap:\n\n";
  printCurrentHeap (Heap.bindings heap);
  Printf.printf "----------------\n";    
  Printf.printf "Store:\n";
  printCurrentStore (Store.bindings store);
  Printf.printf "****************\n" 

(* ------------------------------------------- *)
(* --------- INTERPRETOR --------------------- *)
(* ------------------------------------------- *)

let eval e initialFrameID = 

  let rec eval th frID expr =

    match expr with
    | Syntax.Var n ->
      let location = lookup n frID !heap in
      fetch location !store

    | Syntax.Int k -> 
      mk_int k

    | Syntax.Bool b -> 
      mk_bool b

    | Syntax.ArithOp (op, e1, e2) -> 
        let v1 = eval th frID e1 in
        let v2 = eval th frID e2 in
        let v = arith op (get_int v1) (get_int v2) in
        mk_int v

    | Syntax.Not e ->
        let v = eval th frID e in
        mk_bool (not (get_bool v))

    | Syntax.CmpOp (op, e1, e2) -> 
        let v1 = eval th frID e1 in
        let v2 = eval th frID e2 in
        mk_bool (cmp op (get_int v1) (get_int v2))

    | Syntax.BoolOp (Syntax.And, e1, e2) ->
        mk_bool (get_bool (eval th frID e1) && get_bool (eval th frID e2))

    | Syntax.BoolOp (Syntax.Or, e1, e2) ->
        mk_bool (get_bool (eval th frID e1) || get_bool (eval th frID e2))

    | Syntax.If (e1, e2, e3) ->
        if get_bool (eval th frID e1) then
	        eval th frID e2
        else
	        eval th frID e3

    | Syntax.Skip -> 
      unit_obj

    | Syntax.Seq (e1, e2) ->
        ignore (eval th frID e1); 
        eval th frID e2
    
    (* [let x = e1 in e2]  *)
    | Syntax.Let (x, e1, e2) ->

        let vx = eval th frID e1 in

        (* create new cell in store *)
        let (newStore, newLoc) = extendStore vx !store in
        store := newStore;

        (* update cell in frame *)
        let newHeap = updateSlotValue frID x newLoc !heap in
        heap := newHeap;
          
        (* eval body *)
        eval th frID e2
    
    (* [AppC(f, l) ; l = lista de args, f = FdC(args, body)] *)
    | Syntax.App (e1, e2) -> (

        let f = eval th frID e1 in
        let res = get_func f in

        match res with
          | Closure (th', (x, clFrID, e)) -> (
            let (updatedHeap, newFrameID) = initFrame !heap in
            heap := createLink newFrameID clFrID "P" updatedHeap;

            let arg = eval th frID e2 in
            let sym = x in

            let newLoc = newLocation !store in
            heap := updateSlotValue newFrameID sym newLoc !heap;
            store := updateCell newLoc arg !store;
        
            eval th' newFrameID e )
      )

    | Syntax.Fun (x, e) ->  (
      let fn = Closure(th, (x, frID, e)) in
      mk_func fn)
      
    | Syntax.This ->
        (match th with
          | Some v -> v
          | None -> failwith "invalid use of 'this'")

    | Syntax.Object lst ->
        mk_obj (List.map (
          fun (x,e) -> (x, ref (eval th frID e))) 
          lst)

    | Syntax.Copy e -> 
      copy (eval th frID e)

    (* object extension [e1 with e2] *)
    | Syntax.With (e1, e2) ->

        let join x y = 
          match x, y with  _, 
            ((Some _) as y) -> y 
            | x, _ -> x in
        
        let v1 = eval th frID e1 in
        let v2 = eval th frID e2 in
        { 
          as_int  = join v1.as_int v2.as_int;
          as_bool = join v1.as_bool v2.as_bool;
          as_func = join v1.as_func v2.as_func;
          fields  = (List.fold_left 
                      (fun lst (x,v) -> if not (List.mem_assoc x lst) then (x,v) :: lst else lst)
                      v2.fields v1.fields)
        }
    | Syntax.Project (e, x) ->

        let u = eval th frID e in
        let v = !(get_attr x u) in
        (match v.as_func with
        | None -> v
        | Some (Closure (Some _vl, c)) -> { v with as_func = Some (Closure (Some u, c)) }
        | Some (Closure (None, c)) -> { v with as_func = Some (Closure (Some u, c)) }
        )

    | Syntax.Assign (e1, x, e2) ->

       (let v1 = eval th frID e1 in
       let v2 = eval th frID e2 in
       (get_attr x v1) := v2; 
       v2)
  
  in
  let res = eval None initialFrameID e in
  (* Format.printf "%t@." (print_value res); *)
  res

let parseFile s = 
  let ast = ParserInterface.parse_file s in
  ast

let parseRepl s = 
  let ast = ParserInterface.parse_toplevel s in
  ast

let rec exec ast initialFrameID =
    match ast with 
      | head :: tail -> 
        matchFunction initialFrameID tail head
      | _ -> failwith "???"
        
and matchFunction initialFrameID tail = function
    | Syntax.Expr e -> (
      let v = eval e initialFrameID in
      (* Format.printf "%t@." (print_value v); *)
      if (List.length tail) > 0 then
        exec tail initialFrameID
      else
        v
    )
  | Syntax.Def (x, e) -> 
    (
      let v = eval e initialFrameID in
      
      (* create new cell in store *)
      let (newStore, newLoc) = extendStore v !store in
      store := newStore;

      (* update cell in frame *)
      let newHeap = updateSlotValue initialFrameID x newLoc !heap in
      heap := newHeap;
      
      if (List.length tail) > 0 then
        exec tail initialFrameID
      else
        v 
    )

let interpFile e = 
  let ast = parseFile e in
  
  let (hp, newID) = initFrame (Heap.empty) in
  store := Store.empty;
  heap := hp;
  
  exec ast newID

let interpRepl newID e =
  let ast = parseRepl e in
  exec [ast] newID

let test s = 
  Format.printf "%t@." (print_value (interpFile s));
  printHeapStore !heap !store 

let complete_tests =
  
  test "let x = 1 in let y = 2 in x + y";
  test "let x = 1 in let y = 2 in x + y + 3";
  test "2 + 2";
  test "(if 2 < 4 then 10 else 100) + 2";
  test "(fun x -> x * x + x + 1) 7";
  (* test "(fun x -> x * x + x + 1) ((fun x -> x * x + x + 1) 7)";
  test "let unit = {}";
  test "{a=3} with {c=4, b=5}";
  test "{x=7,y=8} with 42";
  test "({x=7,y=8} with 42) + 10";
  test "if (7 with false) then 10 else 20";
  test "let rec = fun f -> { self = fun x -> f this.self x }.self";
  test "{x=4, y=5}.x"; *)
  (* test "let x = 2 + 2;; 
  
  4+x"; *)

  test "let p = {x = 7, y = 8};;
  p.x := 10;; 
  p\n";

  test "
  let list = {
  isEmpty = fun _ -> this.empty,
  getHead = fun _ -> this.head,
  getTail = fun _ -> this.tail,
  
  nil =  fun _ -> this with { empty = true },
  cons = fun x -> fun xs -> this with { empty = false, head = x, tail = xs },

  iterator = (fun _ ->
    { elements = this,
      hasNext = (fun _ -> not this.elements.empty),
      next = (fun _ -> let x = this.elements.head in this.elements := this.elements.tail; x)
    }),

   get = fun n -> if n = 0 then this.head else this.tail.get (n-1),

   map = fun f ->
     if this.empty then
       this.nil {}
     else
       this.cons (f this.head) (this.tail.map f)
  } ;;
  
  let a = list.cons 1 (list.cons 2 (list.cons 3 (list.nil {}))) ;;
  a.get 2;;
  "
  (* test "{x = 7, y = 8} ;; {x = 9, y = 10} ;;" *)
  
  (* test "
  let a = list.cons 1 (list.cons 2 (list.cons 3 (list.nil {}))) ;;

  let x = a.get 2 ;;
  " *)


let startRepl =
  let (hp, newID) = initFrame (Heap.empty) in
  store := Store.empty;
  heap := hp;
  
  let rec repl _ =
    (
      print_string "\n\n> ";
      let input = read_line () in
    
      try
        Format.printf "%t@." (print_value (interpRepl newID input));
        repl ()
      with (Failure msg) ->
        Printf.printf "Error: %s\n\n" msg;
        repl ()
    ) in 
    
  repl ()
  