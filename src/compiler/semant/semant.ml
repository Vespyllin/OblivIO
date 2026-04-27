open Common
open Tabsyn
open Oper

module A = Absyn
module Err = Errorenv
module Ty = Types
module L = Level
module Ch = Channel

module H = Hashtbl

type context 
  = { gamma: (string, Ty.ty) H.t
    ; lambda: (Ch.channel, (L.level * Ty.ty * int)) H.t
    ; delta: (string, Ty.ty) H.t
    ; pi: (string, Ty.ty) H.t
    ; err:  Err.errorenv 
    }
;;

let _bot base =
  Ty.Type{base;errable=false;level=L.bottom}

let raiseTo (T.Type{base;errable;level}) lvl =
  T.Type{base;errable;level=L.lub level lvl}

let errLvl err pos msg =
  Err.error err pos @@ msg;
  L.bottom

let errTy err pos msg =
  Err.error err pos @@ msg;
  _bot Ty.CRASH

let lookupVar ({gamma;delta;err;_}) v pos = 
  match H.find_opt delta v with
  | Some ty -> LOCAL,ty
  | None ->
    match H.find_opt gamma v with
    | Some ty -> STORE, ty
    | None -> LOCAL, errTy err pos @@ "undeclared variable " ^ v

let lookupInternal ({pi;err;_}) ch pos = 
    match H.find_opt pi ch with
    | Some ty -> ty
    | None -> errTy err pos @@ "undeclared internal channel"

let lookupRemote ({lambda;err;_}) ch pos = 
  match H.find_opt lambda ch with
  | Some lvl_ty_cap -> lvl_ty_cap
  | None -> L.bottom, errTy err pos @@ "undeclared channel " ^ Ch.to_string ch, 0

let e_ty (Exp{ty;_} as e) = (e,ty)
let e_ty_lvl (Exp{ty;_} as e) = (e,ty,Ty.level ty)
let v_ty (Var{ty;_} as v) = (v,ty)
let v_ty_loc (Var{ty;loc;_} as v) = (v,ty,loc)
let v_ty_lvl (Var{ty;_} as v) = (v,ty,T.level ty)

let v_ty_lvl_loc (Var{ty;loc;_} as v) = (v,ty,T.level ty,loc)

let rec isSameBase t1 t2 =
  match Ty.base t1, Ty.base t2 with
  | Ty.CRASH, _ -> true
  | _, Ty.CRASH -> true
  | T.INT, T.INT -> true
  | T.STRING, T.STRING -> true
  | T.PAIR (a1,a2), T.PAIR (b1,b2) ->
    isSameBase a1 b1 && isSameBase a2 b2
  | T.ARRAY t1, T.ARRAY t2 ->
    isSameBase t1 t2
  | _ -> false

let checkBaseType t1 t2 err pos =
  if not (isSameBase t1 t2)
  then Err.error err pos @@ "type " ^ (Ty.base_to_string @@ Ty.base t1) ^ " not equal to type " ^ (Ty.base_to_string @@ Ty.base t2)

let checkFlow l1 l2 err pos =
  if not (L.flows_to l1 l2)
  then Err.error err pos @@ "illegal flow from " ^ L.to_string l1 ^ " to " ^ L.to_string l2

let checkFlowType t1 t2 err pos =
  let l1, l2 = Ty.level t1, Ty.level t2 in
  if not (L.flows_to l1 l2)
  then Err.error err pos @@ "illegal flow from " ^ L.to_string l1 ^ " to " ^ L.to_string l2

let checkComparable t1 t2 err pos =
  let rec _check t1 t2 =
    match T.base t1, T.base t2 with
    | Ty.INT, Ty.INT -> ()
    | Ty.STRING, Ty.STRING -> ()
    | Ty.PAIR (a1,a2), Ty.PAIR (b1,b2) ->
      _check a1 b1; _check a2 b2
    | Ty.ARRAY t1, Ty.ARRAY t2 ->
      _check t1 t2
    | b1, b2 -> Err.error err pos @@ "types " ^ Ty.base_to_string b1 ^ " and " ^ Ty.base_to_string b2 ^ " do not match"
  in _check t1 t2

let rec checkAssignable ?self value dest err pos =
  checkFlowType value dest err pos;
  if Ty.errable value && not (Ty.errable dest)
  then Err.error err pos @@ "cannot assign errable value to non-errable destination";
  
  match T.base value, T.base dest with
  | T.CRASH, _ -> ()
  | _, T.CRASH -> ()

  | T.ANY, _  -> ()
  | T.SELF t1, T.SELF t2 ->
    (* TODO: Are all the cases for 'self' assignment covered? *)
    (match !t2 with
      | Some _ -> ()
      | None -> t2 := !t1)
  | T.SELF t1 , _ -> 
    let _ = match !t1 with 
    | Some(y) -> checkAssignable y dest err pos;
    | None -> Err.error err pos @@ "mismached types: " ^ (T.to_string value) ^ " to " ^ (T.to_string dest) 
    in
    ()
  | _, T.SELF t2 ->
    begin match self with
    | Some t -> 
      t2 := self;
      checkAssignable ?self value t err pos
    | None -> Err.error err pos @@ "mismached types: " ^ (T.to_string value) ^ " to " ^ (T.to_string dest) 
    end
  | T.INT, T.INT -> ()
  | T.STRING, T.STRING -> ()
  | T.PAIR (a1,a2), T.PAIR (b1,b2) ->
    checkAssignable ?self a1 b1 err pos;
    checkAssignable ?self a2 b2 err pos;
  | T.ARRAY t_value, T.ARRAY t_dest ->
    checkAssignable ?self t_value t_dest err pos
  | T.POINTER t_value, T.POINTER t_dest ->
    if not (T.base t_value = T.ANY) && not (L.flows_to (T.level t_value) (T.level t_dest) && L.flows_to (T.level t_dest) (T.level t_value))
      then Err.error err pos @@ "pointer cell levels must be equal: " ^L.to_string (T.level t_value) ^ " vs " ^ L.to_string (T.level t_dest);
    checkAssignable ?self t_value t_dest err pos
  | T.PATH (t_value, s1), T.PATH (t_dest, s2) ->
    if (s1 != s2) then Err.error err pos @@ "cannot assign paths of different sizes: " ^ string_of_int s1 ^ " to " ^ string_of_int s2;
    checkAssignable ?self t_value t_dest err pos

  | b1, b2 -> Err.error err pos @@ "cannot assign expression of type " ^ Ty.base_to_string b1 ^ " to variable of type " ^ Ty.base_to_string b2

let checkLowPC pc err pos =
  if not (L.flows_to pc L.bottom)
  then Err.error err pos @@ "pc must be low"

let checkInt t err pos =
  match Ty.base t with
  | Ty.INT -> ()
  | b -> Err.error err pos @@ "int required, " ^ Ty.base_to_string b ^ " provided"

let checkString t err pos =
  match Ty.base t with
  | Ty.STRING -> ()
  | b -> Err.error err pos @@ "string required, " ^ Ty.base_to_string b ^ " provided"

exception NotImplemented of string
let rec transExp ({err;_} as ctxt) =
  let rec trexp (A.Exp{exp_base;pos}) =
    let (^!) exp_base ty = Exp{exp_base;ty;pos} in
    match exp_base with
    | IntExp n -> IntExp n ^! _bot Ty.INT
    | StringExp s -> StringExp s ^! _bot Ty.STRING
    | VarExp v ->
      let v,ty = v_ty @@ transVar ctxt v in
      VarExp v ^! ty
    | SizeExp e ->
      let e = trexp e in
      SizeExp e ^! _bot Ty.INT
    | OpExp {left;oper;right} ->
      let (left,lty) = e_ty @@ trexp left in
      let (right,rty) = e_ty @@ trexp right in
      let level = L.lub (Ty.level lty) (Ty.level rty) in
  
      let base, errable = match oper with
        | CoalesceOp ->
          begin match Ty.errable lty, Ty.errable rty with
          | true, true ->
            checkAssignable lty rty err pos;
            Ty.base rty, true
          | true, _ ->
            (* Swap rty lty order to make the check go through *)
            checkAssignable rty lty err pos;
            Ty.base lty, false
          | _ ->
            Err.error err pos "left side of coalesce must be an errable type";
            Ty.base lty, false
          end
        | PlusOp | MinusOp | TimesOp | LtOp | LeOp | GtOp | GeOp | AndOp | OrOp ->
          checkInt lty err pos;
          checkInt rty err pos;
          Ty.INT, (Ty.errable lty || Ty.errable rty)
        | EqOp | NeqOp ->
          checkComparable lty rty err pos;
          Ty.INT, (Ty.errable lty || Ty.errable rty)
        | CaretOp ->
          checkString lty err pos;
          checkString rty err pos;
          Ty.STRING, (Ty.errable lty || Ty.errable rty)
        in
      OpExp{left;oper;right} ^! Ty.Type{base;errable;level}
    | ProjExp {proj;exp} -> 
      let (exp,ty,level) = e_ty_lvl @@ trexp exp in
      let proj,ty =
        match proj,T.base ty with
        | Fst, T.PAIR (t,_) -> Fst, raiseTo t level
        | Snd, T.PAIR (_,t) -> Snd, raiseTo t level
        | Fst, _ -> Fst, errTy err pos @@ "not a pair type " ^ T.to_string ty
        | Snd, _ -> Snd, errTy err pos @@ "not a pair type " ^ T.to_string ty in
      ProjExp{proj;exp} ^! ty
    | PairExp (a,b) ->
      let (a,aty) = e_ty @@ trexp a in
      let (b,bty) = e_ty @@ trexp b in
      let base = T.PAIR (aty,bty) in
      PairExp (a,b) ^! T.Type{base;errable=false;level=L.bottom}
    | ArrayExp arr ->
      let ty = match arr with
      | hd::_ ->
        let _, ty = e_ty @@ transExp ctxt hd in
        ty
      | [] ->
        T.Type{base=Ty.ANY;errable=false;level=L.bottom} in
      let f exp =
        let e,ety = e_ty @@ transExp ctxt exp in
        checkBaseType ty ety err pos;
        e in
      let arr = List.map f arr in
      let base = T.ARRAY ty in
      ArrayExp arr ^! T.Type{base;errable=false;level=L.bottom}
    | ArrayConstructorExp {length;value} -> 
      let e, ty = e_ty @@ transExp ctxt value in
      let base = T.ARRAY ty in
      ArrayExp (List.init length (fun _ -> e)) ^! T.Type{base;errable=false;level=L.bottom}
    | NilExp -> NilExp ^! _bot (T.POINTER (T.Type{base=T.ANY;errable=false;level=L.bottom}))
    | OnilExp size -> OnilExp size ^! _bot (T.PATH ((T.Type{base=T.ANY;errable=false;level=L.bottom}), size))
    | AllocExp p -> 
      let e, ty = e_ty @@ trexp p in
      AllocExp e ^! _bot (T.POINTER ty)
    | OramExp{value=p; size=s} -> 
      let e, ty = e_ty @@ trexp p in
      OramExp{value=e; size=s} ^! Ty.Type{base=(T.PATH (ty, s));errable=false;level=L.bottom}
  in trexp

and transVar ({err;_} as ctxt) =
  let rec trvar (A.Var{var_base;pos}) =
    let (^!) var_base ty = Var{var_base;loc=LOCAL;ty;pos} in
    let (^@) var_base ty = Var{var_base;loc=STORE;ty;pos} in
    match var_base with
    | SimpleVar x ->
      let varloc, ty = lookupVar ctxt x pos in
      begin
      match varloc with
        | LOCAL -> SimpleVar x ^! ty
        | STORE -> SimpleVar x ^@ ty
      end
    | SubscriptVar {var;exp} ->
      let var,vty,_,loc = v_ty_lvl_loc @@ trvar var in
      let exp,ety,elvl = e_ty_lvl @@ transExp ctxt exp in
      checkInt ety err pos;
      let cty = match T.base vty with
        | T.ARRAY t -> 
          if not (L.flows_to elvl (Ty.level t)) 
          then errTy err pos @@ "index does not flow to array content level: " ^ T.to_string ety ^ " to " ^ T.to_string t 
          else Ty.Type{base=T.base t; errable=true; level=Ty.level t}
        | _ -> errTy err pos @@ "variable type not an array type: " ^ T.to_string vty in
      begin
      match loc with
      | LOCAL -> SubscriptVar{var;exp} ^! cty
      | STORE -> SubscriptVar{var;exp} ^@ cty
      end
    | HeapVar {var} ->
      let var, vty, _, loc = v_ty_lvl_loc @@ trvar var in
      let t = match T.base vty with
        | T.POINTER t ->
          begin match T.base t with
          | T.SELF _ -> vty
          | _ -> t
          end
        | T.PATH (t, _) ->
          let inner = begin match T.base t with
          | T.SELF _ -> vty
          | _ -> t
          end in
          Ty.Type{base=T.base inner; errable=true; level=Ty.level inner}
        | _ -> errTy err pos @@ "variable is not a pointer type: " ^ T.to_string vty in
      begin
      match loc with
      | LOCAL -> HeapVar{var} ^! t
      | STORE -> HeapVar{var} ^@ t
      end
  in trvar

let rec varname (Var{var_base;_}) =
  match var_base with
  | SimpleVar x -> x
  | SubscriptVar{var;_} -> varname var
  | HeapVar{var} -> "*" ^ varname var

let checkWritable var varloc err pos =
  match varloc with
  | LOCAL -> Err.error err pos @@ "handler variable " ^ varname var ^ " is read-only"
  | STORE -> ()

let transCmd ({err;_} as ctxt) =
  let rec trcmd pc (q: int) (A.Cmd{cmd_base;pos}): cmd * int =
    let fromBase cmd_base = Cmd{cmd_base;pos} in
    match cmd_base with
    | SkipCmd -> fromBase SkipCmd, q
    | SeqCmd {c1;c2} ->
      let (c1,q') = trcmd pc q c1 in
      let (c2,q'') = trcmd pc q' c2 in
      fromBase @@ SeqCmd {c1;c2}, q''
    | AssignCmd {var;exp} ->
      let var,varty,varloc = v_ty_loc @@ transVar ctxt var in
      let e,ety = e_ty @@ transExp ctxt exp in
      checkLowPC pc err pos;
      begin
        match varloc with
        | LOCAL ->
          Err.error err pos @@ "handler variable " ^ varname var ^ " is read-only";
        | STORE -> 
          checkLowPC pc err pos
      end;
      checkAssignable ~self:varty ety varty err pos;
      fromBase @@ AssignCmd{var;exp=e}, q
    | BindCmd {var;exp} ->
      let var,varty,varloc = v_ty_loc @@ transVar ctxt var in
      let e,ety = e_ty @@ transExp ctxt exp in
      checkWritable var varloc err pos;
      checkAssignable (raiseTo ety pc) varty err pos;
      fromBase @@ BindCmd{var;exp=e}, q
    | InputCmd {var;ch;size} ->
      let var,varty,varloc = v_ty_loc @@ transVar ctxt var in
      let size,ety,elvl = e_ty_lvl @@ transExp ctxt size in
      let chty = lookupInternal ctxt ch pos in
      checkInt ety err pos;
      begin
        match varloc with
        | LOCAL ->
          Err.error err pos @@ "handler variable " ^ varname var ^ " is read-only";
        | STORE -> 
          begin 
            match T.base chty with
            | T.STRING -> ()
            | _ -> Err.error err pos @@ "input command expected channel with type string, channel " ^ ch ^ " has type " ^ T.to_string chty;
          end;
          let l = L.lub pc elvl in
          checkFlow l (T.level chty) err pos;
          checkAssignable (T.raiseTo chty l) varty err pos;
      end;
      fromBase @@ InputCmd{var;ch;size}, q
    | OutputCmd {ch;exp} ->
      let exp,ety = e_ty @@ transExp ctxt exp in
      let chty = lookupInternal ctxt ch pos in
      checkAssignable (T.raiseTo ety pc) chty err pos;
      fromBase @@ OutputCmd{ch;exp}, q
    | SendCmd {channel;exp} ->
      let (chlvl,chty,chq) = lookupRemote ctxt channel pos in
      let e,ety = e_ty @@ transExp ctxt exp in
      checkFlow pc chlvl err pos;
      checkAssignable ety chty err pos;

      let r = match L.flows_to pc L.bottom with
        | true -> 0
        | false -> 1+chq in

      begin
      if q < r
      then Err.error ctxt.err pos @@ "insufficient potential for sending on channel " ^ Ch.to_string channel ^ " under pc " ^ L.to_string pc ^ ", required: " ^ Int.to_string r ^ ", remaining: " ^ Int.to_string q;
      end;

      fromBase @@ SendCmd{channel;exp=e}, max 0 (q - r)
    | IfCmd{test;thn;els} ->
      let test,testty,testlvl = e_ty_lvl @@ transExp ctxt test in
      checkInt testty err pos;
      checkFlow testlvl L.bottom err pos;
      let (thn,q') = trcmd pc q thn in
      let (els,q'') = trcmd pc q els in
      fromBase @@ IfCmd{test;thn;els}, min q' q''
    | WhileCmd{test;body} ->
      let test,testty,testlvl = e_ty_lvl @@ transExp ctxt test in
      checkInt testty err pos;
      checkLowPC pc err pos;
      checkFlow testlvl L.bottom err pos;
      let (body,_) = trcmd pc 0 body in
      fromBase @@ WhileCmd{test;body}, q
    | OblivIfCmd{test;thn;els} ->
      let test,testty,testlvl = e_ty_lvl @@ transExp ctxt test in
      checkInt testty err pos;
      let (thn, q') = trcmd (L.lub pc testlvl) q thn in
      let (els, q'') = trcmd (L.lub pc testlvl) q' els in
      if L.flows_to testlvl L.bottom
      then Err.error err pos @@ "test for oblif is labelled public";
      fromBase @@ OblivIfCmd{test;thn;els}, q''
    | ExitCmd -> 
      checkLowPC pc err pos;
      fromBase ExitCmd, q
  in trcmd

let transDecl ({gamma;lambda;pi;err;_} as ctxt: context) dec =
  match dec with
  | A.VarDecl {ty;x;init;pos} ->
    if H.mem gamma x
    then Err.error err pos @@ "variable " ^ x ^ " already declared";
    let init,initty = e_ty @@ transExp ctxt init in
    H.add gamma x ty;
    checkAssignable ~self:ty initty ty err pos;

    let rec checkOramCompatibleTypes ?(strict=false) ty =
      let errmsg = "cannot pass in a variable size value within an array/pair in a path" in
      match T.base ty with
      | T.INT -> ()
      | T.STRING -> 
        if strict 
          then Err.error err pos errmsg
          else ()
      | T.PATH (block, _) ->
        checkOramCompatibleTypes block
      | T.ARRAY content -> 
        if strict 
          then Err.error err pos errmsg
          else checkOramCompatibleTypes ~strict:true content
      | T.PAIR (a, b) -> 
          if strict 
          then Err.error err pos errmsg
          else begin
            checkOramCompatibleTypes ~strict:true a; 
            checkOramCompatibleTypes ~strict:true b
          end
      | T.SELF _ -> ()
      | _ -> Err.error err pos "datatype is not supported in ORAM"
    in
    let rec checkPtrLevels ty =
    match T.base ty with
    | T.SELF _ -> ()
    | T.POINTER cell ->
      if not @@ L.flows_to (T.level ty) (T.level cell)
      then Err.error err pos @@ "pointer cannot be more privileged than pointee";

      checkPtrLevels cell
    | T.PATH (block, _) ->
      if L.flows_to (T.level ty) L.bottom
      then Err.error err pos @@ "path cannot be public";

      begin match T.base block with
      | T.SELF _ -> ()
      | _ ->
        if not @@ L.flows_to (T.level ty) (T.level block) 
        then Err.error err pos @@ "path cannot be more privileged than block";
        checkPtrLevels block;
      end;
      checkOramCompatibleTypes ty;
    | T.ARRAY content ->
      if not @@ L.flows_to (T.level ty) (T.level content)
      then Err.error err pos @@ "array content cannot be more privileged than array";
    | _ -> ()
  in
  checkPtrLevels ty;
    VarDecl{x;ty;init;pos}
  | A.NetworkChannelDecl {channel;level;potential;ty;pos} ->
    if H.mem lambda channel
    then Err.error err pos @@ "network channel " ^ Ch.to_string channel ^ " already declared";
    H.add lambda channel (level,ty,potential);
    if potential < 0
    then Err.error ctxt.err pos @@ "potential " ^ Int.to_string potential ^ " must be non-negative for channel " ^ Ch.to_string channel ^ "@" ^ L.to_string level;
    NetworkChannelDecl{channel;level;potential;ty;pos}
  | A.LocalChannelDecl{ch;ty;pos} ->
    if H.mem pi ch
    then Err.error err pos @@ "internal channel " ^ ch ^ " already declared";
    H.add pi ch ty;
    LocalChannelDecl{ch;ty;pos}

let transHl ctxt node (A.Hl{handler;level;potential;x;ty;body;pos}) =
  let ctxt = {ctxt with delta = H.create 1024} in
  H.add ctxt.delta x ty;

  let hlchannel = Ch.Ch{node;handler} in

  if potential < 0
  then Err.error ctxt.err pos @@ "potential " ^ Int.to_string potential ^ " must be non-negative for handler channel " ^ Ch.to_string hlchannel ^ "@" ^ L.to_string level;

  if handler = "START" && level <> L.bottom
  then Err.error ctxt.err pos @@ "START channel must be public";

  let (body,_) = transCmd ctxt level potential body in

  Hl{handler;level;potential;x;ty;body;pos}

let transProg (A.Prog{node;decls;hls}) =
  let ctxt = 
    { gamma = H.create 1024
    ; lambda = H.create 1024
    ; delta = H.create 0
    ; pi = H.create 1024
    ; err = Err.initial_env
    } in
  let decls = List.map (transDecl ctxt) decls in
  let hls = List.map (transHl ctxt node) hls in
  not (Err.any_errors ctxt.err), Prog{node;decls;hls}
