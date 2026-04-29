module V = Value
module L = Level
module C = Channel
module T = Types

type message
  = Relay of {sender: string; channel: C.channel; lbit: lbit; tvalue: tvalue}
  | Greet of {sender: string}
  | Goodbye of {sender: string}
and lbit
  = Lbit of {bit: int; level: L.level}
and tvalue
  = TypedVal of {value: V.value; ty: T.ty}

let bitAux ladv (Lbit{bit;level}) =
  if (L.flows_to level ladv)
  then Int.to_string bit
  else  "?"

let rec valueAux ladv (TypedVal{value;ty}) =
  match value,ty with
  | IntVal _, T.Type{base=INT;level;_} when L.flows_to level ladv -> V.to_string value
  | StringVal _, T.Type{base=STRING;level;_} when L.flows_to level ladv -> V.to_string value
  | PairVal {data=(a,b);_}, T.Type{base=PAIR (at,bt);level;_} when L.flows_to level ladv ->
    String.concat "" [
      "("
    ; valueAux ladv (TypedVal{value=a;ty=at})
    ; ","
    ; valueAux ladv (TypedVal{value=b;ty=bt})
    ; ")"
    ]
  | ArrayVal {length;data;_}, T.Type{base=ARRAY ty;level;_} when L.flows_to level ladv ->
    let datastr =
      data |> Array.to_list
           |> Util.take length
           |> List.map (fun value -> TypedVal{value;ty})
           |> List.map (valueAux ladv)
           |> String.concat ";" in
    "[" ^ datastr ^ "]"
  | _ -> "?"

let sizeOfLvalue (TypedVal{value;_}) =
  V.size value

let sizeOfMsgValue = function
  | Relay {tvalue;_} ->
    sizeOfLvalue tvalue
  | _ -> 0

let to_string ?(ladv=L.bottom) msg =
  match msg with
  | Relay {sender;channel;lbit;tvalue;_} ->
    String.concat ""
    [ sender
    ; "->"
    ; C.to_string channel
    ; " {"
    ; bitAux ladv lbit
    ; ","
    ; valueAux ladv tvalue
    ; "} ("
    ; Int.to_string @@ sizeOfLvalue tvalue
    ; " bytes)"
    ]
  | Greet {sender} -> "init: " ^ sender
  | Goodbye {sender} -> "exit: " ^ sender
