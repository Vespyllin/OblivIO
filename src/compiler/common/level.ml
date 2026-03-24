module ST = Set.Make(String)
    
type level = ST.t

let bottom = ST.empty
let lub = ST.union
let flows_to = ST.subset
let of_list = ST.of_list

let to_string level =
  "{" ^ (String.concat "," @@ List.of_seq @@ ST.to_seq level) ^ "}"

module SS = Map.Make(ST)
    
type 'a lvlmap = 'a SS.t

let empty = SS.empty
let enter (t, k, v) = SS.add k v t
let look (t, k) = SS.find_opt k t
let numItems = SS.cardinal
