let rec merge s t =
  let rec merge' t =
    match s, t with
         [],     _ -> t
    |     _,    [] -> s
    | x::s', y::t' -> if   x <= y
                     then x :: merge s' t
                     else y :: merge' t'
  in merge' t

let rec cut s t u =
  match t, u with
    y::t', _::_::u' -> cut (y::s) t' u'
  |               _ -> s, t

let split s = cut [] s s

let rec tms s =
  match s with
    [] | [_] -> s
  | _ -> let a, b = split s
        in merge (tms a) (tms b)
