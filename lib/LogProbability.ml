type t = float

let mult a b = a +. b

let to_dec a = exp a
let div a b = a -. b

let add a b =
  if b < a then
    a +. (log1p (exp (b -. a)))
  else
    b +. (log1p (exp (a -. b)))

let make a = log a

let to_string base t =
  string_of_float (t /. log base)
