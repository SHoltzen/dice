type t = float

let mult a b = a +. b

let conv a = a
let to_dec a = exp a
let div a b = a -. b

let add a b =
  if (Float.is_infinite a && Float.is_infinite b) then Float.neg_infinity else
  if b < a then
    a +. (log1p (exp (b -. a)))
  else
    b +. (log1p (exp (a -. b)))

let make a = log a

let rat_div_and_conv a b = Bignum.of_float_decimal (exp ((Bignum.to_float a) -. (Bignum.to_float b)))

let to_string base t =
  string_of_float (t /. log base)
