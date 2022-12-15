(*
                         CS 51 Problem Set 3
                           Bignums and RSA
*)

(* In this problem set, you'll implement arbitrary precision integers
-- "bignums" -- for use in an implementation of the RSA public-key
cryptographic system. As with the previous problem set, you may
express your solution to a particular problem in terms of another
function from a previous problem, and you may use functions from the
`List` module where appropriate.

Before starting on the problem set, read the problem set 3 writeup in
the textbook. It provides context and crucial information for
completing the problems. In addition, make sure that you are familiar
with the problem set procedures in the document "Problem set
procedures for CS51".
 *)
   
(*======================================================================
  Basics: representing bignums, negating and comparing them, and
  converting between bignums and other representations.
 *)
   
(* bignum -- Type for representing bignums (arbitrary precision
   integers. Uses a boolean field neg for negative numbers and a list
   coeffs of coefficients from most to least significant. *)
   
type bignum = {neg : bool; coeffs : int list} ;;

(* cBASE -- Global constant, the base for representing bignums, which
   must be a power of 10. Your code should work for any reasonable
   value of `cBASE`, not just the initial value we've set it to. When
   submitting, have `cBASE` be 1000, as it is here. *)
  
let cBASE = 1000 ;;
  
(*......................................................................
Problem 1: Negation
......................................................................*)

(* negate b -- Returns a `bignum` that is the negation of `b`. *) 
let negate (b : bignum) : bignum =
  match b with
  | {neg = false; coeffs = []} -> {neg = false; coeffs = []}
  | {neg = true; coeffs = _} -> {neg = false; coeffs = b.coeffs}
  | {neg = false; coeffs = _} -> {neg = true; coeffs = b.coeffs} ;;

(*......................................................................
Problem 2: Comparing bignums
......................................................................*)  
  
(* equal b1 b2 -- Predicate returns `true` if and only if `b1` and
   `b2` represent the same number. *)
let rec equal (b1 : bignum) (b2 : bignum) : bool =
  b2 = b1 ;;

(* less b1 b2 -- Predicate returns `true` if and only if `b1`
   represents a smaller number than `b2`. *)
let less (b1 : bignum) (b2 : bignum) : bool =
  match b1.neg, b2.neg with
  | true, true -> b1 > b2
  | true, false -> true
  | false, true -> false
  | false, false -> b2 > b1 ;;

(* greater b1 b2 -- Predicate returns `true` if and only if `b1`
   represents a larger number than `b2`. *)
let greater (b1 : bignum) (b2 : bignum) : bool =
  less b2 b1 ;;

(*......................................................................
Problem 3: Converting to and from bignums
......................................................................*)

(* from_int n -- Returns a bignum representing the integer `n`. *)
let from_int (n : int) : bignum =
  let rec aux num : int list =
    if num = 0 then []
    else abs (num mod cBASE) :: aux (num/cBASE) in
    {neg = n < 0; coeffs = List.rev (aux n)} ;;
     
(* to_int b -- Returns `Some v`, where `v` is the `int` represented by
   the bignum `b`, if possible, or `None` if `b` represents an integer
   out of the representable range of the `int` type. *)
let to_int (b : bignum) : int option =
  let to_int_ =
    List.fold_right (fun x y -> x + (y * cBASE)) b.coeffs 0 in
  if to_int_ = 0 
  then None 
  else Some to_int_ ;;

(*======================================================================
  Helpful functions (not to be used in problems 1 to 3)
 *)

(* trim_leading_zeroes lst -- Removes zero coefficients from the beginning of
   the coefficients part of a bignum representation *)
let rec trim_leading_zeroes (lst : int list) : int list =
  match lst with
  | 0 :: tl -> trim_leading_zeroes tl
  | _ -> lst ;;

(* clean b -- Removes zero coefficients from the beginning of a bignum
   representation *)
let clean (b : bignum) : bignum =
  {neg = b.neg; coeffs = trim_leading_zeroes b.coeffs} ;;

(* rand_bignum bound -- Returns a random bignum from 0 to the absolute
   value of `bound` (inclusive). Useful for randomly testing
   functions. *)
let rand_bignum (bound : bignum) : bignum =
  let rand_base = List.map (fun _ -> Random.int cBASE) in
  let rec rand_bignum_rec (bounds : int list) =
    match bounds with
    | [] -> []
    | h :: t -> let r = Random.int (h + 1) in
                r :: ((if r = h then rand_bignum_rec else rand_base) t) in
  {neg = false; coeffs = trim_leading_zeroes (rand_bignum_rec bound.coeffs)} ;;
       
(* explode s -- Splits a string `s` into a list of its characters. *)
let rec explode (s : string) : char list =
  let len = String.length s in
  if len = 0 then []
  else s.[0] :: explode (String.sub s 1 (len - 1)) ;;

(* implode cs -- Condenses a list of characters `cs` into a string. *)
let rec implode (cs : char list) : string =
  match cs with
  | [] -> ""
  | c :: t -> String.make 1 c ^ implode t ;;
                                          
(* split lst n -- Returns a pair containing the first `n` elements of
   `lst` and the remaining elements of `lst`. *)
let rec split lst n =
  if n = 0 then ([], lst)
  else match lst with
       | [] -> ([], [])
       | hd :: tl -> let lst1, lst2 = split tl (n - 1) in
                     hd :: lst1, lst2 ;;

(* take_first lst n -- Returns the first `n` elements of list `lst`
   (or the whole `lst` if too short). *)
let take_first (lst : 'a list) (n : int) : 'a list =
  fst (split lst n) ;;

(* intlog base -- Returns the floor of the base 10 log of an integer
   `base` *)
let intlog (base : int) : int =
  int_of_float (log10 (float_of_int base)) ;;

(* from_string s -- Converts a string `s` representing an integer to a
   bignum. Assumes the base `cBASE` is a power of 10. *)
let from_string (s : string) : bignum =
  
  let rec from_string_rec (cs : char list) : int list =
    if cs = [] then []
    else
      let (chars_to_convert, rest) = split cs (intlog cBASE) in
      let string_to_convert = implode (List.rev chars_to_convert) in
      int_of_string string_to_convert :: from_string_rec rest in
  
  match explode s with
  | [] -> from_int 0
  | h :: t ->
      if h = '-' || h = '~' then
        {neg = true; coeffs = (List.rev (from_string_rec (List.rev t)))}
      else {neg = false;
            coeffs =
              (trim_leading_zeroes (List.rev (from_string_rec (List.rev (h :: t)))))}

(* to_string b -- Converts a bignum `b` to its string representation.
   Returns a string beginning with `~` for negative integers. Assumes
   the base `cBASE` is a power of 10. *)
let to_string (b : bignum) : string =
  
  let rec pad_leading_zero_chars (s : string) (len : int) =
    if String.length s >= len then s
    else "0" ^ pad_leading_zero_chars s (len - 1) in
  
  let rec trim_leading_zero_chars (s : string) (c : char) =
    if String.length s = 0 then
      "0"
    else if String.get s 0 = '0' then
      trim_leading_zero_chars (String.sub s 1 (String.length s - 1)) c
    else s in

  let rec coeffs_to_string (coeffs : int list) : string =
    match coeffs with
    | [] -> ""
    | h :: t -> pad_leading_zero_chars (string_of_int h) (intlog cBASE)
                ^ coeffs_to_string t in
  
  let trimmed = trim_leading_zeroes b.coeffs in
  if List.length trimmed = 0 then "0"
  else let from_coeffs =
         trim_leading_zero_chars (coeffs_to_string trimmed) '0' in
       if b.neg then "~" ^ from_coeffs else from_coeffs ;;

(*======================================================================
  Arithmetic functions
 *)

(* plus_nonneg b1 b2 -- Returns a bignum representing the sum of `b1` and
   `b2`. NB: Assumes that (and works only when) the sum is nonnegative. *)
let plus_nonneg (b1 : bignum) (b2 : bignum) : bignum =

  let pair_from_carry (carry : int) : bool * int list =
    match carry with
    |  0 -> false, []
    |  1 -> false, [1]
    | -1 -> true,  [1]
    |  _ -> failwith "pair_from_carry: invalid carry" in
       
  let rec plus_with_carry (neg1, coeffs1 : bool * int list)
                          (neg2, coeffs2 : bool * int list)
                          (carry : int)
                        : bool * int list =
    match coeffs1, coeffs2 with
    | [], [] -> pair_from_carry carry
    | [], _ ->
       if carry = 0 then (neg2, coeffs2)
       else plus_with_carry (neg2, coeffs2) (pair_from_carry carry) 0
    | _, [] ->
       plus_with_carry (neg2, coeffs2) (neg1, coeffs1) carry
    | h1 :: t1, h2 :: t2 ->
       let sign1, sign2 =
         (if neg1 then -1 else 1), (if neg2 then -1 else 1) in
       let result = h1 * sign1 + h2 * sign2 + carry in
       if result < 0 then
         let negres, coeffsres =
           plus_with_carry (neg1, t1) (neg2, t2) (-1) in
         negres, result + cBASE :: coeffsres
       else if result >= cBASE then
         let negres, coeffsres = plus_with_carry (neg1, t1) (neg2, t2) 1 in
         negres, result - cBASE :: coeffsres
       else
         let negres, coeffsres = plus_with_carry (neg1, t1) (neg2, t2) 0 in
         negres, result :: coeffsres in
  
  let neg_result, coeffs_result =
    plus_with_carry (b1.neg, List.rev b1.coeffs)
                    (b2.neg, List.rev b2.coeffs)
                    0 in
  {neg = neg_result;
   coeffs = trim_leading_zeroes (List.rev coeffs_result)} ;;
  
(*......................................................................
Problem 4

The `plus` function returns a bignum representing b1 + b2. However, it
does NOT make the same assumption as `plus_nonneg` (that the sum is
nonnegative).

Hint: How can you use `plus_nonneg` to implement `plus`? Make sure that
your implementation preserves the bignum invariant.
......................................................................*)

(* plus b1 b2 -- Returns the bignum sum of `b1` and `b2` *)
let plus (b1 : bignum) (b2 : bignum) : bignum =
  match b1.neg, b2.neg with
  | true, true -> negate (plus_nonneg (negate b1) (negate b2))
  | false, false -> plus_nonneg b1 b2
  | true, false -> let b1_ = negate b1 in
                             negate (plus_nonneg b1_ b2)
  | false, true -> let b2_ = negate b2 in
                             negate (plus_nonneg b1 b2_) ;;

(*......................................................................
Problem 5

The times function returns a bignum representing b1 * b2. 

Think about how you were first taught multiplication, say, 543 x
224. It went something like this:

         5 4 3 
       x 2 2 4
       -------
       2 1 7 2 <--- Partial product 5 4 3 x 4

   + 1 0 8 6 0 <--- Partial product 5 4 3 x 2; note that a zero is 
                    appended after the partial product
 + 1 0 8 6 0 0 <--- Partial product 5 4 3 x 2; note that two zeroes
 -------------      are appended after the partial product
 = 1 2 1 6 3 2 <--- Sum of all (shifted) partial products 

When approaching this problem, it is advisable to break the problem
down into simpler, easier-to-implement sub-problems. That way, you can
test each helper function individually rather than having to test all
of it at once, making locating bugs much easier. What are some natural
subproblems implied by the example above?

You may assume positivity in some of your helper functions if it 
simplifies the code, as long as the invariant is preserved. 
......................................................................*)

(* times b1 b2 -- Returns the bignum product of `b1` and `b2` *)
let times (b1 : bignum) (b2 : bignum) : bignum =
  let rec times_single b1 mpl =
    let rec power_mult (lst : int list) (mplr : int list) (carry : int) =
      match lst, mplr with
      | [], _ -> [carry]
      | _, [] -> [0]
      | hd :: tl, mpl :: _ ->
        let power_res = (hd * mpl) + carry in
        let carry_ = power_res / cBASE in
        let result = (power_res mod cBASE) in
          result :: power_mult tl mplr carry_ in
    clean ({neg = false; coeffs = List.rev(power_mult (List.rev b1.coeffs) mpl 0)}) in  
  let rec times_basepower (bgn : bignum) (p : int) =
    match p with
    | 0 -> bgn
    | 1 -> times_single bgn [cBASE]
    | n -> times_single (times_basepower bgn (p-1)) [cBASE] in
  let rec times_power b1_ lst =
    match List.rev lst with
    | [] -> {neg = false; coeffs = []}
    | s :: [] -> times_single b1_ [s]
    | hd :: tl -> plus (times_single b1_ [hd]) (times_basepower (times_power b1_ (List.rev tl)) 1) in
  if b1.neg <> b2.neg 
  then negate (clean (times_power b1 b2.coeffs))
  else clean (times_power b1 b2.coeffs) ;;

(*======================================================================
Challenge Problem 6: Faster bignum multiplication 
......................................................................*)

(* times_faster b1 b2 -- Returns a bignum representing the product of
   `b1` and `b2`, making use of the Karatsuba algorithm for
   multiplication. *)
let times_faster (b1 : bignum) (b2 : bignum) : bignum =
  failwith "times_faster not implemented" ;;

(*======================================================================
Reflection on the problem set

After each problem set, we'll ask you to reflect on your experience.
We care about your responses and will use them to help guide us in
creating and improving future assignments.

........................................................................
Please give us an honest (if approximate) estimate of how long (in
minutes) this problem set took you to complete. 
......................................................................*)

let minutes_spent_on_pset () : int =
  300 ;;

(*......................................................................
It's worth reflecting on the work you did on this problem set. Where
did you run into problems and how did you end up resolving them? What
might you have done in retrospect that would have allowed you to
generate as good a submission in less time? Please provide us your
thoughts on these questions and any other reflections in the string
below.
......................................................................*)

let reflection () : string =
  "I found that I was making a lot of logical errors throughout this problem set
  I think that many of them could have been solved if I used paper and worked through
  the different cases more logically. I was finding that although the code was
  compiling, it would fail tests because certain things were flipped or backwards
  like getting my negatives switched and etc. " ;;
