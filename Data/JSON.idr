module Data.JSON

%access public export
%default total

public export
data JsonValue : Type where
  JsonNull  : JsonValue
  JsonBool  : Bool -> JsonValue
  JsonArray : (List JsonValue) -> JsonValue

data ParseState = Start | InArray

mutual
  data ArrayRepr : (List Char) -> (List JsonValue) -> Type where
    AREmpty : ArrayRepr [] []
    ARValue : Repr s v -> ArrayRepr s [v]
    ARComma : Repr xs xv -> ArrayRepr s (v :: vs) -> ArrayRepr (xs ++ [','] ++ s) (xv :: v :: vs)

  data Repr : (List Char) -> JsonValue -> Type where
    RNull       : Repr ['n','u','l','l'] JsonNull
    RTrue       : Repr ['t','r','u','e'] (JsonBool True)
    RFalse      : Repr ['f','a','l','s','e'] (JsonBool False)
    RArray      : ArrayRepr inside vs -> Repr ('[' :: inside ++ [']']) (JsonArray vs)

show' : (v : JsonValue) -> (s : List Char ** Repr s v)
show' JsonNull         = (['n','u','l','l'] ** RNull)
show' (JsonBool False) = (['f','a','l','s','e'] ** RFalse)
show' (JsonBool True)  = (['t','r','u','e'] ** RTrue)
show' (JsonArray vs)   = ('[' :: fst insides ++ [']'] ** RArray (snd insides))
                         where
                           makeInsides : (xs : List JsonValue) -> (s : List Char ** ArrayRepr s xs)
                           makeInsides [] = ([] ** AREmpty)
                           makeInsides [x] = let (s ** prf) = show' x in
                                             (s ** ARValue prf)
                           makeInsides (x :: y :: ys) = let (sx ** xProof) = show' x
                                                            (sxs ** xsProof) = makeInsides (y :: ys) in
                                                        (sx ++ [','] ++ sxs ** ARComma xProof xsProof)

                           insides : (s : List Char ** ArrayRepr s vs)
                           insides = makeInsides vs

data ParseResult : (List Char -> ty -> Type) -> List Char -> Type where
  ParseFail : ParseResult a s
  ParseOk : (value : ty) ->
            (remainder : List Char) ->
            (repr : reprType parsed value) ->
            ParseResult reprType (parsed ++ remainder)


data Tail : List a -> List a -> Type where
  TailCons : Tail t (h :: t)
  TailStep : Tail t xs -> Tail t (x :: xs)

WellFounded Tail where
  wellFounded l {a} = Access (acc l)
                      where
                        acc : (full, tail : List a) -> Tail tail full -> Accessible Tail tail
                        acc (h :: tail) tail TailCons           = Access (acc tail)
                        acc (x :: xs)   tail (TailStep witness) = acc xs tail witness

parseStep : (s : List Char) -> ((y : List Char) -> Tail y s -> ParseResult Repr y) -> ParseResult Repr s
parseStep ('n'::'u'::'l'::'l'::rem)      rec = ParseOk JsonNull rem RNull
parseStep ('f'::'a'::'l'::'s'::'e'::rem) rec = ParseOk (JsonBool False) rem RFalse
parseStep ('t'::'r'::'u'::'e'::rem)      rec = ParseOk (JsonBool True) rem RTrue
parseStep _                              rec = ParseFail
