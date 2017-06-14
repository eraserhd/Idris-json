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
  data ArrayRepr : (nonEmpty : Bool) -> (List Char) -> (List JsonValue) -> Type where
    AREmpty : ArrayRepr False [] []
    ARValue : Repr s v -> ArrayRepr True s [v]
    ARComma : Repr xs xv -> ArrayRepr True s vs -> ArrayRepr True (xs ++ [','] ++ s) (xv :: vs)

  data Repr : (List Char) -> JsonValue -> Type where
    RNull       : Repr ['n','u','l','l'] JsonNull
    RTrue       : Repr ['t','r','u','e'] (JsonBool True)
    RFalse      : Repr ['f','a','l','s','e'] (JsonBool False)
    RArray      : ArrayRepr _ inside vs -> Repr ('[' :: inside ++ [']']) (JsonArray vs)

show' : (v : JsonValue) -> (s : List Char ** Repr s v)
show' JsonNull         = (['n','u','l','l'] ** RNull)
show' (JsonBool False) = (['f','a','l','s','e'] ** RFalse)
show' (JsonBool True)  = (['t','r','u','e'] ** RTrue)
show' (JsonArray vs)   = ('[' :: fst (fst insides) ++ [']'] ** RArray (snd insides))
                         where
                           makeInsides : (xs : List JsonValue) -> (inf : (List Char, Bool) ** ArrayRepr (snd inf) (fst inf) xs)
                           makeInsides [] = (([], False) ** AREmpty)
                           makeInsides [x] = let (s ** prf) = show' x in
                                             ((s, True) ** ARValue prf)
                           makeInsides (x :: y :: ys) = let (sx ** xProof) = show' x
                                                            ((sxs, True) ** xsProof) = makeInsides (y :: ys) in
                                                        ((sx ++ [','] ++ sxs, True) ** ARComma xProof xsProof)

                           insides : (inf : (List Char, Bool) ** ArrayRepr (snd inf) (fst inf) vs)
                           insides = makeInsides vs

data Tail : List a -> List a -> Type where
  TailCons : Tail t (h :: t)
  TailStep : Tail t xs -> Tail t (x :: xs)

data ParseResult : (List Char -> ty -> Type) -> List Char -> Type where
  ParseFail : ParseResult a s
  ParseOk : (value : ty) ->
            (remainder : List Char) ->
            (repr : reprType parsed value) ->
            ParseResult reprType (parsed ++ remainder)

WellFounded Tail where
  wellFounded l {a} = Access (acc l)
                      where
                        acc : (full, tail : List a) -> Tail tail full -> Accessible Tail tail
                        acc (h :: tail) tail TailCons           = Access (acc tail)
                        acc (x :: xs)   tail (TailStep witness) = acc xs tail witness

parseArrayMore : (s : List Char) -> ParseResult (ArrayRepr True) s

parseStep : (s : List Char) -> ((y : List Char) -> Tail y s -> ParseResult Repr y) -> ParseResult Repr s
parseStep ('n'::'u'::'l'::'l'::rem)      rec = ParseOk JsonNull rem RNull
parseStep ('f'::'a'::'l'::'s'::'e'::rem) rec = ParseOk (JsonBool False) rem RFalse
parseStep ('t'::'r'::'u'::'e'::rem)      rec = ParseOk (JsonBool True) rem RTrue
parseStep ('['::']'::rem)                rec = ParseOk (JsonArray []) rem (RArray AREmpty)
parseStep ('['::arrayInsides)            rec with (rec arrayInsides TailCons)
  parseStep ('['::arrayInsides)                   rec | ParseFail = ParseFail
  parseStep ('['::(parsed ++ (']' :: remainder))) rec | ParseOk v (']' :: remainder) repr =
    rewrite appendAssociative ('[' :: parsed) [']'] remainder in
    ParseOk (JsonArray [v]) remainder (RArray (ARValue repr))
  parseStep ('['::(parsed ++ (',' :: remainder))) rec | ParseOk v (',' :: remainder) repr with (parseArrayMore remainder)
    parseStep ('['::(parsed ++ (',' :: remainder))) rec | ParseOk v (',' :: remainder) repr | ParseFail = ParseFail
    parseStep ('['::(parsed ++ ((',' :: more) ++ (']'::remainder2)))) rec | ParseOk v (',' :: (more ++ (']'::remainder2))) repr | ParseOk {parsed = more} vs (']'::remainder2) arepr =
      rewrite appendAssociative parsed [','] more in
      ParseOk (JsonArray (v :: vs)) remainder2 (RArray (ARComma repr arepr))
    parseStep _ rec | ParseOk v _ repr | ParseOk _ _ _ = ParseFail
  parseStep ('['::(parsed ++ remainder))          rec | ParseOk _ _ _ = ParseFail

parseStep _                              rec = ParseFail

parse : (s : List Char) -> ParseResult Repr s
parse = wfInd parseStep
