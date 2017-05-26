module Data.JSON

%access public export
%default total

public export
data JsonValue : Type where
  JsonNull  : JsonValue
  JsonBool  : Bool -> JsonValue
  JsonArray : (List JsonValue) -> JsonValue

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

data ParseResult : List Char -> Type where
  ParseFail : ParseResult s
  ParseOk : (value : JsonValue) ->
            (remainder : List Char) ->
            (repr : Repr parsed value) ->
            (prefixProof : parsed ++ remainder = s) ->
            ParseResult s

parse' : (s : List Char) -> ParseResult s
parse' ('n'::'u'::'l'::'l'::rem)      = ParseOk JsonNull rem RNull Refl
parse' ('f'::'a'::'l'::'s'::'e'::rem) = ParseOk (JsonBool False) rem RFalse Refl
parse' ('t'::'r'::'u'::'e'::rem)      = ParseOk (JsonBool True) rem RTrue Refl
parse' _                              = ParseFail
