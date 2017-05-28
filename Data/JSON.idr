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

partial --FIXME
parse' : (s : List Char) -> ParseResult Repr s
parse' ('n'::'u'::'l'::'l'::rem)      = ParseOk JsonNull rem RNull
parse' ('f'::'a'::'l'::'s'::'e'::rem) = ParseOk (JsonBool False) rem RFalse
parse' ('t'::'r'::'u'::'e'::rem)      = ParseOk (JsonBool True) rem RTrue
parse' ('['::arrayInsides)            =
  case parseInsides arrayInsides of
    ParseFail => ParseFail
    ParseOk {parsed} values (']'::remainder) repr =>
      rewrite (appendAssociative parsed [']'] remainder) in
      ParseOk (JsonArray values) remainder (RArray repr)
    _ => ParseFail
  where
    partial --FIXME
    parseInsides : (s : List Char) -> ParseResult ArrayRepr s
    parseInsides s with (parse' s)
      parseInsides s | ParseFail = ParseOk [] s AREmpty
      parseInsides (parsed ++ ',' :: remainder) | (ParseOk value (',' :: remainder) repr) =
        case parseInsides remainder of
          ParseFail => ParseFail
          ParseOk [] _ _ => ParseFail
          ParseOk {parsed = parsed2} (v :: vs) remainder2 repr2 =>
            rewrite (appendAssociative parsed (',' :: parsed2) remainder2) in
            ParseOk {parsed = parsed ++ ',' :: parsed2} (value :: v :: vs) remainder2 (ARComma repr repr2)
      parseInsides (parsed ++ remainder) | (ParseOk value remainder repr) = ParseOk [value] remainder (ARValue repr)

parse' _                              = ParseFail
