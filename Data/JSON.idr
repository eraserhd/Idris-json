module Data.JSON

%default total

export
data JsonValue : Type where
  JsonNull : JsonValue
  JsonBool : Bool -> JsonValue

data Tail : List a -> List a -> Type where
  TailHere  : Tail xs xs
  TailThere : Tail xs ys -> Tail (x :: xs) ys

drops : (n : Nat) -> (cs : List a) -> Tail cs (drop n cs)
drops Z cs = TailHere
drops (S k) [] = TailHere
drops (S k) (x :: xs) = TailThere $ drops k xs

tailComp : Tail a b -> Tail b c -> Tail a c
tailComp TailHere y      = y
tailComp (TailThere z) y = TailThere (tailComp z y)

data ParseResult : Type -> Type where
  ParseFail : String -> ParseResult a
  ParseOk   : {a : Type} ->
              (value : a) ->
              (inp  : List Char) ->
              (outp : List Char) ->
              Tail inp outp ->
              ParseResult a

Parser : Type -> Type
Parser a = (inp : List Char) -> ParseResult a

parseValue : Parser JsonValue
parseValue []                                          = ParseFail "unexpected end of input"
parseValue inp@('n' :: 'u' :: 'l' :: 'l' :: cs)        = ParseOk JsonNull inp cs (drops 4 inp)
parseValue inp@('t' :: 'r' :: 'u' :: 'e' :: cs)        = ParseOk (JsonBool True) inp cs (drops 4 inp)
parseValue inp@('f' :: 'a' :: 'l' :: 's' :: 'e' :: cs) = ParseOk (JsonBool False) inp cs (drops 5 inp)
parseValue (c :: _)                                    = ParseFail $ "unexpected " ++ show c

data ParsesAs : JsonValue -> List Char -> Type where
  MkParsesAs : (v : JsonValue) ->
               (cs : List Char) ->
               parseValue cs = ParseOk v cs [] _ ->
               ParsesAs v cs

showValue : (v : JsonValue) -> Subset (List Char) (ParsesAs v)
showValue (JsonNull)       = Element ['n','u','l','l'] (MkParsesAs JsonNull ['n','u','l','l'] Refl)
showValue (JsonBool True)  = Element ['t','r','u','e'] (MkParsesAs (JsonBool True) ['t', 'r', 'u', 'e'] Refl)
showValue (JsonBool False) = Element ['f','a','l','s','e'] (MkParsesAs (JsonBool False) ['f','a','l','s','e'] Refl)

Show JsonValue where
  show v = pack (getWitness (showValue v))

export
parse : String -> Either String JsonValue
parse s = let cs = unpack s in
          case parseValue cs of
            ParseFail err     => Left err
            ParseOk v cs [] _ => Right v
            _                 => Left "extra data at end of input"
