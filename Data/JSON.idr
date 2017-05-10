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

Parser : Type -> Type
Parser a = (inp : List Char) -> Either String (a, (outp : List Char ** Tail inp outp))

parseValue : Parser JsonValue
parseValue []                                          = Left "unexpected end of input"
parseValue inp@('n' :: 'u' :: 'l' :: 'l' :: cs)        = Right (JsonNull, (cs ** drops 4 inp))
parseValue inp@('t' :: 'r' :: 'u' :: 'e' :: cs)        = Right (JsonBool True, (cs ** drops 4 inp))
parseValue inp@('f' :: 'a' :: 'l' :: 's' :: 'e' :: cs) = Right (JsonBool False, (cs ** drops 5 inp))
parseValue (c :: _)                                    = Left $ "unexpected " ++ show c

data ParsesAs : JsonValue -> List Char -> Type where
  MkParsesAs : (v : JsonValue) ->
               (cs : List Char) ->
               (pf : Tail cs []) ->
               parseValue cs = Right (v, ([] ** pf)) ->
               ParsesAs v cs

showValue : (v : JsonValue) -> Subset (List Char) (ParsesAs v)
showValue (JsonNull)       = Element ['n','u','l','l'] (MkParsesAs JsonNull ['n','u','l','l'] (TailThere (TailThere (TailThere (TailThere TailHere)))) Refl)
showValue (JsonBool True)  = Element ['t','r','u','e'] (MkParsesAs (JsonBool True) ['t', 'r', 'u', 'e'] (TailThere (TailThere (TailThere (TailThere TailHere)))) Refl)
showValue (JsonBool False) = Element ['f','a','l','s','e'] (MkParsesAs (JsonBool False) ['f','a','l','s','e'] (TailThere (TailThere (TailThere (TailThere (TailThere TailHere))))) Refl)

Show JsonValue where
  show v = pack (getWitness (showValue v))

export
parse : String -> Either String JsonValue
parse s = case parseValue (unpack s) of
            Left err             => Left err
            Right (v, ([] ** _)) => Right v
            _                    => Left "extra data at end of input"
