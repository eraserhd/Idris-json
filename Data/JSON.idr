module Data.JSON

%default total

export
data JsonValue : Type where
  JsonNull : JsonValue
  JsonBool : Bool -> JsonValue

data Tail : List a -> List a -> Type where
  TailHere  : Tail xs xs
  TailThere : Tail xs ys -> Tail (x :: xs) ys

Parser : Type -> Type
Parser a = (inp : List Char) -> Either String (a, (outp : List Char ** Tail inp outp))

parseValue : Parser JsonValue
parseValue []                                      = Left "unexpected end of input"
parseValue ('n' :: 'u' :: 'l' :: 'l' :: cs)        = Right (JsonNull, (cs ** TailThere (TailThere (TailThere (TailThere TailHere)))))
parseValue ('t' :: 'r' :: 'u' :: 'e' :: cs)        = Right (JsonBool True, (cs ** TailThere (TailThere (TailThere (TailThere TailHere)))))
parseValue ('f' :: 'a' :: 'l' :: 's' :: 'e' :: cs) = Right (JsonBool False, (cs ** TailThere (TailThere (TailThere (TailThere (TailThere TailHere))))))
parseValue (c :: _)                                = Left $ "unexpected " ++ show c

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
