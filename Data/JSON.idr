module Data.JSON

%default total

export
data JsonValue : Type where
  JsonNull : JsonValue
  JsonBool : Bool -> JsonValue

Parser : Type -> Type
Parser a = List Char -> Either String (a, List Char)

parseValue : Parser JsonValue
parseValue []                                      = Left "unexpected end of input"
parseValue ('n' :: 'u' :: 'l' :: 'l' :: cs)        = Right (JsonNull, cs)
parseValue ('t' :: 'r' :: 'u' :: 'e' :: cs)        = Right (JsonBool True, cs)
parseValue ('f' :: 'a' :: 'l' :: 's' :: 'e' :: cs) = Right (JsonBool False, cs)
parseValue (c :: _)                                = Left $ "unexpected " ++ show c

showValue : (v : JsonValue) -> Subset (List Char) (\s => parseValue s = Right (v, []))
showValue (JsonNull)       = Element ['n', 'u', 'l', 'l'] Refl
showValue (JsonBool True)  = Element ['t', 'r', 'u', 'e'] Refl
showValue (JsonBool False) = Element ['f', 'a', 'l', 's', 'e'] Refl

Show JsonValue where
  show v = pack (getWitness (showValue v))

export
parse : String -> Either String JsonValue
parse s = case parseValue (unpack s) of
            Left err      => Left err
            Right (v, []) => Right v
            _             => Left "extra data at end of input"
