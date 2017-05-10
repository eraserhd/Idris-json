module Data.JSON

%default total

export
data JsonValue : Type where
  JsonNull : JsonValue
  JsonBool : Bool -> JsonValue

parseValue' : List Char -> Either String (JsonValue, List Char)
parseValue' ('n' :: 'u' :: 'l' :: 'l' :: cs)        = Right (JsonNull, cs)
parseValue' ('t' :: 'r' :: 'u' :: 'e' :: cs)        = Right (JsonBool True, cs)
parseValue' ('f' :: 'a' :: 'l' :: 's' :: 'e' :: cs) = Right (JsonBool False, cs)
parseValue' _ = ?parseValue_rhs

showValue' : (v : JsonValue) -> Subset (List Char) (\s => parseValue' s = Right (v, []))
showValue' (JsonNull)       = Element ['n', 'u', 'l', 'l'] Refl
showValue' (JsonBool True)  = Element ['t', 'r', 'u', 'e'] Refl
showValue' (JsonBool False) = Element ['f', 'a', 'l', 's', 'e'] Refl

Show JsonValue where
  show v = pack (getWitness (showValue' v))

export
parse : String -> Either String JsonValue
parse s = case parseValue' (unpack s) of
            Left err      => Left err
            Right (v, []) => Right v
            _             => Left "extra data at end of input"
