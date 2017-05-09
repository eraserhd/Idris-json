module Data.JSON

%default total

export
data JsonValue : Type where
  JsonNull : JsonValue

mutual
  parseValue' : List Char -> Either String (JsonValue, List Char)
  parseValue' ('n' :: 'u' :: 'l' :: 'l' :: cs)  = Right (JsonNull, cs)
  parseValue' _ = ?parseValue_rhs

  showValue' : (v : JsonValue) -> Subset (List Char) (\s => parseValue' s = Right (v, []))
  showValue' JsonNull = Element ['n', 'u', 'l', 'l'] Refl


Show JsonValue where
  show v = pack (getWitness (showValue' v))


export
parse : String -> Either String JsonValue
parse s = case parseValue' (unpack s) of
            Left err      => Left err
            Right (v, []) => Right v
            _             => Left "extra data at end of input"
