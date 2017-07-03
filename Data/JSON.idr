module Data.JSON

import public Data.JSON.Type
import Data.JSON.Semantics

unpadded : S_value v text -> S_JSON_text v text
unpadded {text} value = replace (appendNilRightNeutral text) $
                        MkS_JSON_text (MkConsecutive Nil (MkConsecutive value Nil))

show' : (v : JsonValue) -> (text : List Char ** S_JSON_text v text)
show' JsonNull         = (['n','u','l','l']     ** unpadded S_null)
show' (JsonBool False) = (['f','a','l','s','e'] ** unpadded S_false)
show' (JsonBool True)  = (['t','r','u','e']     ** unpadded S_true)
show' (JsonArray xs)   = ?show'_rhs_2
show' (JsonString x)   = ?show'_rhs_3
show' (JsonObject xs)  = ?show'_rhs_5
show' (JsonNumber x)   = ?show'_rhs_6

implementation Show JsonValue where
  show v = pack $ fst $ show' v
