module Data.JSON

import public Data.JSON.Type
import Data.JSON.Semantics

show' : (v : JsonValue) -> (text : List Char ** S_JSON_text v text)
show' JsonNull         = (['n','u','l','l'] ** (MkS_JSON_text (MkConsecutive Nil (MkConsecutive S_null Nil))))
show' (JsonBool False) = (['f','a','l','s','e'] ** (MkS_JSON_text (MkConsecutive Nil (MkConsecutive S_false Nil))))
show' (JsonBool True)  = (['t','r','u','e'] ** MkS_JSON_text (MkConsecutive Nil (MkConsecutive S_true Nil)))
show' (JsonString x)   = ?show'_rhs_3
show' (JsonArray xs)   = ?show'_rhs_4
show' (JsonObject xs)  = ?show'_rhs_5
show' (JsonNumber x)   = ?show'_rhs_6

implementation Show JsonValue where
  show v = pack $ fst $ show' v
