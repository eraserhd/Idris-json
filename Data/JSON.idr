module Data.JSON

import public Data.JSON.Type
import Data.JSON.Semantics

%default total

------------------------------------------------------------------------------
-- show
------------------------------------------------------------------------------

showBeginArray : S_begin_array () ['[']
showBeginArray = MkMap $ MkConsecutive Nil (MkConsecutive MkCharS Nil)

showEndArray : S_end_array () [']']
showEndArray = MkMap $ MkConsecutive Nil (MkConsecutive MkCharS Nil)

showValue : (v : JsonValue) -> (text : List Char ** S_value v text)
showValue JsonNull         = (['n','u','l','l']     ** S_null)
showValue (JsonBool False) = (['f','a','l','s','e'] ** S_false)
showValue (JsonBool True)  = (['t','r','u','e']     ** S_true)
showValue (JsonArray [])   = (['[',']']             ** array)
                             where
                               array : S_value (JsonArray []) ['[',']']
                               array = S_array (MkConsecutive showBeginArray (MkConsecutive NothingS showEndArray))
showValue (JsonArray (x :: xs)) = ?show'_rhs_4
showValue (JsonString x)        = ?showValue_rhs_3
showValue (JsonObject xs)       = ?showValue_rhs_5
showValue (JsonNumber x)        = ?showValue_rhs_6

showJSONText : (v : JsonValue) -> (text : List Char ** S_JSON_text v text)
showJSONText v = let (text ** s_value) = showValue v in
                 (text ** replace (appendNilRightNeutral text) $
                          MkS_JSON_text (MkConsecutive Nil (MkConsecutive s_value Nil)))

implementation Show JsonValue where
  show v = pack $ fst $ showJSONText v
