module Data.JSON.Token

import Data.So

public export
data JsonValue : Type where
  JsonNull   : JsonValue
  JsonBool   : Bool -> JsonValue
  JsonString : String -> JsonValue
  JsonArray  : List JsonValue -> JsonValue
  JsonObject : List (String, JsonValue) -> JsonValue


infixr 7 ..

data (..) : (fstValueType -> List Char -> Type) ->
            (sndValueType -> List Char -> Type) ->
            (fstValueType, sndValueType) ->
            List Char ->
            Type where
  Consecutive : sem1 v1 text1 -> sem2 v2 text2 -> (..) sem1 sem2 (v1, v2) (text1 ++ text2)

data MaybeS : (valueType -> List Char -> Type) ->
              Maybe valueType ->
              List Char ->
              Type where
  JustS    : sem v text -> MaybeS sem (Just v) text
  NothingS : MaybeS sem Nothing []

data ListS : (valueType -> List Char -> Type) ->
             List valueType ->
             List Char ->
             Type where
  Nil  : ListS sem [] []
  (::) : sem v r -> ListS sem vs rs -> ListS sem (v :: vs) (r ++ rs)

data CharS : Char ->
             Char ->
             List Char ->
             Type where
  Found : CharS c c [c]

data Map : (func : a -> b) ->
           (a -> List Char -> Type) ->
           b -> List Char -> Type where
  MakeMap : sem v text -> Map func sem (func v) text

data S_whitespace' : Char -> List Char -> Type where
  Space          : S_whitespace' ' '  [' ']
  HorizontalTab  : S_whitespace' '\t' ['\t']
  VerticalTab    : S_whitespace' '\v' ['\v']
  LineFeed       : S_whitespace' '\n' ['\n']
  CarriageReturn : S_whitespace' '\r' ['\r']

S_whitespace : List Char -> List Char -> Type
S_whitespace = ListS S_whitespace'

S_structural_char : Char -> () -> List Char -> Type
S_structural_char c = Map (const ()) (S_whitespace .. CharS c .. S_whitespace)

S_begin_array : () -> List Char -> Type
S_begin_array = S_structural_char '['

S_begin_object : () -> List Char -> Type
S_begin_object = S_structural_char '{'

S_end_array : () -> List Char -> Type
S_end_array = S_structural_char ']'

S_end_object : () -> List Char -> Type
S_end_object = S_structural_char '}'

S_name_separator : () -> List Char -> Type
S_name_separator = S_structural_char ':'

S_value_separator : () -> List Char -> Type
S_value_separator = S_structural_char ','

total
allowedUnescaped : Char -> Bool
allowedUnescaped c = let cv = ord c in
                     (cv >= 0x20 && cv <= 0x21) ||
                     (cv >= 0x23 && cv <= 0x5B) ||
                     (cv >= 0x5D && cv <= 0x10FFFF)

data S_char : Char -> List Char -> Type where
  S_unescaped               : (c : Char) -> So (allowedUnescaped c) -> S_char c [c]

  S_escape_quotation_mark   : S_char '"'  ['\\','"']
  S_escape_reverse_solidus  : S_char '\\' ['\\','\\']
  S_escape_solidus          : S_char '/'  ['\\','/']
  S_escape_backspace        : S_char '\b' ['\\','b']
  S_escape_form_feed        : S_char '\f' ['\\','f']
  S_escape_line_feed        : S_char '\n' ['\\','n']
  S_escape_carriage_return  : S_char '\r' ['\\','r']
  S_escape_tab              : S_char '\t' ['\\','t']



total
toJsonList : ((), Maybe (JsonValue, List ((), JsonValue)), ()) -> List JsonValue
toJsonList (_, (Just (v, vs)), _) = v :: map snd vs
toJsonList (_, Nothing, _) = []

data S_value : JsonValue -> List Char -> Type where
  S_null   : S_value JsonNull ['n','u','l','l']
  S_true   : S_value (JsonBool True) ['t','r','u','e']
  S_false  : S_value (JsonBool False) ['f','a','l','s','e']
  S_string : (CharS '"' .. ListS S_char .. CharS '"') (_, cs,_) text ->
             S_value (JsonString $ pack cs) text
  S_array  : (S_begin_array .. (MaybeS (S_value .. ListS (S_value_separator .. S_value))) .. S_end_array) value text ->
             S_value (JsonArray $ toJsonList value) text
