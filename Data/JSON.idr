module Data.JSON.Token

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
toJsonArray : ((), Maybe (JsonValue, List ((), JsonValue)), ()) -> List JsonValue
toJsonArray (_, (Just (v, vs)), _) = v :: map snd vs
toJsonArray (_, Nothing, _) = []

data S_value : JsonValue -> List Char -> Type where
  S_null  : S_value JsonNull ['n','u','l','l']
  S_true  : S_value (JsonBool True) ['t','r','u','e']
  S_false : S_value (JsonBool False) ['f','a','l','s','e']
  S_array : (S_begin_array .. (MaybeS (S_value .. ListS (S_value_separator .. S_value))) .. S_end_array) value text ->
            S_value (JsonArray $ toJsonArray value) text
