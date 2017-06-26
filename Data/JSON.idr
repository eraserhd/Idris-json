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

data WhitespaceChar : Char -> List Char -> Type where
  Space          : WhitespaceChar ' '  [' ']
  HorizontalTab  : WhitespaceChar '\t' ['\t']
  VerticalTab    : WhitespaceChar '\v' ['\v']
  LineFeed       : WhitespaceChar '\n' ['\n']
  CarriageReturn : WhitespaceChar '\r' ['\r']

Whitespace : List Char -> List Char -> Type
Whitespace = ListS WhitespaceChar

StructuralChar : Char -> () -> List Char -> Type
StructuralChar c = Map (const ()) (Whitespace .. CharS c .. Whitespace)

BeginArray : () -> List Char -> Type
BeginArray = StructuralChar '['

BeginObject : () -> List Char -> Type
BeginObject = StructuralChar '{'

EndArray : () -> List Char -> Type
EndArray = StructuralChar ']'

EndObject : () -> List Char -> Type
EndObject = StructuralChar '}'

NameSeparator : () -> List Char -> Type
NameSeparator = StructuralChar ':'

ValueSeparator : () -> List Char -> Type
ValueSeparator = StructuralChar ','

total
toJsonArray : ((), Maybe (JsonValue, List ((), JsonValue)), ()) -> List JsonValue
toJsonArray (_, (Just (v, vs)), _) = v :: map snd vs
toJsonArray (_, Nothing, _) = []

data Value : JsonValue -> List Char -> Type where
  NullValue  : Value JsonNull ['n','u','l','l']
  TrueValue  : Value (JsonBool True) ['t','r','u','e']
  FalseValue : Value (JsonBool False) ['f','a','l','s','e']
  ArrayValue : (BeginArray .. (MaybeS (Value .. ListS (ValueSeparator .. Value))) .. EndArray) value text ->
               Value (JsonArray $ toJsonArray value) text
