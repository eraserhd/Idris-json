module Data.JSON.Token

public export
data JsonValue : Type where
  JsonNull   : JsonValue
  JsonBool   : Bool -> JsonValue
  JsonString : String -> JsonValue
  JsonArray  : List JsonValue -> JsonValue
  JsonObject : List (String, JsonValue) -> JsonValue

data WhitespaceChar : Char -> Type where
  Space          : WhitespaceChar ' '
  HorizontalTab  : WhitespaceChar '\t'
  VerticalTab    : WhitespaceChar '\v'
  LineFeed       : WhitespaceChar '\n'
  CarriageReturn : WhitespaceChar '\r'

data Whitespace : List Char -> Type where
  Nil  : Whitespace []
  (::) : WhitespaceChar x -> Whitespace xs -> Whitespace (x :: xs)

data StructuralCharChar : Char -> Type where
  BeginArray     : StructuralCharChar '['
  BeginObject    : StructuralCharChar '{'
  EndArray       : StructuralCharChar ']'
  EndObject      : StructuralCharChar '}'
  NameSeparator  : StructuralCharChar ':'
  ValueSeparator : StructuralCharChar ','

data StructuralChar : StructuralCharChar ch -> List Char -> Type where
  MakeStructuralChar : Whitespace ws1 ->
                       (scc : StructuralCharChar ch) ->
                       Whitespace ws2 ->
                       StructuralChar scc (ws1 ++ ch :: ws2)

mutual
  data ArrayInsides : List JsonValue -> List Char -> Type where
    EmptyArrayInsides  : ArrayInsides [] []
    SingleArrayInsides : Value v insides -> ArrayInsides [v] insides
    CommaArrayInsides  : Value v1 firstText ->
                         StructuralChar ValueSeparator sepText ->
                         ArrayInsides (v2 :: vs) restInsides ->
                         ArrayInsides (v1 :: v2 :: vs) (firstText ++ sepText ++ restInsides)

  data Value : JsonValue -> List Char -> Type where
    NullValue  : Value JsonNull ['n','u','l','l']
    TrueValue  : Value (JsonBool True) ['t','r','u','e']
    FalseValue : Value (JsonBool False) ['f','a','l','s','e']
    ArrayValue : StructuralChar BeginArray begin ->
                 ArrayInsides vs insides ->
                 StructuralChar EndArray end ->
                 Value (JsonArray vs) (begin ++ insides ++ end)
