module Data.JSON.Token

public export
data JsonValue : Type where
  JsonNull   : JsonValue
  JsonBool   : Bool -> JsonValue
  JsonString : String -> JsonValue
  JsonArray  : List JsonValue -> JsonValue
  JsonObject : List (String, JsonValue) -> JsonValue

mutual
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

  data Value : JsonValue -> List Char -> Type where
    NullValue  : Value JsonNull ['n','u','l','l']
    TrueValue  : Value (JsonBool True) ['t','r','u','e']
    FalseValue : Value (JsonBool False) ['f','a','l','s','e']
