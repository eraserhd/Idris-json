module Data.JSON.Token

import Data.So
import Data.Bits

%default total

public export
data JsonValue : Type where
  JsonNull   : JsonValue
  JsonBool   : Bool -> JsonValue
  JsonString : String -> JsonValue
  JsonArray  : List JsonValue -> JsonValue
  JsonObject : List (String, JsonValue) -> JsonValue
  JsonNumber : Double -> JsonValue


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

data CharS : Char -> Char -> List Char -> Type where
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

allowedUnescaped : Char -> Bool
allowedUnescaped c = let cv = ord c in
                     (cv >= 0x20 && cv <= 0x21) ||
                     (cv >= 0x23 && cv <= 0x5B) ||
                     (cv >= 0x5D && cv <= 0x10FFFF)

hexValue : Char -> Int
hexValue c = if isDigit c
             then ord c - ord '0'
             else ord (toUpper c) - ord 'A' + 10

data S_DIGIT : Int -> List Char -> Type where
  Digit : (c : Char) -> {auto ok : So (isDigit c)} -> S_DIGIT (hexValue c) [c]
data S_HEXDIG : Int -> List Char -> Type where
  HexDigit : (c : Char) -> {auto ok : So (isHexDigit c)} -> S_HEXDIG (hexValue c) [c]
data S_digit1_9 : Int -> List Char -> Type where
  Digit1_9 : (c : Char) -> {auto ok : So (isDigit c && c /= '0')} -> S_digit1_9 (hexValue c) [c]

data S_int : Integer -> List Char -> Type where
  S_zero  : S_int 0 ['0']
  NonZero : (S_digit1_9 .. ListS S_DIGIT) (x, xs) text -> S_int (cast $ pack text) text

HexQuad : Int -> List Char -> Type
HexQuad = Map (\(a,b,c,d) => a*0x1000 + b*0x100 + c*0x10 +d*0x1) (S_HEXDIG .. S_HEXDIG .. S_HEXDIG .. S_HEXDIG)

unicodeSurrogatePair : (c : Char) -> So (ord c > 0xFFFF) -> (Int, Int)
unicodeSurrogatePair c prf = case (highSurrogate, lowSurrogate) of
                               (MkBits l, MkBits h) => (prim__sextB32_Int l, prim__sextB32_Int h)
                             where
                               cv : Bits 20
                               cv = cast (the Integer (cast $ ord c - 0x010000))

                               highSurrogate : Bits 20
                               highSurrogate = (shiftRightLogical cv (cast 10)) `Data.Bits.or` (cast 0xD800)

                               lowSurrogate : Bits 20
                               lowSurrogate = (cv `and` (cast 0x3FF)) `Data.Bits.or` (cast 0xDC00)

data S_char : Char -> List Char -> Type where
  S_unescaped               : (c : Char) -> So (allowedUnescaped c) -> S_char c [c]

  S_unicode_escape          : (c : Char) ->
                              So (ord c <= 0xFFFF) ->
                              HexQuad (ord c) text ->
                              S_char c ('\\' :: 'u' :: text)
  S_unicode_surrogate_pair  : (c : Char) ->
                              (rangeProof : So (ord c > 0xFFFF)) ->
                              HexQuad (fst $ unicodeSurrogatePair c rangeProof) text1 ->
                              HexQuad (snd $ unicodeSurrogatePair c rangeProof) text2 ->
                              S_char c ('\\' :: 'u' :: text1 ++ ('\\' :: 'u' :: text2))


  S_escape_quotation_mark   : S_char '"'  ['\\','"']
  S_escape_reverse_solidus  : S_char '\\' ['\\','\\']
  S_escape_solidus          : S_char '/'  ['\\','/']
  S_escape_backspace        : S_char '\b' ['\\','b']
  S_escape_form_feed        : S_char '\f' ['\\','f']
  S_escape_line_feed        : S_char '\n' ['\\','n']
  S_escape_carriage_return  : S_char '\r' ['\\','r']
  S_escape_tab              : S_char '\t' ['\\','t']


S_string' : String -> List Char -> Type
S_string' = Map (\(_, cs, _) => pack cs) $ CharS '"' .. ListS S_char .. CharS '"'


toJsonList : ((), Maybe (JsonValue, List ((), JsonValue)), ()) -> List JsonValue
toJsonList (_, (Just (v, vs)), _) = v :: map snd vs
toJsonList (_, Nothing, _) = []

toJsonPropList : ((), Maybe ((String, JsonValue), List ((), String, JsonValue)), ()) -> List (String, JsonValue)
toJsonPropList (_, Just (kv, kvs), _) = kv :: map snd kvs
toJsonPropList (_, Nothing, _) = []

mutual
  data S_member : (String, JsonValue) -> List Char -> Type where
    MkMember : (S_string' .. S_name_separator .. S_value) (k, _, v) text -> S_member (k, v) text

  data S_value : JsonValue -> List Char -> Type where
    S_null   : S_value JsonNull ['n','u','l','l']
    S_true   : S_value (JsonBool True) ['t','r','u','e']
    S_false  : S_value (JsonBool False) ['f','a','l','s','e']
    S_string : S_string' s text -> S_value (JsonString s) text
    S_array  : (S_begin_array .. (MaybeS (S_value .. ListS (S_value_separator .. S_value))) .. S_end_array) value text ->
               S_value (JsonArray $ toJsonList value) text
    S_object : (S_begin_object .. (MaybeS (S_member .. ListS (S_value_separator .. S_member))) .. S_end_object) value text ->
               S_value (JsonObject $ toJsonPropList value) text
