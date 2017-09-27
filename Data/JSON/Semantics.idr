module Data.JSON.Semantics

import Data.So
import Data.Bits
import Data.JSON.Type

%default total
%access public export

------------------------------------------------------------------------------
-- Combinators
------------------------------------------------------------------------------

infixr 7 ..

||| (..) combines two sems to relate the pair of their results to the concatenation of
||| their representations.
data (..) : (fstValueType -> List Char -> Type) ->
            (sndValueType -> List Char -> Type) ->
            (fstValueType, sndValueType) ->
            List Char ->
            Type where
  MkConsecutive : sem1 v1 text1 -> sem2 v2 text2 -> (..) sem1 sem2 (v1, v2) (text1 ++ text2)

||| (MaybeS sem) is semantics for an optional sem.
data MaybeS : (valueType -> List Char -> Type) ->
              Maybe valueType ->
              List Char ->
              Type where
  JustS    : sem v text -> MaybeS sem (Just v) text
  NothingS : MaybeS sem Nothing []

||| (ListS sem) is semantics for zero or more sems (the Kleene operator).
data ListS : (valueType -> List Char -> Type) ->
             List valueType ->
             List Char ->
             Type where
  Nil  : ListS sem [] []
  (::) : sem v r -> ListS sem vs rs -> ListS sem (v :: vs) (r ++ rs)

||| (CharS c) is semantics for a literal character.  Its value is the Char itself.
data CharS : Char -> Char -> List Char -> Type where
  MkCharS : CharS c c [c]

||| Change the type of a sem with a mapping function.
data Map : (func : a -> b) ->
           (a -> List Char -> Type) ->
           b -> List Char -> Type where
  MkMap : sem v text -> Map func sem (func v) text

------------------------------------------------------------------------------
-- Whitespace
------------------------------------------------------------------------------

||| A whitespace character.
data S_ws' : Char -> List Char -> Type where
  Space          : S_ws' ' '  [' ']
  HorizontalTab  : S_ws' '\t' ['\t']
  VerticalTab    : S_ws' '\v' ['\v']
  LineFeed       : S_ws' '\n' ['\n']
  CarriageReturn : S_ws' '\r' ['\r']

||| Insignificant whitespace, §2
S_ws : List Char -> List Char -> Type
S_ws = ListS S_ws'

------------------------------------------------------------------------------
-- Structural Characters
------------------------------------------------------------------------------

||| Structural characters, §2
StructuralChar : Char -> () -> List Char -> Type
StructuralChar c = Map (const ()) (S_ws .. CharS c .. S_ws)

S_begin_array : () -> List Char -> Type
S_begin_array = StructuralChar '['

S_begin_object : () -> List Char -> Type
S_begin_object = StructuralChar '{'

S_end_array : () -> List Char -> Type
S_end_array = StructuralChar ']'

S_end_object : () -> List Char -> Type
S_end_object = StructuralChar '}'

S_name_separator : () -> List Char -> Type
S_name_separator = StructuralChar ':'

S_value_separator : () -> List Char -> Type
S_value_separator = StructuralChar ','

------------------------------------------------------------------------------
-- Numbers
------------------------------------------------------------------------------

hexValue : Char -> Int
hexValue c = if isDigit c
             then ord c - ord '0'
             else ord (toUpper c) - ord 'A' + 10

data S_DIGIT : Int -> List Char -> Type where
  MkS_DIGIT : (c : Char) -> {auto ok : So (isDigit c)} -> S_DIGIT (hexValue c) [c]
data S_digit1_9 : Int -> List Char -> Type where
  MkS_digit1_9 : (c : Char) -> {auto ok : So (isDigit c && c /= '0')} -> S_digit1_9 (hexValue c) [c]

data S_int : Integer -> List Char -> Type where
  S_zero  : S_int 0 ['0']
  NonZero : (S_digit1_9 .. ListS S_DIGIT) (x, xs) text -> S_int (cast $ pack text) text

data S_e : () -> List Char -> Type where
  UpperCaseE : S_e () ['E']
  LowerCaseE : S_e () ['e']

data Sign = Plus | Minus
data S_sign : Bool -> Sign -> List Char -> Type where
  S_plus : S_sign True Plus ['+']
  S_minus : S_sign plusAllowed Minus ['-']

signed : Maybe Sign -> Integer -> Integer
signed (Just Minus) x = -x
signed _ x = x

fromDigits : Int -> List Int -> Integer
fromDigits x [] = cast x
fromDigits x (y :: ys) = 10 * (cast x) + fromDigits y ys

data S_decimal_point : () -> List Char -> Type where
  MkS_decimal_point : S_decimal_point () ['.']

data S_frac : Integer -> List Char -> Type where
  MkS_frac : (S_decimal_point .. S_DIGIT .. ListS S_DIGIT) (_, d, ds) text ->
             S_frac (fromDigits d ds) text

data S_exp : Integer -> List Char -> Type where
  MkS_exp : (S_e .. MaybeS (S_sign True) .. S_DIGIT .. ListS S_DIGIT) (e, s, d, ds) text ->
            S_exp (signed s $ fromDigits d ds) text

------------------------------------------------------------------------------
-- Strings
------------------------------------------------------------------------------

data S_HEXDIG : Nat -> List Char -> Type where
  MkS_HEXDIG_0 : (x : Nat) -> x `LTE` 9 -> S_HEXDIG x [chr (ord '0' + (toIntNat x))]
  MkS_HEXDIG_A : (x : Nat) -> x `LTE` 15 -> (x `LTE` 9 -> Void) -> S_HEXDIG x [chr (ord 'A' - 10 + (toIntNat x))]
  MkS_HEXDIG_a : (x : Nat) -> x `LTE` 15 -> (x `LTE` 9 -> Void) -> S_HEXDIG x [chr (ord 'a' - 10 + (toIntNat x))]

HexQuad : Int -> List Char -> Type
HexQuad = Map (\(a,b,c,d) => (toIntNat a)*0x1000 + (toIntNat b)*0x100 + (toIntNat c)*0x10 +(toIntNat d)*0x1) (S_HEXDIG .. S_HEXDIG .. S_HEXDIG .. S_HEXDIG)

unicodeSurrogatePair : (c : Char) -> (Int, Int)
unicodeSurrogatePair c = case (highSurrogate, lowSurrogate) of
                           (MkBits l, MkBits h) => (prim__sextB32_Int l, prim__sextB32_Int h)
                         where
                           cv : Bits 20
                           cv = cast (the Integer (cast $ ord c - 0x010000))

                           highSurrogate : Bits 20
                           highSurrogate = (shiftRightLogical cv (cast 10)) `Data.Bits.or` (cast 0xD800)

                           lowSurrogate : Bits 20
                           lowSurrogate = (cv `and` (cast 0x3FF)) `Data.Bits.or` (cast 0xDC00)

allowedUnescaped : Char -> Bool
allowedUnescaped c = let cv = ord c in
                     (cv >= 0x20 && cv <= 0x21) ||
                     (cv >= 0x23 && cv <= 0x5B) ||
                     (cv >= 0x5D && cv <= 0x10FFFF)

||| Semantics for characters in JSON strings, rfc7159 §7
data S_char : Char -> List Char -> Type where
  S_unescaped               : (c : Char) -> So (allowedUnescaped c) -> S_char c [c]

  S_unicode_escape          : (c : Char) ->
                              So (c <= chr 0xFFFF) ->
                              HexQuad (ord c) text ->
                              S_char c ('\\' :: 'u' :: text)
  S_unicode_surrogate_pair  : (c : Char) ->
                              (rangeProof : So (not (c <= chr 0xFFFF))) ->
                              HexQuad (fst $ unicodeSurrogatePair c) text1 ->
                              HexQuad (snd $ unicodeSurrogatePair c) text2 ->
                              S_char c ('\\' :: 'u' :: text1 ++ ('\\' :: 'u' :: text2))


  S_escape_quotation_mark   : S_char '"'  ['\\','"']
  S_escape_reverse_solidus  : S_char '\\' ['\\','\\']
  S_escape_solidus          : S_char '/'  ['\\','/']
  S_escape_backspace        : S_char '\b' ['\\','b']
  S_escape_form_feed        : S_char '\f' ['\\','f']
  S_escape_line_feed        : S_char '\n' ['\\','n']
  S_escape_carriage_return  : S_char '\r' ['\\','r']
  S_escape_tab              : S_char '\t' ['\\','t']


||| JSON string semantics, rfc7159 §7
S_string' : String -> List Char -> Type
S_string' = Map (\(_, cs, _) => pack cs) $ CharS '"' .. ListS S_char .. CharS '"'

------------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------------

toJsonList : ((), Maybe (JsonValue, List ((), JsonValue)), ()) -> List JsonValue
toJsonList (_, (Just (v, vs)), _) = v :: map snd vs
toJsonList (_, Nothing, _) = []

toJsonPropList : ((), Maybe ((String, JsonValue), List ((), String, JsonValue)), ()) -> List (String, JsonValue)
toJsonPropList (_, Just (kv, kvs), _) = kv :: map snd kvs
toJsonPropList (_, Nothing, _) = []

mutual
  ||| Semantics for JSON object members, rfc7159 §4
  data S_member : (String, JsonValue) -> List Char -> Type where
    MkS_member : (S_string' .. S_name_separator .. S_value) (k, _, v) text -> S_member (k, v) text

  ||| JSON value semantics, rfc7159 §3
  data S_value : JsonValue -> List Char -> Type where

    ||| JSON null semantics, rfc7159 §3
    S_null   : S_value JsonNull ['n','u','l','l']

    ||| JSON true semantics, rfc7159 §3
    S_true   : S_value (JsonBool True) ['t','r','u','e']

    ||| JSON false semantics, rfc7159 §3
    S_false  : S_value (JsonBool False) ['f','a','l','s','e']

    ||| JSON string semantics, rfc7159 §7
    S_string : S_string' s text -> S_value (JsonString s) text

    ||| JSON object semantics, rfc7159 §4
    S_object : (S_begin_object .. (MaybeS (S_member .. ListS (S_value_separator .. S_member))) .. S_end_object) value text ->
               S_value (JsonObject $ toJsonPropList value) text

    ||| JSON arrays semantics, rfc7159 §5
    S_array  : (S_begin_array .. (MaybeS (S_value .. ListS (S_value_separator .. S_value))) .. S_end_array) value text ->
               S_value (JsonArray $ toJsonList value) text

    ||| JSON number semantics, rfc7159 §6
    S_number : (MaybeS (S_sign False) .. S_int .. MaybeS S_frac .. MaybeS S_exp) value text ->
               S_value (JsonNumber $ cast $ pack text) text

------------------------------------------------------------------------------
-- Top-level
------------------------------------------------------------------------------

||| Semantics for the top-level JSON document, rfc7159 §2
data S_JSON_text : JsonValue -> List Char -> Type where
  MkS_JSON_text : (S_ws .. S_value .. S_ws) (_, v, _) text -> S_JSON_text v text
