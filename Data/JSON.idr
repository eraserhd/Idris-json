module Data.JSON

import public Data.JSON.Type
import Data.JSON.Semantics

import Data.So

%default total

------------------------------------------------------------------------------
-- show
------------------------------------------------------------------------------

showBeginArray : S_begin_array () ['[']
showBeginArray = MkMap $ MkConsecutive Nil (MkConsecutive MkCharS Nil)

showEndArray : S_end_array () [']']
showEndArray = MkMap $ MkConsecutive Nil (MkConsecutive MkCharS Nil)

showBeginObject : S_begin_object () ['{']
showBeginObject = MkMap $ MkConsecutive Nil (MkConsecutive MkCharS Nil)

showEndObject : S_end_object () ['}']
showEndObject = MkMap $ MkConsecutive Nil (MkConsecutive MkCharS Nil)

showValueSeparator : S_value_separator () [',']
showValueSeparator = MkMap $ MkConsecutive Nil (MkConsecutive MkCharS Nil)

toSnd : a -> ((), a)
toSnd v = ((), v)

mapIdNeutral : (vs : List a) -> map (\x => x) vs = vs
mapIdNeutral [] = Refl
mapIdNeutral (x :: xs) = rewrite mapIdNeutral xs in Refl

toJsonListLemma : (v : JsonValue) ->
                  (vs : List JsonValue) ->
                  v :: vs = toJsonList ((), Just (v, map Data.JSON.toSnd vs), ())
toJsonListLemma v vs = rewrite ((map Prelude.Basics.snd (map toSnd vs)) = (map (snd . toSnd) vs)) <== mapFusion in
                       rewrite (map (\x => x) vs = vs) <== mapIdNeutral in
                       Refl

showHEXDIG : (x : Nat) -> {auto xOk : x `LTE` 15} -> (text : List Char ** S_HEXDIG x text)
showHEXDIG {xOk} x with (x `isLTE` 9)
  showHEXDIG {xOk} x | (Yes prf)   = ([chr (ord '0' + (toIntNat x))] ** MkS_HEXDIG_0 x prf)
  showHEXDIG {xOk} x | (No contra) = ([chr (ord 'A' - 10 + (toIntNat x))] ** MkS_HEXDIG_A x xOk contra)

showHexQuad : (value : Int) -> (text : List Char ** HexQuad value text)

showStringChar : (c : Char) -> (text : List Char ** S_char c text)
showStringChar c with (choose $ allowedUnescaped c)
  showStringChar c    | (Left prf) = ([c] ** S_unescaped c prf)
  showStringChar '"'  | _ = (['\\','"'] ** S_escape_quotation_mark)
  showStringChar '\\' | _ = (['\\','\\'] ** S_escape_reverse_solidus)
  showStringChar '\b' | _ = (['\\','b'] ** S_escape_backspace)
  showStringChar '\f' | _ = (['\\','f'] ** S_escape_form_feed)
  showStringChar '\n' | _ = (['\\','n'] ** S_escape_line_feed)
  showStringChar '\r' | _ = (['\\','r'] ** S_escape_carriage_return)
  showStringChar '\t' | _ = (['\\','t'] ** S_escape_tab)
  showStringChar c    | _ with (choose $ c <= chr 0xFFFF)
    showStringChar c | _ | (Left unicodeEscapableProof) =
      let (hqText ** hqProof) = showHexQuad (ord c) in
      ('\\' :: 'u' :: hqText ** S_unicode_escape c unicodeEscapableProof hqProof)
    showStringChar c | _ | (Right surrogatePairProof) =
      let (hq1Text ** hq1Proof) = showHexQuad (fst (unicodeSurrogatePair c))
          (hq2Text ** hq2Proof) = showHexQuad (snd (unicodeSurrogatePair c)) in
      ('\\' :: 'u' :: hq1Text ++ '\\' :: 'u' :: hq2Text **
       S_unicode_surrogate_pair c surrogatePairProof hq1Proof hq2Proof)

mutual
  showValueList : (vs : List JsonValue) ->
                  (text : List Char ** ListS (S_value_separator .. S_value) (map Data.JSON.toSnd vs) text)
  showValueList []        = ([] ** Nil)
  showValueList (v :: vs) = let (vText ** vValue) = showValue v
                                (vsText ** vsValues) = showValueList vs in
                            ((',' :: vText ++ vsText) ** (MkConsecutive showValueSeparator vValue) :: vsValues)

  showValue : (v : JsonValue) -> (text : List Char ** S_value v text)
  showValue JsonNull               = (['n','u','l','l']     ** S_null)
  showValue (JsonBool False)       = (['f','a','l','s','e'] ** S_false)
  showValue (JsonBool True)        = (['t','r','u','e']     ** S_true)
  showValue (JsonArray [])         = (['[',']']             ** array)
                                     where
                                       array : S_value (JsonArray []) ['[',']']
                                       array = S_array (MkConsecutive showBeginArray (MkConsecutive NothingS showEndArray))
  showValue (JsonArray (v :: vs))  = let (vText ** vValue) = showValue v
                                         (vsText ** vsValues) = showValueList vs
                                         text = '[' :: (vText ++ vsText) ++ [']'] in
                                     (text **
                                       rewrite (toJsonListLemma v vs) in
                                       S_array (MkConsecutive
                                                 showBeginArray
                                                 (MkConsecutive
                                                   (JustS (MkConsecutive vValue vsValues))
                                                   showEndArray)))
  showValue (JsonObject [])        = (['{','}'] ** object)
                                     where
                                       object : S_value (JsonObject []) ['{','}']
                                       object = S_object (MkConsecutive showBeginObject (MkConsecutive NothingS showEndObject))
  showValue (JsonObject (x :: xs)) = ?showValue_rhs_2
  showValue (JsonString x)         = ?showValue_rhs_3
  showValue (JsonNumber x)         = ?showValue_rhs_6

showJSONText : (v : JsonValue) -> (text : List Char ** S_JSON_text v text)
showJSONText v = let (text ** s_value) = showValue v in
                 (text ** replace (appendNilRightNeutral text) $
                          MkS_JSON_text (MkConsecutive Nil (MkConsecutive s_value Nil)))

implementation Show JsonValue where
  show v = pack $ fst $ showJSONText v
