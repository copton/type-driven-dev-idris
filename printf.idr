module Main

data Format
  = End
  | FVerbatim String Format -- Todo: use `List Char`
  | FInt Format
  | FStr Format
  | FChar Char Format

fromList : List Char -> Format
fromList fmt = case span (/= '%') fmt of
  (text, '%' :: 'd' :: rest) => FVerbatim (pack text) $ FInt (fromList rest)
  (text, '%' :: 's' :: rest) => FVerbatim (pack text) $ FStr (fromList rest)
  (text, '%' :: '%' :: rest) => FVerbatim (pack (text ++ ['%'])) (fromList rest)
  (text, [])                 => FVerbatim (pack text) End
  (text, _ )                 => End -- how to signal a compile time error?

PrintfType : Format -> Type
PrintfType End                = String
PrintfType (FInt rest)        = Int -> PrintfType rest
PrintfType (FVerbatim _ rest) = PrintfType rest
PrintfType (FStr rest)        = String -> PrintfType rest
PrintfType (FChar c rest)     = PrintfType rest

rec : (f: Format) -> String -> PrintfType f
rec End acc                   = acc
rec (FInt rest) acc           = \i: Int => rec rest (acc ++ (show i))
rec (FVerbatim text rest) acc = rec rest (acc ++ text)
rec (FStr rest) acc           = \s: String => rec rest (acc ++ s)
rec (FChar c rest) acc        = rec rest (acc ++ (strCons c ""))

printf : (fmt: String) -> PrintfType (fromList $ unpack fmt)
printf fmt = rec (fromList $ unpack fmt) ""

test : String
test =
  let f = the (String -> Int -> String) (printf "the %s is %d")
  in f "answer" 42
--
-- main : IO ()
-- main = putStrLn test
