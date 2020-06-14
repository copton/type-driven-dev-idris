module Main

data Format
  = End
  | FInt Format
  | FStr Format
  | FTxt (List Char) Format

fromList : List Char -> Format
fromList fmt = case span (/= '%') fmt of
  (text, ('%' :: 'd' :: rest)) => FTxt text (FInt (fromList rest))
  (text, ('%' :: 's' :: rest)) => FTxt text (FStr (fromList rest))
  (text, ('%' :: '%' :: rest)) => FTxt text (FTxt ['%'] (fromList rest))
  (text, rest)                 => FTxt text (FTxt rest End)
  (text, [])                   => FTxt text End

PrintfType : Format -> Type
PrintfType End           = String
PrintfType (FInt rest)   = Int -> PrintfType rest
PrintfType (FStr rest)   = String -> PrintfType rest
PrintfType (FTxt _ rest) = PrintfType rest

printf : (fmt: String) -> PrintfType (fromList $ unpack fmt)
printf fmt = printFormat (fromList $ unpack fmt)
  where
    rec : (f: Format) -> String -> PrintfType f
    rec End acc           = acc
    rec (FInt rest) acc   = \i: Int => rec rest (acc ++ (show i))
    rec (FStr rest) acc   = \s: String => rec rest (acc ++ s)
    rec (FTxt t rest) acc = rec rest (acc ++ pack t)

    printFormat : (fmt: Format) -> PrintfType fmt
    printFormat fmt = rec fmt ""

test : String
test = printf "The %s is %d" "answer" 42

-- main : IO ()
-- main = putStrLn test
