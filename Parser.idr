module Main

data Parser : Type -> Type where
  MkParser : (List Char -> Either String (a, List Char)) -> Parser a

implementation Functor Parser where
  map f (MkParser g) = MkParser $ \s =>
    case g s of
      Left e => Left e
      Right (a, s') => Right (f a, s')

implementation Applicative Parser where
  pure a = MkParser $ \s => Right (a, s)
  (MkParser f) <*> (MkParser g) = MkParser $
    \s => case g s of
      Left e => Left e
      Right (a, s') => case f s' of
        Left e => Left e
        Right (h, s'') => Right (h a, s'')

implementation Monad Parser where
  (MkParser f) >>= g = MkParser $
    \s => case f s of
      Left e => Left e
      Right (a, s') => case g a of
        MkParser h => h s'

get : Parser (List Char)
get = MkParser $ \s => Right (s, s)

put : List Char -> Parser ()
put s = MkParser $ \_ => Right ((), s)

err : String -> Parser a
err e = MkParser $ \s => Left e

runParser : Parser a -> String -> Either String (a, String)
runParser (MkParser f) s = map pack' $ f (unpack s)
  where
    pack' (a, s) = (a, pack s)

parseChar : Char -> Parser Char
parseChar c = do
  chars <- get
  case chars of
    [] => err "parseChar"
    (h :: t) =>
      if c == h
        then do
          put t
          pure c
        else err "parseChar"

parseInt : Parser Int
parseInt = do
  chars <- get
  let (digits, rest) = span isDigit chars
  put rest
  pure $ cast $ pack digits

parseQuoted : Parser a -> Parser a
parseQuoted p = do
  _ <- parseChar '"'
  a <- p
  _ <- parseChar '"'
  pure a
