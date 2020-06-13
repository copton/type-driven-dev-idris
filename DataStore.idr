module Main

import Data.Vect

infixr 5 .+.

data Schema
  = SString
  | SInt
  | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Integer
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

display : {schema : Schema} -> SchemaType schema -> String
display {schema} item = case schema of
  SString => show item
  SInt => show item
  (x .+. y) =>
    let (l, r) = item in
    display l ++ ", " ++ display r

record DataStore where
    constructor MkData
    schema : Schema
    size : Nat
    items : Vect size (SchemaType schema)

addToStore : (store : DataStore)
           -> SchemaType (schema store)
           -> DataStore
addToStore (MkData schema size items) newItem =
  MkData schema (S size) (insertAt last newItem items)

emptyStore : Schema -> DataStore
emptyStore s = MkData s 0 []

getEntry : (store : DataStore)
        -> Integer
        -> Maybe (SchemaType (schema store))
getEntry store idx =
  case integerToFin idx (size store) of
    Nothing => Nothing
    Just idx' => Just (index idx' (items store))

data Command : Schema -> Type where
  SetSchema : (new_schema : Schema) -> Command schema
  Add       : SchemaType schema -> Command schema
  Get       : Integer -> Command schema
  Quit      : Command schema

eval : (store : DataStore)
    -> Command (schema store)
    -> Maybe (String , DataStore) -- Nothing => Terminate
eval store (SetSchema new_schema) =
  case size store of
    Z => Just ("new schema", MkData new_schema 0 [])
    _ => Just ("data store is not empty", store)
eval store (Add item) = Just ("added", addToStore store item)
eval store (Get idx) =
  case getEntry store idx of
    Nothing => Just ("index out of bounds", store)
    Just item => Just (display item, store)
eval store Quit = Nothing


parseInt : String -> Maybe (Integer, String)
parseInt text =
  case span isDigit (unpack text) of
    ([], _)        => Nothing
    (digits, rest) => Just (cast (pack digits), pack rest)


parseComma : String -> Maybe ((), String)
parseComma text = case unpack text of
  (',' :: ' ' :: rest) => Just $ ((), pack rest)
  _                    => Nothing

parseQuoted : String -> Maybe (String, String)
parseQuoted text = case unpack text of
  '"' :: rest => case span (/= '"') rest of
    (quoted, '"' :: rest') => Just (pack quoted, pack rest')
  _ => Nothing

parseItem : (schema : Schema)
          -> String
          -> Maybe (SchemaType schema, String)
parseItem SString text = parseQuoted text
parseItem SInt text = parseInt text
parseItem (schema_l .+. schema_r) text = do
  (item_l, text')   <- parseItem schema_l text
  ((), text'')      <- parseComma text'
  (item_r, text''') <- parseItem schema_r text''
  pure ((item_l, item_r), text''')

parseCommand : (schema : Schema)
            -> String
            -> String
            -> Maybe (Command schema)
parseCommand schema "add" args =
  case parseItem schema args of
   -- failure to parse item will yield an "invalid command"
    Nothing => Nothing
    Just (item, "") => Just $ Add item
    Just _ => Nothing
parseCommand _ "get" args = case parseInt args of
  Just (i, "") => Just $ Get i
  _ => Nothing
parseCommand _ "quit" _ = Just Quit
parseCommand _ "schema" _ = Just Quit
parseCommand _ _ _ = Nothing

parseInput : (schema : Schema)
          -> String
          -> Maybe (Command schema)
parseInput schema input =
  case span (/= ' ') input of
    (cmd, rest) => parseCommand schema cmd (ltrim rest)

addNewline : (String, a) -> (String, a)
addNewline (text, x) = (text ++ "\n", x)

onInput : DataStore
       -> String
       -> Maybe (String , DataStore) -- Nothing => Terminate)
onInput store input = addNewline <$> res
  where
    res = case parseInput (schema store) input of
        Nothing => Just ("invalid command", store)
        Just command => eval store command

prompt : String
prompt = "Command: "

main : IO ()
main = replWith (emptyStore (SString .+. SInt)) prompt onInput
