module DataStore

import Data.Vect

infixr 5 .+.

public export
data Schema = SString | SInt | (.+.) Schema Schema

public export total
SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

export
record DataStore (schema: Schema) where
  constructor MkDataStore
  size : Nat
  items : Vect size (SchemaType schema)

export
empty : DataStore schema
empty = MkDataStore 0 []

export
addToStore : (item: SchemaType schema)
          -> (store: DataStore schema)
          -> DataStore schema
addToStore item (MkDataStore size items) = MkDataStore _ (item :: items)

public export
data StoreView : DataStore schema -> Type where
  SNil : StoreView empty
  SAdd : (rec: StoreView store) -> StoreView (addToStore item store)

total
storeView' : (items: Vect size (SchemaType schema))
          -> StoreView (MkDataStore size items)
storeView' [] = SNil
storeView' (x :: xs) = SAdd (storeView' xs) -- ??? how does `x` become the `item`

export total
storeView : (store: DataStore schema) -> StoreView store
storeView (MkDataStore size items) = storeView' items

testStore : DataStore (SString .+. SString .+. SInt)
testStore = addToStore ("Mercury", "Mariner 10", 1974) $
            -- ??? shouldn't this be ("Mercury", ("Mariner 10", 1974))
            addToStore ("Venus", "Venera", 1961) $
            addToStore ("Uranus", "Voyager 2", 1986) $
            addToStore ("Pluto", "New Horizons", 2015) $
            empty

filterKeys : (test: SchemaType val_schema -> Bool)
          -> (DataStore (SString .+. val_schema))
          -> List String
filterKeys test store with (storeView store)
  filterKeys test store | SNil = []
  filterKeys test (addToStore item rec_store) | (SAdd rec) =
    case test (snd item) of
      True => fst item :: (filterKeys test rec_store | rec)
      False => filterKeys test rec_store | rec

total
getValues : DataStore (SString .+. val_schema) -> List (SchemaType val_schema)
getValues store with (storeView store)
  getValues x | SNil = []
  getValues (addToStore item store) | (SAdd rec) = snd item :: getValues store | rec
