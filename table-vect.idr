module Main

import Data.Vect
import HVect

ColumnName : Type
ColumnName = String

Sort : Type
Sort = Type

Schema : {n: Nat} -> Type
Schema = Vect n (ColumnName, Sort)

data Row : Schema -> Type where
  End   : Row []
  Cell  : (col_name: ColumnName) -> (val: a) -> Row rs -> Row ((col_name, a) :: rs)

row : {n: Nat} -> {s: Schema {n}} -> HVect n (map (\x => snd x) s) -> Row s
row {s=[]} Nil  = End
row {s=((c, _)::cns)} (v||vs) = Cell c v $ row vs {s=cns}

Table : {n: Nat} -> Schema -> Type
Table s = Vect n (Row s)

-- students: a simple table with no values missing.
students : Table {n=3} [("name", String), ("age", Int), ("favorite color", String)]
students = [
  row ("Bob"   || 12 || "blue"   || Nil),
  row ("Alice" || 17 || "green"  || Nil),
  row ("Eve"   || 13 || "red"    || Nil)
]

-- studentsMissing: a simple table with some values missing.
studentsMissing : Table {n=3} [("name", Maybe String), ("age", Maybe Int), ("favorite color", Maybe String)]
studentsMissing = [
  Cell "name" (Just "Bob")   $ Cell "age" Nothing   $ Cell "favorite color" (Just "blue")  $ End,
  Cell "name" (Just "Alice") $ Cell "age" (Just 17) $ Cell "favorite color" (Just "green") $ End,
  Cell "name" (Just "Eve")   $ Cell "age" (Just 13) $ Cell "favorite color" Nothing        $ End
]

-- employees: a table that contains employees and their department IDs.
-- employees : Table {n=1} [("Last Name",)]