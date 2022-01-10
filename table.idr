module Main

import Data.Vect
import Data.List
import Data.HVect
import Data.OpenUnion
import OneOf

ColumnName : Type
ColumnName = String

Sort : Type
Sort = Type

Schema : {n: Nat} -> Type
Schema = Vect n (ColumnName, Sort)

data Row : Schema -> Type where
  End   : Row []
  Cell  : (col_name: ColumnName) -> (val: a) -> Row rs -> Row ((col_name, a) :: rs)

row : {n: Nat} -> {s: Schema {n}} -> HVect (map (\x => snd x) s) -> Row s
row {s=[]} Nil  = End
row {s=((c, _)::cns)} (v::vs) = Cell c v $ row vs {s=cns}

data Table : Type -> Schema -> Type where
  MkTable : (indexType -> Row schema) -> Table indexType schema

infixr 10 |=>

-- Table type written in the style of dex
(|=>): Type -> Schema -> Type
(|=>) indexType schema = Table indexType schema

-- helper that forces to speicfy the table type
table : (indexType: Type) -> (schema: Schema) ->
        (indexType -> Row schema) -> Table indexType schema
table _ _ x = MkTable x

data Symbol : tag -> Type where
  MkSymbol : (label: tag) -> Symbol label

symbols : List a -> List Type
symbols = map (\s => Symbol s)

-- students: a simple table with no values missing.
students: (Fin 3) |=> [("name", String), ("age", Int), ("favorite color", String)]
students = MkTable (\idx => case idx of 
    0 => row (["Bob",   12, "blue"])
    1 => row (["Alice", 17, "green"])
    2 => row (["Eve",   13, "red"])
  )

-- studentsMissing: a simple table with no values missing.
studentsMissing: (Fin 3) |=> [("name",           Maybe String),
                              ("age",            Maybe Int),
                              ("favorite color", Maybe String)]
studentsMissing = MkTable (\idx => case idx of
    0 => row ([Just "Bob",   Nothing, Just "blue"])
    1 => row ([Just "Alice", Just 17, Just "green"])
    2 => row ([Just "Eve",   Just 13, Nothing])
  )

-- employees: a table that contains employees and their department IDs
EmployeeNames : List Type
EmployeeNames =
  symbols ["Rafferty", "Jones", "Heisenberg", "Robinson", "Smith", "Williams"]

IDs : List Type
IDs = symbols [31, 33, 34, 35]

employees: (OneOf EmployeeNames) |=> [("Department ID", Maybe (OneOf IDs))]
employees = MkTable (cases [
    (\_: Symbol "Rafferty"  => row [Just (make (MkSymbol 31))]),
    (\_: Symbol "Jones"     => row [Just (make (MkSymbol 33))]),
    (\_: Symbol "Heisenberg"=> row [Just (make (MkSymbol 33))]),
    (\_: Symbol "Robinson"  => row [Just (make (MkSymbol 34))]),
    (\_: Symbol "Smith"     => row [Just (make (MkSymbol 34))]),
    (\_: Symbol "Williams"  => row [Nothing])
  ])

-- departments: a table that contains departments and their IDs
departments: (OneOf IDs) |=> [("Department Name", Maybe String)]
departments = MkTable (cases [
    (\_ => row [Just "Sales"]),
    (\_ => row [Just "Engineering"]),
    (\_ => row [Just "Clerical"]),
    (\_ => row [Just "Marketing"])
  ])

-- jellyAnon: a jelly bean table that contains only boolean data
jellyAnon: (Fin 2) |=> [("get_acne",  Bool),
                        ("red",       Bool),
                        ("black",     Bool),
                        ("white",     Bool),
                        ("green",     Bool),
                        ("yellow",    Bool),
                        ("brown",     Bool),
                        ("orange",    Bool),
                        ("pink",      Bool),
                        ("purple",    Bool)]
jellyAnon = MkTable (\idx => case idx of
    0 => row [True,False,False,False,True,False,False,True,False,False]
    1 => row [True,False,True,False,True,True,False,False,False,False]  
  )

-- jellyNamed: a jelly bean table that contains booleans and strings
JellyNames : List Type
JellyNames = symbols ["Emily", "Jacob"]

jellyNamed: (OneOf JellyNames) |=> [("get_acne",  Bool),
                        ("red",       Bool),
                        ("black",     Bool),
                        ("white",     Bool),
                        ("green",     Bool),
                        ("yellow",    Bool),
                        ("brown",     Bool),
                        ("orange",    Bool),
                        ("pink",      Bool),
                        ("purple",    Bool)]
jellyNamed = MkTable (cases [
  (\_=> row [True,False,False,False,True,False,False,True,False,False]),
  (\_=> row [True,False,True,False,True,True,False,False,False,False])
 ])

-- gradebook: a gradebook table with no missing values.
gradebook : (OneOf (symbols ["Bob", "Alice", "Eve"]))
  |=> [("age",      Int),
       ("quiz1",    Int),
       ("quiz2",    Int),
       ("midterm",  Int),
       ("quiz3",    Int),
       ("quiz4",    Int),
       ("final",    Int)]
gradebook = MkTable (cases [
    (\_: Symbol "Bob"   => row [12,8,9,77,7,9,87]),
    (\_: Symbol "Alice" => row [17,6,8,88,8,7,85]),
    (\_: Symbol "Eve"   => row [13,7,9,84,8,8,77])
  ])

-- gradebookMissing: a gradebook table with some missing values.
gradebookMissing : (OneOf (symbols ["Bob", "Alice", "Eve"]))
  |=> [("age",      Maybe Int),
       ("quiz1",    Maybe Int),
       ("quiz2",    Maybe Int),
       ("midterm",  Maybe Int),
       ("quiz3",    Maybe Int),
       ("quiz4",    Maybe Int),
       ("final",    Maybe Int)]
gradebookMissing = MkTable (cases [
    (\_: Symbol "Bob"   =>
      row [Just 12, Just 8, Just 9, Just 77, Just 7, Just 9, Just 87]),
    (\_: Symbol "Alice" =>
      row [Just 17, Just 6, Just 8, Just 88, Just 8, Just 7, Just 85]),
    (\_: Symbol "Eve"   =>
      row [Just 13, Just 7, Just 9, Just 84, Just 8, Just 8, Just 77])
  ])


-- gradebookSeq: a gradebook table with sequence cells
gradebookSeq : (OneOf (symbols ["Bob", "Alice", "Eve"]))
  |=> [("age",      Int),
       ("quizzes",  Vect 4 Int),
       ("midterm",  Int),
       ("final",    Int)]
gradebookSeq = MkTable (cases [
    (\_: Symbol "Bob"   => row [12, [8, 9, 7, 9], 77, 87]),
    (\_: Symbol "Alice" => row [17, [6, 8, 8, 7], 88, 85]),
    (\_: Symbol "Eve"   => row [13, [7, 9, 8, 8], 84, 77])
  ])

-- gradebookTable: a gradebook table with table cells
gradebookTable : (OneOf (symbols ["Bob", "Alice", "Eve"]))
  |=> [("age", Int),
       ("quizzes", (Fin 4) |=> [("grade", Int)]),
       ("midterm", Int),
       ("final", Int)]
gradebookTable = MkTable (cases [
    (\_: Symbol "Bob" =>
      row [ 12, table (Fin 4) [("grade", Int)]
                (\quiz => case quiz of
                      0 => row [8]
                      1 => row [9]
                      2 => row [7]
                      3 => row [9]), 77 , 87 ]),
    (\_: Symbol "Alice" =>
      row [ 17, table (Fin 4) [("grade", Int)]
                (\quiz => case quiz of
                      0 => row [6]
                      1 => row [8]
                      2 => row [8]
                      3 => row [7]), 88, 85 ]),
    (\_: Symbol "Eve" =>
      row [ 13, table (Fin 4) [("grade", Int)]
                (\quiz => case quiz of
                      0 => row [7]
                      1 => row [9]
                      2 => row [8]
                      3 => row [8]), 84, 77 ])
  ])

-- API
-- auxilirary functions
even : Int -> Bool
even n = if mod n 2 == 0 then True else False

length : List a -> Nat
length = List.length


-- (|=>): Type -> Schema -> Type
-- (|=>) indexType schema = indexType -> Row schema

-- schema : (indexType -> s) -> Schema

-- emptyTable :: t:Table

