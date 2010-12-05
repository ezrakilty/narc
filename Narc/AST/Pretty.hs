module Narc.AST.Pretty where

import Narc.AST
import Narc.Pretty
import Narc.Util (mapstrcat)

-- Pretty-printing ------------------------------------------------=====

instance Pretty (Term' a) where
  pretty (Unit) = "()"
  pretty (Bool b) = show b
  pretty (Num n) = show n
  pretty (PrimApp f args) = f ++ "("++mapstrcat "," (pretty.fst) args ++")"
  pretty (Var x) = x
  pretty (Abs x n) = "(fun " ++ x ++ " -> " ++ (pretty.fst) n ++ ")"
  pretty (App l m) = (pretty.fst) l ++ " " ++ (pretty.fst) m
  pretty (Table tbl t) = "table " ++ tbl ++ " : " ++ show t
  pretty (If c a b) = "(if " ++ (pretty.fst) c ++ " then " ++ (pretty.fst) a ++ 
                      " else " ++ (pretty.fst) b ++ " )"
  pretty (Singleton m) = "[" ++ (pretty.fst) m ++ "]" 
  pretty (Nil) = "[]"
  pretty (Union m n) = "("++(pretty.fst) n++" ++ "++(pretty.fst) n++")"
  pretty (Record fields) = 
      "{" ++ mapstrcat "," (\(l,m) -> l ++ "=" ++(pretty.fst) m) fields++ "}"
  pretty (Project m l) = "("++(pretty.fst) m++"."++l++")"
  pretty (Comp x m n)= "for ("++x++" <- "++(pretty.fst) m++") " ++ (pretty.fst)n

