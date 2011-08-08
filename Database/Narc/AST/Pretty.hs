{-# LANGUAGE TypeSynonymInstances #-}

module Database.Narc.AST.Pretty where

import Database.Narc.AST
import Database.Narc.Pretty
import Database.Narc.Util (mapstrcat)

-- Pretty-printing ------------------------------------------------=====

instance Pretty (Term' a) where
  pretty (Unit) = "()"
  pretty (Bool b) = show b
  pretty (Num n) = show n
  pretty (String s) = show s
  pretty (PrimApp f args) = f ++ "(" ++ mapstrcat "," pretty args ++ ")"
  pretty (Var x) = x
  pretty (Abs x n) = "(fun " ++ x ++ " -> " ++ pretty n ++ ")"
  pretty (App l m) = pretty l ++ " " ++ pretty m
  pretty (Table tbl t) = "(table " ++ tbl ++ " : " ++ show t ++ ")"
  pretty (If c a b) =
      "(if " ++ pretty c ++ " then " ++ pretty a ++ 
      " else " ++ pretty b ++ " )"
  pretty (Singleton m) = "[" ++ pretty m ++ "]" 
  pretty (Nil) = "[]"
  pretty (Union m n) = "(" ++ pretty n ++ " ++ " ++ pretty n ++ ")"
  pretty (Record fields) = 
      "{" ++ mapstrcat "," (\(l,m) -> l ++ "=" ++ pretty m) fields ++ "}"
  pretty (Project m l) = "(" ++ pretty m ++ "." ++ l ++ ")"
  pretty (Comp x m n) =
      "(for (" ++ x ++ " <- " ++ pretty m ++ ") " ++ pretty n ++ ")"

instance Pretty (Term a) where
  pretty (m, t) = pretty m
