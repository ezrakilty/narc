module Database.Narc.SQL.Pretty where

import Database.Narc.Pretty
import Database.Narc.SQL
import Database.Narc.Util (mapstrcat)

instance Pretty Query where
  pretty (Select{rslt=flds, tabs=tabs, cond=cond}) = 
         "select " ++ mapstrcat ", " (\(alias, expr) -> 
                                          pretty expr ++ " as " ++ alias)
                      flds ++ 
         (if null tabs then "" else
         " from " ++ mapstrcat ", " (\(name, alias, _ty) -> serialize name ++ " as " ++ alias) 
                         tabs) ++ 
         " where " ++ pretty_conds cond

  pretty (Union a b) = pretty a ++ " union all " ++ pretty b

pretty_conds :: Pretty a => [a] -> String
pretty_conds [] = "true"
pretty_conds cond = mapstrcat " and " pretty cond

instance Pretty QBase where
  pretty (Lit lit) = pretty lit
   
  pretty (Field a b) = a ++ "." ++ b
  pretty (Not b) = "not " ++ pretty b
  pretty (Op lhs op rhs) = pretty lhs ++ pretty op ++ pretty rhs

  pretty (If c t f) = "if " ++ pretty c ++ " then " ++ pretty t
                       ++ " else " ++ pretty f

  pretty (Exists q) = "exists (" ++ pretty q ++ ")"

instance Pretty DataItem where
  pretty (Num n) = show n
  pretty (String s) = show s -- FIXME use SQL-style quoting.
  pretty (Bool True) = "true"
  pretty (Bool False) = "false"

-- Pretty-printing for Op, common to both AST and SQL languages.

instance Pretty Op where
  pretty Plus   = " + "
  pretty Minus  = " - "
  pretty Times  = " * "
  pretty Divide = " / "
  pretty Eq     = " = "
  pretty NonEq  = " <> "
  pretty Less   = " < "
  pretty Greater= " > "
  pretty LessOrEq   = " <= "
  pretty GreaterOrEq= " >= "
