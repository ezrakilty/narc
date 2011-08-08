module Database.Narc.SQL.Pretty where

import Database.Narc.Pretty
import Database.Narc.SQL
import Database.Narc.Util (mapstrcat)

instance Pretty Query where
  pretty (Select{rslt=QRecord flds, tabs=tabs, cond=cond}) = 
         "select " ++ mapstrcat ", " (\(alias, expr) -> 
                                          pretty expr ++ " as " ++ alias)
                      flds ++ 
         (if null tabs then "" else
         " from " ++ mapstrcat ", " (\(name, al, ty) -> name ++ " as " ++ al) 
                         tabs) ++ 
         " where " ++ pretty_cond cond
                   where pretty_cond [] = "true"
                         pretty_cond cond = mapstrcat " and " pretty cond
  pretty (QRecord fields) = "{"++ mapstrcat ", "
                               (\(lbl,expr) -> 
                                    lbl ++ "=" ++ show expr) fields
                          ++ "}"

  pretty (QUnion a b) = pretty a ++ " union all " ++ pretty b

instance Pretty QBase where
  pretty (BNum n) = show n
  pretty (BBool True) = "true"
  pretty (BBool False) = "false"
   
  pretty (BField a b) = a ++ "." ++ b
  pretty (BNot b) = "not " ++ pretty b
  pretty (BOp lhs op rhs) = pretty lhs ++ pretty op ++ pretty rhs

  pretty (BIf c t f) = "if " ++ pretty c ++ " then " ++ pretty t
                       ++ " else " ++ pretty f

-- Pretty-printing for Op, common to both AST and SQL languages.

instance Pretty Op where
  pretty Plus = " + "
  pretty Eq = " = "
  pretty Less = " < "
