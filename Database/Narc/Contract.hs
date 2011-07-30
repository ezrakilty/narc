module Database.Narc.Contract where

-- Contractual assertions ----------------------------------------------

contract p x = if p x then x else error "Contract broken"

assert x e = if x then e else error "assertion failed"
