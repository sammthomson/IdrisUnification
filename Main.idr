module Main

import Data.Vect
import Data.Fin
import Unification

f : Term (Fin 2)
f = identifier (MkName "f")

c : Term (Fin 2)
c = identifier (MkName "c")

cc : Term (Fin 2)
cc = fork c c

x : Term (Fin 2)
x = var 0

y : Term (Fin 2)
y = var 1

unifyXY : Maybe (Exists (SubstList 2))
unifyXY = unify x y

unifyXFCC : Maybe (Exists (SubstList 2))
unifyXFCC = unify x (fork f cc)

toNatPair : Fin n -> (Nat, Nat)
toNatPair (FZ {k=k}) = (1, S k)
toNatPair (FS i {k=k}) = (1 + fst (toNatPair i), S k)

Show (Fin n) where
  showPrec d i = case toNatPair i of
    (i, n) => showCon d "Fin" (" " ++ show i ++ "/" ++ show n)

Show n => Show (Term n) where
  showPrec d = fold
    (\i => showCon d "Var" (showArg i))
    (\c => case c of (MkName n) => showCon d "Identifier" (showArg n))
    (\l, r => showCon d "Fork" (" " ++ l ++ " " ++ r))

Show (Subst m) where
  showPrec d (MkSubst x t) = showCon d "Subst" ((showArg x) ++ (showArg t))

Show (SubstList m n) where
  show Nil = "[]"
  show (s :: ss) = (show s) ++ " :: " ++ (show ss)

Show (Exists (SubstList n)) where
  show (Evidence _ ss) = show ss

main : IO ()
main = do
  printLn unifyXY
  printLn $ unify (fork f (fork f c)) (fork f y)
  printLn unifyXFCC
