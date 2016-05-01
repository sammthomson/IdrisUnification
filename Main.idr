module Main

import Data.Vect
import Data.Fin
import Unification

f : Name 1
f = MkName 1 "f"

r : Name 2
r = MkName 2 "r"

c : Term 2 1
c = FuncApp (MkName 0 "c") []

x : Term 2 0
x = Var 0

y : Term 2 0
y = Var 1

unifyXY : Maybe (Exists (SubstList 2))
unifyXY = unify x y

unifyXFC : Maybe (Exists (SubstList 2))
unifyXFC = unify x (FuncApp f [c])

toNatPair : Fin n -> (Nat, Nat)
toNatPair (FZ {k=k}) = (1, S k)
toNatPair (FS i {k=k}) = (1 + fst (toNatPair i), S k)

Show (Fin n) where
  showPrec d i = case toNatPair i of
    (i, n) => showCon d "Fin" (" " ++ show i ++ "/" ++ show n)

Show (Term n d) where
  showPrec d (Var i) = showCon d "Var" (showArg i)
  showPrec d (FuncApp (MkName _ name) args) =
    showCon d "FuncApp" (showArg name ++ showArg args)

Show (SubstList m n) where
  show Nil = "[]"
  show (s :: ss) = show s ++ " :: " ++ show ss



--main : IO ()
--main = do
--  printLn (map getProof unifXY)
--  printLn $ map getProof $ unify (FuncApp f [FuncApp f [c]]) (FuncApp f [x])
