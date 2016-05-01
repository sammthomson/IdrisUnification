||| ported from https://github.com/pepijnkokke/FirstOrderUnificationInAgda
module Unification

import Data.Fin
import Data.Vect


%default total
%access public export

||| An identifier for an arity-k function
data Name : (k : Nat) -> Type where
  MkName : (k : Nat) -> (name : String) -> Name k


||| A term in the language.
||| Either a variable, or an arity-k function applied to k argument terms.
||| @ n an upper bound on the number of variables in the term
||| @ d an upper bound on the depth of the syntax tree (starting at 0)
data Term : (n : Nat) -> (d : Nat) -> Type where
  ||| A variable with index i
  ||| @ i the index
  Var : {d : Nat} -> (i : Fin n) -> Term n d  -- d >= 0, n >= 1
  ||| An arity-k function applied to k arguments
  ||| Increases d by 1
  FuncApp : (func : Name k) -> (args : Vect k (Term n d)) -> Term n (S d)

||| Relaxes the upper bound on depth, `d`
implicit
relaxD : Term n d -> Term n (d + diff)
relaxD (Var i) = Var i
relaxD (FuncApp f args) = FuncApp f (map relaxD args)

||| A substitution of a `Term n d` for a variable `Fin (n+1)`
||| @ n the number of vars after applying the substitution.
||| @ d the depth of the term to be substituted
data Subst : (n : Nat) -> (d : Nat) -> Type where
  MkSubst : (i : Fin (S n)) -> (t : Term n d) -> Subst n d

||| A list of substitutions, of the form
||| `[Subst m d, Subst m-1 d, Subst m-2 d, ...]`
||| Each `s` in a SubstList reduces the number of variables by one, so
||| successive substitutions operate on the reduced set of var idxs.
||| @ m the number of vars before applying the substitutions.
||| @ n the number of vars remaining after applying the substitutions.
data SubstList : (m : Nat) -> (n : Nat) -> Type where
  Nil : {n : Nat} -> SubstList n n  -- no op
  (::) : (s : Subst m d) ->
         (tail : SubstList m n)
           -> SubstList (S m) n

||| `thin x` maps each `Fin n` to a unique `Fin (S n)` that is not `x`.
||| y |-> FS y, if y >= x,
|||       y,    if y < x
thin : (x : Fin (S n)) -> (y : Fin n) -> Fin (S n)
thin FZ     y      = FS y
thin x      FZ     = FZ
thin (FS x) (FS y) = FS (thin x y)

||| `thick x` maps each `Fin (S n)` that is not `x` to a unique `Fin n`.
||| y |-> Just y,        if y < x,
|||       Nothing,       if y = x,
|||       Just (pred y), if y > x
thick : (x, y : Fin (S n)) -> Maybe (Fin n)
thick {n=S k} FZ     (FS y) = Just y
thick {n=S k} x      FZ     = Just FZ
thick {n=S k} (FS x) (FS y) = FS <$> thick x y
thick         _      _      = Nothing

||| replaces any occurrance of a `Var i` in `t` with `f i`
--||| @ f a function from variable idx to a term to replace it with
||| @ t the term to search and replace in
subst : Subst m d1 ->
            (t : Term (S m) d2)
              -> Term m (d1 + d2)
subst (MkSubst x t) (Var i) = relaxD (maybe t Var (thick x i))
subst {d1=d1} s (FuncApp {d=d2} f args) =
  retype (FuncApp f (map (subst s) args)) where
    retype = replace (plusSuccRightSucc d1 d2)  -- convince idris this has the right type


||| Given an idx `y` of a Var, `t \`for\` x` substitutes `t` for `x`,
||| (where `t` is a term not mentioning `x`), thereby
||| reducing the number of vars (`n`).
-- for : (Subst n d) -> (y : Fin (S n)) -> Term n d
-- for (MkSubst x t) y = maybe t Var (thick x y)

-- compose : (f : Fin m -> Term n d2) ->
--           (g : Fin l -> Term m d1) ->
--           Fin l
--             -> Term n (d2 + d1)
-- compose f g = subst f . g

-- ||| apply a substitution
-- apply : {d, m, n : Nat} -> SubstList m n -> Fin m -> Term n (d1 + d2)
-- apply Nil i = Var i
-- apply ((t, x) :: s) y = (apply s) `compose` (t `for` x) y


-- ||| composes two substitution lists
-- (++) : SubstList m n -> SubstList l m -> SubstList l n
-- xs ++ [] = xs
-- xs ++ (y :: ys) = y :: (xs ++ ys)


||| Check that `x` doesn't appear in `t`.
||| If it does, return Nothing.
||| If it doesn't, return `t` but with a tighter upper bound `n`.
check : (x : Fin (S n)) -> (t : Term (S n) d) -> Maybe (Term n d)
check x (Var y)   = Var <$> thick x y
check x (FuncApp s ts) = FuncApp s <$> traverse (check x) ts


flexRigid : Fin n -> Term n d -> Maybe (Exists (SubstList n))
flexRigid {n=Z} _ _ = Nothing
flexRigid {n=S k} x t = case check x t of
  Nothing => Nothing
  Just t' => Just (Evidence k [MkSubst x t'])

flexFlex : (x, y : Fin n) -> Exists (SubstList n)
flexFlex {n=Z} _ _ = Evidence Z []  -- impossible
flexFlex {n=S k} x y = case thick x y of
  Nothing => Evidence (S k) ([] {n=S k})
  Just y' => Evidence k [MkSubst x (Var y' {d=0})]



mkNameInjective : {k : Nat} -> {x : String} -> {y : String}
                    -> (MkName k x = MkName k y) -> (x = y)
mkNameInjective Refl = Refl

DecEq (Name k) where
  decEq (MkName _ x) (MkName _ y) = case decEq x y of
    Yes pf => Yes (cong pf)
    No pf  => No (pf . mkNameInjective)

varInjective : {k : Nat} -> {x : Fin n} -> {y : Fin n}
                    -> (Var x = Var y) -> (x = y)
varInjective Refl = Refl

funcAppInjective : {k1 : Nat} -> {s1 : Name k1} -> {ts1 : Vect k1 (Term n d)} ->
               {k2 : Nat} -> {s2 : Name k2} -> {ts2 : Vect k2 (Term n d)} ->
               (FuncApp s1 ts1 = FuncApp s2 ts2)
                 -> (k1 = k2, s1 = s2, ts1 = ts2)
funcAppInjective Refl = (Refl, Refl, Refl)

varNotFuncApp : {x : Fin n} -> {s : Name k} -> {ts : Vect k (Term n d)} -> Var x = FuncApp s ts -> Void
varNotFuncApp Refl impossible

DecEq (Term n _) where
  decEq (Var x1) (Var x2) = case decEq x1 x2 of
    No pf => No (pf . (varInjective {k=n}))
    Yes Refl => Yes Refl
  decEq (FuncApp {k=k1} s1 ts1) (FuncApp {k=k2} s2 ts2) = case decEq k1 k2 of
    No pf => No (pf . fst . funcAppInjective)
    Yes Refl =>
      case decEq s1 s2 of
        No pf => No (pf . Prelude.Basics.fst . snd . funcAppInjective)
        Yes Refl => case decEq ts1 ts2 of
          No pf => No (pf . snd . snd . funcAppInjective)
          Yes Refl => Yes Refl
  decEq (Var _) (FuncApp s ts) = No varNotFuncApp
  decEq (FuncApp s ts) (Var x) = No (negEqSym varNotFuncApp)


-- maxNatBy : (f : a -> Nat) -> Vect k a -> Nat
-- maxNatBy _ [] = Z
-- maxNatBy f (x :: xs) = max (f x) (maxNatBy f xs)

-- depth : Term n d -> Nat
-- depth (Var i) = Z
-- depth (FuncApp s ts) = S (maxNatBy depth ts)

-- depthLteqD : (t : Term n d) -> LTE (depth t) d
-- depthLteqD (Var {d=d} i) = LTEZero {right=d}
-- depthLteqD (FuncApp {d=d} f args) = LTEZero {right=d}


unify' : (t1 : Term m d1) ->
         (t2 : Term m d2) ->
         Exists (SubstList m)
           -> Maybe (Exists (SubstList m))
unify' (FuncApp {k=k1} s1 ts1) (FuncApp {k=k2} s2 ts2) acc =
  case decEq k1 k2 of
    No _ => Nothing
    Yes Refl => case decEq s1 s2 of
      No _ => Nothing
      Yes Refl => foldl (>>=) (Just acc) (zipWith unify' ts1 ts2)
unify' (Var x1) (Var x2) (Evidence n []) = Just (flexFlex x1 x2)
unify' (Var x1) t2       (Evidence n []) = flexRigid x1 t2
unify' t1       (Var x2) (Evidence n []) = flexRigid x2 t1
unify' t1 t2 (Evidence n (s :: ss)) =
  case unify' (subst s t1) (subst s t2) (Evidence n ss) of
    Nothing => Nothing
    Just (Evidence n sl) => Just (Evidence n (s :: sl))

unify : (t1 : Term m d1) -> (t2 : Term m d2) -> Maybe (Exists (SubstList m))
unify {m=m} t1 t2 = unify' t1 t2 (Evidence m [])
