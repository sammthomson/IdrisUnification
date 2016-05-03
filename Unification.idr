||| ported from https://github.com/pepijnkokke/FirstOrderUnificationInAgda
module Unification

import Data.Fin


%default total
%access public export


||| An identifier
data Name = MkName String

Eq Name where
  (MkName x) == (MkName y) = x == y

||| A term in an untyped lambda-calculus with variables indexed by `v`.
||| Either a variable, an identifier, or a function applied to an argument.
||| We keep track of the depth `d` to ensure terms are finite.
||| @ v the type `Var`s are indexed by
||| @ d the depth of the AST
data TermD : (v : Type) -> (d : Nat) -> Type where
  ||| A variable with index `i`
  Var : (i : v) -> TermD v Z
  ||| an identifier with name `n`
  Identifier : (n : Name) -> TermD v Z
  ||| function application, `f` applied to `x`
  App : (f : TermD v d1) -> (x : TermD v d2) -> TermD v (S (max d1 d2))

||| A TermD with `d` as a reified witness instead of a type param
data Term : (v : Type) -> Type where
  MkTerm : Exists (TermD v) -> Term v

namespace Term
  depth : Term v -> Nat
  depth (MkTerm t) = getWitness t

  {- implicit conversions to/from TermD -}
  implicit
  toTermD : (t : Term v) -> TermD v (depth t)
  toTermD (MkTerm t) = getProof t

  implicit
  fromTermD : TermD v d -> Term v
  fromTermD {d=d} t = MkTerm (Evidence d t)

  {- constructors for Term (making use of implicit conversions to/from TermD) -}
  var : v -> Term v
  var v = Var v

  identifier : {v : Type} -> Name -> Term v
  identifier c = Identifier c

  app : Term v -> Term v -> Term v
  app left right = App left right

  ||| The catamorphism for Term.
  ||| We unpack and use `d` to convince idris `fold'` is total,
  ||| so callers of `fold` can ignore `d` and not worry about totality.
  fold : (v -> r) -> (Name -> r) -> (r -> r -> r) -> Term v -> r
  fold v n f (MkTerm (Evidence d t)) = fold' v n f d t where
    fold' v n f d t = case t of
      Var i => v i
      Identifier c => n c
      App {d1=d1} {d2=d2} l r => f (fold' v n f d1 l) (fold' v n f d2 r)

Functor Term where
  map f t = fold (var . f) identifier app t

Applicative Term where
  pure = var
  mf <*> ma = fold (\f => map f ma) identifier app mf

Monad Term where
  t >>= f = fold f identifier app t

Foldable Term where
  foldr op z t = fold op (const id) (.) t z

Traversable Term where
  traverse f = fold
    (\y => [| var (f y) |])
    (\c => pure (identifier c))
    (\l, r => [| app l r |])


{- Now for some unification... -}


||| A substitution of a `Term (Fin n)` for a variable in `Fin (S n)`.
||| @ n the number of vars after applying the substitution.
data Subst : (n : Nat) -> Type where
  ||| Make a Subst
  ||| @ x the variable to replace
  ||| @ t the term (not mentioning `x`) to replace `x` with
  MkSubst : (x : Fin (S n)) -> (t : Term (Fin n)) -> Subst n

{-
  thick and thin help keep track of var indexes when vars are
  introduced or removed.
-}
||| `thick x` maps each `Fin (S n)` that is not `x` to a unique `Fin n`.
||| Useful when removing `x` from the set of vars (e.g. with a `Subst`).
||| y |-> Just y,        if y < x,
|||       Nothing,       if y = x,
|||       Just (pred y), if y > x
thick : (x, y : Fin (S n)) -> Maybe (Fin n)
thick {n=S k} FZ     (FS y) = Just y              -- y < x
thick {n=S k} (FS x) FZ     = Just FZ             -- y > x
thick {n=S k} (FS x) (FS y) = FS <$> thick x y    -- recurse
thick         _      _      = Nothing             -- y = x

||| `thin x` maps each `Fin n` to a unique `Fin (S n)` that is not `x`.
||| The inverse of `y |-> thick x y` for `y`s s.t. `y != x`.
||| Useful for undoing a `Subst`.
||| y |-> FS y, if y >= x,
|||       y,    if y < x
thin : (x : Fin (S n)) -> (y : Fin n) -> Fin (S n)
thin FZ     y      = FS y
thin x      FZ     = FZ
thin (FS x) (FS y) = FS (thin x y)

||| replaces any occurrance of a `Var y` in `t` with `r` if
||| `x == y` or `Var (thick x y)` otherwise.
||| @ s the substitution to make
||| @ t the term to search and replace in
subst : (s : Subst m) -> (t : Term (Fin (S m))) -> Term (Fin m)
subst (MkSubst x r) t = map (thick x) t >>= (maybe r var)

||| A list of substitutions, of the form
||| `[Subst m d, Subst m-1 d, Subst m-2 d, ...]`.
||| Substitutions are applied left to right.
||| Each `s` in a SubstList reduces the number of variables by one, so
||| successive substitutions operate on the reduced set of var idxs.
||| @ m the number of vars before applying the substitutions.
||| @ n the number of vars remaining after applying the substitutions.
data SubstList : (m : Nat) -> (n : Nat) -> Type where
  Nil : {n : Nat} -> SubstList n n  -- no op, number of vars is unchanged
  (::) : (s : Subst m) ->
         (tail : SubstList m n)
           -> SubstList (S m) n

||| Check that `x` doesn't appear in `t`.
||| If it does, return Nothing.
||| If it doesn't, return `t` but over a smaller set of vars.
check : (x : Fin (S n)) -> (t : Term (Fin (S n))) -> Maybe (Term (Fin n))
check x = traverse (thick x)


||| As long as the var x doesn't appear in t, we can unify x and t
||| by substituting t for x.
flexRigid : Fin n -> Term (Fin n) -> Maybe (Exists (SubstList n))
flexRigid {n=Z} _ _ = Nothing  -- impossible, Fin Z is uninhabited
flexRigid {n=S n'} x t = map (\t' => Evidence n' [MkSubst x t']) (check x t)

||| we can always unify two variables
flexFlex : (x, y : Fin n) -> Exists (SubstList n)
flexFlex {n=Z} _ _ = Evidence Z []  -- impossible, Fin Z is uninhabited
flexFlex {n=S n'} x y = case thick x y of
  Nothing => Evidence (S n') []                -- x = y, no subst needed
  Just y' => Evidence n' [MkSubst x (Var y')]  -- x != y, sub y' for x

||| helper function for unify
unify' : (t1 : TermD (Fin m) d1) ->
         (t2 : TermD (Fin m) d2) ->
         (acc : Exists (SubstList m))
           -> Maybe (Exists (SubstList m))
unify' t1 t2 (Evidence n (s :: tail)) =  -- non-empty `acc`
  map consS $ unify' (subst s t1) (subst s t2) (Evidence n tail) where
    consS (Evidence n' sl) = Evidence n' (s :: sl)
unify' (Var x1) (Var x2) _ = Just (flexFlex x1 x2)
unify' (Var x1) t2       _ = flexRigid x1 t2
unify' t1       (Var x2) _ = flexRigid x2 t1
unify' {m=m} (Identifier c1) (Identifier c2) acc =
  if c1 == c2 then Just acc else Nothing
unify' (App la ra) (App lb rb) acc =
  Just acc >>= unify' la lb >>= unify' ra rb
unify' _ _ _ = Nothing  -- can't unify identifier with function application
                        -- (in first-order unification, anyway)

||| Finds the most general substitutions of terms for variables that makes
||| the two terms equal.
unify : (t1 : Term (Fin m)) -> (t2 : Term (Fin m)) -> Maybe (Exists (SubstList m))
unify {m=m} t1 t2 = unify' t1 t2 (Evidence m [])
