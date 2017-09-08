-- Lightweight calculus for composing patterns as functions.
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Verifier.SAW.Recognizer
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Recognizer
  ( Recognizer
  , (<:), emptyl, endl
  , (:*:)(..)
  , asFTermF

  , asGlobalDef
  , isGlobalDef
  , asApp
  , (<@>), (@>)
  , asApplyAll
  , asPairType
  , asPairValue
  , asPairSelector
  , asTupleType
  , asTupleValue
  , asTupleSelector
  , asFieldType
  , asFieldValue
  , asRecordType
  , asRecordValue
  , asRecordSelector
  , asCtor
  , asDataType
  , isDataType
  , asNatLit
  , asStringLit
  , asLambda
  , asLambdaList
  , asPi
  , asPiList
  , asLocalVar
  , asConstant
  , asExtCns
  , asSort
    -- * Prelude recognizers.
  , asBool
  , asBoolType
  , asIntegerType
  , Nat
  , asBitvectorType
  , asVectorType
  , asVecType
  , isVecType
  , asMux
  ) where

import Control.Applicative
import Control.Lens
import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import Verifier.SAW.Prim
import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.Pretty

data a :*: b = (:*:) a b
  deriving (Eq,Ord,Show)

instance Field1 (a :*: b) (a' :*: b) a a' where
  _1 k (a :*: b) = indexed k (0 :: Int) a <&> (:*: b)

instance Field2 (a :*: b) (a :*: b') b b' where
  _2 k (a :*: b) = (a :*:) <$> indexed k (1 :: Int) b

type Recognizer m t a = t -> m a

-- | Tries both recognizers.
(<>) :: Alternative f => Recognizer f t a -> Recognizer f t a -> Recognizer f t a
(<>) f g t = f t <|> g t

-- | Recognizes the head and tail of a list, and returns head.
(<:) :: Monad f
     => Recognizer f t a -> Recognizer f [t] () -> Recognizer f [t] a
(<:) f g (h:r) = do x <- f h; _ <- g r; return x
(<:) _ _ [] = fail "empty-list"

-- | Recognizes the head and tail of a list, and returns head.
(<:>) :: Monad f
     => Recognizer f t a -> Recognizer f [t] b -> Recognizer f [t] (a :*: b)
(<:>) f g (h:r) = do x <- f h; y <- g r; return (x :*: y)
(<:>) _ _ [] = fail "empty-list"

-- | Recognizes empty list
emptyl :: Monad m => Recognizer m [t] ()
emptyl [] = return ()
emptyl _ = fail "non-empty"

-- | Recognizes singleton list
endl :: Monad f => Recognizer f t a -> Recognizer f [t] a
endl f = f <: emptyl

asFTermF :: (Monad f) => Recognizer f Term (FlatTermF Term)
asFTermF (unwrapTermF -> FTermF ftf) = return ftf
asFTermF _ = fail "not ftermf"

asGlobalDef :: (Monad f) => Recognizer f Term Ident
asGlobalDef t = do GlobalDef i <- asFTermF t; return i

isGlobalDef :: (Monad f) => Ident -> Recognizer f Term ()
isGlobalDef i t = do
  o <- asGlobalDef t
  if i == o then return () else fail ("not " ++ show i)

asApp :: (Monad f) => Recognizer f Term (Term, Term)
asApp (unwrapTermF -> App x y) = return (x, y)
asApp _ = fail "not app"

(<@>) :: (Monad f)
      => Recognizer f Term a -> Recognizer f Term b -> Recognizer f Term (a :*: b)
(<@>) f g t = do
  (a,b) <- asApp t
  liftM2 (:*:) (f a) (g b)

-- | Recognizes a function application, and returns argument.
(@>) :: (Monad f) => Recognizer f Term () -> Recognizer f Term b -> Recognizer f Term b
(@>) f g t = do
  (x, y) <- asApp t
  liftM2 (const id) (f x) (g y)

asApplyAll :: Term -> (Term, [Term])
asApplyAll = go []
  where go xs t =
          case asApp t of
            Nothing -> (t, xs)
            Just (t', x) -> go (x : xs) t'

asPairType :: (Monad m) => Recognizer m Term (Term, Term)
asPairType t = do
  ftf <- asFTermF t
  case ftf of
    PairType x y -> return (x, y)
    _            -> fail "asPairType"

asPairValue :: (Monad m) => Recognizer m Term (Term, Term)
asPairValue t = do
  ftf <- asFTermF t
  case ftf of
    PairValue x y -> return (x, y)
    _             -> fail "asPairValue"

asPairSelector :: (Monad m) => Recognizer m Term (Term, Bool)
asPairSelector t = do
  ftf <- asFTermF t
  case ftf of
    PairLeft x  -> return (x, False)
    PairRight x -> return (x, True)
    _           -> fail "asPairSelector"

asTupleType :: (Monad m) => Recognizer m Term [Term]
asTupleType t = do
  ftf <- asFTermF t
  case ftf of
    UnitType     -> return []
    PairType x y -> do xs <- asTupleType y; return (x : xs)
    _            -> fail "asTupleType"

asTupleValue :: (Monad m) => Recognizer m Term [Term]
asTupleValue t = do
  ftf <- asFTermF t
  case ftf of
    UnitValue     -> return []
    PairValue x y -> do xs <- asTupleValue y; return (x : xs)
    _             -> fail "asTupleValue"

asTupleSelector :: (Monad m) => Recognizer m Term (Term, Int)
asTupleSelector t = do
  ftf <- asFTermF t
  case ftf of
    PairLeft x  -> return (x, 1)
    PairRight y -> do (x, i) <- asTupleSelector y; return (x, i+1)
    _           -> fail "asTupleSelector"

asFieldType :: (Monad m) => Recognizer m Term (Term, Term, Term)
asFieldType t = do
  ftf <- asFTermF t
  case ftf of
    FieldType x y z -> return (x, y, z)
    _               -> fail "asFieldType"

asFieldValue :: (Monad m) => Recognizer m Term (Term, Term, Term)
asFieldValue t = do
  ftf <- asFTermF t
  case ftf of
    FieldValue x y z -> return (x, y, z)
    _                -> fail "asFieldValue"

asRecordType :: (Monad m) => Recognizer m Term (Map FieldName Term)
asRecordType t = do
  ftf <- asFTermF t
  case ftf of
    EmptyType       -> return Map.empty
    FieldType f x y -> do m <- asRecordType y
                          s <- asStringLit f
                          return (Map.insert s x m)
    _               -> fail $ "asRecordType: " ++ showTerm t

asRecordValue :: (Monad m) => Recognizer m Term (Map FieldName Term)
asRecordValue t = do
  ftf <- asFTermF t
  case ftf of
    EmptyValue       -> return Map.empty
    FieldValue f x y -> do m <- asRecordValue y
                           s <- asStringLit f
                           return (Map.insert s x m)
    _                -> fail $ "asRecordValue: " ++ showTerm t

asRecordSelector :: (Monad m) => Recognizer m Term (Term, FieldName)
asRecordSelector t = do
  RecordSelector u i <- asFTermF t
  s <- asStringLit i
  return (u, s)

asCtor :: (Monad f) => Recognizer f Term (Ident, [Term])
asCtor t = do CtorApp c l <- asFTermF t; return (c,l)

asDataType :: (Monad f) => Recognizer f Term (Ident, [Term])
asDataType t = do DataTypeApp c l <- asFTermF t; return (c,l)

isDataType :: (Monad f) => Ident -> Recognizer f [Term] a -> Recognizer f Term a
isDataType i p t = do
  (o,l) <- asDataType t
  if i == o then p l else fail "not datatype"

asNatLit :: (Monad f) => Recognizer f Term Nat
asNatLit t = do NatLit i <- asFTermF t; return (fromInteger i)

asStringLit :: (Monad f) => Recognizer f Term String
asStringLit t = do StringLit i <- asFTermF t; return i

asLambda :: (Monad m) => Recognizer m Term (String, Term, Term)
asLambda (unwrapTermF -> Lambda s ty body) = return (s, ty, body)
asLambda _ = fail "not a lambda"

asLambdaList :: Term -> ([(String, Term)], Term)
asLambdaList = go []
  where go r (asLambda -> Just (nm,tp,rhs)) = go ((nm,tp):r) rhs
        go r rhs = (reverse r, rhs)

asPi :: (Monad m) => Recognizer m Term (String, Term, Term)
asPi (unwrapTermF -> Pi nm tp body) = return (nm, tp, body)
asPi _ = fail "not a Pi term"

-- | Decomposes a term into a list of pi bindings, followed by a right
-- term that is not a pi binding.
asPiList :: Term -> ([(String, Term)], Term)
asPiList = go []
  where go r (asPi -> Just (nm,tp,rhs)) = go ((nm,tp):r) rhs
        go r rhs = (reverse r, rhs)

asLocalVar :: (Monad m) => Recognizer m Term DeBruijnIndex
asLocalVar (unwrapTermF -> LocalVar i) = return i
asLocalVar _ = fail "not a local variable"

asConstant :: (Monad m) => Recognizer m Term (String, Term, Term)
asConstant (unwrapTermF -> Constant s x t) = return (s, x, t)
asConstant _ = fail "asConstant: not a defined constant"

asExtCns :: (Monad m) => Recognizer m Term (ExtCns Term)
asExtCns t = do
  ftf <- asFTermF t
  case ftf of
    ExtCns ec -> return ec
    _         -> fail "asExtCns"

asSort :: (Monad m) => Recognizer m Term Sort
asSort t = do
  ftf <- asFTermF t
  case ftf of
    Sort s -> return s
    _      -> fail $ "asSort: " ++ showTerm t

-- | Returns term as a constant Boolean if it is one.
asBool :: (Monad f) => Recognizer f Term Bool
asBool (asCtor -> Just ("Prelude.True",  [])) = return True
asBool (asCtor -> Just ("Prelude.False", [])) = return False
asBool _ = fail "not bool"

asBoolType :: (Monad f) => Recognizer f Term ()
asBoolType = isDataType "Prelude.Bool" emptyl

asIntegerType :: (Monad f) => Recognizer f Term ()
asIntegerType = isDataType "Prelude.Integer" emptyl

asVectorType :: (Monad f) => Recognizer f Term (Term, Term)
asVectorType = isDataType "Prelude.Vec" r
  where r [n, t] = return (n, t)
        r _ = fail "asVectorType: wrong number of arguments"

isVecType :: (Monad f)
          => Recognizer f Term a -> Recognizer f Term (Nat :*: a)
isVecType tp = isDataType "Prelude.Vec" (asNatLit <:> endl tp)

asVecType :: (Monad f) => Recognizer f Term (Nat :*: Term)
asVecType = isVecType return

asBitvectorType :: (Alternative f, Monad f) => Recognizer f Term Nat
asBitvectorType =
  (isGlobalDef "Prelude.bitvector" @> asNatLit)
  <> isDataType "Prelude.Vec"
                (asNatLit <: endl (isDataType "Prelude.Bool" emptyl))

asMux :: (Monad f) => Recognizer f Term (Term :*: Term :*: Term :*: Term)
asMux = isGlobalDef "Prelude.ite" @> return <@> return <@> return <@> return
