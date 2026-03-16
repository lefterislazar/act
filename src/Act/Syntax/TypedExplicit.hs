{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE InstanceSigs #-}

{-|
Module      : Syntax.TypedExplicit
Description : AST data types where all implicit timings have been made explicit.
-}
module Act.Syntax.TypedExplicit (module Act.Syntax.TypedExplicit) where

import qualified Act.Syntax.Typed as Typed
import Act.Syntax.Typed (Timing(..),setPre,setPost)

-- Reexports
import Act.Syntax.Typed as Act.Syntax.TypedExplicit hiding (Timing(..),Timable(..),Time,Neither,Act,Contract,Invariant,InvariantPred,Constructor,Behaviour,StorageUpdate,TypedRef,Exp,TypedExp,Ref,Case(..),Block(..),Interaction)
import Act.Syntax.Typed as Act.Syntax.TypedExplicit (pattern Act, pattern Contract, pattern Invariant, pattern Constructor, pattern Behaviour, pattern Exp, pattern Case, pattern Block)


-- We shadow all timing-agnostic AST types with explicitly timed versions.
type Act              = Typed.Act              Timed
type Contract         = Typed.Contract         Timed
type Invariant        = Typed.Invariant        Timed
type InvariantPred    = Typed.InvariantPred    Timed
type Constructor      = Typed.Constructor      Timed
type Behaviour        = Typed.Behaviour        Timed
type StorageUpdate    = Typed.StorageUpdate    Timed
type TypedRef         = Typed.TypedRef         Timed
type Ref            k = Typed.Ref            k Timed
type Exp            a = Typed.Exp            a Timed
type TypedExp         = Typed.TypedExp         Timed
type Case             = Typed.Case             Timed
type Block            = Typed.Block            Timed
type Interaction      = Typed.Interaction     Timed

------------------------------------------
-- * How to make all timings explicit * --
------------------------------------------

instance Annotatable Typed.Act where
  annotate (Typed.Act store act) = Typed.Act store $ fmap annotate act

instance Annotatable Typed.Contract where
  annotate (Typed.Contract src ctor behv) = Typed.Contract src (annotate ctor) (fmap annotate behv)

instance Annotatable Typed.Invariant where
  annotate inv@Invariant{..} = inv
    { _ipreconditions = setPre <$> _ipreconditions
    , _istoragebounds = setPre <$> _istoragebounds
    , _predicate = annotate _predicate
    }

instance Annotatable Typed.InvariantPred where
  annotate (PredUntimed p) = PredTimed (setPre p) (setPost p)

instance Annotatable Typed.Constructor where
  annotate ctor@Constructor{..} = ctor
    { _cblock = annotate _cblock
    , _cpostconditions = setPost <$> _cpostconditions
    , _invariants  = annotate <$> _invariants
    }

instance Annotatable Typed.Behaviour where
  annotate behv@Behaviour{..} = behv
    { _block = annotate _block
    -- , _cases = annotate <$> _cases
    }

instance Annotatable Typed.TypedExp where
  annotate (Typed.TExp t e) = Typed.TExp t (setPre e)

instance Annotatable Typed.StorageUpdate where
  -- The timing in items only refers to the timing of mapping indices of a
  -- storage update. Hence, it should be Pre
  annotate :: Typed.StorageUpdate Untimed -> Typed.StorageUpdate Timed
  annotate (Typed.Update typ item expr) = Typed.Update typ (setPre item) (setPre expr)

instance Annotatable Typed.Case where
  annotate :: Typed.Case Untimed -> Typed.Case Timed
  annotate (Typed.Case pn cond effs) = Typed.Case pn (setPre cond) (annotate effs)

instance Annotatable Typed.Block where
  annotate :: Typed.Block Untimed -> Typed.Block Timed
  annotate (Block iffs cases) = Block (setPre <$> iffs) (annotate <$> cases)

instance Annotatable Typed.Effects where
  annotate :: Typed.Effects Untimed -> Typed.Effects Timed
  annotate (LocalOnly upds ret) = LocalOnly (annotate <$> upds) (annotate <$> ret)
  annotate (LocalAndInteraction upds inter next) = LocalAndInteraction (annotate <$> upds) (annotate inter) (annotate next)

instance Annotatable Typed.Interaction where
  annotate :: Typed.Interaction Untimed -> Typed.Interaction Timed
  annotate (TypedCallI pn static addr fn args val rets) = TypedCallI pn static (setPre addr) fn (setPre <$> args) (setPre <$> val) rets
  annotate (UntypedCallI pn static addr fn args val rets) = UntypedCallI pn static (setPre addr) fn (setPre <$> args) (setPre <$> val) rets
  annotate (CreateI pn addrVar contract args val) = CreateI pn addrVar contract (setPre <$> args) (setPre <$> val)
