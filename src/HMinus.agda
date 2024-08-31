module HMinus 
  (TmVar : Set)  -- Term variables
  (TpVar : Set)  -- Type variables
  (Class : Set)  -- Class names
  (BaseTp : Set) -- Type constants
  (BaseTm : Set) -- Term constants
  (Inst : Set)   -- Instance names
  where

import Data.List.Relation.Unary.All using ([]; _∷_)
import Data.List
open Data.List using (List)
import Data.Maybe
open Data.Maybe using (Maybe)
import Data.Product
open Data.Product using (_,_; _×_)
import Data.String
open Data.String using (String)

data Type : Set where
  tpvar : (τ : TpVar) → Type
  tpbase : (K : BaseTp) → Type
  _↣_ : Type → Type → Type

infixr 5 _↣_

record Predicate : Set where
  field 
    classname : Class
    types : List Type

mutual
  data Qualified : Set where
    QBase : (τ : Type) → Qualified
    QConstraint : (π : Predicate) → (ρ : Qualified) → Qualified

  data Scheme : Set where
    SQualified : (ρ : Qualified) → Scheme
    STyVar : (t : TpVar) → (σ : Scheme) → Scheme

data Tm : Set where
  tmvar : TmVar → Tm
  basetm : BaseTm → Tm
  lam : (x : TmVar) → (M : Tm) → Tm
  app : (M : Tm) → (N : Tm) → Tm
  letin : (x : TmVar) → (M : Tm) → (N : Tm) → Tm
  fix : (x : TmVar) → (M : Tm) → Tm

record Axiom : Set where
  field
    name : Inst
    class : (t : List TpVar) → (P : List Predicate) → Predicate 

record ψ : Set where
  field
    Si : TmVar → Maybe (Predicate × Scheme)
    Im : Inst × TmVar → Maybe Tm
    Ax : Axiom

postulate
  varName : String → TmVar
  subst : TmVar → BaseTm
 
example : Tm
example = lam (varName "x") (Tm.basetm (subst (varName "x")))