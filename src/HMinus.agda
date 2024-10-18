module HMinus 
  (TmVar : Set)  -- Term variables
  (TpVar : Set)  -- Type variables
  (Class : Set)  -- Class names
  (BaseTp : Set) -- Type constants
  (BaseTm : Set) -- Term constants
  (InstName : Set)   -- Instance names
  where

import Data.List.Relation.Unary.All using ([]; _∷_)
import Data.List
open Data.List using (List ; _∷_ ; [])
import Data.Maybe
open Data.Maybe using (Maybe)
import Data.Product
open Data.Product using (_,_; _×_)
import Data.String
open Data.String using (String)

data Type : Set where
  tpvar : (τ : TpVar) → Type
  tpbase : (K : BaseTp) → Type
  _⇒_ : Type → Type → Type

infixr 5 _⇒_

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
  constructor _＂∀＂_,_=>_ 
  field
    name : InstName
    tyvars : List TpVar 
    constraints : List Predicate 
    head : Predicate 

record ψ : Set where
  field
    Si : TmVar → Maybe (Predicate × Scheme)
    Im : InstName × TmVar → Maybe Tm
    Ax : List Axiom

postulate
  varName : String → TmVar
 
example : Tm
example = lam (varName "x") (tmvar (varName "x")) -- λx.x

open import Agda.Primitive

data _∈_ {A : Set} : (a : A) → (List A) → Set where
  insert : (a : A) → (as : List A) → a ∈ (a ∷ as)

liftTy : Type → Scheme
liftTy ty = SQualified (QBase ty)

data _∣_⊢_∶_ : (p : List Predicate) → (Γ : List (TmVar × Scheme)) → (M : Tm) → (σ : Scheme) → Set where
  Var : ∀ p Γ → (x : TmVar) → (σ : Scheme) → ( (x , σ) ∈ Γ) → p ∣ Γ ⊢ tmvar x ∶ σ
  [→I] : ∀ p Γ M → (x : TmVar) → (τ τ′ : Type) 
       → p ∣ ((x , liftTy τ) ∷ Γ) ⊢ M ∶ liftTy τ′ 
       -----------------------------
       → p ∣ Γ ⊢ (lam x M) ∶ (liftTy (τ ⇒ τ′))


exampleTy : (τ : Type) → [] ∣ [] ⊢ (lam (varName "x") (tmvar (varName "x"))) ∶ (liftTy (τ ⇒ τ)) 
exampleTy τ = [→I] [] [] (tmvar (varName "x")) (varName "x") τ τ 
  (Var [] ((varName "x" , liftTy τ) ∷ [])  (varName "x") (liftTy τ) (insert (varName "x" , liftTy τ) []))

-- Write the typing derivation for example
-- enumerate some more inference rules (App [])

-- exampleDeriv : []∣[]⊢_∶_ 