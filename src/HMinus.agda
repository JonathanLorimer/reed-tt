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
open Data.List using (List ; _∷_ ; [] ; [_])
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
  className : String → Class
 
example : Tm
example = lam (varName "x") (tmvar (varName "x")) -- λx.x

open import Agda.Primitive

data _∈_ {A : Set} : (a : A) → (List A) → Set where
  bury : {a : A} → {as : List A} → (b : A) → a ∈ as → a ∈ (b ∷ as) 
  insert : (a : A) → (as : List A) → a ∈ (a ∷ as)

liftTy : Type → Scheme
liftTy ty = SQualified (QBase ty)

data _∣_⊢_∶_ : (P : List Predicate) → (Γ : List (TmVar × Scheme)) → (M : Tm) → (σ : Scheme) → Set where
  Var  : ∀ P Γ → (x : TmVar) → (σ : Scheme) 
       → ( (x , σ) ∈ Γ) 
       -----------------------------
       → P ∣ Γ ⊢ tmvar x ∶ σ

  [→I] : ∀ P Γ M → (x : TmVar) → (τ τ′ : Type) 
       → P ∣ ((x , liftTy τ) ∷ Γ) ⊢ M ∶ liftTy τ′ 
       -----------------------------
       → P ∣ Γ ⊢ (lam x M) ∶ (liftTy (τ ⇒ τ′))

  [→E] : ∀ P Γ M N → (τ τ′ : Type) 
       → P ∣ Γ ⊢ M ∶ (liftTy (τ ⇒ τ′))
       → P ∣ Γ ⊢ N ∶ (liftTy τ)
       -----------------------------
       → P ∣ Γ ⊢ app M N ∶ (liftTy τ′)

  μ    : ∀ P Γ M → (τ : Type) → (x : TmVar)
       → P ∣ ((x , liftTy τ) ∷ Γ) ⊢ M ∶ (liftTy τ)
       -----------------------------
       → P ∣ Γ ⊢ fix x M ∶ (liftTy τ) 

  [⇒I] : ∀ P Γ M → (π : Predicate) → (ρ : Qualified)
       → (π ∷ P) ∣ Γ ⊢ M ∶ SQualified ρ
       -----------------------------
       → P ∣ Γ ⊢ M ∶ SQualified (QConstraint π ρ) 
  
  [⇒E] : ∀ P Γ M → (π : Predicate) → (ρ : Qualified) 
       → P ∣ Γ ⊢ M ∶ SQualified (QConstraint π ρ) 
       → {! π !}
       -----------------------------
       → P ∣ Γ ⊢ M ∶ SQualified ρ

  [∀I] : {!   !}

  [∀E] : {!   !}

  Let  : {!   !}
    
 
open import Data.Nat

example-∈ : 2 ∈ (1 ∷ 2 ∷ [])
example-∈ = bury 1 (insert 2 [])

exampleTy : (τ : Type) → [] ∣ [] ⊢ (lam (varName "x") (tmvar (varName "x"))) ∶ (liftTy (τ ⇒ τ)) 
exampleTy τ = [→I] [] [] (tmvar (varName "x")) (varName "x") τ τ 
  (Var [] ((varName "x" , liftTy τ) ∷ [])  (varName "x") (liftTy τ) (insert (varName "x" , liftTy τ) []))

-- Write the typing derivation for example
-- enumerate some more inference rules (App [])
