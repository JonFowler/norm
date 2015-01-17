module lambdacalculus where

open import Data.Vec
open import Data.Nat
open import Data.Fin

data Type : Set where
  bool : Type
  _↦_ : Type → Type → Type
  
Cxt : ℕ → Set
Cxt n = Vec Type n

data Val {n : ℕ} (Γ : Cxt n) : Type → Set 

data Exp {n : ℕ} (Γ : Cxt n) : Type → Set where
   val : {t : Type} → (a : Val Γ t) → Exp Γ t
   var : {t : Type} → (x : Fin n) → Γ [ x ]= t → Exp Γ t
   if_then_else_ : {t : Type} → (e : Exp Γ bool) → (e1 : Exp Γ t) → (e2 : Exp Γ t) → Exp Γ t
   app : {u t : Type} → (f : Exp Γ (u ↦ t)) → (e : Exp Γ u) → Exp Γ t

data Val {n : ℕ} (Γ : Cxt n) where
  true : Val Γ bool
  false : Val Γ bool
  ƛ : {u t : Type} → (f : Exp (u ∷ Γ) t) → Val Γ (u ↦ t)
  
