module lambdacalculus where

open import Data.Vec
open import Data.Nat
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Sum
open import Data.Product

data Type : Set where
  bool : Type
  _↦_ : Type → Type → Type
  
Cxt : ℕ → Set
Cxt n = Vec Type n

data Val {n : ℕ} (Γ : Cxt n) : Type → Set 

data Exp {n : ℕ} (Γ : Cxt n) : Type → Set where
   val : {t : Type} → (a : Val Γ t) → Exp Γ t
   var : {t : Type} → (v : Fin n) → (ty : Γ [ v ]= t) → Exp Γ t
   if_then_else_ : {t : Type} → (e : Exp Γ bool) → (e1 : Exp Γ t) → (e2 : Exp Γ t) → Exp Γ t
   app : {u t : Type} → (f : Exp Γ (u ↦ t)) → (e : Exp Γ u) → Exp Γ t

data Val {n : ℕ} (Γ : Cxt n) where
  true : Val Γ bool
  false : Val Γ bool
  ƛ : {u t : Type} → (f : Exp (u ∷ Γ) t) → Val Γ (u ↦ t)
  
swapE : {m n : ℕ} {s : Type} {Γ : Cxt n} {t t1 : Type} (Δ : Cxt m)  → 
      Exp (Δ ++ t ∷ t1 ∷ Γ) s → Exp (Δ ++ t1 ∷ t ∷ Γ) s
swapV : {m n : ℕ} {s : Type}  {Γ : Cxt n} {t t1 : Type} (Δ : Cxt m) → 
      Val (Δ ++ t ∷ t1 ∷ Γ) s → Val (Δ ++ t1 ∷ t ∷ Γ) s

swapVar : ∀{m n}{Γ : Cxt n}{s : Type}{t t1 : Type} → (Δ : Cxt m) → (x : Fin (m + suc (suc n))) → 
   (Δ ++ t ∷ t1 ∷ Γ) [ x ]= s → Σ (Fin (m + suc (suc n))) (λ x1 → (Δ ++ t1 ∷ t ∷ Γ) [ x1 ]= s )
swapVar [] zero here = suc zero , there here
swapVar [] (suc zero) (there here) = zero , here
swapVar [] (suc (suc x)) (there (there p)) = suc (suc x) , there (there p)
swapVar (s ∷ Δ) zero here = zero , here
swapVar (x ∷ Δ) (suc y) (there p) with swapVar Δ y p 
swapVar (x ∷ Δ) (suc y) (there p) | v , p' = (suc v) , (there p')

swapE Δ (val a) = val (swapV Δ a)
swapE Δ (var x p) with swapVar Δ x p
swapE Δ (var x p) | v , p' = var v p'
swapE Δ (if e then e1 else e2) = if (swapE Δ e) then (swapE Δ e1) else (swapE Δ e2)
swapE Δ (app f e) = app (swapE Δ f) (swapE Δ e) 

swapV Δ true = true
swapV Δ false = false 
swapV Δ (ƛ {u = u} e) = ƛ (swapE (u ∷ Δ) e)

_∷E_ : {n : ℕ} {s : Type} {Γ : Cxt n} → (t : Type) → Exp Γ s → Exp (t ∷ Γ) s
_∷V_ : {n : ℕ} {s : Type} {Γ : Cxt n} → (t : Type) → Val Γ s → Val (t ∷ Γ) s

t ∷E val a = val (t ∷V a)
t ∷E var v ty = var (suc v) (there ty)
t ∷E (if e then e₁ else e₂) = if (t ∷E e) then (t ∷E e₁) else (t ∷E e₂)
t ∷E app e e₁ = app (t ∷E e) (t ∷E e₁)

t ∷V true = true
t ∷V false = false 
t ∷V ƛ f = ƛ (swapE [] (t ∷E f))


  
subsV : {m n : ℕ}{t u : Type} (Δ : Cxt m) {Γ : Cxt n} → 
        Val (Δ ++ t ∷ Γ) u → Exp Γ t → Val (Δ ++ Γ) u
        
subVar : ∀ {m n t u} (Δ : Cxt m) {Γ : Cxt n } → 
       (x : Fin (m + suc n)) → (Δ ++ t ∷ Γ [ x ]= u)  → Exp Γ t →
       Σ (Fin (m + n)) (λ i → (Δ ++ Γ) [ i ]= u) ⊎ Exp (Δ ++ Γ) u
subVar [] zero here e' = inj₂ e'
subVar [] (suc x) (there p) e' = inj₁ (x , p)
subVar (u ∷ Δ) zero here e' = inj₁ (zero , here)
subVar (x ∷ Δ) (suc x₁) (there p) e' with subVar Δ x₁ p e'
subVar (x₂ ∷ Δ) (suc x₁) (there p) e' | inj₁ (x' , p') = inj₁ (suc x' , there p')
subVar (x ∷ Δ) (suc x₁) (there p) e' | inj₂ e'' = inj₂ (x ∷E e'')
  
subsE : {m n : ℕ}{t u : Type} (Δ : Cxt m) {Γ : Cxt n } → 
        Exp (Δ ++ t ∷ Γ) u → Exp Γ t → Exp (Δ ++ Γ) u
subsE Δ (val a) e' = val (subsV Δ a e')
subsE Δ (var v ty) e' with subVar Δ v ty e'
subsE Δ (var v ty) e' | inj₁ (v' , p') = var v' p'
subsE Δ (var v ty) e' | inj₂ y = y 
subsE Δ (if e then e₁ else e₂) e' = if (subsE Δ e e') then (subsE Δ e₂ e') else 
      (subsE Δ e₂ e')
subsE Δ (app f e) e' = app (subsE Δ f e') (subsE Δ e e')
  
subsV Δ true e' = true
subsV Δ false e' = false 
subsV Δ (ƛ {u = u} f) e' = ƛ (subsE (u ∷ Δ) f e')

_⟨_⟩ : ∀{ n u t } {Γ : Cxt n} → Exp (u ∷ Γ) t → Exp Γ u → Exp Γ t
f ⟨ e ⟩ = subsE [] f e

data _⇒_ {n : ℕ}{t : Type}{Γ : Cxt n} : Exp Γ t → Exp Γ t → Set where
  ⇒iftrue : {e1 e2 : Exp Γ t} → if (val true) then e1 else e2 ⇒ e1
  ⇒iffalse : {e1 e2 : Exp Γ t} → if (val false) then e1 else e2 ⇒ e1
  ⇒ifred : {e e' : Exp Γ bool} {e1 e2 : Exp Γ t} → e ⇒ e' →
         if e then e1 else e2 ⇒ if e' then e1 else e2
  ⇒app : {u : Type} {f f' : Exp Γ (u ↦ t)} {e : Exp Γ u} → f ⇒ f' → app f e ⇒ app f' e
  ⇒subs : {u : Type} {f : Exp (u ∷ Γ) t} {e : Exp Γ u} → app (val (ƛ f)) e ⇒  f ⟨ e ⟩ 
  
data _⇒*_ {n : ℕ}{t : Type}{Γ : Cxt n} : Exp Γ t → Exp Γ t → Set where
   _∷_ :  {e e' e'' : Exp Γ t} → e ⇒ e' → e' ⇒* e'' → e ⇒* e''
   [] : {e : Exp Γ t} → e ⇒* e

data _⇓_ {n : ℕ}{t : Type}{Γ : Cxt n} : Exp Γ t → Val Γ t → Set where
   ⇓val : (a : Val Γ t) → val a ⇓ a
   ⇓iftrue : {e : Exp Γ bool}{e1 e2 : Exp Γ t}{a : Val Γ t} → 
       e ⇓ true → e1 ⇓ a → if e then e1 else e2 ⇓ a
   ⇓iffalse : {e : Exp Γ bool}{e1 e2 : Exp Γ t}{a : Val Γ t} → 
       e ⇓ false → e1 ⇓ a → if e then e1 else e2 ⇓ a
   ⇓app : ∀{u}{f : Exp Γ (u ↦ t)}{f' : Exp (u ∷ Γ) t}{e : Exp Γ u}
           {a : Val Γ t} → (f ⇓ ƛ f') → (f' ⟨ e ⟩ ⇓ a) → app f e ⇓ a
