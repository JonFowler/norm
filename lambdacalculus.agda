module lambdacalculus where

open import Data.Vec
open import Data.Nat
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

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
   [] : {e : Exp Γ t} → e ⇒* e
   _∷_ :  {e e' e'' : Exp Γ t} → e ⇒ e' → e' ⇒* e'' → e ⇒* e''
   
data _⇒|_ {n : ℕ}{t : Type}{Γ : Cxt n} : Exp Γ t → Val Γ t → Set where
  norm : {e : Exp Γ t} {a : Val Γ t} → e ⇒* val a → e ⇒| a
  
data Env : {n : ℕ} → Cxt n → Set where
  [] : Env []
  _∷_ : {n : ℕ}{t : Type}{Γ : Cxt n} → (e : Exp Γ t) → (s : Env Γ) → Env (t ∷ Γ)
  
_+*_ : ∀ {n t}{Γ : Cxt n}{e e' e'' : Exp Γ t} → 
        e ⇒* e' → e' ⇒* e'' → e ⇒* e''
_+*_ [] q = q
_+*_ (x ∷ p) q = x ∷ (p +* q)

⇒*-app : ∀ {n u t}{Γ : Cxt n}{e e' : Exp Γ (u ↦ t)}{e'' : Exp Γ u}{er : Exp Γ t} → 
        e ⇒* e' → app e' e'' ⇒* er → app e e'' ⇒* er 
⇒*-app [] q = q
⇒*-app (x ∷ p) q = ⇒app x  ∷ ⇒*-app p q

envG : ∀ {m n t}  {Γ : Cxt m} → (Δ : Cxt n) → Exp (Δ ++ Γ) t → Env Γ → Exp Δ t
envVG : ∀ {m n t} {Γ : Cxt m} → (Δ : Cxt n) → Val (Δ ++ Γ) t → Env Γ → Val Δ t
envVar : ∀ {m n t} {Γ : Cxt m} → (Δ : Cxt n) → (x : Fin (n + m)) → (Δ ++ Γ) [ x ]= t → Env Γ → Exp Δ t ⊎ Σ (Fin n) (λ x → Δ [ x ]= t)
envVar [] zero here (e ∷ s) = inj₁ (envG [] e s)
envVar [] (suc x) (there p) (e ∷ s) = envVar [] x p s
envVar (t ∷ Δ) zero here s = inj₂  (zero , here)
envVar (t ∷ Δ) (suc x) (there p) s with envVar Δ x p s
envVar (t ∷ Δ) (suc x) (there p) s | inj₁ e = inj₁ (t ∷E e) 
envVar (t ∷ Δ) (suc x) (there p) s | inj₂ (x' , p') = inj₂ (suc x' , there p')

envG Δ (val a) s = val (envVG Δ a s)
envG Δ (var v ty) s with envVar Δ v ty s 
envG Δ (var v ty) s | inj₁ x = x
envG Δ (var v ty) s | inj₂ (v' , ty') = var v' ty'
envG Δ (if e then e₁ else e₂) s = if envG Δ e s then envG Δ e₁ s else envG Δ e₂ s
envG Δ (app e e₁) s = app (envG Δ e s) (envG Δ e₁ s)

envVG Δ true s = true
envVG Δ false s = false
envVG Δ (ƛ {u = u} f) s = ƛ (envG (u ∷ Δ) f s)

_⟪_⟫ : ∀ {n t} {Γ : Cxt n} → Exp Γ t → Env Γ → Exp [] t
e ⟪ s ⟫ = envG [] e s

_⟪V_⟫ : ∀ {n t} {Γ : Cxt n} → Val Γ t → Env Γ → Val [] t
e ⟪V s ⟫ = envVG [] e s

Norm : ∀{n t}{Γ : Cxt n} → Exp Γ t → Set
Norm {t = t} {Γ = Γ} e = Σ (Val Γ t) (λ a → e ⇒| a )

SN : (t : Type) → Exp [] t → Set
SN' : (t : Type) → Exp [] t → Set

SN t e = SN' t e × Norm e

SN' bool e = Fin 1
SN' (u ↦ t) e =  ((e' : Exp [] u) → SN u e' → SN t (app e e'))



lem⇒ : (t : Type){e e' : Exp [] t}
         → e ⇒ e' → SN t e'  → SN t e
lem⇒ bool p (q , a , norm x) = zero , a , norm (p ∷ x)  
lem⇒ (u ↦ t) {e}{e'} p (f , a , norm x) = l , a , norm (p ∷ x)
  where l : (ev : Exp [] u) → SN u ev → SN t (app e ev)
        l ev sn with f ev sn
        l ev sn | sn' = lem⇒ t (⇒app p) sn'
        
lem⇒* : (t : Type){e e' : Exp [] t}
         → e ⇒* e' → SN t e'  → SN t e
lem⇒* t [] sn = sn
lem⇒* t (x ∷ p) sn = lem⇒ t x (lem⇒* t p sn)
        
⇒-uniq : ∀{n}{t : Type}{Γ : Cxt n}{e e' e'' : Exp Γ t} → e ⇒ e' → e ⇒ e'' → e' ≡ e''
⇒-uniq ⇒iftrue ⇒iftrue = refl
⇒-uniq ⇒iftrue (⇒ifred ())
⇒-uniq ⇒iffalse ⇒iffalse = refl
⇒-uniq ⇒iffalse (⇒ifred ())
⇒-uniq (⇒ifred ()) ⇒iftrue
⇒-uniq (⇒ifred ()) ⇒iffalse
⇒-uniq (⇒ifred {e1 = e1}{e2} p) (⇒ifred q) = cong (λ z → if z then e1 else e2) (⇒-uniq p q)
⇒-uniq (⇒app {e = e} p) (⇒app q) = cong (λ z → app z e) (⇒-uniq p q)
⇒-uniq (⇒app ()) ⇒subs
⇒-uniq ⇒subs (⇒app ())
⇒-uniq ⇒subs ⇒subs = refl
        
lem<= : (t : Type){e e' : Exp [] t}
         → e ⇒ e' → SN t e  → SN t e'
lem<= bool () (proj₁ , proj₂ , norm [])
lem<= bool p (proj₁ , proj₂ , norm (x ∷ x₁)) with ⇒-uniq p x
lem<= bool p (proj₁ , proj₂ , norm (x ∷ x₁)) | refl = proj₁ , proj₂ , norm x₁
lem<= (t ↦ t₁) () (proj₁ , proj₂ , norm [])
lem<= (t ↦ t₁) p (proj₁ , proj₂ , norm (x ∷ x₁)) with ⇒-uniq p x
lem<= (t ↦ t₁) p (f , proj₂ , norm (x ∷ x₁)) | refl = 
  (λ e' x₂ → lem<= t₁ (⇒app x) (f e' x₂)) , (proj₂ , norm x₁) 
  
lem<=* : (t : Type){e e' : Exp [] t}
         → e ⇒* e' → SN t e  → SN t e'
lem<=* t [] sn = sn
lem<=* t (x ∷ p) sn = lem<=* t p (lem<= t x sn)

mapIf : ∀{n} {Γ : Cxt n} {t : Type}  {e e' : Exp Γ bool} {e1 e2 : Exp Γ t} 
      → e ⇒* e' → if e then e1 else e2 ⇒* if e' then e1 else e2
mapIf [] = []
mapIf (x ∷ p) = ⇒ifred x ∷ mapIf p

ifLem :  (t : Type) {e : Exp [] bool} {e1 e2 : Exp [] t} → 
          e ⇒* val true → SN t e1 → SN t (if e then e1 else e2)
ifLem bool p (proj₁ , a , norm x₁) = proj₁ , a , norm (mapIf p +* (⇒iftrue ∷ x₁))
ifLem (t ↦ t₁) {e}{e1}{e2} p (f , a , norm x) =  l , a , norm (mapIf p +* (⇒iftrue ∷ x))
  where l : (ev : Exp [] t) → SN t ev → SN t₁ (app (if e then e1 else e2) ev)
        l ev p' with f ev p'          
        l ev (b , a , q) | b' , a' , q' = {!!} , ({!!} , {!!}) 
        
ras : ∀ {t m n}{Δ : Cxt m} (Γ : Cxt n) →
    (x : Fin m) → Δ [ x ]= t → Σ (Fin (m + n)) (λ x' → (Δ ++ Γ [ x' ]= t))
ras Γ zero here = zero , here
ras Γ (suc x) (there p) with ras Γ x p 
ras Γ (suc x) (there p) | x' , p' = suc x' , there p'

genE : ∀ {t m n o}(Δ : Cxt m){Γ : Cxt n}{Γ' : Cxt o} → 
     (∀{t' m'}(Δ' : Cxt m')(x : Fin (m' + n)) → Δ' ++ Γ [ x ]= t' → 
            Exp (Δ' ++ Γ') t'  ⊎ Σ (Fin (m' + o)) (λ x' → Δ' ++ Γ' [ x' ]= t') ) → 
     Exp (Δ ++ Γ) t → Exp (Δ ++ Γ') t

genV : ∀ {t m n o}(Δ : Cxt m){Γ : Cxt n}{Γ' : Cxt o} → 
   (∀{t' m'}(Δ' : Cxt m')(x : Fin (m' + n)) → Δ' ++ Γ [ x ]= t' → 
            Exp (Δ' ++ Γ') t'  ⊎ Σ (Fin (m' + o)) (λ x' → Δ' ++ Γ' [ x' ]= t') ) → 
   Val (Δ ++ Γ) t → Val (Δ ++ Γ') t
genV Δ P true = true
genV Δ P false = false
genV Δ P (ƛ {u = u} f) = ƛ (genE (u ∷ Δ) P f)

genE Δ P (val a) = val (genV Δ P a)
genE Δ P (var v ty) with P Δ v ty 
genE Δ P (var v ty) | inj₁ x = x
genE Δ P (var v ty) | inj₂ (proj₁ , proj₂) = var proj₁ proj₂
genE Δ P (if e then e₁ else e₂) = if genE Δ P e then genE Δ P e₁ else genE Δ P e₂
genE Δ P (app e e₁) = app (genE Δ P e) (genE Δ P e₁)

addΓV : ∀ {t m n}{Δ : Cxt m} (Γ : Cxt n) → Val Δ t → Val (Δ ++ Γ) t
addΓ  : ∀ {t m n}{Δ : Cxt m} (Γ : Cxt n) → Exp Δ t → Exp (Δ ++ Γ) t
addΓ Γ (val a) = val (addΓV Γ a)
addΓ {m = m} Γ (var v ty) with ras Γ v ty
addΓ Γ (var v ty) | proj₁ , proj₂ = var proj₁ proj₂ 
addΓ Γ (if e then e₁ else e₂) = if addΓ Γ e then addΓ Γ e₁ else addΓ Γ e₂
addΓ Γ (app e e₁) = app (addΓ Γ e) (addΓ Γ e₁)

addΓV Γ true = true
addΓV Γ false = false
addΓV {Δ = Δ} Γ (ƛ {u = u} f) = ƛ (addΓ {Δ = u ∷ Δ} Γ f) 

--  (λ e'' x → ? ) 

⇒normLem : ∀ {n} {Γ : Cxt n} → (t : Type) → 
         (e : Exp Γ t) → (s : Env Γ) → SN t (e ⟪ s ⟫)
⇒normLem bool (val a) s = zero , a ⟪V s ⟫ , norm [] 
⇒normLem {Γ = Γ} (u ↦ t₁) (val (ƛ f)) s = (λ e' x → lem⇒ t₁ {!!} (z e' x)) , ƛ (envG (u ∷ []) f s)  , norm []
  where z : (e' : Exp [] u) → SN u e' → SN t₁ (f ⟪ addΓ Γ e' ∷ s ⟫) 
        z e' x = ⇒normLem t₁ f (_∷_ (addΓ Γ e') s) 
⇒normLem t (var zero here) (e ∷ s) = {!!} -- ⇒normLem t e s
⇒normLem t (var (suc v) (there ty)) (e ∷ s) = ⇒normLem t (var v ty) s
⇒normLem t (if e then e₁ else e₂) s with ⇒normLem bool e s 
⇒normLem t (if e then e₁ else e₂) s | r , true , p with ⇒normLem t e₁ s
⇒normLem t (if e then e₁ else e₂) s | r , true , norm x | a 
  = let l = mapIf{e1 = e₁ ⟪ s ⟫}{e₂ ⟪ s ⟫} x +* (⇒iftrue ∷ []) in lem⇒* t l a
⇒normLem t (if e then e₁ else e₂) s | r , false , p = {!!}
⇒normLem t (app {u = u} e e') s = {!!}  
⇒norm : (t : Type) {e : Exp [] t} → SN t e → Norm e 
⇒norm t (b , p) = p 

data _⇓_ {n : ℕ}{t : Type}{Γ : Cxt n} : Exp Γ t → Val Γ t → Set where
   ⇓val : (a : Val Γ t) → val a ⇓ a
   ⇓iftrue : {e : Exp Γ bool}{e1 e2 : Exp Γ t}{a : Val Γ t} → 
       e ⇓ true → e1 ⇓ a → if e then e1 else e2 ⇓ a
   ⇓iffalse : {e : Exp Γ bool}{e1 e2 : Exp Γ t}{a : Val Γ t} → 
       e ⇓ false → e1 ⇓ a → if e then e1 else e2 ⇓ a
   ⇓app : ∀{u}{f : Exp Γ (u ↦ t)}{f' : Exp (u ∷ Γ) t}{e : Exp Γ u}
           {a : Val Γ t} → (f ⇓ ƛ f') → (f' ⟨ e ⟩ ⇓ a) → app f e ⇓ a

