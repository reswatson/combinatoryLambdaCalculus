
{-# OPTIONS --safe #-}
--{-# OPTIONS --without-K #-}
--{-# OPTIONS --guardedness #-}
{-# OPTIONS --no-main #-}
--{-# OPTIONS --cubical-compatible #-}

module combolambda where

open import Data.Nat -- hiding ( _≤_ )
open import Data.Fin renaming (pred to predF ; _+_ to _plus_) -- hiding  ( _≤_ )
open import Data.Maybe
open import Data.List.Base --hiding ( [_] )
--open import Data.Vec
open import Data.Product
open import Data.Bool
open import Data.Empty
open import Data.Sum --hiding ( [_,_] )
open import Relation.Binary.PropositionalEquality --hiding ( [_] )
open import Relation.Nullary.Negation
open import Data.Integer renaming ( _⊔_ to _⊔'_ ; suc to suc' ; pred to pred' ; _+_ to _+'_) 

---------------------------
-- PRELIMINARIES
---------------------------

false≡true→⊥ : false ≡ true → ⊥
false≡true→⊥ ()

a∨b≡c∨d-lemma : {a b c d : Bool} → a ≡ c → b ≡ d → a ∨ b ≡ c ∨ d
a∨b≡c∨d-lemma {a} {b} {.a} {.b} refl refl = refl

false-∨ : {bool1 bool2 : Bool} → (false ≡ bool1) → (false ≡ bool2) → false ≡ bool1 ∨ bool2
false-∨ {false} {false} refl refl = refl

∨-elim-left :  {bool1 bool2 : Bool} → (false ≡ bool1 ∨ bool2) → (false ≡ bool1)
∨-elim-left {false} {false} refl = refl

∨-elim-right :  {bool1 bool2 : Bool} → (false ≡ bool1 ∨ bool2) → (false ≡ bool2)
∨-elim-right {false} {false} refl = refl

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

Bool-Dec : (A : Bool) → (B : Bool) → Dec (A ≡ B)
Bool-Dec false false = yes refl
Bool-Dec false true = no λ ()
Bool-Dec true false = no λ ()
Bool-Dec true true = yes refl

A≡0∧B≡0→A⊔B≡0 : {A B : ℕ} → (A ≡ 0) → (B ≡ 0) → (A ⊔ B) ≡ 0
A≡0∧B≡0→A⊔B≡0 {.0} {.0} refl refl = refl

A⊔B≡B⊔A : (A : ℕ) → (B : ℕ) → (A ⊔ B) ≡ (B ⊔ A)
A⊔B≡B⊔A zero zero = refl
A⊔B≡B⊔A zero (suc B) = refl
A⊔B≡B⊔A (suc A) (zero) = refl
A⊔B≡B⊔A (suc A) (suc B) = cong (λ x → suc x) (A⊔B≡B⊔A A B)

x⊔-invariant : {x : ℕ} →  x ≡ (x ⊔ 0)
x⊔-invariant {x} = A⊔B≡B⊔A zero x

x≡x⊔x : {x : ℕ} →  x ≡ (x ⊔ x)
x≡x⊔x {zero} = refl
x≡x⊔x {suc x} = cong (λ x -> suc x) x≡x⊔x

predA⊔B≡predA⊔predB : {A B : ℕ} → (pred (A ⊔ B)) ≡ (pred A) ⊔ (pred B)
predA⊔B≡predA⊔predB {zero} {B} = refl
predA⊔B≡predA⊔predB {suc A} {zero} rewrite (A⊔B≡B⊔A A zero) = refl
predA⊔B≡predA⊔predB {suc A} {suc B} = refl 

term-scope-lemma-hlp : (scope : ℕ) →  suc scope ≡ (scope ⊔ (suc scope)) 
term-scope-lemma-hlp zero = refl
term-scope-lemma-hlp (suc scope) = cong (λ x -> suc x) (term-scope-lemma-hlp scope)

∧-elim-left : {A B : Bool} -> A ∧ B ≡ true → A ≡ true
∧-elim-left {true} {B} prf = refl

∧-elim-right : {A B : Bool} -> A ∧ B ≡ true → B ≡ true
∧-elim-right {A} {true} prf = refl
∧-elim-right {false} {false} prf = prf
∧-elim-right {true} {false} prf = prf

∧-def : {A B : Bool} -> A ≡ true → B ≡ true → (A ∧ B) ≡ true
∧-def {false} {B} = λ z _ → z
∧-def {true} {B} = λ _ z → z

+-assoc : Set
+-assoc = ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z

+-assoc-proof : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+-assoc-proof zero y z = refl
+-assoc-proof (suc x) y z = cong suc (+-assoc-proof x y z)

+-comm :  {a b : ℕ} → (a + b) ≡ (b + a)
+-comm {zero} {zero} = refl
+-comm {zero} {suc b} = cong (λ x -> suc x) (+-comm {0}{b})
+-comm {suc a} {zero} = cong (λ x -> suc x) (+-comm {a}{0})
+-comm {suc a} {suc b} = cong (λ x -> suc x) (trans step3 (+-comm {suc a}{b})) 
                       where
                         step1 : a + (1 + b) ≡ (a + 1) + b
                         step1 = +-assoc-proof a 1 b
                         step2 : (a + 1) + b ≡ (1 + a) + b
                         step2 = cong (λ x -> x + b) (+-comm {a}{1})
                         step3 : a + suc b ≡ suc a + b
                         step3 = trans step1 step2

n≡n+0 : {n : ℕ} → n ≡ n + 0
n≡n+0 {n} = +-comm {zero}{n}

pred0≡0 : pred 0 ≡ 0
pred0≡0 = refl

predSuc-id : {n : ℕ} → pred (suc n) ≡ n
predSuc-id {zero} = refl
predSuc-id {suc n} = refl

sucPred-id : {n : ℕ} → suc (pred (suc n)) ≡ (suc n)
sucPred-id {zero} = refl
sucPred-id {suc n} = refl

suc'Pred'-id : {n : ℤ} → suc' (pred' n) ≡ n
suc'Pred'-id {+_ zero} = refl
suc'Pred'-id {+[1+ n ]} = refl
suc'Pred'-id { -[1+_] zero} = refl
suc'Pred'-id { -[1+_] (suc n)} = refl

0≡Sucx→⊥ : {x : ℕ} -> 0 ≡ suc x -> ⊥
0≡Sucx→⊥ {zero} ()
0≡Sucx→⊥ {suc x} ()

predn≢0 : {n : ℕ} → pred n ≢ 0 → n ≢ 0
predn≢0 {zero} prd = prd
predn≢0 {suc n} prd = λ x → 0≡Sucx→⊥ (sym x)

predX≡sucn→X≡sucsucn : {x n : ℕ} → (pred x) ≡ (suc n) → x ≡ (suc (suc n))
predX≡sucn→X≡sucsucn {suc .1} {zero} refl = refl
predX≡sucn→X≡sucsucn {suc .(2+ n)} {suc n} refl = refl

x+sucy≡sucx+y : {x y : ℕ} -> (x + (suc y)) ≡ suc (x + y)
x+sucy≡sucx+y {x} {zero} = trans (+-comm {x}{1}) (cong (λ x -> suc x) n≡n+0) 
x+sucy≡sucx+y {zero} {suc y} = refl
x+sucy≡sucx+y {suc x} {suc y} = cong (λ x -> suc x) x+sucy≡sucx+y

suc≡suc-lemma : {x y : ℕ} → (suc x ≡ suc y) → x ≡ y
suc≡suc-lemma {x} {.x} refl = refl

suc-lemma-right : {x y z : ℕ} → x + y ≡ z → x + (suc y) ≡ (suc z)
suc-lemma-right {x} {y} {.(x + y)} refl = x+sucy≡sucx+y

ℕ-Dec : (A : ℕ) → (B : ℕ) → Dec (A ≡ B)
ℕ-Dec zero zero = yes refl
ℕ-Dec zero (suc B) = no (λ ())
ℕ-Dec (suc A) zero = no (λ ())
ℕ-Dec (suc A) (suc B) with ℕ-Dec A B  
...                    | no x = no (λ z → x (suc≡suc-lemma z))
...                    | yes y = yes (cong (λ z → suc z) y)

_<=_ : ℕ → ℕ → Bool
zero <= b = true
suc a <= zero = false
suc a <= suc b = a <= b

_==_ : ℕ → ℕ → Bool
zero == zero = true
zero == suc b = false
suc a == zero = false
suc a == suc b = a == b

ℕ<=-Dec : (A : ℕ) → (B : ℕ) → Dec ((A <= B) ≡ true)
ℕ<=-Dec zero zero = yes refl
ℕ<=-Dec zero (suc B) = yes refl
ℕ<=-Dec (suc A) zero = no (λ ())
ℕ<=-Dec (suc A) (suc B) = ℕ<=-Dec A B

<=-def-hlp : {y z : ℕ} →  Σ-syntax ℕ (λ x → x + y ≡ z) →  Σ-syntax ℕ (λ x → x + (suc y) ≡ (suc z))
<=-def-hlp (fst , snd) = fst , (suc-lemma-right snd)

<=-def : {m n : ℕ} → (m <= n) ≡ true → Σ[ x ∈ ℕ ] (x + m ≡ n)
<=-def {zero} {zero} m<=n = zero , refl
<=-def {zero} {suc n} m<=n = (suc n) , cong (λ x -> suc x) (trans (+-comm {n}{zero}) refl)
<=-def {suc m} {suc n} m<=n =  <=-def-hlp (<=-def m<=n)

predn>0 : {n : ℕ} →  pred (suc n) ≢ 0 → (1 <= n) ≡ true
predn>0 {zero} prd = ⊥-elim (prd refl)
predn>0 {suc n} prd = refl

predn>1 : {n : ℕ} → pred n ≢ 0 → 2 <= n ≡ true
predn>1 {zero} prd = ⊥-elim (prd refl)
predn>1 {suc n} prd = predn>0 prd

x⊔y<=n-elim-left : {x y n : ℕ} → ((x ⊔ y) <= n) ≡ true → x <= n ≡ true
x⊔y<=n-elim-left {zero} {zero} {zero} eqn = refl
x⊔y<=n-elim-left {suc x} {zero} {zero} eqn = eqn
x⊔y<=n-elim-left {suc x} {suc y} {zero} eqn = eqn
x⊔y<=n-elim-left {zero} {zero} {suc n} eqn = refl
x⊔y<=n-elim-left {zero} {suc y} {suc n} eqn = refl
x⊔y<=n-elim-left {suc x} {zero} {suc n} eqn = eqn
x⊔y<=n-elim-left {suc x} {suc y} {suc n} eqn = x⊔y<=n-elim-left {x}{y}{n} eqn

x⊔y<=n-elim-right : {x y n : ℕ} → ((x ⊔ y) <= n) ≡ true → y <= n ≡ true
x⊔y<=n-elim-right {zero} {zero} {zero} eqn = refl
x⊔y<=n-elim-right {suc x} {zero} {zero} eqn = refl
x⊔y<=n-elim-right {suc x} {suc y} {zero} eqn = eqn
x⊔y<=n-elim-right {zero} {zero} {suc n} eqn = refl
x⊔y<=n-elim-right {zero} {suc y} {suc n} eqn = eqn
x⊔y<=n-elim-right {suc x} {zero} {suc n} eqn = refl
x⊔y<=n-elim-right {suc x} {suc y} {suc n} eqn = x⊔y<=n-elim-right {x}{y}{n} eqn

x⊔y<=n-intro : {x y n : ℕ} → (x <= n) ≡ true → y <= n ≡ true → ((x ⊔ y) <= n) ≡ true
x⊔y<=n-intro {zero} {zero} {n} xn yn = refl
x⊔y<=n-intro {zero} {suc y} {n} xn yn = yn
x⊔y<=n-intro {suc x} {zero} {n} xn yn = xn
x⊔y<=n-intro {suc x} {suc y} {suc n} xn yn = x⊔y<=n-intro {x}{y}{n} xn yn

x⊔y<=n-intro' : {x y n : ℕ} → (x <= n) ≡ true → y <= n ≡ true → ((x ⊔ (y ⊔ 0)) <= n) ≡ true
x⊔y<=n-intro' {zero} {zero} {n} xn yn = refl
x⊔y<=n-intro' {zero} {suc y} {n} xn yn = yn
x⊔y<=n-intro' {suc x} {zero} {n} xn yn = xn
x⊔y<=n-intro' {suc x} {suc y} {suc n} xn yn = x⊔y<=n-intro {x}{y}{n} xn yn

m==n-def : {m n : ℕ} → (m == n) ≡ true → m ≡ n
m==n-def {zero} {zero} m==n = refl
m==n-def {suc m} {suc n} m==n = cong (λ x → suc x) (m==n-def m==n)

minus : (a : ℕ) → (b : ℕ) → (b <= a ≡ true) →  ℕ
minus a zero b<=a = a
minus (suc a) (suc b) b<=a = minus a b b<=a

0∸d≡0 : {d : ℕ} ->  0 ∸ d ≡ 0
0∸d≡0 {zero} = refl
0∸d≡0 {suc d} = refl

NatPredSuc≡ : {n m : ℕ} → suc n ≡ suc m → n ≡ m
NatPredSuc≡ {zero} {zero} eq = refl
NatPredSuc≡ {suc n} {suc .n} refl = refl

+swapSuc : {n m : ℕ} → (suc n) + m ≡ n + (suc m)
+swapSuc {n} {zero} = trans lemma2 (+-comm {1}{n})
                 where
                   lemma : (n + zero) ≡ n
                   lemma = +-comm {n}{0}
                   lemma2 : suc (n + zero) ≡ 1 + n
                   lemma2 = cong (λ x → suc x) lemma
+swapSuc {zero} {suc m} = refl
+swapSuc {suc n} {suc m} = cong (λ x → suc x) +swapSuc

∸NatCancel :  {n m d : ℕ} → n ∸ d ≡ suc m → n ≡ (suc m) + d
∸NatCancel {.(suc m)} {m} {zero} refl = cong (λ x → suc x) n≡n+0
∸NatCancel {suc n} {m} {suc d} eq = cong (λ x → suc x) (trans lemma lemma2)
                              where
                                lemma : n ≡ (suc m) + d
                                lemma = ∸NatCancel eq
                                lemma2 : (suc m) + d ≡ m + (suc d)
                                lemma2 = +swapSuc
                             
NatPredSuc≡' :  {n m d : ℕ} → (suc n) ∸ d ≡ suc m → n ∸ d ≡ m
NatPredSuc≡' {n} {m} {zero} x = NatPredSuc≡ x
NatPredSuc≡' {zero} {m} {suc d} x = ⊥-elim (0≡Sucx→⊥ {m} (trans (sym (0∸d≡0 {d})) x))
NatPredSuc≡' {suc n} {m} {suc d} x = NatPredSuc≡' {n}{m}{d} x

Justx≡justy→x≡y : {ty : Set} → {x y : ty} → (just x) ≡ (just y) → x ≡ y
Justx≡justy→x≡y {ty} {x} {.x} refl = refl

nothing≢just : {ty : Set} → {x : ty} → nothing ≡ just x → ⊥
nothing≢just {ty} {x} ()

just≢nothing : {ty : Set} → {x : ty} → just x ≡ nothing → ⊥
just≢nothing {ty} {x} ()  
  
------------------------------
-- BASIC DEFINITIONS
------------------------------

infixl 7 _·_

-- TERMS --

mutual
 data Term : Set
 Scope : (trm : Term) → ℕ

 data Term where
   Self     : Term                                  -- a special constant 
   `_       : (x : ℕ) -> Term                       -- variables
   Λ        : (n : ℕ) → (trm : Term) → {scoping : ((Scope trm) <= n) ≡ true} → Term   -- Λ term with n+1 arguments 
   _·_      : Term → Term → Term                  

 Scope Self = 0                                     
 Scope (` x) = x
 Scope (Λ n trm) = 0
 Scope (trm1 · trm2) = (Scope trm1) ⊔ (Scope trm2)
-----

-- Basic functions using Terms --

·head : Term → Term
·head Self = Self
·head (` x) = (` x)
·head (Λ n trm {scoping}) =  (Λ n trm {scoping})
·head (trm1 · trm2) = ·head trm1  

Application-Count : (trm : Term) → ℕ
Application-Count Self = 0
Application-Count (` x) = 0
Application-Count (Λ n trm) = 0
Application-Count (trm1 · trm2) = suc (Application-Count trm1)

Arity : (trm : Term) → ℕ
Arity Self = 0
Arity (` x) = 0
Arity (Λ n trm) = suc n
Arity (trm1 · trm2) = pred (Arity trm1)

Arity' : (trm : Term) → ℤ  -- this goes negative to record over-application
Arity' Self = + zero
Arity' (` x) = + zero
Arity' (Λ n trm) = + (suc n)
Arity' (trm1 · trm2) = pred' (Arity' trm1)

isLambda? : (trm : Term) → Bool
isLambda? Self = false
isLambda?  (` x) = false
isLambda? (Λ n trm) = true
isLambda? (trm1 · trm2) = false

isLambda?n : (n : ℕ) → (trm : Term) → Bool
isLambda?n n Self = false
isLambda?n n (` x) = false
isLambda?n n (Λ m trm) with ℕ-Dec n m 
...                       | no x = false
...                       | yes x = true
isLambda?n n (trm1 · trm2) = false

isLambda?→n : {trm : Term} → (isl : isLambda? trm ≡ true) → ℕ
isLambda?→n {Λ n trm} refl = n

isLambda?→inner : {trm : Term} → isLambda? trm ≡ true → Term
isLambda?→inner {Λ n trm} isl = trm

`x≡`y→x≡y : {x y : ℕ} → (` x) ≡ (` y) → x ≡ y
`x≡`y→x≡y {zero} {zero} xy = refl
`x≡`y→x≡y {suc x} {suc y} xy = cong (λ w → suc w) (`x≡`y→x≡y (hlp xy)) 
                                where
                                  hlp : {x y : ℕ} → (` suc x) ≡ (` suc y) →  (` x) ≡ (` y)
                                  hlp {x} {.x} refl = refl

·-elim-left : {trm1 trm3 trm2 trm4 : Term} → trm1 · trm3 ≡ trm2 · trm4 → trm1 ≡ trm2
·-elim-left refl = refl

·-elim-right : {trm1 trm3 trm2 trm4 : Term} → trm1 · trm3 ≡ trm2 · trm4 → trm3 ≡ trm4
·-elim-right refl = refl

scoping≡ : {x n : ℕ} → (scoping1 : (x <= n) ≡ true) → (scoping2 : (x <= n) ≡ true) → scoping1 ≡ scoping2
scoping≡ {zero} {zero} refl refl = refl
scoping≡ {zero} {suc n} refl refl = refl
scoping≡ {suc x} {suc n} scoping1 scoping2 = scoping≡ {x}{n} scoping1 scoping2

·Scoping-elim-left : {n : ℕ} → {trm1 trm2 : Term} → ((Scope trm1 ⊔ Scope trm2) <= n) ≡ true → (Scope trm1 <= n) ≡ true
·Scoping-elim-left {n} {trm1}{trm2} eqn = x⊔y<=n-elim-left {Scope trm1}{Scope trm2} {n} eqn

·Scoping-elim-right : {n : ℕ} → {trm1 trm2 : Term} → ((Scope trm1 ⊔ Scope trm2) <= n) ≡ true → (Scope trm2 <= n) ≡ true
·Scoping-elim-right {n} {trm1}{trm2} eqn = x⊔y<=n-elim-right {Scope trm1}{Scope trm2} {n} eqn

⊔Scoping : {m : ℕ} → {trm1 trm2 : Term} → (Scope trm1 <= m) ≡ true → (Scope trm2 <= m) ≡ true →  ((Scope trm1 ⊔ Scope trm2) <= m) ≡ true
⊔Scoping {m}{trm1}{trm2} scp1 scp2 = x⊔y<=n-intro {Scope trm1}{Scope trm2}{m} scp1 scp2

⊔Scoping' :  {m : ℕ} → {trm1 trm2 : Term} → (Scope trm1 <= m) ≡ true → (Scope trm2 <= m) ≡ true → ((Scope trm1 ⊔ (Scope trm2 ⊔ 0)) <= m) ≡ true
⊔Scoping' {m} {trm1} {trm2} scp1 scp2 = x⊔y<=n-intro' {Scope trm1} {Scope trm2} {m} scp1 scp2

-- Combine two Λ terms with same arity
combineΛ : {trm1 : Term} → isLambda? trm1 ≡ true  → {trm2 : Term} → isLambda? trm2 ≡ true → Arity trm1 ≡ Arity trm2 → Term
combineΛ {Λ m trm1 {scoping1}} refl {Λ .m trm2 {scoping2}} refl refl = Λ m (trm1 · trm2) {⊔Scoping {m} {trm1} {trm2} scoping1 scoping2}

¬trm1≡trm2→¬trm1·trm3≡trm2·trm4 : {trm1 trm3 trm2 trm4 : Term} → ¬ trm1 ≡ trm2 → ¬ (trm1 · trm3 ≡ trm2 · trm4)
¬trm1≡trm2→¬trm1·trm3≡trm2·trm4  ¬trm12 = λ w → ¬trm12 (·-elim-left w)

¬trm3≡trm4→¬trm1·trm3≡trm2·trm4 : {trm1 trm3 trm2 trm4 : Term} → ¬ trm3 ≡ trm4 → ¬ (trm1 · trm3 ≡ trm2 · trm4)
¬trm3≡trm4→¬trm1·trm3≡trm2·trm4  ¬trm12 = λ w → ¬trm12 (·-elim-right w)

Λn≡Λm→n≡m : {n m : ℕ} → {trm1 trm2 : Term} → {scoping1 : (Scope trm1 <= n) ≡ true} → {scoping2 : (Scope trm2 <= m) ≡ true} → (Λ n trm1 {scoping1}) ≡ (Λ m trm2 {scoping2}) → n ≡ m
Λn≡Λm→n≡m {n} {.n} {trm1} {.trm1} {scoping1} {.scoping1} refl = refl

Λtrm1≡Λtrm2→trm1≡trm2 : {n m : ℕ} → {trm1 trm2 : Term} → {scoping1 : (Scope trm1 <= n) ≡ true} → {scoping2 : (Scope trm2 <= m) ≡ true} → (Λ n trm1 {scoping1}) ≡ (Λ m trm2 {scoping2}) → trm1 ≡ trm2
Λtrm1≡Λtrm2→trm1≡trm2 {n} {.n} {trm1} {.trm1} {scoping1} {.scoping1} refl = refl

¬trm1≡trm2→¬Λntrm1≡Λmtrm2 : ∀ {n m : ℕ}  → {trm1 trm2 : Term} → ∀ {scoping1 : (Scope trm1 <= n) ≡ true} → ∀  {scoping2 : (Scope trm2 <= m) ≡ true} →  ¬ trm1 ≡ trm2 → ¬ Λ n trm1 {scoping1} ≡ Λ m trm2 {scoping2}
¬trm1≡trm2→¬Λntrm1≡Λmtrm2 {n}{m}{trm1}{trm2} {scoping1}{scoping2} ineq = λ x → ineq (Λtrm1≡Λtrm2→trm1≡trm2 x)

trm1≡trm→Λntrm1≡Λmtrm2-hlp : {n : ℕ} → {trm1 : Term} → {scoping1 scoping2 : (Scope trm1 <= n) ≡ true} →  Λ n trm1 {scoping1} ≡ Λ n trm1 {scoping2}
trm1≡trm→Λntrm1≡Λmtrm2-hlp {n} {trm1} {scoping1} {scoping2} = cong (λ w → Λ n trm1 {w}) (scoping≡ {Scope trm1} {n}  scoping1 scoping2)

trm1≡trm→Λntrm1≡Λmtrm2 : {n m : ℕ} → (eqn : n ≡ m) → {trm1 trm2 : Term} → {scoping1 : (Scope trm1 <= n) ≡ true} → {scoping2 : (Scope trm2 <= m) ≡ true} → (eqn2 : trm1 ≡ trm2) → Λ n trm1 {scoping1} ≡ Λ m trm2 {scoping2}
trm1≡trm→Λntrm1≡Λmtrm2 {n} {.n} refl {Self} {.Self} {refl} {refl} refl = refl
trm1≡trm→Λntrm1≡Λmtrm2 {n} {.n} refl {` x} {.(` x)} {scoping1} {scoping2} refl with scoping≡ {x} {n} scoping1 scoping2
... | refl = refl
trm1≡trm→Λntrm1≡Λmtrm2 {n} {.n} refl {Λ m trm1} {.(Λ m trm1)} {refl} {refl} refl = refl
trm1≡trm→Λntrm1≡Λmtrm2 {n} {.n} refl {trm1 · trm2} {.(trm1 · trm2)} {scoping1} {scoping2} refl = trm1≡trm→Λntrm1≡Λmtrm2-hlp

------------------------------------
-- Definitional Equality of Terms --
------------------------------------

term-Dec : (trm1 : Term) → (trm2 : Term) → Dec (trm1 ≡ trm2)
term-Dec Self Self = yes refl
term-Dec Self (` x) = no (λ ())
term-Dec Self (Λ n trm2) = no (λ ())
term-Dec Self (trm2 · trm3) = no (λ ())
term-Dec (` x) Self = no (λ ())
term-Dec (` x) (` y) with ℕ-Dec x y 
...                   | no w = no (λ v → w (`x≡`y→x≡y v))
...                   | yes w = yes (cong (λ v → ` v) w)
term-Dec (` x) (Λ n trm2) = no (λ ())
term-Dec (` x) (trm2 · trm3) = no (λ ())
term-Dec (Λ n trm1) Self = no (λ ())
term-Dec (Λ n trm1) (` x) = no (λ ())
term-Dec (Λ n trm1 {scoping1}) (Λ m trm2 {scoping2}) with ℕ-Dec n m 
term-Dec (Λ n trm1 {scoping1}) (Λ m trm2 {scoping2})  | yes x with term-Dec trm1 trm2
term-Dec (Λ n trm1 {scoping1}) (Λ m trm2 {scoping2})  | yes x  | yes y = yes (trm1≡trm→Λntrm1≡Λmtrm2 x y) 
term-Dec (Λ n trm1 {scoping1}) (Λ m trm2 {scoping2})  | yes x  | no y = no (¬trm1≡trm2→¬Λntrm1≡Λmtrm2 y)  
term-Dec (Λ n trm1 {scoping1}) (Λ m trm2 {scoping2})  | no x = no λ w → x (Λn≡Λm→n≡m w)
term-Dec (Λ n trm1) (trm2 · trm3) = no (λ ())
term-Dec (trm1 · trm3) Self = no (λ ())
term-Dec (trm1 · trm3) (` x) = no (λ ())
term-Dec (trm1 · trm3) (Λ n trm2) = no (λ ())
term-Dec (trm1 · trm3) (trm2 · trm4) with (term-Dec trm1 trm2) | (term-Dec trm3 trm4) 
...                                  | yes x | yes y = yes (cong₂ (λ a b → a · b) x y)
...                                  | yes x | no y = no (¬trm3≡trm4→¬trm1·trm3≡trm2·trm4 y)
...                                  | no x  | yes y =  no (¬trm1≡trm2→¬trm1·trm3≡trm2·trm4 x)
...                                  | no x  | no y =  no (¬trm1≡trm2→¬trm1·trm3≡trm2·trm4 x)


Term-Eq : Term → Term → Bool
Term-Eq trm1 trm2 with term-Dec trm1 trm2 
...                    | no x = false
...                    | yes y = true

-----------------
-- Combinators --
-----------------

-- A combinator is a Term constructed from Λ terms and application alone --
-- variables must be put inside a Λ term, so, for example (S x) shall be written:  Λ 0 (S (` 0) {refl})  --

S : Term 
S =  Λ 2 ((((` 2) · (` 0))) · (((` 1) ·  (` 0)))) {refl}

ExampleSx : Term
ExampleSx =  Λ 0 (S · (` 0)) {refl}

-- A combinator: 
isCombinator : Term → Bool
isCombinator Self = false
isCombinator (` x) = false
isCombinator (Λ n trm) = true
isCombinator (trm1 · trm2) = isCombinator trm1 ∧ isCombinator trm2

-- Compare the following two definitions to understand how variables are expressed in combinator terms:
-- This shows how variables are to be wrapped in a Λ:
isCombinatorSx : isCombinator ExampleSx ≡ true
isCombinatorSx = refl

is¬CombinatorSx : isCombinator (S · (` 0)) ≡ false
is¬CombinatorSx = refl

CombinatorScope0 : {trm : Term} → isCombinator trm ≡ true → (Scope trm <= zero) ≡ true
CombinatorScope0 {Λ n trm} refl = refl
CombinatorScope0 {trm1 · trm2} isc = ⊔Scoping {zero}{trm1}{trm2} (CombinatorScope0 {trm1} (∧-elim-left isc)) (CombinatorScope0 {trm2} (∧-elim-right isc))

-- COMBINATORS --

K : Term                                               -- K combinator (1)
K = (Λ 1 (` 1) {refl})                                               
I : Term                                               -- I combinator (0)
I = (Λ 0 (` 0) {refl})                                              
B : Term                                               -- B combinator 2(10)
B = (Λ 2 ((` 2) · ((` 1) · (` 0))) {refl})                   
C : Term                                               -- C combinator (201)
C = (Λ 2 ((` 2) · ((` 0)) · ((` 1))) {refl})                    
S' : Term                                              -- S' combinator 3(20)(10)   
S' = (Λ 3 ((` 3) · ((` 2) · (` 0)) · ((` 1) · (` 0))) {refl})
B3 : Term                                              -- B' combinator of Turner [Joy, Axford] 32(10)
B3 = (Λ 3 (((` 3) · (  (` 2))) · ((` 1) · (` 0))) {refl})
C' : Term                                              -- C' of Turner 3(20)1
C' = (Λ 3 ((` 3) · (((` 2)) · ((` 0))) · (` 1)) {refl})
B' : Term                                              -- B' combinator 1(20)
B' = (Λ 2 ((` 1) · ((` 2) · (` 0))) {refl})
M : Term                                               -- M combinator (00)
M = (Λ 0 ((` 0) · (` 0)) {refl}) 
W : Term                                               -- W combinator (100)
W = (Λ 1 ((` 1) · (` 0) · (` 0) ) {refl}) 
J' : Term                                              -- J combinator 32(301)
J' = (Λ 3 (((` 3) · ((` 2))) · ((` 3) · (` 0) · (` 1)) ) {refl})

R : Term                                               -- R is the Ruslan combinator
R = Λ 2 (` 2) {refl}                                   -- requires all three arguments

R2 : Term                                              -- requires 2 arguments before evaluation
R2 =  Λ 1 ((Λ 1 (` 1) {refl}) · (` 1)) {refl}

R3 : Term                                              -- evaluates in steps, more like a regular λ term
R3 =  Λ 0 ((Λ 1 ((Λ 1 (` 1) {refl}) · (` 1)) {refl}) · (` 0)) {refl}

-- The improper Y combinator 
-- Here we can see the relative disadvantage of the present calculus in terms of some verbosity.
-- However, there is also the advantage that De Bruijn index manipulation is much less as each sub-Λ-term is itself a combinator: 
Yλ : Term
Yλ = (Λ 0 (
            ((Λ 1 ((` 1) · (` 0) · (` 0)) {refl}) · (` 0)) · ((Λ 1 ((` 1) · (` 0) · (` 0)) {refl}) · (` 0))      
          ) {refl})

-- Alternative definition: Y will be substituted into Self
Y : Term
Y =  (Λ 0 (
            (` 0) · (Self · (` 0))      
          ) {refl})

-- definitional equality makes Y and Yλ different terms:
Y≢Yλ : Y ≢ Yλ
Y≢Yλ with term-Dec Y Yλ
... | no x = λ ()
... | yes x = λ ()


-- Inspired by To Mock A Mockingbird, new combinators can be made by compositionality:

Comp : {trm1 : Term} -> {trm2 : Term} → isCombinator trm1 ≡ true → isCombinator trm2 ≡ true -> Term
Comp {trm1} {trm2} isc1 isc2 = Λ 0 (trm1 · (trm2 · ` 0)) {⊔Scoping' {zero}{trm1}{trm2} scoping1 scoping2}
                        where
                          scoping1 : (Scope trm1 <= zero) ≡ true
                          scoping1 = CombinatorScope0 {trm1} isc1
                          scoping2 : (Scope trm2 <= zero) ≡ true
                          scoping2 = CombinatorScope0 {trm2} isc2

-- Combinators compose to form combinators:
CompComb : {A B : Term} → (isc1 : isCombinator A ≡ true) → (isc2 : isCombinator B ≡ true) → isCombinator (Comp {A}{B} isc1 isc2) ≡ true
CompComb {A}{B} iscA iscB = refl

-- A base combinator (in the event we want them) is any lambda term
-- that contains no further lamda terms.
-- A basis is a list of chosen base combinators:

noLambdas? : (trm : Term) → Bool
noLambdas? Self = true
noLambdas? (` x) = true
noLambdas? (Λ n trm) = false
noLambdas? (trm1 · trm2) = (noLambdas? trm1) ∧ (noLambdas? trm2)

isBase? : (trm : Term) → Bool
isBase? trm with isLambda? trm in isl
...          | false = false
...          | true = noLambdas? (isLambda?→inner isl)

SKI-Basis : List (Σ[ trm ∈ Term ] (isBase? trm ≡ true))
SKI-Basis =  (S , refl) ∷ (K , refl) ∷ (I , refl) ∷ []

Empty-Basis : List (Σ[ trm ∈ Term ] (isBase? trm ≡ true))
Empty-Basis = []

Turner-Basis : List (Σ[ trm ∈ Term ] (isBase? trm ≡ true))
Turner-Basis  = (S , refl) ∷ (K , refl) ∷ (I , refl) ∷ (B , refl) ∷ (C , refl) ∷ (S' , refl) ∷ (B3 , refl) ∷ (C' , refl ) ∷ (Y , refl) ∷ []

-- A further difference between Y and Yλ:
NoticeThatYλIsNotBase : isBase? Yλ ≡ false
NoticeThatYλIsNotBase = refl

------------------------------------------
-- SUBSTITUTION AND APPLICATION : STEPS --
------------------------------------------

-- Top level substitution of Self
SelfSub : (self : Term) → (trm : Term) → Term
SelfSub self Self = self          
SelfSub self (` x) = (` x)
SelfSub self (Λ n trm {scoping}) = (Λ n trm {scoping})
SelfSub self (trm1 · trm2) =  (SelfSub self trm1) · (SelfSub self trm2)

Substitute : (n : ℕ) → (target : Term) → (arg : Term) → Term
Substitute n Self arg = Self
Substitute n (` x) arg with ℕ-Dec n x 
...                | no w = (` x)
...                | yes w = arg 
Substitute n (Λ m target {scoping}) arg = (Λ m target {scoping})
Substitute n (target1 · target2) arg = Substitute n target1 arg · Substitute n target2 arg

Scopetrm<=n≡true→ : {n : ℕ} → {trm trm' : Term} → (scoping : (Scope trm <= n) ≡ true) → (scoping' : (Scope trm' <= n) ≡ true) → (Scope (SelfSub (Λ n trm' {scoping'}) trm) <= n) ≡ true
Scopetrm<=n≡true→ {n} {Self} {trm'} scoping scoping' = scoping
Scopetrm<=n≡true→ {n} {` x} {trm'} scoping scoping' = scoping
Scopetrm<=n≡true→ {n} {Λ m trm} {trm'} scoping scoping' = scoping
Scopetrm<=n≡true→ {n} {trm1 · trm2} {trm'} scoping scoping' = ⊔Scoping {n}{SelfSub (Λ n trm') trm1}{SelfSub (Λ n trm') trm2} scopetrmSelf scopetrm'Self
                                         where
                                           scopetrm :  (Scope trm1 <= n) ≡ true
                                           scopetrm = ·Scoping-elim-left {n} {trm1}{trm2} scoping
                                           scopetrm' : (Scope trm2 <= n) ≡ true
                                           scopetrm' = ·Scoping-elim-right {n} {trm1}{trm2} scoping
                                           scopetrmSelf : (Scope (SelfSub (Λ n trm' {scoping'}) trm1) <= n) ≡ true
                                           scopetrmSelf = Scopetrm<=n≡true→ {n}{trm1}{trm'} scopetrm scoping'
                                           scopetrm'Self : (Scope (SelfSub (Λ n trm' {scoping'}) trm2) <= n) ≡ true
                                           scopetrm'Self = Scopetrm<=n≡true→  {n}{trm2}{trm'} scopetrm' scoping'
                                           
-- This function takes a Λ term and plugs in Λtrm to top level Self.
SubΛ-base : (Λtrm : Term) → (isl : isLambda? Λtrm ≡ true) → Term
SubΛ-base (Λ n (trm1 · trm2) {scoping}) refl = Λ n ((SelfSub (Λ n (trm1 · trm2) {scoping}) trm1)
                                                  · (SelfSub (Λ n (trm1 · trm2) {scoping}) trm2)) {uScope} 
          where
            scopetrm1' : (Scope (SelfSub (Λ n (trm1 · trm2) {scoping}) trm1) <= n) ≡ true
            scopetrm1' = Scopetrm<=n≡true→ {n} {trm1}{trm1 · trm2} (x⊔y<=n-elim-left {Scope trm1}{Scope trm2}{n} scoping) scoping
            scopetrm2' : (Scope (SelfSub (Λ n (trm1 · trm2) {scoping}) trm2) <= n) ≡ true
            scopetrm2' = Scopetrm<=n≡true→ {n} {trm2}{trm1 · trm2} (x⊔y<=n-elim-right {Scope trm1}{Scope trm2}{n} scoping) scoping
            uScope : (((Scope (SelfSub (Λ n (trm1 · trm2) {scoping}) trm1))
                        ⊔  (Scope (SelfSub (Λ n (trm1 · trm2) {scoping}) trm2))) <= n) ≡ true
            uScope = ⊔Scoping {n} {SelfSub (Λ n (trm1 · trm2) {scoping}) trm1}
                        {SelfSub (Λ n (trm1 · trm2) {scoping}) trm2} scopetrm1' scopetrm2'        
SubΛ-base (Λ n trm {scoping}) isl = Λ n (SelfSub (Λ n trm {scoping}) trm) {Scopetrm<=n≡true→ {n} {trm} {trm} scoping scoping}
            
AppFold : {n : ℕ} → (trm : Term) → {arity : Arity' trm ≡ + n} → {isc : isCombinator trm ≡ true} → Term
AppFold {.suc n} (Λ m trm {scoping}) {refl} {refl} = SubΛ-base (Λ m trm {scoping}) refl
AppFold {n} (trm1 · trm2) {arity} {isc} = Substitute n (AppFold {suc n} trm1 {trans (sym suc'Pred'-id) (cong (λ w → suc' w) arity)} {∧-elim-left isc}) trm2   -- Substitute trm2 into  (` n) at top level of Appfolded trm1

-- REDUCTION STEPS --

-- A type that expresses when a term can reduce to another term without imposing a specific reduction strategy.
-- Note that only application is without a prior 'step' (see terms called 'legit'),
-- thus a single step is a single set of applications in one appFold.
data Step : Term → Term → Set where
  left-step : {trm1 : Term} → {trm2 : Term} → {trm1' : Term} → (legit : Step trm1 trm1' ) → Step (trm1 · trm2) (trm1' · trm2)
  right-step : {trm1 : Term} → {trm2 : Term} → {trm2' : Term} → (legit : Step trm2 trm2') → Step (trm1 · trm2) (trm1 · trm2')
  Λ-step : {Λtrm : Term} → {Λtrm' : Term} → (isl : isLambda? Λtrm ≡ true) → (isl' : isLambda? Λtrm' ≡ true)
               → (legit : Step (isLambda?→inner {Λtrm} isl)  (isLambda?→inner {Λtrm'} isl')) → Step Λtrm Λtrm'
  appFold : {trm : Term} → (arity : Arity' trm ≡ + zero) → (isc : isCombinator trm ≡ true) → Step trm (AppFold trm {arity} {isc})

