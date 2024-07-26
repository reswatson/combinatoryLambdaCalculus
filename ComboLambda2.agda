{-# OPTIONS --safe #-}
{-# OPTIONS --with-K #-}
--{-# OPTIONS --guardedness #-}

module ComboLambda2 where

open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)

open import Data.Nat -- hiding ( _≤_ )
open import Data.Fin renaming (pred to predF ; _+_ to _plus_) -- hiding  ( _≤_ )
open import Data.Maybe
--open import Data.List
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

sym' : {ty : Set} → {a b : ty} → a ≢ b → b ≢ a
sym' {ty} {a} {.a} ab refl = ab refl

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

just-elim : {ty : Set} → {x y : ty} → (just x) ≡ (just y) → x ≡ y
just-elim {ty} {x} {.x} refl = refl

just-cong : {ty : Set} {x y : ty} → x ≡ y → just x ≡ just y
just-cong {ty} {x} {.x} refl = refl

nothing≢just : {ty : Set} → {x : ty} → nothing ≡ just x → ⊥
nothing≢just {ty} {x} ()

just≢nothing : {ty : Set} → {x : ty} → just x ≡ nothing → ⊥
just≢nothing {ty} {x} ()

just≢ℕ : {n : ℕ} → just +[1+ n ] ≡  just (+ 0) → ⊥
just≢ℕ {n} ()

just≢negpos : {n m : ℕ} → just ( -[1+ n ]) ≡ just ( +[1+ m ]) → ⊥
just≢negpos {n} {m} ()

just1+n≡m : {n m : ℕ} →  just +[1+ n ] ≡  just +[1+ m ] → n ≡ m
just1+n≡m {n} {.n} refl = refl

just≢0 : {n : ℕ} → just +[1+ n ] ≡ just (+ zero) → ⊥
just≢0 {n} ()

justx≢justy : {x y  : ℕ} → (x ≢ y) → just x ≢ just y
justx≢justy {x}{y} xy = λ z → xy (just-elim z) 

justx≢justyℤ : {x y  : ℤ} → (x ≢ y) → just x ≢ just y
justx≢justyℤ {x}{y} xy = λ z → xy (just-elim z) 

0≡Sucx→⊥ : {x : ℕ} -> 0 ≡ suc x -> ⊥
0≡Sucx→⊥ {zero} ()
0≡Sucx→⊥ {suc x} ()

x≡Sucx→⊥ : {x : ℕ} → x ≡ suc x -> ⊥
x≡Sucx→⊥ {zero} ()
x≡Sucx→⊥ {suc x} ()

z≡Suc'z→⊥ : {x : ℤ} → x ≡ suc' x -> ⊥
z≡Suc'z→⊥ { -[1+_] zero} ()
z≡Suc'z→⊥ { -[1+_] (suc n)} ()

justn≢justn+1 : {n : ℕ} → just (+ n) ≢ just (+ suc n)
justn≢justn+1 {n} = λ x → justx≢justyℤ {+ n} {+ suc n} (λ z → z≡Suc'z→⊥ z) x

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

A≡A'∧B≡B'→A⊔B≡A'⊔B' : {A B A' B' : ℕ} → (A ≡ A') → (B ≡ B') → (A ⊔ B) ≡ (A' ⊔ B')
A≡A'∧B≡B'→A⊔B≡A'⊔B' {A} {B} {.A} {.B} refl refl = refl

A⊔B≡B⊔A : (A : ℕ) → (B : ℕ) → (A ⊔ B) ≡ (B ⊔ A)
A⊔B≡B⊔A zero zero = refl
A⊔B≡B⊔A zero (suc B) = refl
A⊔B≡B⊔A (suc A) (zero) = refl
A⊔B≡B⊔A (suc A) (suc B) = cong (λ x → suc x) (A⊔B≡B⊔A A B)

x⊔-invariant : {x : ℕ} →  x ≡ (x ⊔ 0)
x⊔-invariant {x} = A⊔B≡B⊔A zero x

x⊔≡0-left-elim : {x y : ℕ} →  x ⊔ y ≡ 0 → x ≡ 0
x⊔≡0-left-elim {zero} {.0} refl = refl
x⊔≡0-left-elim {suc x} {suc y} xy = ⊥-elim (0≡Sucx→⊥ {_} (sym xy))

x⊔≡0-right-elim : {x y : ℕ} →  x ⊔ y ≡ 0 → y ≡ 0
x⊔≡0-right-elim {zero} {.0} refl = refl
x⊔≡0-right-elim {suc x} {suc y} xy = ⊥-elim (0≡Sucx→⊥ {_} (sym xy))

x≡x⊔x : {x : ℕ} →  x ≡ (x ⊔ x)
x≡x⊔x {zero} = refl
x≡x⊔x {suc x} = cong (λ x -> suc x) x≡x⊔x

x⊔x≡x : {x : ℕ} → (x ⊔ x) ≡ x
x⊔x≡x {x} = sym (x≡x⊔x {x})

x⊔x≡x' : {x y z : ℕ} → (y ≡ x) → (z ≡ x) → (y ⊔ z) ≡ x
x⊔x≡x' {x} {.x} {.x} refl refl = x⊔x≡x 

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

∧-intro : {A B : Bool} -> A ≡ true → B ≡ true → (A ∧ B) ≡ true
∧-intro {false} {B} = λ z _ → z
∧-intro {true} {B} = λ _ z → z

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

suc'+ℕ≢+0 : {n : ℕ} → +[1+ n ] ≢ (+ zero)
suc'+ℕ≢+0 {zero} = λ ()
suc'+ℕ≢+0 {suc n} = λ ()

pred'x≡z→x≡+1+z : {x z : ℤ} → (pred' x) ≡ z → x ≡ ((+ 1) +' z)
pred'x≡z→x≡+1+z {+_ zero} {.(pred' (+ zero))} refl = refl
pred'x≡z→x≡+1+z {+[1+ n ]} {.(pred' +[1+ n ])} refl = refl
pred'x≡z→x≡+1+z { -[1+_] n} {.(pred' -[1+ n ])} refl = refl

Predsuc-lemma : {n a : ℕ}  → (pred a ≡ suc n) → a ≡ suc (suc n)
Predsuc-lemma {zero} {suc .1} refl = refl
Predsuc-lemma {suc n} {suc .(2+ n)} refl = refl

Suc'Pred'≡ : {n : ℕ} → {z : ℤ}  → (pred' z ≡ + n) → z ≡ + suc n
Suc'Pred'≡ {n}{z} prd = trans (sym suc'Pred'-id) (cong (λ w → suc' w) prd)

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

ℤ→ℕ : ℤ → ℕ
ℤ→ℕ (+_ n) = n
ℤ→ℕ (-[1+_] n) = n

ℤ-Dec : (A : ℤ) → (B : ℤ) → Dec (A ≡ B)
ℤ-Dec (+_ n) (+_ m) with ℕ-Dec n m 
...                 | yes x = yes (cong (λ w → (+ w)) x)
...                 | no x = no λ w → x (cong (λ z → ℤ→ℕ z) w)
ℤ-Dec (+_ n) (-[1+_] m) = no (λ ())
ℤ-Dec (-[1+_] n) (+_ m) = no (λ ())
ℤ-Dec (-[1+_] n) (-[1+_] m) with ℕ-Dec n m 
...                 | yes x = yes (cong (λ w → -[1+  w ]) x)
...                 | no x = no (λ w → x (cong (λ z → ℤ→ℕ z) w))

Maybeℕ-Dec : (A : Maybe ℕ) → (B : Maybe ℕ) → Dec (A ≡ B)
Maybeℕ-Dec (just zero) (just zero) = yes refl
Maybeℕ-Dec (just zero) (just (suc y)) = no (λ ())
Maybeℕ-Dec (just (suc x)) (just zero) = no (λ ())
Maybeℕ-Dec (just (suc x)) (just (suc y)) with ℕ-Dec x y 
...                      | no z = no λ w → z (suc≡suc-lemma (just-elim w))
...                      | yes refl = yes refl
Maybeℕ-Dec (just x) nothing = no (λ ())
Maybeℕ-Dec nothing (just x) = no (λ ())
Maybeℕ-Dec nothing nothing = yes refl

_<=_ : ℕ → ℕ → Bool
zero <= b = true
suc a <= zero = false
suc a <= suc b = a <= b

_<='_ : ℤ → ℤ → Bool
+_ n <=' +_ m = n <= m
+_ n <=' -[1+_] m = false
-[1+_] n <=' +_ m = true
-[1+_] n <=' -[1+_] m = m <= n

suc<=suc : {a b : ℕ} → a <= b ≡ true → suc a <= suc b ≡ true
suc<=suc {zero} {b} refl = refl
suc<=suc {suc a} {suc b} a<=b = a<=b

<=suc : {a b : ℕ} → a <= b ≡ true → a <= suc b ≡ true
<=suc {zero} {b} ab = refl
<=suc {suc a} {suc b} ab = <=suc {a} {b} ab

trans<= : {a b c : ℕ} → a <= b ≡ true → b <= c ≡ true  → a <= c ≡ true
trans<= {zero} {zero} {zero} refl refl = refl
trans<= {zero} {zero} {suc c} refl refl = refl
trans<= {zero} {suc b} {suc c} refl bc = refl
trans<= {suc a} {suc b} {suc c} ab bc = trans<= {a}{b}{c} ab bc

sub<= :  {a a' n : ℕ} → (a ≡ a') → a <= n ≡ true → a' <= n ≡ true
sub<= {a} {.a} refl a<=n = a<=n

m<=0≡true→m≡0 : {m : ℕ} → (m <= 0) ≡ true → m ≡ 0
m<=0≡true→m≡0 {zero} refl = refl

_==_ : ℕ → ℕ → Bool
zero == zero = true
zero == suc b = false
suc a == zero = false
suc a == suc b = a == b

_=='_ : ℤ → ℤ → Bool
+_ n ==' +_ m = n == m
+_ n ==' -[1+_] m = false
-[1+_] n ==' +_ m = false
-[1+_] n ==' -[1+_] m = n == m

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

x<=x≡true : {x : ℕ} → (x <= x) ≡ true
x<=x≡true {zero} = refl
x<=x≡true {suc x} = x<=x≡true {x}

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

x⊔y<=n-intro : {x y n : ℕ} → (x <= n) ≡ true → (y <= n ≡ true) → ((x ⊔ y) <= n) ≡ true
x⊔y<=n-intro {zero} {zero} {n} xn yn = refl
x⊔y<=n-intro {zero} {suc y} {n} xn yn = yn
x⊔y<=n-intro {suc x} {zero} {n} xn yn = xn
x⊔y<=n-intro {suc x} {suc y} {suc n} xn yn = x⊔y<=n-intro {x}{y}{n} xn yn

x⊔y<=0-intro : {x y : ℕ} → (x <= 0) ≡ true → y <= 0 ≡ true → ((x ⊔ y) <= 0) ≡ true
x⊔y<=0-intro {zero} {zero} x0 y0 = refl

x⊔y<=n-intro' : {x y n : ℕ} → (x <= n) ≡ true → y <= n ≡ true → ((x ⊔ (y ⊔ 0)) <= n) ≡ true
x⊔y<=n-intro' {zero} {zero} {n} xn yn = refl
x⊔y<=n-intro' {zero} {suc y} {n} xn yn = yn
x⊔y<=n-intro' {suc x} {zero} {n} xn yn = xn
x⊔y<=n-intro' {suc x} {suc y} {suc n} xn yn = x⊔y<=n-intro {x}{y}{n} xn yn

x≡y→x<=y≡true : {x y : ℕ} → x ≡ y → (x <= y) ≡ true
x≡y→x<=y≡true {zero} {.zero} refl = refl
x≡y→x<=y≡true {suc x} {.(suc x)} refl = x≡y→x<=y≡true {x}{x} refl

x<=y→x<=y⊔n :  {x y n : ℕ} → (x <= y) ≡ true → (x <= (y ⊔ n)) ≡ true
x<=y→x<=y⊔n {zero} {zero} {n} xy = refl
x<=y→x<=y⊔n {zero} {suc y} {n} xy = refl
x<=y→x<=y⊔n {suc x} {suc y} {zero} xy = xy
x<=y→x<=y⊔n {suc x} {suc y} {suc n} xy = x<=y→x<=y⊔n {x}{y}{n} xy

x<=y→x=x'→x'<=y :  {x x' y : ℕ} → (x <= y) ≡ true → (x ≡ x') → (x' <= y) ≡ true
x<=y→x=x'→x'<=y {x} {.x} {y} xy refl = xy

x<=y→x<=n⊔y : {x y n : ℕ} → (x <= y) ≡ true → (x <= (n ⊔ y)) ≡ true
x<=y→x<=n⊔y {zero} {y} {n} xy = refl
x<=y→x<=n⊔y {suc x} {suc y} {zero} xy = xy
x<=y→x<=n⊔y {suc x} {suc y} {suc n} xy = x<=y→x<=n⊔y {x}{y}{n} xy

x<=y→x⊔y⊔ : {x y n : ℕ} → (x <= y) ≡ true → ((x ⊔ n) <= (y ⊔ n)) ≡ true
x<=y→x⊔y⊔ {zero} {y} {zero} xy = refl
x<=y→x⊔y⊔ {suc x} {suc y} {zero} xy = xy
x<=y→x⊔y⊔ {zero} {zero} {suc n} xy = x<=y→x⊔y⊔ {zero}{zero}{n} refl
x<=y→x⊔y⊔ {zero} {suc y} {suc n} xy = x<=y→x⊔y⊔ {zero}{y}{n} refl
x<=y→x⊔y⊔ {suc x} {suc y} {suc n} xy = x<=y→x⊔y⊔ {x}{y}{n} xy

x⊔n⊔n<=x⊔n≡true : {x n : ℕ} → ((x ⊔ n ⊔ n) <= (x ⊔ n)) ≡ true
x⊔n⊔n<=x⊔n≡true {zero} {zero} = refl
x⊔n⊔n<=x⊔n≡true {suc x} {zero} = x<=x≡true {x}
x⊔n⊔n<=x⊔n≡true {zero} {suc n} = x⊔n⊔n<=x⊔n≡true {zero} {n}
x⊔n⊔n<=x⊔n≡true {suc x} {suc n} = x⊔n⊔n<=x⊔n≡true {x}{n}

x<=y→u<=v→x⊔u<=y⊔v :  {x y u v : ℕ} → (x <= y) ≡ true → (u <= v) ≡ true → ((x ⊔ u) <= (y ⊔ v)) ≡ true
x<=y→u<=v→x⊔u<=y⊔v {zero} {zero} {zero} {zero} xy = λ _ → refl
x<=y→u<=v→x⊔u<=y⊔v {zero} {zero} {zero} {suc v} xy = λ _ → refl
x<=y→u<=v→x⊔u<=y⊔v {zero} {zero} {suc u} {v} xy = λ z → z
x<=y→u<=v→x⊔u<=y⊔v {zero} {suc y} {zero} {v} xy = λ _ → refl
x<=y→u<=v→x⊔u<=y⊔v {zero} {suc y} {suc u} {zero} xy = λ ()
x<=y→u<=v→x⊔u<=y⊔v {zero} {suc y} {suc u} {suc v} xy = x<=y→u<=v→x⊔u<=y⊔v {zero}{y}{u}{v} refl
x<=y→u<=v→x⊔u<=y⊔v {suc x} {suc y} {zero} {zero} xy = λ _ → xy
x<=y→u<=v→x⊔u<=y⊔v {suc x} {suc y} {zero} {suc v} xy = λ _ → x<=y→x<=y⊔n {x}{y}{v} xy
x<=y→u<=v→x⊔u<=y⊔v {suc x} {suc y} {suc u} {zero} xy = λ ()
x<=y→u<=v→x⊔u<=y⊔v {suc x} {suc y} {suc u} {suc v} xy = x<=y→u<=v→x⊔u<=y⊔v {x}{y}{u}{v} xy

x<=n→xy→y<=n : {x y n : ℕ} → (x <= n) ≡ true → (x ≡ y) → (y <= n) ≡ true
x<=n→xy→y<=n {x} {.x} {n} xn refl = xn

⊔<=-right-distr : {x y n : ℕ} → (((x ⊔ n) ⊔ (y ⊔ n)) <= (x ⊔ y ⊔ n)) ≡ true
⊔<=-right-distr {zero} {zero} {zero} = refl
⊔<=-right-distr {zero} {zero} {suc n} = ⊔<=-right-distr {zero}{zero}{n}
⊔<=-right-distr {zero} {suc y} {zero} = x<=x≡true {y}
⊔<=-right-distr {zero} {suc y} {suc n} = ⊔<=-right-distr {zero}{y}{n}
⊔<=-right-distr {suc x} {zero} {zero} = x<=x≡true {x}
⊔<=-right-distr {suc x} {zero} {suc n} = x⊔n⊔n<=x⊔n≡true {x}{n}
⊔<=-right-distr {suc x} {suc y} {zero} =  x<=x≡true {x ⊔ y} 
⊔<=-right-distr {suc x} {suc y} {suc n} = ⊔<=-right-distr {x}{y}{n}

x⊔y<=n-left-elim : {x y n : ℕ} → ((x ⊔ y) <= n) ≡ true → (x <= n) ≡ true
x⊔y<=n-left-elim {zero} {zero} {n} xy = refl
x⊔y<=n-left-elim {zero} {suc y} {n} xy = refl
x⊔y<=n-left-elim {suc x} {zero} {n} xy = xy
x⊔y<=n-left-elim {suc x} {suc y} {suc n} xy = x⊔y<=n-left-elim {x}{y}{n} xy

x⊔y<=n-right-elim : {x y n : ℕ} → ((x ⊔ y) <= n) ≡ true → (y <= n) ≡ true
x⊔y<=n-right-elim {zero} {zero} {n} xy = refl
x⊔y<=n-right-elim {zero} {suc y} {n} xy = xy
x⊔y<=n-right-elim {suc x} {zero} {n} xy = refl
x⊔y<=n-right-elim {suc x} {suc y} {suc n} xy = x⊔y<=n-right-elim {x}{y}{n} xy

n≡x<=-lemma : {n x : ℕ} → ¬ (suc n) ≡ x → (x <= suc n) ≡ true → (x <= n) ≡ true
n≡x<=-lemma {zero} {zero} sx xs = refl
n≡x<=-lemma {zero} {suc zero} sx refl = ⊥-elim (sx refl)
n≡x<=-lemma {suc n} {zero} sx refl = refl
n≡x<=-lemma {suc n} {suc x} sx xs = n≡x<=-lemma {n} {x} (λ y → sx (cong suc y)) xs

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

-- K-like properties

K-bool : {a : Bool} → (atrue : a ≡ true) → (atrue' : a ≡ true) → atrue ≡ atrue'
K-bool {true} refl refl = refl

K-bool' : {a b : Bool} → (ab : a ≡ b) → (ab' : a ≡ b) → ab ≡ ab'
K-bool' {false} {.false} refl refl = refl
K-bool' {true} {.true} refl refl = refl

cong-a≡b-lemma : {a b : ℕ} (ab : a ≡ b) → (cong pred (cong suc ab) ≡ ab) 
cong-a≡b-lemma {a} {.a} refl = refl

K-Ax : {ty : Set} {x : ty} → (p : x ≡ x) -> p ≡ refl
K-Ax refl = refl

AB-K : {A : Set}{a : A}{b : A} → (ab : a ≡ b) → (ab' : a ≡ b) → ab ≡ ab'
AB-K {A} {a} {.a} refl refl = refl

K-Maybeℤ : {A B : Maybe ℤ} → (AB : A ≡ B) → (AB' : A ≡ B) → AB ≡ AB'
K-Maybeℤ {A} {.A} refl AB' = sym (K-Ax AB')

≡K-lemma : {a b : Bool} → (ab : a ≡ b) → (ab' : a ≡ b) → ab ≡ ab'
≡K-lemma {a} {.a} refl refl = refl

------------------------------
-- BASIC DEFINITIONS
------------------------------

infixl 7 _·_

-- TERMS --

mutual
 data Term : Set
 Scope : (trm : Term) → ℕ

 data Term where
   Self     : Term                                  -- a special operator for recursion 
   !_       : (n : ℕ) → Term                        -- constants (or global variables)
   `_       : (x : ℕ) -> Term                       -- local variables
   Λ        : (n : ℕ) → (trm : Term) → {scoping : ((Scope trm) <= n) ≡ true} → Term   -- a Λ term is like a λ term, except it takes n+1 arguments in one reduction step 
   _·_      : Term → Term → Term                    -- application of two Terms

 Scope Self = 0                                     -- (` 0) is always in scope by default, so that any lambda term has at least one variable
 Scope (! n) = 0
 Scope (` x) = x
 Scope (Λ n trm {scoping}) = 0
 Scope (trm1 · trm2) = (Scope trm1) ⊔ (Scope trm2)
-----

scoping≡ : {x n : ℕ} → (scoping1 : (x <= n) ≡ true) → (scoping2 : (x <= n) ≡ true) → scoping1 ≡ scoping2
scoping≡ {zero} {zero} refl refl = refl
scoping≡ {zero} {suc n} refl refl = refl
scoping≡ {suc x} {suc n} scoping1 scoping2 = scoping≡ {x}{n} scoping1 scoping2

·Scoping-elim-left : {n : ℕ} → {trm1 trm2 : Term} → ((Scope trm1 ⊔ Scope trm2) <= n) ≡ true → (Scope trm1 <= n) ≡ true
·Scoping-elim-left {n} {trm1}{trm2} eqn = x⊔y<=n-elim-left {Scope trm1}{Scope trm2} {n} eqn

·Scoping-elim-right : {n : ℕ} → {trm1 trm2 : Term} → ((Scope trm1 ⊔ Scope trm2) <= n) ≡ true → (Scope trm2 <= n) ≡ true
·Scoping-elim-right {n} {trm1}{trm2} eqn = x⊔y<=n-elim-right {Scope trm1}{Scope trm2} {n} eqn

-- Basic functions using Terms --

`0≡Sucx→⊥ : {x : ℕ} -> ` 0 ≡ ` suc x -> ⊥
`0≡Sucx→⊥ {x} ()

·head : Term → Term
·head Self = Self
·head (! n) = (! n)
·head (` x) = (` x)
·head (Λ n trm {scoping}) =  (Λ n trm {scoping})
·head (trm1 · trm2) = ·head trm1

Application-Count : (trm : Term) → ℕ
Application-Count Self = 0
Application-Count (! n) = 0
Application-Count (` x) = 0
Application-Count (Λ n trm) = 0
Application-Count (trm1 · trm2) = suc (Application-Count trm1)

Arity : (trm : Term) → ℕ
Arity Self = 0
Arity (! n) = 0
Arity (` x) = 0
Arity (Λ n trm) = suc n
Arity (trm1 · trm2) = pred (Arity trm1)

Arity' : (trm : Term) → ℤ  -- this goes negative to record over-application
Arity' Self = + zero
Arity' (! n) = + zero
Arity' (` x) = + zero
Arity' (Λ n trm) = + (suc n)
Arity' (trm1 · trm2) = pred' (Arity' trm1)

SuperArity : (trm : Term) → Maybe ℤ
SuperArity Self = nothing
SuperArity (! n) = nothing
SuperArity (` x) = nothing
SuperArity (Λ n trm) = just (+ (suc n))
SuperArity (trm1 · trm2) with SuperArity trm1
... | nothing = nothing
... | just y = just (pred' y)

·SuperArity-lemma : {z : ℤ} → {trm1 trm2 : Term} → SuperArity (trm1 · trm2) ≡ just z → SuperArity trm1 ≡ just (suc' z)
·SuperArity-lemma {z} {Self} {trm2} = λ ()
·SuperArity-lemma {z} {(! n)} {trm2} = λ ()
·SuperArity-lemma {z} {` x} {trm2} = λ ()
·SuperArity-lemma {z} {Λ n trm1} {trm2} w = just-cong (cong suc' (just-elim w))
·SuperArity-lemma {z} {trm1 · trm3} {trm2} with (SuperArity (trm1 · trm3)) in sa13
...                                        | (just x) = λ w → just-cong (pred'x≡z→x≡+1+z (just-elim w))
...                                        | nothing  = λ ()

·SuperArity-lemma-nothing : {n : ℕ} → {trm1 trm2 : Term} → (superarity : SuperArity  (trm1 · trm2) ≡ nothing) → SuperArity trm1 ≡ nothing
·SuperArity-lemma-nothing {n} {Self} {trm2} superarity = refl
·SuperArity-lemma-nothing {n} {(! n₁)} {trm2} superarity = refl
·SuperArity-lemma-nothing {n} {` x} {trm2} superarity = refl
·SuperArity-lemma-nothing {n} {trm1 · trm3} {trm2} superarity  with (SuperArity (trm1 · trm3)) in sa13
... | nothing  = refl

·SuperArity-lemma' : {n : ℕ} → {trm1 trm2 : Term} → (superarity : ((SuperArity (trm1 · trm2)) ≡ just (+ n))) → (SuperArity trm1 ≡ just (+[1+ n ] ))
·SuperArity-lemma' {n} {trm1}{trm2} superarity = ·SuperArity-lemma {+ n}{trm1}{trm2} superarity 

·SuperArity-suc-lemma : {n : ℕ} {trm1 trm2 : Term} → (arity : SuperArity trm1 ≡ just (+ suc n)) → (SuperArity (trm1 · trm2) ≡ just (+ n))
·SuperArity-suc-lemma {n} {trm1}{trm2} arity with SuperArity (trm1 · trm2) in satt 
·SuperArity-suc-lemma {n} {trm1}{trm2} arity | just (+_ m) with ℕ-Dec m n  
·SuperArity-suc-lemma {.m} {trm1} {trm2} arity | just (+_ m) | yes refl = refl
·SuperArity-suc-lemma {n} {trm1}{trm2} arity | just (+_ m) | no x = ⊥-elim (x (sym n≡m))
             where
               hlp : SuperArity trm1 ≡ just +[1+ m ]
               hlp = ·SuperArity-lemma' {m}{trm1}{trm2} satt
               hlp' : just +[1+ n ] ≡  just +[1+ m ]
               hlp' = trans (sym arity) hlp
               n≡m : n ≡ m
               n≡m = just1+n≡m hlp'
·SuperArity-suc-lemma {n} {trm1}{trm2} arity | just (-[1+_] zero) = ⊥-elim (just≢ℕ contra)
             where
               hlp : (SuperArity trm1) ≡ just (+ 0)
               hlp = ·SuperArity-lemma { -[1+ zero ]} {trm1}{trm2} satt
               contra : just +[1+ n ] ≡  just (+ 0)
               contra = trans (sym arity) hlp
·SuperArity-suc-lemma {n} {trm1}{trm2} arity | just (-[1+_] (suc m)) = ⊥-elim (just≢negpos {m}{n} hlp')
             where
               hlp : SuperArity trm1 ≡ just -[1+ m ] 
               hlp = ·SuperArity-lemma { -[1+ suc m ]} {trm1}{trm2} satt
               hlp' : just ( -[1+ m ]) ≡ just ( +[1+ n ])
               hlp' = trans (sym hlp) arity
·SuperArity-suc-lemma {n} {trm1}{trm2} arity | nothing = ⊥-elim (nothing≢just contraft)
              where
               contra : SuperArity trm1 ≡ nothing
               contra = ·SuperArity-lemma-nothing {n} {trm1}{trm2} satt
               contraft : nothing ≡ just +[1+ n ]
               contraft = trans (sym contra) arity

ssuc' : Maybe ℤ → Maybe ℤ
ssuc' (just x) = just (suc' x)
ssuc' nothing = nothing

apredz : Maybe ℤ → Maybe ℕ
apredz (just (+_ zero)) = nothing
apredz (just +[1+ n ]) = just n
apredz (just (-[1+_] n)) = nothing
apredz nothing = nothing

1+m≡1+n→m≡n : {m n : ℕ} → +[1+ m ] ≡ +[1+ n ] → m ≡ n
1+m≡1+n→m≡n {m} {.m} refl = refl

Scope<=n-Dec : (trm : Term) → (n : ℕ) → Dec (Scope trm <= n ≡ true)
Scope<=n-Dec Self n = yes refl
Scope<=n-Dec (! n) m = yes refl
Scope<=n-Dec (` x) n = ℕ<=-Dec x n 
Scope<=n-Dec (Λ n trm) m = yes refl
Scope<=n-Dec (trm1 · trm2) n = ℕ<=-Dec (Scope trm1 ⊔ Scope trm2) n

isLambda? : (trm : Term) → Bool
isLambda? Self = false
isLambda? (! n) = false
isLambda?  (` x) = false
isLambda? (Λ n trm) = true
isLambda? (trm1 · trm2) = false

isLambda?-def :  {trm : Term} → (islA  : isLambda? trm ≡ true) → (islB : isLambda? trm ≡ true) → islA ≡ islB
isLambda?-def {Λ n trm} refl refl = refl

isLambda?n : (n : ℕ) → (trm : Term) → Bool
isLambda?n n Self = false
isLambda?n n (! n') = false
isLambda?n n (` x) = false
isLambda?n n (Λ m trm) with ℕ-Dec n m 
...                       | no x = false
...                       | yes x = true
isLambda?n n (trm1 · trm2) = false

isLambda?n-def' : {n : ℕ} → {trm : Term} → {scoping : (Scope trm <= n) ≡ true} → isLambda?n n (Λ n trm {scoping}) ≡ true
isLambda?n-def' {n} {Self} {refl} with ℕ-Dec n n 
... | yes x = refl
... | no x = ⊥-elim (x refl)
isLambda?n-def' {n} {(! n₁)} {scoping} with ℕ-Dec n n 
... | yes x = refl
... | no x = ⊥-elim (x refl)
isLambda?n-def' {n} {` x} {scoping} with ℕ-Dec n n 
... | yes x = refl
... | no x = ⊥-elim (x refl)
isLambda?n-def' {n} {Λ m trm} {scoping} with ℕ-Dec n n 
... | yes x = refl
... | no x = ⊥-elim (x refl)
isLambda?n-def' {n} {trm1 · trm2} {scoping} with ℕ-Dec n n 
... | yes x = refl
... | no x = ⊥-elim (x refl)

isLambda?n≡m-lemma : {n m : ℕ} {M : Term} (isl : isLambda?n n M ≡ true) → (isl' : isLambda?n m M ≡ true) → n ≡ m
isLambda?n≡m-lemma {n} {m} {Λ n' M'} isl isl' with ℕ-Dec m n' | ℕ-Dec n n'
... | yes x | yes y = trans y (sym x)

-- A variant of axiom K (without assuming such):
isLambda?n≡-lemma : {n : ℕ} {M : Term} (isl : isLambda?n n M ≡ true) → (isl' : isLambda?n n M ≡ true) →  isl ≡ isl'
isLambda?n≡-lemma {n}{M} isl isl' = K-bool' isl isl'

isLambda?n-def : {n : ℕ} → {trm trm' : Term} → {scoping : (Scope trm' <= n) ≡ true} → (isl≡ : trm ≡ Λ n trm' {scoping}) → isLambda?n n trm ≡ true 
isLambda?n-def {n} {.(Λ n trm' {scoping})} {trm'} {scoping} refl = isLambda?n-def' {n}{trm'}{scoping}

isLambda?→n : {trm : Term} → (isl : isLambda? trm ≡ true) → ℕ
isLambda?→n {Λ n trm} refl = n

isLambda?n→isLambda? : {n : ℕ} {trm : Term} → isLambda?n n trm ≡ true → isLambda? trm ≡ true
isLambda?n→isLambda? {n} {Λ m trm} isl = refl

ScopeIsLambda?-lemma : {trm : Term} → (isLambda? trm ≡ true) → Scope trm ≡ 0
ScopeIsLambda?-lemma {Λ n trm {scoping}} refl = refl

isLambda?→SuperArity≢just0 : {trm : Term} → isLambda? trm ≡ true → (SuperArity trm ≢ just (+ 0)) 
isLambda?→SuperArity≢just0 {Λ n trm {scoping}} refl = λ ()

isLambda?→inner : {trm : Term} → isLambda? trm ≡ true → Term
isLambda?→inner {Λ n trm} isl = trm

isLambda?→inner-def :  {trm : Term} → (islA  : isLambda? trm ≡ true) → (islB : isLambda? trm ≡ true) → isLambda?→inner islA ≡ isLambda?→inner islB
isLambda?→inner-def {trm} islA islB = cong (λ x → isLambda?→inner x) (isLambda?-def islA islB)

isLambda?n→SuperArity : {n : ℕ} → {trm : Term} → isLambda?n n trm ≡ true → SuperArity trm ≡ just +[1+ n ]
isLambda?n→SuperArity {n} {Λ m trm {scoping}} isl with ℕ-Dec n m 
... | yes refl = refl

isLambda?-inner-Scope : {n : ℕ}{M : Term} (isl : isLambda?n n M ≡ true) → (Scope (isLambda?→inner (isLambda?n→isLambda? {n}{M} isl)) <= n) ≡ true
isLambda?-inner-Scope {n} {Λ m M' {scoping}} isl with ℕ-Dec n m
... | yes refl = scoping

isLambda?nΛ : {m : ℕ} → {trm : Term} → (scoping : (Scope trm <= m) ≡ true) →  (isLambda?n m (Λ m trm {scoping})) ≡ true
isLambda?nΛ {m} {Self} refl with ℕ-Dec m m 
... | yes x = refl
... | no x = ⊥-elim (x refl)
isLambda?nΛ {m} {(! n)} scoping with ℕ-Dec m m 
... | yes x = refl
... | no x = ⊥-elim (x refl)
isLambda?nΛ {m} {` x} scoping with ℕ-Dec m m 
... | yes x = refl
... | no x = ⊥-elim (x refl)
isLambda?nΛ {m} {Λ n trm} scoping with ℕ-Dec m m 
... | yes x = refl
... | no x = ⊥-elim (x refl)
isLambda?nΛ {m} {trm · trm₁} scoping with ℕ-Dec m m 
... | yes x = refl
... | no x = ⊥-elim (x refl)

islambda-?n-lemma : {n n₁ : ℕ} → (M1 : Term) -> (scoping : (Scope M1 <= n₁) ≡ true) → isLambda?n n (Λ n₁ M1 {scoping}) ≡ true → n ≡ n₁
islambda-?n-lemma {n}{n₁} M1 scoping isl' with ℕ-Dec n n₁ 
... | yes refl = refl


ΛisLambda?-def :  (trms : Σ[ x ∈ Term ] ((isLambda?n 1 x) ≡ true)) → (proj₁ trms) ≡ Λ 1 (isLambda?→inner {proj₁ trms} (isLambda?n→isLambda? {1} (proj₂ trms))) {isLambda?-inner-Scope {1}{proj₁ trms} (proj₂ trms)}
ΛisLambda?-def (Λ (suc zero) Self {refl} , isltrm) = refl
ΛisLambda?-def (Λ (suc zero) (! n₁) {scoping} , isltrm) = refl
ΛisLambda?-def (Λ (suc zero) (` x) {scoping} , isltrm) = refl
ΛisLambda?-def (Λ (suc zero) (Λ n₁ trm {scoping'}) {scoping} , isltrm) = refl
ΛisLambda?-def (Λ (suc zero) (trm · trm₁) {scoping} , isltrm) = refl

ΛisLambda?-def' : {n : ℕ} (trms : Σ[ x ∈ Term ] ((isLambda?n n x) ≡ true)) → (proj₁ trms) ≡ Λ n (isLambda?→inner {proj₁ trms} (isLambda?n→isLambda? {n} (proj₂ trms))) {isLambda?-inner-Scope {n}{proj₁ trms} (proj₂ trms)}
ΛisLambda?-def' {n} (Λ n₁ fst {scoping} , snd) with ℕ-Dec n n₁ 
... | yes refl = refl


`x≡`y→x≡y : {x y : ℕ} → (` x) ≡ (` y) → x ≡ y
`x≡`y→x≡y {zero} {zero} xy = refl
`x≡`y→x≡y {suc x} {suc y} xy = cong (λ w → suc w) (`x≡`y→x≡y (hlp xy)) 
                                where
                                  hlp : {x y : ℕ} → (` suc x) ≡ (` suc y) →  (` x) ≡ (` y)
                                  hlp {x} {.x} refl = refl

!x≡!y→x≡y : {x y : ℕ} → (! x) ≡ (! y) → x ≡ y
!x≡!y→x≡y {zero} {zero} xy = refl
!x≡!y→x≡y {suc x} {suc y} xy = cong (λ w → suc w) (!x≡!y→x≡y (hlp xy)) 
                                where
                                  hlp : {x y : ℕ} → (! suc x) ≡ (! suc y) →  (! x) ≡ (! y)
                                  hlp {x} {.x} refl = refl

·-elim-left : {trm1 trm3 trm2 trm4 : Term} → trm1 · trm3 ≡ trm2 · trm4 → trm1 ≡ trm2
·-elim-left refl = refl

·-elim-right : {trm1 trm3 trm2 trm4 : Term} → trm1 · trm3 ≡ trm2 · trm4 → trm3 ≡ trm4
·-elim-right refl = refl

·-intro-left-contra : {trm trm' trm2 trm2' : Term} -> trm ≢ trm' → trm · trm2 ≢ trm' · trm2'
·-intro-left-contra {trm} {trm'} {trm2} {trm2'} trmtrm' = λ x -> (trmtrm' (·-elim-left x))

⊔Scoping : {m : ℕ} → {trm1 trm2 : Term} → (Scope trm1 <= m) ≡ true → (Scope trm2 <= m) ≡ true →  ((Scope trm1 ⊔ Scope trm2) <= m) ≡ true
⊔Scoping {m}{trm1}{trm2} scp1 scp2 = x⊔y<=n-intro {Scope trm1}{Scope trm2}{m} scp1 scp2

Scope0 : {trm : Term} → Scope trm <= 0 ≡ true → Scope trm ≡ 0
Scope0 {Self} scoping = refl
Scope0 {(! n)} scoping = refl
Scope0 {` zero} scoping = refl
Scope0 {Λ n trm} scoping = refl
Scope0 {trm1 · trm2} scoping = A≡0∧B≡0→A⊔B≡0 {Scope trm1}{Scope trm2}(Scope0 {trm1} (·Scoping-elim-left {0} {trm1}{trm2} scoping)) (Scope0 {trm2} (·Scoping-elim-right {0} {trm1}{trm2} scoping))

Scope0' :  (n : ℕ) → {trm : Term} → Scope trm ≡ 0 → Scope trm <= n ≡ true
Scope0' n {Self} s0 = refl
Scope0' n {(! m)} s0 = refl
Scope0' n {` .0} refl = refl
Scope0' n {Λ m trm} s0 = refl
Scope0' n {trm1 · trm2} s0 = ⊔Scoping {n}{trm1}{trm2} (Scope0' n {trm1} (x⊔≡0-left-elim {Scope trm1}{Scope trm2} s0)) (Scope0' n {trm2} ((x⊔≡0-right-elim {Scope trm1}{Scope trm2} s0)))

Scope0<=-lemma : (n : ℕ) → {trm : Term} → (Scope trm <= zero) ≡ true → (Scope trm <= n) ≡ true
Scope0<=-lemma n {Self} sc0 = refl
Scope0<=-lemma n {(! m)} sc0 = refl
Scope0<=-lemma n {` zero} refl = refl
Scope0<=-lemma n {Λ m trm} sc0 = refl
Scope0<=-lemma n {trm1 · trm2} sc0 = ⊔Scoping {n} {trm1}{trm2} (Scope0<=-lemma n {trm1} (·Scoping-elim-left {0}{trm1}{trm2} sc0)) (Scope0<=-lemma n {trm2} (·Scoping-elim-right {0} {trm1} {trm2} sc0))

⊔Scoping' :  {m : ℕ} → {trm1 trm2 : Term} → (Scope trm1 <= m) ≡ true → (Scope trm2 <= m) ≡ true → ((Scope trm1 ⊔ (Scope trm2 ⊔ 0)) <= m) ≡ true
⊔Scoping' {m} {trm1} {trm2} scp1 scp2 = x⊔y<=n-intro' {Scope trm1} {Scope trm2} {m} scp1 scp2

isLambda?0-inner-Scope0-Lemma : {Λtrm : Term} → (isl : isLambda?n 0 Λtrm ≡ true) → Scope (isLambda?→inner {Λtrm} (isLambda?n→isLambda? {0}{Λtrm} isl)) ≡ 0
isLambda?0-inner-Scope0-Lemma {Λ n Λtrm {scoping}} isl with ℕ-Dec 0 n
... | yes refl = Scope0 {Λtrm}  scoping

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
trm1≡trm→Λntrm1≡Λmtrm2 {n} {.n} refl {trm1} {.trm1} {scoping1} {scoping2} refl = trm1≡trm→Λntrm1≡Λmtrm2-hlp

n≢m→Λntrm≢Λmtrm : {n m : ℕ}{trm1 : Term}{trm2 : Term} {scoping : (Scope trm1 <= n) ≡ true }{scoping' : (Scope trm2 <= m) ≡ true} → n ≢ m → (Λ n (trm1) {scoping}) ≢ (Λ m (trm2) {scoping'})
n≢m→Λntrm≢Λmtrm {zero} {zero} {trm1} {trm2} {scoping} {scoping'} nm = ⊥-elim (nm refl)
n≢m→Λntrm≢Λmtrm {zero} {suc m} {trm1} {trm2} {scoping} {scoping'} nm = λ x → ⊥-elim (nm (Λn≡Λm→n≡m x))
n≢m→Λntrm≢Λmtrm {suc n} {m} {trm1} {trm2} {scoping} {scoping'} nm = λ x → ⊥-elim (nm (Λn≡Λm→n≡m x))

------------------------------------
-- Definitional Equality of Terms --
------------------------------------

term-Dec : (trm1 : Term) → (trm2 : Term) → Dec (trm1 ≡ trm2)
term-Dec Self Self = yes refl
term-Dec Self (! n) = no (λ ())
term-Dec Self (` x) = no (λ ())
term-Dec Self (Λ n trm2) = no (λ ())
term-Dec Self (trm2 · trm3) = no (λ ())
term-Dec (! n) Self = no (λ ())
term-Dec (! n) (! m)  with ℕ-Dec n m 
...                   | no w = no (λ v → w (!x≡!y→x≡y v))
...                   | yes w = yes (cong (λ v → (! v)) w) 
term-Dec (! n) (` x) = no (λ ())
term-Dec (! n) (Λ n₁ trm2) = no (λ ())
term-Dec (! n) (trm2 · trm3) = no (λ ())
term-Dec (` x) Self = no (λ ())
term-Dec (` x) (! n) = no (λ ())
term-Dec (` x) (` y) with ℕ-Dec x y 
...                   | no w = no (λ v → w (`x≡`y→x≡y v))
...                   | yes w = yes (cong (λ v → ` v) w)
term-Dec (` x) (Λ n trm2) = no (λ ())
term-Dec (` x) (trm2 · trm3) = no (λ ())
term-Dec (Λ n trm1) Self = no (λ ())
term-Dec (Λ n trm1) (! m) = no (λ ())
term-Dec (Λ n trm1) (` x) = no (λ ())
term-Dec (Λ n trm1 {scoping1}) (Λ m trm2 {scoping2}) with ℕ-Dec n m 
term-Dec (Λ n trm1 {scoping1}) (Λ m trm2 {scoping2})  | yes x with term-Dec trm1 trm2
term-Dec (Λ n trm1 {scoping1}) (Λ m trm2 {scoping2})  | yes x  | yes y = yes (trm1≡trm→Λntrm1≡Λmtrm2 x y) 
term-Dec (Λ n trm1 {scoping1}) (Λ m trm2 {scoping2})  | yes x  | no y = no (¬trm1≡trm2→¬Λntrm1≡Λmtrm2 y)  
term-Dec (Λ n trm1 {scoping1}) (Λ m trm2 {scoping2})  | no x = no λ w → x (Λn≡Λm→n≡m w)
term-Dec (Λ n trm1) (trm2 · trm3) = no (λ ())
term-Dec (trm1 · trm3) Self = no (λ ())
term-Dec (trm1 · trm3) (! n) = no (λ ())
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

-- A combinator expression:
isCombinator : Term → Bool
isCombinator Self = false
isCombinator (! n) = true 
isCombinator (` x) = false
isCombinator (Λ n trm) = true
isCombinator (trm1 · trm2) = isCombinator trm1 ∧ isCombinator trm2


isCombinatorScope : {trm : Term} → (isc : isCombinator trm ≡ true) → Scope trm ≡ 0
isCombinatorScope {(! n)} isc = refl
isCombinatorScope {Λ n trm} isc = refl
isCombinatorScope {trm1 · trm2} isc = A≡0∧B≡0→A⊔B≡0 (isCombinatorScope {trm1} (∧-elim-left isc)) (isCombinatorScope {trm2} (∧-elim-right isc))

isCombinator?n : (n : ℕ) → Term → Bool
isCombinator?n n Self = false
isCombinator?n n (! m) = false
isCombinator?n n (` x) = false
isCombinator?n n (Λ m trm {scoping}) with ℕ-Dec n m 
... | yes x = true
... | no x = false
isCombinator?n n (trm1 · trm2) with (isCombinator trm2) 
... | false = false
... | true = isCombinator?n (suc n) trm1

isLambdaHeaded : Term → Bool
isLambdaHeaded Self = false
isLambdaHeaded ((! n)) = false
isLambdaHeaded (` x) = false
isLambdaHeaded (Λ n trm) = true
isLambdaHeaded (trm1 · trm2) = isLambdaHeaded trm1

isLambda?n→isCombinator : {n : ℕ} → {trm : Term} → isLambda?n n trm ≡ true → isCombinator trm ≡ true 
isLambda?n→isCombinator {n} {Λ m trm {scoping}} isl = refl

-- Compare the following two definitions to understand how variables are expressed in combinator terms:
-- This shows how variables are to be wrapped in a Λ:
isCombinatorSx : isCombinator ExampleSx ≡ true
isCombinatorSx = refl

is¬CombinatorSx : isCombinator (S · (` 0)) ≡ false
is¬CombinatorSx = refl

ScopeCombinator0 : {trm : Term} -> (isc : isCombinator trm ≡ true) → Scope trm ≡ 0
ScopeCombinator0 {(! n)} refl = refl
ScopeCombinator0 {Λ n trm} refl = refl
ScopeCombinator0 {trm1 · trm2} isc = x⊔x≡x' ((ScopeCombinator0 {trm1} (∧-elim-left isc))) (ScopeCombinator0 {trm2} (∧-elim-right isc))

CombinatorScope0 : {trm : Term} → isCombinator trm ≡ true → (Scope trm <= zero) ≡ true
CombinatorScope0 {Λ n trm} refl = refl
CombinatorScope0 {(! n)} isc = refl
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
noLambdas? (! n) = true
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
SelfSub self (! n) = (! n)
SelfSub self (` x) = (` x)
SelfSub self (Λ n trm {scoping}) = (Λ n trm {scoping})
SelfSub self (trm1 · trm2) =  (SelfSub self trm1) · (SelfSub self trm2)

ScopeSelfSub0Trm : {trm1 trm2 : Term} → (Scope trm1 ≡ 0) → Scope (SelfSub trm1 trm2) ≡ Scope trm2
ScopeSelfSub0Trm {Self} {Self} refl = refl
ScopeSelfSub0Trm {(! n)} {Self} refl = refl
ScopeSelfSub0Trm {` .0} {Self} refl = refl
ScopeSelfSub0Trm {Λ n trm1} {Self} refl = refl
ScopeSelfSub0Trm {trm1 · trm2} {Self} sc = sc
ScopeSelfSub0Trm {Self} {(! n)} sc = refl
ScopeSelfSub0Trm {(! n₁)} {(! n)} sc = refl
ScopeSelfSub0Trm {` x} {(! n)} sc = refl
ScopeSelfSub0Trm {Λ n₁ trm1} {(! n)} sc = refl
ScopeSelfSub0Trm {trm1 · trm2} {(! n)} sc = refl
ScopeSelfSub0Trm {trm1} {` x} sc = refl
ScopeSelfSub0Trm {trm1} {Λ n trm2} sc = refl
ScopeSelfSub0Trm {trm1} {trm2 · trm3} sc = A≡A'∧B≡B'→A⊔B≡A'⊔B' hlp1 hlp2
                  where
                    hlp1 : Scope (SelfSub trm1 trm2) ≡ Scope trm2 
                    hlp1 = ScopeSelfSub0Trm {trm1}{trm2} sc
                    hlp2 : Scope (SelfSub trm1 trm3) ≡ Scope trm3
                    hlp2 = ScopeSelfSub0Trm {trm1}{trm3} sc

ScopeSelfSub0 : {trm1 : Term} → {trm2 : Term} → (Scope trm1 ≡ 0) → (Scope trm2 ≡ 0) → Scope (SelfSub trm1 trm2) ≡ 0
ScopeSelfSub0 {Self} {Self} refl refl = refl
ScopeSelfSub0 {Self} {(! n)} refl sc2 = refl
ScopeSelfSub0 {Self} {` .0} refl refl = refl
ScopeSelfSub0 {Self} {Λ n trm2} refl sc2 = refl
ScopeSelfSub0 {Self} {trm2 · trm3} refl sc2 = A≡A'∧B≡B'→A⊔B≡A'⊔B' left-hlp right-hlp
                             where
                               left-hlp : Scope (SelfSub Self trm2) ≡ 0
                               left-hlp = ScopeSelfSub0 {Self} {trm2} (x⊔≡0-left-elim sc2) (x⊔≡0-left-elim sc2)
                               right-hlp : Scope (SelfSub Self trm3) ≡ 0
                               right-hlp = ScopeSelfSub0 {Self} {trm3} refl (x⊔≡0-right-elim sc2)
ScopeSelfSub0 {(! n)} {Self} refl sc2 = refl
ScopeSelfSub0 {(! n)} {(! n₁)} refl sc2 = refl
ScopeSelfSub0 {(! n)} {` x} refl sc2 = sc2
ScopeSelfSub0 {(! n)} {Λ n₁ trm2} refl sc2 = refl
ScopeSelfSub0 {(! n)} {trm2 · trm3} refl sc2 = A≡A'∧B≡B'→A⊔B≡A'⊔B' left-hlp right-hlp
                             where
                               left-hlp : Scope (SelfSub (! n) trm2) ≡ 0
                               left-hlp = ScopeSelfSub0 {(! n)} {trm2} (x⊔≡0-left-elim sc2) (x⊔≡0-left-elim sc2)
                               right-hlp : Scope (SelfSub (! n) trm3) ≡ 0
                               right-hlp = ScopeSelfSub0 {(! n)} {trm3} refl (x⊔≡0-right-elim sc2)
ScopeSelfSub0 {` x} {Self} sc1 sc2 = sc1
ScopeSelfSub0 {` x} {(! n)} sc1 sc2 = refl
ScopeSelfSub0 {` x} {` x₁} sc1 sc2 = sc2
ScopeSelfSub0 {` x} {Λ n trm2} sc1 sc2 = refl
ScopeSelfSub0 {` .0} {trm2 · trm3} refl sc2 = A≡A'∧B≡B'→A⊔B≡A'⊔B' left-hlp right-hlp
                             where
                               left-hlp : Scope (SelfSub (` 0) trm2) ≡ 0
                               left-hlp = ScopeSelfSub0 {` 0} {trm2} (x⊔≡0-left-elim sc2) (x⊔≡0-left-elim sc2)
                               right-hlp : Scope (SelfSub (` 0) trm3) ≡ 0
                               right-hlp = ScopeSelfSub0 {` 0} {trm3} refl (x⊔≡0-right-elim sc2)
ScopeSelfSub0 {Λ n trm1} {Self} refl sc2 = refl
ScopeSelfSub0 {Λ n trm1} {(! n₁)} refl sc2 = refl
ScopeSelfSub0 {Λ n trm1} {` x} refl sc2 = sc2
ScopeSelfSub0 {Λ n trm1} {Λ n₁ trm2} refl sc2 = refl
ScopeSelfSub0 {Λ n trm1 {scoping}} {trm2 · trm3} refl sc2 = A≡A'∧B≡B'→A⊔B≡A'⊔B' left-hlp right-hlp
                             where
                               left-hlp : Scope (SelfSub (Λ n trm1 {scoping}) (trm2)) ≡ 0
                               left-hlp = ScopeSelfSub0 {Λ n trm1} {trm2} (x⊔≡0-left-elim sc2) (x⊔≡0-left-elim sc2)
                               right-hlp : Scope (SelfSub (Λ n trm1 {scoping}) trm3) ≡ 0
                               right-hlp = ScopeSelfSub0 {Λ n trm1} {trm3} refl (x⊔≡0-right-elim sc2)
ScopeSelfSub0 {trm1 · trm3} {Self} sc1 sc2 = sc1
ScopeSelfSub0 {trm1 · trm3} {(! n)} sc1 sc2 = refl
ScopeSelfSub0 {trm1 · trm3} {` x} sc1 sc2 = sc2
ScopeSelfSub0 {trm1 · trm3} {Λ n trm2} sc1 sc2 = refl
ScopeSelfSub0 {trm1 · trm3} {trm2 · trm4} sc1 sc2 = A≡A'∧B≡B'→A⊔B≡A'⊔B' left-hlp right-hlp
                             where
                               left-hlp : Scope (SelfSub (trm1 · trm3) (trm2)) ≡ 0
                               left-hlp = ScopeSelfSub0 {trm1 · trm3}{trm2} sc1 (x⊔≡0-left-elim sc2)  
                               right-hlp : Scope (SelfSub (trm1 · trm3) trm4) ≡ 0
                               right-hlp = ScopeSelfSub0 {trm1 · trm3} {trm4} sc1 (x⊔≡0-right-elim sc2)

Substitute : (n : ℕ) → (target : Term) → (arg : Term) → Term
Substitute n Self arg = Self
Substitute n (! m) arg = (! m)
Substitute n (` x) arg with ℕ-Dec n x   -- Only part where n is used. 
...                | no w = (` x)
...                | yes w = arg 
Substitute n (Λ m target {scoping}) arg = (Λ m target {scoping})
Substitute n (target1 · target2) arg = Substitute n target1 arg · Substitute n target2 arg

Substitute-lemma : {n : ℕ} → {trm : Term} → {arg : Term} → (iscx : isCombinator arg ≡ true) → (scoping : (Scope trm <= (suc n)) ≡ true) → (Scope (Substitute (suc n) trm arg) <= n) ≡ true
Substitute-lemma {n} {Self} {arg} iscx scoping = refl
Substitute-lemma {n} {(! m)} {arg} iscx scoping = refl
Substitute-lemma {n} {` x} {arg} iscx scoping with ℕ-Dec (suc n) x 
... | yes refl = Scope0<=-lemma n {arg} (CombinatorScope0 {arg} iscx)
... | no y = n≡x<=-lemma y scoping
Substitute-lemma {n} {Λ m trm} {arg} iscx scoping = refl
Substitute-lemma {n} {trm1 · trm2} {arg} iscx scoping = ⊔Scoping {_}{Substitute (suc n) trm1 arg}{Substitute (suc n) trm2 arg} hlp1 hlp2
                      where
                       hlp1 : (Scope (Substitute (suc n) trm1 arg) <= n) ≡ true
                       hlp1 = Substitute-lemma {n} {trm1}{arg} iscx (x⊔y<=n-left-elim {Scope trm1} {Scope trm2} {suc n} scoping)
                       hlp2 : (Scope (Substitute (suc n) trm2 arg) <= n) ≡ true
                       hlp2 = Substitute-lemma {n}{trm2}{arg} iscx (x⊔y<=n-right-elim {Scope trm1} {Scope trm2} {suc n} scoping) 

SubstituteScope-lemma' : (n : ℕ) → (trm : Term) → (isc : isCombinator trm ≡ true) → (arg : Term) → (iscx : isCombinator arg ≡ true) →  Scope (Substitute n trm arg) ≡ 0
SubstituteScope-lemma' n ((! m)) isc arg iscx = refl
SubstituteScope-lemma' n (Λ m trm {scoping}) isc arg iscx = refl
SubstituteScope-lemma' n (trm1 · trm2) isc arg iscx = A≡0∧B≡0→A⊔B≡0 (SubstituteScope-lemma' n trm1 (∧-elim-left isc) arg iscx) (SubstituteScope-lemma' n trm2 (∧-elim-right isc) arg iscx)

Scope0SubstituteScope-lemma : {trm arg : Term} → Scope trm ≡ 0 → Scope arg ≡ 0 → Scope (Substitute 0 trm arg) ≡ 0
Scope0SubstituteScope-lemma {Self} {arg} refl scparg = refl
Scope0SubstituteScope-lemma {(! n)} {arg} refl scparg = refl
Scope0SubstituteScope-lemma {` zero} {arg} refl scparg = scparg
Scope0SubstituteScope-lemma {Λ n trm} {arg} refl scparg = refl
Scope0SubstituteScope-lemma {trm1 · trm2} {arg} scptrm scparg = A≡0∧B≡0→A⊔B≡0 hlp1 hlp2
                                  where
                                    hlp1 : Scope (Substitute 0 trm1 arg) ≡ 0
                                    hlp1 = Scope0SubstituteScope-lemma {trm1}{arg} (x⊔≡0-left-elim scptrm) scparg
                                    hlp2 : Scope (Substitute 0 trm2 arg) ≡ 0
                                    hlp2 = Scope0SubstituteScope-lemma {trm2}{arg} (x⊔≡0-right-elim scptrm) scparg

isCombinatorSubstitute-lemma : {trm arg : Term} → isCombinator trm ≡ true → isCombinator arg ≡ true → isCombinator (Substitute 0 trm arg) ≡ true
isCombinatorSubstitute-lemma {(! n)} {arg} refl isca = refl
isCombinatorSubstitute-lemma {Λ n trm} {arg} isct isca = refl
isCombinatorSubstitute-lemma {trm1 · trm2} {arg} isct isca = ∧-intro (isCombinatorSubstitute-lemma {trm1}{arg} (∧-elim-left isct) isca) (isCombinatorSubstitute-lemma {trm2}{arg} (∧-elim-right isct) isca)

-- ** Substitutes next arg into a Λ
SubstituteΛ : {n : ℕ} -> (Λtrm : Term) → (isLambda?n n Λtrm ≡ true) → (arg : Term) → (isc : isCombinator arg ≡ true) → Term
SubstituteΛ {zero} (Λ zero trm) isln arg isc = Substitute zero trm arg
SubstituteΛ {suc n} (Λ (suc m) trm {scoping}) isln arg isc with ℕ-Dec n m
... | yes refl = Λ m (Substitute (suc m) trm arg) {Substitute-lemma {n} {trm}{arg} isc scoping} 
                                   
SubstituteΛ-def : {n : ℕ} → {trm arg : Term} → {scoping : (Scope trm <= (suc n)) ≡ true} → (isc : isCombinator arg ≡ true)
                          → SubstituteΛ {suc n} (Λ (suc n) trm {scoping}) (isLambda?nΛ {suc n}{trm} scoping) arg isc ≡ Λ n (Substitute (suc n) trm arg) {Substitute-lemma {n}{trm}{arg} isc scoping}
SubstituteΛ-def {n} {Self} {arg} {refl} isc with ℕ-Dec (suc n) (suc n) | ℕ-Dec n n
... | yes refl | yes refl = refl
... | yes x | no y = ⊥-elim (y refl)
... | no x | v = ⊥-elim (x refl)
SubstituteΛ-def {n} {(! m)} {arg} {refl} isc with ℕ-Dec (suc n) (suc n) | ℕ-Dec n n
... | yes refl | yes refl = refl
... | yes x | no y = ⊥-elim (y refl)
... | no x | v = ⊥-elim (x refl)
SubstituteΛ-def {n} {` x} {arg} {scoping} isc with ℕ-Dec (suc n) (suc n) | ℕ-Dec n n
... | yes refl | yes refl = refl
... | yes x | no y = ⊥-elim (y refl)
... | no x | v = ⊥-elim (x refl)
SubstituteΛ-def {n} {Λ m trm {scoping}} {arg} {refl} isc with ℕ-Dec (suc n) (suc n) | ℕ-Dec n n
... | yes refl | yes refl = refl
... | yes x | no y = ⊥-elim (y refl)
... | no x | v = ⊥-elim (x refl)
SubstituteΛ-def {n} {trm1 · trm2} {arg} {scoping} isc with ℕ-Dec (suc n) (suc n) | ℕ-Dec n n
... | yes refl | yes refl = refl
... | yes x | no y = ⊥-elim (y refl)
... | no x | v = ⊥-elim (x refl)

Substitute-Λlemma : {n : ℕ} → {trm : Term} →  (scoping : (Scope trm <= suc n) ≡ true)
                             → {arg : Term} → (isc : isCombinator arg ≡ true)
                             → (isLambda?n n (Λ n (Substitute (suc n) trm arg) {Substitute-lemma {n}{trm}{arg} isc scoping})) ≡ true
Substitute-Λlemma {n} {trm} scoping {arg} isc = isLambda?n-def {n}{Λ n (Substitute (suc n) trm arg) {Substitute-lemma {n}{trm}{arg} isc scoping}}{_}{Substitute-lemma {n}{trm}{arg} isc scoping} refl

SubstituteΛ-lemma : {n : ℕ} -> (Λtrm : Term) → (isl : isLambda?n (suc n) Λtrm ≡ true) → (arg : Term) → (isc : isCombinator arg ≡ true)
                              → (isLambda?n n (SubstituteΛ {suc n} Λtrm isl arg isc)) ≡ true
SubstituteΛ-lemma {n} (Λ (suc m) trm {scoping}) isl arg isc with ℕ-Dec n m 
... | yes refl = Substitute-Λlemma {n}{trm} scoping {arg} isc

ScopeSubstitute : {n : ℕ} → {trm arg : Term} → (Scope (Substitute n trm arg) <= (Scope trm ⊔ Scope arg)) ≡ true
ScopeSubstitute {n} {Self} {arg} = refl
ScopeSubstitute {n} {(! m)} {arg} = refl
ScopeSubstitute {n} {` x} {arg} with ℕ-Dec n x 
... | yes w = x<=y→x<=n⊔y {Scope arg}{Scope arg}{x} (x<=x≡true {Scope arg})
... | no w = x<=y→x<=y⊔n {x}{x}{Scope arg} (x<=x≡true {x})
ScopeSubstitute {n} {Λ m trm} {arg} = refl
ScopeSubstitute {n} {trm1 · trm2} {arg} = trans<= {(Scope (Substitute n trm1 arg)) ⊔ (Scope (Substitute n trm2 arg))}
                                                  {(Scope trm1 ⊔ Scope arg) ⊔ (Scope trm2 ⊔ Scope arg)}
                                                  {Scope trm1 ⊔ Scope trm2 ⊔ Scope arg} hlp3 hlp4
        where
          hlp1 : ((Scope (Substitute n trm1 arg))
                   <= (Scope trm1 ⊔ Scope arg)) ≡ true
          hlp1 = ScopeSubstitute {n}{trm1}{arg}        
          hlp2 : ((Scope (Substitute n trm2 arg))
                   <= (Scope trm2 ⊔ Scope arg)) ≡ true
          hlp2 = ScopeSubstitute {n}{trm2}{arg}
          hlp3 : (((Scope (Substitute n trm1 arg)) ⊔ (Scope (Substitute n trm2 arg)))
                   <= ((Scope trm1 ⊔ Scope arg) ⊔ (Scope trm2 ⊔ Scope arg))) ≡ true
          hlp3 = x<=y→u<=v→x⊔u<=y⊔v {(Scope (Substitute n trm1 arg))}{(Scope trm1 ⊔ Scope arg)}
                                    {(Scope (Substitute n trm2 arg))}{(Scope trm2 ⊔ Scope arg)} hlp1 hlp2
          hlp4 : (((Scope trm1 ⊔ Scope arg) ⊔ (Scope trm2 ⊔ Scope arg)) <= (Scope trm1 ⊔ Scope trm2 ⊔ Scope arg)) ≡ true
          hlp4 = ⊔<=-right-distr {Scope trm1}{Scope trm2}{Scope arg}

Scopetrm<=n≡true→ : {n : ℕ} → {trm trm' : Term} → (scoping : (Scope trm <= n) ≡ true) → (scoping' : (Scope trm' <= n) ≡ true) → (Scope (SelfSub (Λ n trm' {scoping'}) trm) <= n) ≡ true
Scopetrm<=n≡true→ {n} {Self} {trm'} scoping scoping' = scoping
Scopetrm<=n≡true→ {n} {(! m)} {trm'} scoping scoping' = scoping
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

Scopetrm<=n≡true→2 : {n : ℕ} → {trm : Term} → (scoping : (Scope trm <= n) ≡ true) → (Scope (SelfSub (Λ n trm {scoping}) trm) <= n) ≡ true
Scopetrm<=n≡true→2 {n} {trm} scoping = Scopetrm<=n≡true→ {n}{trm} scoping scoping

ScopeSelfSub : {n : ℕ} → (arg : Term) → (trm : Term) → (scoping : (Scope arg <= n) ≡ true) → (scoping' : (Scope trm <= n) ≡ true) → (Scope (SelfSub arg trm) <= n) ≡ true 
ScopeSelfSub {n} arg Self scoping scoping' = scoping
ScopeSelfSub {n} arg (! n₁) scoping scoping' = refl
ScopeSelfSub {n} arg (` x) scoping scoping' = scoping'
ScopeSelfSub {n} arg (Λ n₁ trm) scoping scoping' = refl
ScopeSelfSub {n} arg (trm1 · trm2) scoping scoping' = x⊔y<=n-intro {Scope (SelfSub arg trm1)}{Scope (SelfSub arg trm2)}{n} hlp1 hlp2
           where
             hlp1 : ((Scope (SelfSub arg trm1)) <= n) ≡ true
             hlp1 = ScopeSelfSub arg trm1 scoping (x⊔y<=n-left-elim {Scope trm1}{Scope trm2}{n} scoping')
             hlp2 : ((Scope (SelfSub arg trm2)) <= n) ≡ true
             hlp2 =  ScopeSelfSub arg trm2 scoping (x⊔y<=n-right-elim {Scope trm1} {Scope trm2} {n} scoping')

-- This function takes a Λ term and plugs in Λtrm to top level Self.
SubΛ-base : (Λtrm : Term) → (isl : isLambda? Λtrm ≡ true) → Term
SubΛ-base (Λ n trm {scoping}) refl = Λ n (SelfSub (Λ n trm {scoping}) trm) {ScopeSelfSub {n} (Λ n trm {scoping}) trm refl scoping}   
 
SubΛ-base-lemma : {Λtrm : Term} → (isl : isLambda? Λtrm ≡ true) → (Scope (SubΛ-base Λtrm isl) <= 0) ≡ true
SubΛ-base-lemma {Λ n (! m) {scoping}} refl = refl
SubΛ-base-lemma {Λ n (` x) {scoping}} refl = refl
SubΛ-base-lemma {Λ n (Λ m Λtrm) {scoping}} refl = refl
SubΛ-base-lemma {Λ n (Λtrm · Λtrm₁) {scoping}} refl = refl
SubΛ-base-lemma {Λ (n) Self {scoping}} refl = refl

SubΛ-base-lemma' : {Λtrm : Term} → (isl : isLambda? Λtrm ≡ true) → (Scope (SubΛ-base Λtrm isl) ≡ 0)
SubΛ-base-lemma' {Λ n Self} refl = refl
SubΛ-base-lemma' {Λ n ((! m))} refl = refl
SubΛ-base-lemma' {Λ n (` x)} refl = refl
SubΛ-base-lemma' {Λ n (Λ m Λtrm)} refl = refl
SubΛ-base-lemma' {Λ n (Λtrm1 · Λtrm2)} refl = refl

SubΛ-base-eq : {trm trm' : Term}{eqn : trm ≡ trm'}{isl : isLambda? trm ≡ true}{isl' : isLambda? trm' ≡ true} → SubΛ-base trm isl ≡ SubΛ-base trm' isl'
SubΛ-base-eq {trm} {.trm} {refl} {isl} {isl'}  = cong (λ w -> SubΛ-base trm w) (AB-K isl isl')

isCombinator-SubΛ-base : {m : ℕ} {trm : Term}{scoping : (Scope trm <= m) ≡ true} → (isl : isLambda? (Λ m trm {scoping}) ≡ true) → isCombinator (SubΛ-base (Λ m trm {scoping}) isl) ≡ true
isCombinator-SubΛ-base {m} {Self} {scoping} refl = refl
isCombinator-SubΛ-base {m} {(! n)} {scoping} refl = refl
isCombinator-SubΛ-base {m} {` x} {scoping} refl = refl
isCombinator-SubΛ-base {m} {Λ n trm} {scoping} refl = refl
isCombinator-SubΛ-base {m} {trm1 · trm2} {scoping} refl = refl

ssuc'Pred'-id : {trm1 trm2 : Term} → (ssuc' (SuperArity (trm1 · trm2)) ≡ SuperArity trm1)
ssuc'Pred'-id {trm1}{trm2} with SuperArity trm1 
...                   | nothing = refl
...                   | just z = cong (λ w → just w) suc'Pred'-id

isLambda?nSubΛ : {n : ℕ} → {trm : Term} → (scoping : (Scope trm <= n) ≡ true) → isLambda?n n (SubΛ-base (Λ n trm {scoping}) refl) ≡ true 
isLambda?nSubΛ {zero} {Self} refl = refl
isLambda?nSubΛ {suc n} {Self} refl with ℕ-Dec (suc n) (suc n) 
... | yes x = refl
... | no x = ⊥-elim (x refl)
isLambda?nSubΛ {zero} {(! m)} refl = refl
isLambda?nSubΛ {suc n} {(! m)} refl with ℕ-Dec (suc n) (suc n) 
... | yes x = refl
... | no x = ⊥-elim (x refl)
isLambda?nSubΛ {zero} {` x} scoping = refl
isLambda?nSubΛ {suc n} {` x} scoping with ℕ-Dec (suc n) (suc n) 
... | yes x = refl
... | no x = ⊥-elim (x refl)
isLambda?nSubΛ {zero} {Λ m trm {scoping'}} scoping = refl
isLambda?nSubΛ {suc n} {Λ m trm {scoping'}} scoping  with ℕ-Dec (suc n) (suc n) 
... | yes x = refl
... | no x = ⊥-elim (x refl)
isLambda?nSubΛ {zero} {trm · trm₁} scoping = refl
isLambda?nSubΛ {suc n} {trm · trm₁} scoping  with ℕ-Dec (suc n) (suc n) 
... | yes x = refl
... | no x = ⊥-elim (x refl)

AppFold' : {n : ℕ} → (trm : Term) → (superarity : SuperArity trm ≡ just (+ (suc n))) → (isc : isCombinator trm ≡ true) → Σ[ x ∈ Term ] ((isLambda?n n x) ≡ true)
AppFold' {n} (Λ m trm {scoping}) superarity isc with ℕ-Dec n m
... | yes refl = ((SubΛ-base (Λ n trm {scoping}) refl)) , isLambda?nSubΛ {n}{trm} scoping
... | no x = ⊥-elim (x (suc≡suc-lemma (sym hlp)))
            where
              hlp : suc m ≡ suc n
              hlp = cong ℤ→ℕ (just-elim superarity)
AppFold' {n} (trm1 · trm2) superarity isc = (SubstituteΛ {suc n}
                                             (proj₁ (AppFold' {(suc n)} trm1 (·SuperArity-lemma' {suc n}{trm1}{trm2} superarity) (∧-elim-left isc)))
                                             (proj₂ (AppFold' {(suc n)} trm1 (·SuperArity-lemma' {suc n}{trm1}{trm2} superarity) (∧-elim-left isc)))
                                             trm2
                                             (∧-elim-right isc)
                                             ) ,
                                             SubstituteΛ-lemma
                                             (proj₁ (AppFold' {(suc n)} trm1 (·SuperArity-lemma' {suc n}{trm1}{trm2} superarity) (∧-elim-left isc)))
                                             (proj₂ (AppFold' {(suc n)} trm1 (·SuperArity-lemma' {suc n}{trm1}{trm2} superarity) (∧-elim-left isc)))
                                             trm2
                                             (∧-elim-right isc)
         where
           hlp : (isLambda?n (suc n) (proj₁ (AppFold' {(suc n)} trm1 (·SuperArity-lemma' {suc n}{trm1}{trm2} superarity) (∧-elim-left isc)))) ≡ true
           hlp =  (proj₂ (AppFold' {(suc n)} trm1 (·SuperArity-lemma' {suc n}{trm1}{trm2} superarity) (∧-elim-left isc)))

·AppFold'-lemma : {trm1 trm3 : Term}{superarity : SuperArity (trm1 · trm3) ≡ just +[1+ 0 ]}{isc : isCombinator trm1 ∧ isCombinator trm3 ≡ true} →
                  (AppFold' {0} (trm1 · trm3) superarity isc) ≡
                  ((SubstituteΛ {1} (proj₁ (AppFold' {1} trm1 (·SuperArity-lemma' {1} {trm1}{trm3} superarity) (∧-elim-left isc)))
                                    (proj₂ (AppFold' {(1)} trm1 (·SuperArity-lemma' {1}{trm1}{trm3} superarity) (∧-elim-left isc)))
                                     trm3 (∧-elim-right isc)) ,
                                        SubstituteΛ-lemma (proj₁ (AppFold' {1} trm1 (·SuperArity-lemma' {1}{trm1}{trm3} superarity) (∧-elim-left isc)))
                                                          (proj₂ (AppFold' {1} trm1 (·SuperArity-lemma' {1}{trm1}{trm3} superarity) (∧-elim-left isc)))
                                                           trm3 (∧-elim-right isc))   
·AppFold'-lemma {trm1}{trm3} = refl

AppFold'-def :  {n : ℕ} → (trm : Term) → (isl : isLambda?n n trm ≡ true) → proj₁ (AppFold' {n} trm (isLambda?n→SuperArity {n}{trm} isl) (isLambda?n→isCombinator {n} {trm} isl)) ≡ SubΛ-base trm (isLambda?n→isLambda? {n} {trm} isl) 
AppFold'-def {n} (Λ m trm {scoping}) isl with ℕ-Dec n m 
... | yes refl = refl

AppFold'-def2 : {n : ℕ} → (trm' : Term) → (scoping : (Scope trm' <= n) ≡ true) →
    proj₁ (AppFold' {n} (Λ n trm' {scoping}) (isLambda?n→SuperArity {n}{Λ n trm' {scoping}} (isLambda?nΛ {n} {trm'} scoping)) (isLambda?n→isCombinator {n} {Λ n trm' {scoping}} (isLambda?nΛ {n} {trm'} scoping))) ≡
    SubΛ-base (Λ n trm' {scoping}) (isLambda?n→isLambda? {n} {Λ n trm' {scoping}} (isLambda?nΛ {n} {trm'} scoping)) 
AppFold'-def2 {n} trm' scoping = AppFold'-def {n} trm isl
                     where
                       trm : Term
                       trm = Λ n trm' {scoping}
                       isl : isLambda?n n (Λ n trm' {scoping}) ≡ true
                       isl = isLambda?nΛ {n} {trm'} scoping

AppFold'-def4-hlp : {n : ℕ} → (trm' : Term) → (scoping : (Scope trm' <= n) ≡ true) →
                                    (·SuperArity-lemma' {n} {Λ n trm' {scoping}} {trm'} refl) ≡
                                    (isLambda?n→SuperArity {n}{Λ n trm' {scoping}} (isLambda?nΛ {n} {trm'} scoping))
AppFold'-def4-hlp {n} trm' scoping = K-Maybeℤ hlp hlp'
    where
      hlp : (SuperArity (Λ n trm' {scoping}) ≡ just (+[1+ n ] ))
      hlp = (·SuperArity-lemma' {n} {Λ n trm' {scoping}} {trm'} refl) 
      hlp' : (SuperArity (Λ n trm' {scoping}) ≡ just (+[1+ n ] ))
      hlp' = (isLambda?n→SuperArity {n}{Λ n trm' {scoping}} (isLambda?nΛ {n} {trm'} scoping))

AppFold'-def3 : {n : ℕ} → (trm' : Term) → (scoping : (Scope trm' <= n) ≡ true) →
    proj₁ (AppFold' {n} (Λ n trm' {scoping}) (isLambda?n→SuperArity {n}{Λ n trm' {scoping}} (isLambda?nΛ {n} {trm'} scoping)) refl) ≡
    SubΛ-base (Λ n trm' {scoping}) (isLambda?n→isLambda? {n} {Λ n trm' {scoping}} (isLambda?nΛ {n} {trm'} scoping)) 
AppFold'-def3 {n} trm' scoping = AppFold'-def {n} trm isl
                     where
                       trm : Term
                       trm = Λ n trm' {scoping}
                       isl : isLambda?n n (Λ n trm' {scoping}) ≡ true
                       isl = isLambda?nΛ {n} {trm'} scoping

AppFold'-def4 : {n : ℕ} → (trm' : Term) → (scoping : (Scope trm' <= n) ≡ true) →
    proj₁ (AppFold' {n} (Λ n trm' {scoping}) (·SuperArity-lemma' {n} {Λ n trm' {scoping}} {trm'} refl) refl) ≡
    proj₁ (AppFold' {n} (Λ n trm' {scoping}) (isLambda?n→SuperArity {n}{Λ n trm' {scoping}} (isLambda?nΛ {n} {trm'} scoping)) refl) 
AppFold'-def4 {n} trm' scoping = cong (λ w → proj₁ (AppFold' {n} ((Λ n trm' {scoping})) w refl)) (AppFold'-def4-hlp trm' scoping)
                   

AppFold : {n : ℕ} → (trm : Term) → (superarity : SuperArity trm ≡ just (+ n)) → (isc : isCombinator trm ≡ true) → Term
AppFold {zero} (trm1 · trm2) superarity isc = Substitute zero (isLambda?→inner {proj₁ hlp'} (isLambda?n→isLambda? (proj₂ hlp'))) trm2
                                where
                                  hlp' :  Σ[ x ∈ Term ] ((isLambda?n zero x) ≡ true)
                                  hlp' = AppFold' {zero} trm1 (·SuperArity-lemma' {zero}{trm1}{trm2} superarity) (∧-elim-left isc)
AppFold {suc n} trm superarity isc = proj₁ (AppFold' {n} trm superarity isc)

AppFold'Λ-lemma : {m : ℕ} → {trm : Term} → (scoping : (Scope trm <= m) ≡ true) → Scope (proj₁ (AppFold' (Λ m trm {scoping}) refl refl)) ≡ 0
AppFold'Λ-lemma {m} {trm} scoping with  (AppFold' (Λ m trm {scoping}) refl refl) 
... | Λ n fst {scoping} , snd = refl

ScopeAppFold'-lemma : {n : ℕ} → {trm : Term} → (arity : SuperArity trm ≡ just (+ (suc n))) → (isc : isCombinator trm ≡ true) → Scope (proj₁ (AppFold' {n} trm arity isc)) ≡ 0
ScopeAppFold'-lemma {n} {trm} arity isc with (AppFold' {n} trm arity isc) 
... | Λ m fst , snd = refl

isCombinatorAppFold'-lemma : {n : ℕ} → {trm : Term} → (arity : SuperArity trm ≡ just (+ (suc n))) → (isc : isCombinator trm ≡ true) → isCombinator (proj₁ (AppFold' {n} trm arity isc)) ≡ true
isCombinatorAppFold'-lemma {n} {trm} arity isc with (proj₂ (AppFold' {n} trm arity isc)) 
... | w = isLambda?n→isCombinator {n} {proj₁ ((AppFold' {n} trm arity isc))} w

ScopeAppFold-lemma : {n : ℕ} → {trm : Term} → (arity : SuperArity trm ≡ just (+ n)) → (isc : isCombinator trm ≡ true) → Scope (AppFold trm arity isc) ≡ 0
ScopeAppFold-lemma {zero} {trm1 · trm2} arity isc = Scope0SubstituteScope-lemma {isLambda?→inner {proj₁ hlp} (isLambda?n→isLambda? {0}{proj₁ hlp} (proj₂ hlp))}{trm2} hlp' (isCombinatorScope {trm2} (∧-elim-right isc))
                                where
                                 hlp : Σ _ λ x → isLambda?n zero x ≡ true 
                                 hlp = (AppFold' {zero} trm1 (·SuperArity-lemma' {zero}{trm1}{trm2} arity) (∧-elim-left isc))
                                 hlp' :  Scope (isLambda?→inner {proj₁ hlp} (isLambda?n→isLambda? {0}{proj₁ hlp} (proj₂ hlp))) ≡ 0
                                 hlp' = isLambda?0-inner-Scope0-Lemma {proj₁ hlp} (proj₂ hlp) 
ScopeAppFold-lemma {suc n} {trm} arity isc = ScopeAppFold'-lemma {n} {trm} arity isc 

ScopeAppFold-lemma' : {n : ℕ} → {trm : Term} → (arity : SuperArity trm ≡ just (+ n)) → (isc : isCombinator trm ≡ true) → Scope trm ≡ Scope (AppFold {n} trm arity isc)
ScopeAppFold-lemma' {n} {trm} arity isc = trans hlp (sym (ScopeAppFold-lemma arity isc))
                                     where
                                        hlp : Scope trm ≡ 0
                                        hlp = ScopeCombinator0 {trm} isc

ScopeSubstituteCombinator-lemma : {n : ℕ} {trm1 trm2 : Term} → (isCombinator trm1 ≡ true) → (isCombinator trm2 ≡ true) → (Scope (Substitute n trm1 trm2) <= 0) ≡ true
ScopeSubstituteCombinator-lemma {n}{trm1}{trm2} isc1 isc2 = trans<= {Scope (Substitute n trm1 trm2)}{ (Scope trm1 ⊔ Scope trm2)}{0} hlp (x⊔y<=0-intro {Scope trm1} {Scope trm2} (x≡y→x<=y≡true {Scope trm1} {0} scope1) (x≡y→x<=y≡true {Scope trm2} {0} scope2))
                                     where
                                      hlp : (Scope (Substitute n trm1 trm2) <= (Scope trm1 ⊔ Scope trm2)) ≡ true
                                      hlp = ScopeSubstitute {n}{trm1}{trm2}
                                      scope1 : Scope trm1 ≡ 0
                                      scope1 = ScopeCombinator0 {trm1} isc1
                                      scope2 : Scope trm2 ≡ 0
                                      scope2 = ScopeCombinator0 {trm2} isc2

ScopeSubstituteCombinator-lemma' : {trm1 trm2 : Term} → (scoping : (Scope trm1 <= 1) ≡ true) → (isCombinator trm2 ≡ true) → (Scope (Substitute 1 trm1 trm2) <= 0) ≡ true
ScopeSubstituteCombinator-lemma' {Self} {trm2} scoping isc = refl
ScopeSubstituteCombinator-lemma' {(! n)} {trm2} scoping isc = refl
ScopeSubstituteCombinator-lemma' {` zero} {trm2} scoping isc = refl
ScopeSubstituteCombinator-lemma' {` suc zero} {trm2} scoping isc = CombinatorScope0 {trm2} isc
ScopeSubstituteCombinator-lemma' {Λ n trm1} {trm2} scoping isc = refl
ScopeSubstituteCombinator-lemma' {trm1 · trm3} {trm2} scoping isc = x⊔y<=n-intro {Scope (Substitute 1 trm1 trm2)}{Scope (Substitute 1 trm3 trm2)}{0} hlp-left hlp-right
                                 where
                                   hlp-left : (Scope (Substitute 1 trm1 trm2)) <= 0 ≡ true
                                   hlp-left = ScopeSubstituteCombinator-lemma' {trm1}{trm2} (x⊔y<=n-left-elim {Scope trm1}{Scope trm3}{_} scoping) isc
                                   hlp-right : (Scope (Substitute 1 trm3 trm2)) <= 0 ≡ true
                                   hlp-right =  ScopeSubstituteCombinator-lemma' {trm3}{trm2} (x⊔y<=n-right-elim {Scope trm1}{Scope trm3}{_} scoping) isc

NoSelf : (trm : Term) → Bool
NoSelf Self = false
NoSelf (! n) = true
NoSelf (` x) = true
NoSelf (Λ n trm) = true
NoSelf (trm1 · trm2) = NoSelf trm1 ∧ NoSelf trm2

NoSelfSubΛ : {n : ℕ} → (trm : Term) → (scoping : (Scope trm <= n) ≡ true) → NoSelf (SubΛ-base (Λ n trm {scoping}) refl) ≡ true
NoSelfSubΛ Self scoping = refl
NoSelfSubΛ ((! n)) scoping = refl
NoSelfSubΛ (` x) scoping = refl
NoSelfSubΛ (Λ n trm) scoping = refl
NoSelfSubΛ (trm1 · trm2) scoping = refl

SelfSub-lemma : {n : ℕ} (trm : Term) → (trm' : Term) → (scoping : (Scope trm <= n) ≡ true) → NoSelf (SelfSub (Λ n trm {scoping}) trm') ≡ true
SelfSub-lemma {n} trm Self scoping = refl
SelfSub-lemma {n} trm (! n₁) scoping = refl
SelfSub-lemma {n} trm (` x) scoping = refl
SelfSub-lemma {n} trm (Λ n₁ trm') scoping = refl
SelfSub-lemma {n} trm (trm' · trm'') scoping = ∧-intro (SelfSub-lemma trm trm' scoping) (SelfSub-lemma trm trm'' scoping)

NoSelfSelfSub : (trm1 : Term) → (trm2 : Term) → (scoping : ((Scope trm1 ⊔ Scope trm2) <= zero) ≡ true) → NoSelf (SelfSub (Λ zero (trm1 · trm2) {scoping}) trm1) ≡ true
NoSelfSelfSub trm1 trm2 scoping = SelfSub-lemma (trm1 · trm2) trm1 scoping

NoSelfSelfSub' : (trm1 : Term) → (trm2 : Term) → (scoping : ((Scope trm1 ⊔ Scope trm2) <= zero) ≡ true) → NoSelf (SelfSub (Λ zero (trm1 · trm2) {scoping}) trm2) ≡ true
NoSelfSelfSub' trm1 trm2 scoping = SelfSub-lemma (trm1 · trm2) trm2 scoping

NoSelfIsCombinatorExpr : {trm : Term} → isCombinator trm ≡ true → NoSelf trm ≡ true
NoSelfIsCombinatorExpr {(! n)} refl = refl
NoSelfIsCombinatorExpr {Λ n trm {scoping}} isc = refl
NoSelfIsCombinatorExpr {trm1 · trm2} isc = ∧-intro (NoSelfIsCombinatorExpr {trm1} (∧-elim-left isc)) (NoSelfIsCombinatorExpr {trm2} (∧-elim-right isc))

NoSelfAppFold : {n : ℕ} → (trm : Term) → (superarity : SuperArity trm ≡ just +[1+ n ]) → (isc : isCombinator trm ≡ true) → (NoSelf (proj₁ (AppFold' {n} trm superarity isc))) ≡ true
NoSelfAppFold {n} trm superarity isc = NoSelfIsCombinatorExpr {(proj₁ (AppFold' {n} trm superarity isc))} (isCombinatorAppFold'-lemma {n}{trm} superarity isc)

NoSelfAppFold'Λ : {m : ℕ} → {trm : Term} → (scoping : (Scope trm <= m) ≡ true) → NoSelf (proj₁ (AppFold' {m} (Λ m trm {scoping}) refl refl)) ≡ true
NoSelfAppFold'Λ {zero} {trm} scoping = NoSelfSubΛ {0} trm scoping
NoSelfAppFold'Λ {suc m} {trm} scoping = NoSelfAppFold {suc m} (Λ (suc m) trm {scoping}) refl refl

NoSelf-inner : {trm arg : Term} → (scoping : Scope trm ≡ 0) → (NoSelf trm ≡ true) → (iscx : isCombinator arg ≡ true) → (isCombinator (Substitute zero trm arg)) ≡ true
NoSelf-inner {(! n)} {arg} scoping refl iscx = refl
NoSelf-inner {` .0} {arg} refl noself iscx = iscx
NoSelf-inner {Λ n trm {scoping'}} {arg} refl noself iscx = refl
NoSelf-inner {trm1 · trm2} {arg} scoping noself iscx = ∧-intro hlp hlp'
                               where
                                 hlp : isCombinator (Substitute zero trm1 arg) ≡ true
                                 hlp = NoSelf-inner {trm1}{arg} (x⊔≡0-left-elim scoping) (∧-elim-left noself) iscx
                                 hlp' : isCombinator (Substitute zero trm2 arg) ≡ true
                                 hlp' = NoSelf-inner {trm2}{arg} (x⊔≡0-right-elim scoping) (∧-elim-right noself) iscx

NoSelf-inner' : {n : ℕ} {trm arg : Term} → (scoping : Scope trm <= n ≡ true) → (NoSelf trm ≡ true) → (iscx : isCombinator arg ≡ true) → (NoSelf (Substitute n trm arg)) ≡ true
NoSelf-inner' {n} {(! m)} {arg} scoping refl iscx = refl
NoSelf-inner' {zero} {` zero} {arg} scoping refl iscx = NoSelfIsCombinatorExpr {arg} iscx
NoSelf-inner' {suc n} {` zero} {arg} scoping refl iscx = refl
NoSelf-inner' {suc n} {` suc x} {arg} scoping refl iscx with ℕ-Dec n x
... | yes y =  NoSelfIsCombinatorExpr {arg} iscx
... | no y = refl
NoSelf-inner' {n} {Λ m trm {scoping'}} {arg} scoping refl iscx = refl
NoSelf-inner' {n} {trm1 · trm2} {arg} scoping noself iscx = ∧-intro (NoSelf-inner' {n}{trm1}{arg}  (x⊔y<=n-elim-left {Scope trm1}{Scope trm2}{n} scoping) (∧-elim-left noself) iscx) (NoSelf-inner' {n}{trm2}{arg} (x⊔y<=n-elim-right {Scope trm1}{Scope trm2}{n} scoping) (∧-elim-right noself) iscx)

isCombinatorExprSubstitute-lemma' : {trm arg : Term} → Scope trm ≡ 0 → NoSelf trm ≡ true → isCombinator arg ≡ true → isCombinator (Substitute 0 trm arg) ≡ true
isCombinatorExprSubstitute-lemma' {Self} {arg} scp () isc
isCombinatorExprSubstitute-lemma' {(! n)} {arg} scp noself isc = refl
isCombinatorExprSubstitute-lemma' {` 0} {arg} refl refl isc = isc
isCombinatorExprSubstitute-lemma' {Λ n trm {scoping}} {arg} scp noself isc = refl
isCombinatorExprSubstitute-lemma' {trm1 · trm2} {arg} scp noself isc = ∧-intro 
                                  (isCombinatorExprSubstitute-lemma' {trm1} {arg} (x⊔≡0-left-elim scp) (∧-elim-left noself) isc) 
                                  (isCombinatorExprSubstitute-lemma' {trm2} {arg} (x⊔≡0-right-elim scp) (∧-elim-right noself) isc)

myterm-lemma : {arg : Term} → (mypair : Σ Term λ x → (isLambda?n 0 x) ≡ true) → (isc : isCombinator arg ≡ true)
                                → NoSelf (isLambda?→inner {proj₁ mypair}
                                  (isLambda?n→isLambda? {0}{proj₁ mypair} (proj₂ mypair))) ≡ true
                                → isCombinator (Substitute zero (isLambda?→inner {proj₁ mypair}
                                  (isLambda?n→isLambda? {0}{proj₁ mypair} (proj₂ mypair))) arg) ≡ true
myterm-lemma {arg} (Λ n ((! m)) {scoping} , isl0) isc noself = refl
myterm-lemma {arg} (Λ n (` m) {scoping} , isl0) isc noself with ℕ-Dec 0 n | ℕ-Dec 0 m 
... | yes refl | yes refl = isc
... | yes refl | no x = ⊥-elim (x (sym (m<=0≡true→m≡0 scoping)))
myterm-lemma {arg} (Λ n (Λ m myinner) {scoping} , isl0) isc noself = refl
myterm-lemma {arg} (Λ n (myinner · myinner₁) {scoping} , isl0) isc noself with ℕ-Dec 0 n
... | yes refl = ∧-intro hlp1 hlp2
                 where
                   hlp1 : isCombinator (Substitute zero myinner arg) ≡ true
                   hlp1 = NoSelf-inner {myinner}{arg} (Scope0 {myinner} (·Scoping-elim-left {0}{myinner} {myinner₁} scoping)) (∧-elim-left noself) isc
                   hlp2 : isCombinator (Substitute zero myinner₁ arg) ≡ true
                   hlp2 = NoSelf-inner {myinner₁}{arg} (Scope0 {myinner₁} (·Scoping-elim-right {0}{myinner} {myinner₁} scoping)) (∧-elim-right noself) isc


noSelfSubstituteΛ-lemma :  {trm arg : Term} → (isl : isLambda?n 1 trm ≡ true) → (isc-arg : isCombinator arg ≡ true)
                               →  NoSelf (isLambda?→inner {trm} (isLambda?n→isLambda? {suc 0} isl)) ≡ true
                                →  NoSelf (isLambda?→inner {SubstituteΛ trm isl arg isc-arg}
                                           ( isLambda?n→isLambda? {0} (SubstituteΛ-lemma {0} trm isl arg isc-arg) )) ≡ true
noSelfSubstituteΛ-lemma {Λ (suc zero) (! m) {refl}} {arg} isl isc-arg refl = refl
noSelfSubstituteΛ-lemma {Λ (suc zero) (` zero) {scoping}} {arg} refl isc-arg refl = refl
noSelfSubstituteΛ-lemma {Λ (suc zero) (` suc zero) {refl}} {arg} refl isc-arg refl = NoSelfIsCombinatorExpr {arg} isc-arg
noSelfSubstituteΛ-lemma {Λ (suc zero) (Λ zero trm {scoping'}) {refl}} {arg} isl isc-arg refl = refl
noSelfSubstituteΛ-lemma {Λ (suc zero) (Λ (suc m) trm {scoping'}) {refl}} {arg} isl isc-arg refl = refl
noSelfSubstituteΛ-lemma {Λ (suc zero) (trm1 · trm2) {scoping}} {arg} isl isc-arg noself = ∧-intro (NoSelf-inner' {1} {trm1}{arg} (·Scoping-elim-left {1}{trm1}{trm2} scoping) (∧-elim-left noself) isc-arg) ((NoSelf-inner' {1} {trm2}{arg} (·Scoping-elim-right {1}{trm1}{trm2} scoping) (∧-elim-right noself) isc-arg))

noSelfSubstituteΛn-lemma : {n : ℕ} {trm arg : Term} → (isl : isLambda?n (suc n) trm ≡ true) → (isc-arg : isCombinator arg ≡ true)
                               →  NoSelf (isLambda?→inner {trm} (isLambda?n→isLambda? {suc n} isl)) ≡ true
                                →  NoSelf (isLambda?→inner {SubstituteΛ trm isl arg isc-arg}
                                           ( isLambda?n→isLambda? {n} (SubstituteΛ-lemma {n} trm isl arg isc-arg) )) ≡ true
noSelfSubstituteΛn-lemma {zero} {Λ (suc m) (! y) {refl}} {arg} isl isc-arg refl with ℕ-Dec 0 m 
... | yes refl = refl
noSelfSubstituteΛn-lemma {suc n} {Λ (suc m) (! y) {refl}} {arg} isl isc-arg refl with ℕ-Dec (suc n) m 
... | yes refl = refl
noSelfSubstituteΛn-lemma {zero} {Λ (suc zero) (` zero) {refl}} {arg} isl isc-arg refl = refl
noSelfSubstituteΛn-lemma {zero} {Λ (suc zero) (` suc zero) {refl}} {arg} refl isc-arg refl = NoSelfIsCombinatorExpr {arg} isc-arg
noSelfSubstituteΛn-lemma {suc n} {Λ (2+ m) (` zero) {refl}} {arg} isl isc-arg refl with ℕ-Dec n m 
... | yes refl = refl
noSelfSubstituteΛn-lemma {suc n} {Λ (2+ m) (` suc x) {scoping}} {arg} isl isc-arg refl with ℕ-Dec n m | ℕ-Dec ((suc n)) (x) 
... | yes refl | yes refl = NoSelf-inner' {suc x}{` suc x}{arg} scoping refl isc-arg
... | yes refl | no y = NoSelf-inner' {suc (suc n)}{` suc x}{arg} scoping refl isc-arg
noSelfSubstituteΛn-lemma {zero} {Λ (suc zero) (Λ m' trm' {scoping'}) {refl}} {arg} refl isc-arg refl = refl
noSelfSubstituteΛn-lemma {suc n} {Λ (2+ m) (Λ m' trm' {scoping'}) {refl}} {arg} isl isc-arg refl with ℕ-Dec n m  
... | yes refl = refl
noSelfSubstituteΛn-lemma {zero} {Λ (suc zero) (trm1 · trm2) {scoping}} {arg} refl isc-arg noself =  ∧-intro (NoSelf-inner' {1} {trm1}{arg} (·Scoping-elim-left {1}{trm1}{trm2} scoping) (∧-elim-left noself) isc-arg) ((NoSelf-inner' {1} {trm2}{arg} (·Scoping-elim-right {1}{trm1}{trm2} scoping) (∧-elim-right noself) isc-arg)) 
noSelfSubstituteΛn-lemma {suc n} {Λ (2+ m) (trm1 · trm2) {scoping}} {arg} isl isc-arg noself with ℕ-Dec (suc n) (suc m) -- {!!} ∧-intro
... | yes refl = ∧-intro  (NoSelf-inner' {_}{trm1}{arg} (·Scoping-elim-left {suc (suc n)}{trm1}{trm2} scoping) (∧-elim-left noself) isc-arg) (NoSelf-inner' {suc (suc n)} {trm2}{arg} (·Scoping-elim-right {suc (suc n)}{trm1}{trm2} scoping) (∧-elim-right noself) isc-arg)
  
NoSelfAppFold'-hlp2 : {n : ℕ} -> (trm : Term) -> (scoping : (Scope trm <= n) ≡ true) -> 
  NoSelf ( isLambda?→inner {SubΛ-base (Λ n trm {scoping}) refl} (isLambda?n→isLambda? {n} {SubΛ-base (Λ n trm {scoping}) (isLambda?n→isLambda? {n}{Λ n trm {scoping}} (isLambda?nΛ {n}{trm} scoping))} (isLambda?nSubΛ {n}{trm} scoping))) ≡ true
NoSelfAppFold'-hlp2 {n} Self refl = refl
NoSelfAppFold'-hlp2 {n} (! n₁) scoping = refl
NoSelfAppFold'-hlp2 {n} (` x) scoping = refl
NoSelfAppFold'-hlp2 {n} (Λ n₁ trm) scoping = refl
NoSelfAppFold'-hlp2 {n} (trm1 · trm2) scoping = ∧-intro hlp hlp'
                          where
                            hlp : NoSelf (SelfSub (Λ n (trm1 · trm2)) trm1) ≡ true
                            hlp = SelfSub-lemma (trm1 · trm2) trm1 scoping
                            hlp' : NoSelf (SelfSub (Λ n (trm1 · trm2)) trm2) ≡ true
                            hlp' = SelfSub-lemma (trm1 · trm2) trm2 scoping  

NoSelfBool-lemma : {n' : ℕ} -> (trm' : Term) -> (scoping : (Scope trm' <= n') ≡ true) ->
   (SubΛ-base (Λ n' trm' {scoping}) (isLambda?n→isLambda? {n'}{Λ n' trm' {scoping}} (isLambda?nΛ {n'}{trm'} scoping)) ≡
   (proj₁ (AppFold' {n'} (Λ n' trm' {scoping}) (·SuperArity-lemma' {n'} {Λ n' trm' {scoping}} {trm'} refl) refl))) 
NoSelfBool-lemma {n'} trm' scoping = trans (sym (AppFold'-def3 trm' scoping)) (sym (AppFold'-def4 trm' scoping))


NoSelf≡-lemma-hlp :  {n : ℕ} → {trm : Term} → (isl : isLambda?n n trm ≡ true) → (isl' : isLambda?n n trm ≡ true) →  (noself1 : NoSelf (isLambda?→inner {_} (isLambda?n→isLambda? {_} {trm} isl)) ≡ true) → (isl ≡ isl') →  NoSelf (isLambda?→inner {_} (isLambda?n→isLambda? {_} {trm} isl')) ≡ true
NoSelf≡-lemma-hlp {n} {trm} isl .isl eqn refl = eqn

NoSelf≡-lemma : {n : ℕ} → {trm trm' : Term} → (isl : isLambda?n n trm ≡ true) → (isl' : isLambda?n n trm' ≡ true) → (eqn : trm ≡ trm') → (noself1 : NoSelf (isLambda?→inner {_} (isLambda?n→isLambda? {_} {trm} isl)) ≡ true) →  NoSelf (isLambda?→inner {_} (isLambda?n→isLambda? {_} {trm'} isl')) ≡ true
NoSelf≡-lemma {n} {trm} {.trm} isl isl' refl noself1 = NoSelf≡-lemma-hlp {n} {trm} isl isl' noself1 (isLambda?n≡-lemma {n} {trm} isl isl') 

NoSelfAppFold'-hlp : {n : ℕ} -> (trm : Term) -> (arg : Term) -> (scoping : (Scope trm <= n) ≡ true) -> NoSelf
  (isLambda?→inner {_} (isLambda?n→isLambda? {_} 
    {(proj₁ (AppFold' {n} (Λ n trm {scoping}) (·SuperArity-lemma' {n} {Λ n trm {scoping}} {arg} refl) refl) )}
    ((proj₂ (AppFold' {n} (Λ n trm {scoping}) (·SuperArity-lemma' {n} {Λ n trm {scoping}} {arg} refl) refl) )))) ≡ true
NoSelfAppFold'-hlp {n} trm arg scoping = NoSelf≡-lemma {n}
                      {SubΛ-base (Λ n trm {scoping}) (isLambda?n→isLambda? {n}{Λ n trm {scoping}} (isLambda?nΛ {n}{trm} scoping))}
                      {(proj₁ (AppFold' {n} (Λ n trm {scoping}) (·SuperArity-lemma' {n} {Λ n trm {scoping}} {arg} refl) refl) )}
                      (isLambda?nSubΛ {n}{trm} scoping)
                      (proj₂ (AppFold' {n} (Λ n trm {scoping}) (·SuperArity-lemma' {n} {Λ n trm {scoping}} {arg} refl) refl))
                      (NoSelfBool-lemma trm scoping)
                      (NoSelfAppFold'-hlp2 {n} trm scoping) 

NoSelfAppFold' : {n : ℕ} (trm  : Term) → (arg : Term) → (superarity : ((SuperArity (trm · arg)) ≡ just (+ n))) → (isc : isCombinator trm ≡ true) → (iscx : isCombinator arg ≡ true) →           
                     NoSelf (isLambda?→inner {_} (isLambda?n→isLambda? {n}
                            {(proj₁ (AppFold' trm (·SuperArity-lemma' {n}{trm}{arg} superarity) (isc)))}
                             (proj₂ (AppFold' trm (·SuperArity-lemma' {n}{trm}{arg} superarity) (isc))) )) ≡ true 
NoSelfAppFold' {n} (Λ n trm {scoping}) arg refl refl noself = hlp
                       where
                         myterm : Term
                         myterm = (proj₁ (AppFold' {n} (Λ n trm {scoping}) (·SuperArity-lemma' {n} {Λ n trm {scoping}} {arg} refl) refl) )
                         myisl : isLambda?n (n) myterm ≡ true
                         myisl = (proj₂ (AppFold' {n} (Λ n trm {scoping}) (·SuperArity-lemma' {n} {Λ n trm {scoping}} {arg} refl) refl) )
                         hlp : NoSelf (isLambda?→inner {myterm} (isLambda?n→isLambda? {n}{myterm} myisl)) ≡ true
                         hlp = NoSelfAppFold'-hlp trm arg scoping
NoSelfAppFold' {n} (trm1 · trm2) arg superarity isc iscx = hlp
                      where                     
                         myterm : Term
                         myterm = (proj₁ (AppFold' trm1 (·SuperArity-lemma' {suc n}{trm1}{trm2}
                                                        (·SuperArity-lemma' {n}{trm1 · trm2}{arg} superarity)) (∧-elim-left isc)))
                         myisl : isLambda?n (suc n) myterm ≡ true
                         myisl = (proj₂ (AppFold' trm1 (·SuperArity-lemma' {suc n}{trm1}{trm2}
                                                        (·SuperArity-lemma' {n}{trm1 · trm2}{arg} superarity)) (∧-elim-left isc)))
                         subsmyterm : Term
                         subsmyterm = SubstituteΛ {suc n} myterm myisl trm2 (∧-elim-right isc)
                         subsisl : isLambda?n n (subsmyterm) ≡ true
                         subsisl = SubstituteΛ-lemma {n} myterm myisl trm2 (∧-elim-right isc)
                         hlp' : NoSelf (isLambda?→inner {myterm} (isLambda?n→isLambda? {suc n}{myterm} myisl)) ≡ true
                         hlp' = NoSelfAppFold' {suc n} trm1 trm2 (·SuperArity-lemma' {n}{trm1 · trm2}{arg} superarity) (∧-elim-left isc) (∧-elim-right isc)
                         hlp : NoSelf (isLambda?→inner {subsmyterm} (isLambda?n→isLambda? {n}{subsmyterm} subsisl)) ≡ true
                         hlp = noSelfSubstituteΛn-lemma {n}{myterm}{trm2} myisl (∧-elim-right isc)  hlp'       

myterm-lemma' : {trm1 trm2 : Term} → (superarity : SuperArity (trm1 · trm2) ≡ just +[1+ zero ]) → (isc1 : isCombinator trm1 ∧ isCombinator trm2 ≡ true) 
                                → NoSelf ( isLambda?→inner { (SubstituteΛ {suc 0}
                      (proj₁ (AppFold' trm1 (·SuperArity-lemma' {suc 0}{trm1}{trm2} superarity) (∧-elim-left isc1)))
                      (proj₂ (AppFold' trm1 (·SuperArity-lemma' {suc 0}{trm1}{trm2} superarity) (∧-elim-left isc1)))
                       trm2 (∧-elim-right isc1))}
                                         ( isLambda?n→isLambda? {0}{ (SubstituteΛ {suc 0}
                      (proj₁ (AppFold' trm1 (·SuperArity-lemma' {suc 0}{trm1}{trm2} superarity) (∧-elim-left isc1)))
                      (proj₂ (AppFold' trm1 (·SuperArity-lemma' {suc 0}{trm1}{trm2} superarity) (∧-elim-left isc1)))
                       trm2 (∧-elim-right isc1))} ( SubstituteΛ-lemma {0}
                      (proj₁ (AppFold' trm1 (·SuperArity-lemma' {suc 0}{trm1}{trm2} superarity) (∧-elim-left isc1)))
                      (proj₂ (AppFold' trm1 (·SuperArity-lemma' {suc 0}{trm1}{trm2} superarity) (∧-elim-left isc1)))
                                       trm2 (∧-elim-right isc1)) ) ) ≡ true
myterm-lemma' {trm1}{trm2} superarity isc1 = noSelfSubstituteΛ-lemma
                                              {proj₁ (AppFold' trm1 (·SuperArity-lemma' {suc 0}{trm1}{trm2} superarity) (∧-elim-left isc1))}
                                              {trm2}
                                              (proj₂ (AppFold' trm1 (·SuperArity-lemma' {suc 0}{trm1}{trm2} superarity) (∧-elim-left isc1)))
                                              (∧-elim-right isc1) (NoSelfAppFold' trm1 trm2 superarity (∧-elim-left isc1) (∧-elim-right isc1))

isCombinatorSubstitute-lemma' : {trm : Term} → (superarity : SuperArity trm ≡ just +[1+ zero ]) → (isc1 : isCombinator trm ≡ true) → {arg : Term} → (isc : isCombinator arg ≡ true)
    → isCombinator (Substitute zero (isLambda?→inner {proj₁ (AppFold' {zero} trm superarity (isc1))}
                       (isLambda?n→isLambda? {zero}{proj₁ (AppFold' {zero} trm superarity (isc1))}
                       (proj₂ (AppFold' trm superarity isc1)) ))
                        arg) ≡ true
isCombinatorSubstitute-lemma' {Λ 0 Self {scoping}} refl refl {arg} isc2 = refl
isCombinatorSubstitute-lemma' {Λ 0 (! n) {scoping}} refl refl {arg} isc2 = refl
isCombinatorSubstitute-lemma' {Λ 0 (` 0) {scoping}} refl refl {arg} isc2 = isc2
isCombinatorSubstitute-lemma' {Λ 0 (Λ n trm) {scoping}} refl refl {arg} isc2 = refl
isCombinatorSubstitute-lemma' {Λ 0 (trm1 · trm2) {scoping}} refl refl {arg} isc2 = ∧-intro hlp1 hlp2
                    where
                      hlp1-hlpa : Scope (SelfSub (Λ zero (trm1 · trm2) {scoping}) trm1) ≡ 0
                      hlp1-hlpa = ScopeSelfSub0 {Λ zero (trm1 · trm2) {scoping}}{trm1} refl (Scope0 {trm1} (·Scoping-elim-left {0} {trm1}{trm2} scoping)) 
                      hlp1-hlpb : Scope (SelfSub (Λ zero (trm1 · trm2) {scoping}) trm2) ≡ 0
                      hlp1-hlpb = ScopeSelfSub0 {Λ zero (trm1 · trm2) {scoping}}{trm2} refl (Scope0 {trm2} (·Scoping-elim-right {0} {trm1}{trm2} scoping)) 
                      hlp1 : isCombinator (Substitute zero (SelfSub (Λ zero (trm1 · trm2) {scoping}) trm1) arg) ≡ true
                      hlp1 = isCombinatorExprSubstitute-lemma' {SelfSub (Λ zero (trm1 · trm2) {scoping}) trm1}{arg}
                                                        hlp1-hlpa (NoSelfSelfSub trm1 trm2 scoping) isc2
                      hlp2 : isCombinator (Substitute zero (SelfSub (Λ zero (trm1 · trm2) {scoping}) trm2) arg) ≡ true
                      hlp2 = isCombinatorExprSubstitute-lemma' {SelfSub (Λ zero (trm1 · trm2) {scoping}) trm2}{arg} hlp1-hlpb (NoSelfSelfSub' trm1 trm2 scoping) isc2
isCombinatorSubstitute-lemma' {trm1 · trm2} superarity isc1 {arg} isc2 = hlp'
             where
               myterm : Term
               myterm = (SubstituteΛ {suc 0}
                     ((proj₁ (AppFold' trm1 (·SuperArity-lemma' {suc 0}{trm1}{trm2} superarity) (∧-elim-left isc1))))
                     ((proj₂ (AppFold' trm1 (·SuperArity-lemma' {suc 0}{trm1}{trm2} superarity) (∧-elim-left isc1))))
                                       trm2 (∧-elim-right isc1))
               hlp : (isLambda?n 0 myterm) ≡ true
               hlp = SubstituteΛ-lemma {0}
                     ((proj₁ (AppFold' trm1 (·SuperArity-lemma' {suc 0}{trm1}{trm2} superarity) (∧-elim-left isc1))))
                     ((proj₂ (AppFold' trm1 (·SuperArity-lemma' {suc 0}{trm1}{trm2} superarity) (∧-elim-left isc1))))
                                       trm2 (∧-elim-right isc1)
               myterm-pair : Σ Term λ x → (isLambda?n 0 x) ≡ true
               myterm-pair = myterm , hlp
               noself-myterm-hlp : NoSelf ((proj₁ (AppFold' trm1 (·SuperArity-lemma' {suc 0}{trm1}{trm2} superarity) (∧-elim-left isc1)))) ≡ true
               noself-myterm-hlp = NoSelfAppFold {suc 0} trm1 (·SuperArity-lemma' {suc 0}{trm1}{trm2} superarity) (∧-elim-left isc1)
               noself-trm2 : NoSelf trm2 ≡ true
               noself-trm2 = NoSelfIsCombinatorExpr {trm2} (∧-elim-right isc1)
               noself-myterm : NoSelf (isLambda?→inner (isLambda?n→isLambda? {0}{proj₁ myterm-pair} (proj₂ myterm-pair))) ≡ true
               noself-myterm = myterm-lemma' {trm1} {trm2} superarity isc1
               hlp' : isCombinator (Substitute zero (isLambda?→inner {proj₁ myterm-pair}
                                       (isLambda?n→isLambda? {0}{proj₁ myterm-pair} (proj₂ myterm-pair))) arg) ≡ true
               hlp' = myterm-lemma myterm-pair isc2 noself-myterm 

isCombinatorSubBase :{m : ℕ} → (trm : Term) → (scoping : (Scope trm <= m) ≡ true) → isCombinator (SubΛ-base (Λ m trm {scoping}) refl) ≡ true
isCombinatorSubBase {m} Self scoping = refl
isCombinatorSubBase {m} (! n) scoping = refl
isCombinatorSubBase {m} (` x) scoping = refl
isCombinatorSubBase {m} (Λ n trm {scoping'}) scoping = refl
isCombinatorSubBase {m} (trm1 · trm2) scoping = refl

isCombinatorExprAppFold : {n : ℕ}{trm : Term} → (superarity : SuperArity trm ≡ just (+ n)) → (isc : (isCombinator trm) ≡ true) → isCombinator (AppFold {n} trm superarity isc) ≡ true
isCombinatorExprAppFold {.(suc m)} {Λ m trm {scoping}} refl isc with ℕ-Dec m m
... | yes refl = isCombinatorSubBase trm scoping
... | no x = ⊥-elim (x refl) 
isCombinatorExprAppFold {zero} {trm1 · trm2} superarity isc = isCombinatorSubstitute-lemma' {trm1} (·SuperArity-lemma' {zero}{trm1}{trm2} superarity) (∧-elim-left isc) (∧-elim-right isc)
isCombinatorExprAppFold {suc n} {trm1 · trm2} superarity isc = isLambda?n→isCombinator {n}
                                 {SubstituteΛ (proj₁ (AppFold' trm1 (·SuperArity-lemma' {suc n}{trm1}{trm2} superarity) (∧-elim-left isc)))
                                              (proj₂ (AppFold' {suc n} trm1 (·SuperArity-lemma' {suc n}{trm1}{trm2} superarity) (∧-elim-left isc)))
                                                trm2 (∧-elim-right isc)}
                                 (SubstituteΛ-lemma {n}
                                              (proj₁ (AppFold' trm1 (·SuperArity-lemma' {suc n}{trm1}{trm2} superarity) (∧-elim-left isc)))
                                              (proj₂ (AppFold' {suc n} trm1 (·SuperArity-lemma' {suc n}{trm1}{trm2} superarity) (∧-elim-left isc)))
                                                trm2 (∧-elim-right isc))

superarity-K : {n : ℕ}{trm : Term} → (arity : SuperArity trm ≡ just (+ n)) → (arity' : SuperArity trm ≡ just (+ n)) → arity ≡ arity'
superarity-K {n}{trm} arity arity' = AB-K arity arity'

isCombinator-K : {trm : Term} → (isc : isCombinator trm ≡ true) →  (isc' : isCombinator trm ≡ true) → isc ≡ isc'
isCombinator-K {trm} isc isc' = AB-K isc isc'

isCombinator≡ :  {trm trm' : Term} → (isc : isCombinator trm ≡ true) → (eqn : trm ≡ trm') → isCombinator trm' ≡ true
isCombinator≡ {trm} {.trm} isc refl = isc

-------------------------
-- REDUCTION STEPS -----
------------------------

-- A type that expresses when a term can reduce to another term without imposing a specific reduction strategy.
-- Note that only application is without a prior 'step' (see terms called 'legit')
-- appFold reduces only when all the arguments are available. This is combinator behaviour.

data Step : Term → Term → Set where
 left-step : {trm1 : Term} → {trm2 : Term} → {trm1' : Term} → (legit : Step trm1 trm1' ) → Step (trm1 · trm2) (trm1' · trm2)
 right-step : {trm1 : Term} → {trm2 : Term} → {trm2' : Term} → (legit : Step trm2 trm2') → Step (trm1 · trm2) (trm1 · trm2')
 Λ-step : {n : ℕ} → {trm : Term} → {trm' : Term} → (legit : Step trm trm') → (scoping : (Scope trm <= n) ≡ true) → (scoping' : (Scope trm' <= n) ≡ true) → Step (Λ n trm {scoping}) (Λ n trm' {scoping'})
 appFold : {trm : Term} → (arity : SuperArity trm ≡ just (+ zero)) → (isc : isCombinator trm ≡ true) → {trm' : Term} → (eqn : trm' ≡ (AppFold {zero} trm arity isc)) →  Step trm trm'

ScopeStep-lemma :  {trm : Term} → {trm' : Term} → (legit : Step trm trm') → Scope trm ≡ Scope trm'
ScopeStep-lemma {.(_ · _)} {.(_ · _)} (left-step {trm1}{trm2}{trm'} legit) = cong (λ w → w  ⊔ (Scope trm2)) (ScopeStep-lemma {trm1}{trm'} legit )
ScopeStep-lemma {.(_ · _)} {.(_ · _)} (right-step {trm1}{trm2}{trm2'} legit) = cong (λ w → (Scope trm1) ⊔ w) (ScopeStep-lemma {trm2}{trm2'} legit )
ScopeStep-lemma {.(Λ _ _)} {.(Λ _ _)} (Λ-step legit scoping scoping') = refl
ScopeStep-lemma {trm} {.(AppFold trm arity isc)} (appFold {trm} arity isc refl) = ScopeAppFold-lemma' {_} {trm} arity isc

ScopeStep-lemma2 : {n : ℕ} {trm : Term}{trm' : Term} → (legit : Step trm trm') → ((Scope trm <= n) ≡ true) → ((Scope trm' <= n) ≡ true)
ScopeStep-lemma2 {n}{trm}{trm'} legit x = x<=n→xy→y<=n x (ScopeStep-lemma {trm}{trm'} legit)

isCombinatorExpr-Step-invar : {trm trm' : Term} -> (isc : isCombinator trm ≡ true) -> (arrow : Step trm trm') -> isCombinator trm' ≡ true
isCombinatorExpr-Step-invar {.(_ · _)} {.(_ · _)} isc (left-step {trm1} {trm2}{trm1'} arrow) = ∧-intro {isCombinator trm1'}{isCombinator trm2} (isCombinatorExpr-Step-invar (∧-elim-left isc) arrow) (∧-elim-right isc)
isCombinatorExpr-Step-invar {.(_ · _)} {.(_ · _)} isc (right-step {trm1}{trm2}{trm1'} arrow) = ∧-intro {isCombinator trm1}{isCombinator trm1'} (∧-elim-left isc) (isCombinatorExpr-Step-invar (∧-elim-right isc) arrow)
isCombinatorExpr-Step-invar {.(Λ _ _)} {.(Λ _ _)} isc (Λ-step arrow scoping scoping') = refl
isCombinatorExpr-Step-invar {trm} {.(AppFold trm arity isc₁)} isc (appFold {n} arity isc₁ refl) = isCombinatorExprAppFold {0} {trm} arity isc₁ 

SuperArityΛ-Step : {n : ℕ} {trm trm' : Term} {scoping : (Scope trm <= n) ≡ true} → Step (Λ n trm {scoping}) trm' → SuperArity trm' ≡ just +[1+ n ]
SuperArityΛ-Step {n} {trm} {.(Λ n _)} {scoping} (Λ-step steps .scoping scoping') = refl

Subst≡-Step :  {trm trm' trm'' : Term} → (trm' ≡ trm'') → (step : Step trm trm') → Step trm trm''
Subst≡-Step {trm}{trm'}{trm'} refl step = step

StepΛ-n≡0-lemma : {n m : ℕ} {trm arg trm' : Term} {scoping : (Scope trm <= n) ≡ true}{scoping' : (Scope trm' <= m) ≡ true} → Step ((Λ n trm {scoping}) · arg) (Λ m trm' {scoping'}) → n ≡ 0
StepΛ-n≡0-lemma {.zero} {m} {trm} {arg} {trm'} {scoping} {scoping'} (appFold {.(Λ zero trm · arg)} refl _ _) = refl

StepΛ-extract-lemma : {n m : ℕ} {trm trm' : Term} {scoping : (Scope trm <= n) ≡ true}{scoping' : (Scope trm' <= m) ≡ true} → Step (Λ n trm {scoping}) (Λ m trm' {scoping'}) → Step trm trm'  
StepΛ-extract-lemma {n} {.n} {trm} {trm'} {scoping} {scoping'} (Λ-step step .scoping .scoping') = step

!nToSelf→⊥ : {n : ℕ} → Step (! n) Self → ⊥
!nToSelf→⊥ {n} (appFold () refl eqn)

`xToSelf→⊥ : {x : ℕ} → Step (` x) Self → ⊥
`xToSelf→⊥ {x} (appFold arity () eqn)

-- The reflexive, multi-step version of Step (includes zero and chains of n steps).
-- This might be seen as the usual β reduction:
data StepN : Term → Term → Set where
  reflexive : (trm : Term) → StepN trm trm
  step1 : {trm : Term} → {trm' : Term}  → (step1 : Step trm trm') → StepN trm trm'
  step+ : {trm : Term} → {trm' : Term} → {trm'' : Term} → (chain : StepN trm trm') → (next : Step trm' trm'') → StepN trm trm''

transitivity : {trm : Term} → {trm' : Term} → {trm'' : Term} → (chain1 : StepN trm trm') → (chain2 : StepN trm' trm'') → StepN trm trm''
transitivity {trm} {trm'} {.trm'} chain1 (reflexive .trm') = chain1
transitivity {trm} {trm'} {trm''} chain1 (step1 step2) = step+ chain1 step2
transitivity {trm} {trm'} {trm''} chain1 (step+ chain2 next) = step+ (transitivity chain1 chain2) next

ScopeStepN-lemma : {trm trm' : Term} → (steps : StepN trm trm') → Scope trm ≡ Scope trm'
ScopeStepN-lemma {trm} {.trm} (reflexive .trm) = refl
ScopeStepN-lemma {trm} {trm'} (step1 step2) = ScopeStep-lemma step2
ScopeStepN-lemma {trm} {trm'} (step+ chain next) = trans (ScopeStepN-lemma chain) (ScopeStep-lemma next)

+step : {trm : Term} → {trm' : Term} → {trm'' : Term} → (previous : Step trm trm') → (chain : StepN trm' trm'') → StepN trm trm''
+step {trm} {trmì} {trm''} previous chain = transitivity (step1 previous) chain

Λ-stepN-hlp :  {n : ℕ} {trm : Term} → (scoping1 : (Scope trm <= n) ≡ true) → (scoping2 : (Scope trm <= n) ≡ true) → scoping1 ≡ scoping2 →  StepN (Λ n trm {scoping1}) (Λ n trm {scoping1}) →  StepN (Λ n trm {scoping1}) (Λ n trm {scoping2})
Λ-stepN-hlp {n} {trm} scoping1 .scoping1 refl stepn = stepn

Λ-stepN-hlp2 : {n : ℕ} {trm trm' : Term} → (scoping1 : (Scope trm <= n) ≡ true) → Scope trm ≡ Scope trm' → (Scope trm' <= n) ≡ true 
Λ-stepN-hlp2 {n}{trm}{trm'} scoping1 scopes = sub<= scopes scoping1

Λ-stepN : {n : ℕ} {trm : Term} → {trm' : Term} → (scoping1 : (Scope trm <= n) ≡ true) → (scoping2 : (Scope trm' <= n) ≡ true) → StepN trm trm' → StepN (Λ n trm {scoping1}) (Λ n trm' {scoping2})
Λ-stepN {n} {trm} {.trm} scoping1 scoping2 (reflexive .trm) = Λ-stepN-hlp {n} {trm} scoping1 scoping2 hlp hlp2
                                          where
                                            hlp : scoping1 ≡ scoping2
                                            hlp = K-bool scoping1 scoping2
                                            hlp2 : StepN (Λ n trm {scoping1}) (Λ n trm {scoping1})
                                            hlp2 = reflexive (Λ n trm {scoping1})
Λ-stepN {n} {trm} {trm'} scoping1 scoping2 (step1 step2) = step1 (Λ-step step2 scoping1 scoping2)
Λ-stepN {n} {trm} {trm'} scoping1 scoping2 (step+ {trm}{trm''}{trm'} stepn next) = transitivity hlpN hlpN'
                                               where
                                                 scoping3 : (Scope trm'' <= n) ≡ true
                                                 scoping3 = Λ-stepN-hlp2 {n}{trm}{trm''} scoping1 (ScopeStepN-lemma {trm}{trm''} stepn)
                                                 hlpN : StepN (Λ n trm {scoping1}) (Λ n trm'' {scoping3})
                                                 hlpN = Λ-stepN scoping1 scoping3 stepn
                                                 hlpN' : StepN (Λ n trm'' {scoping3}) (Λ n trm' {scoping2})
                                                 hlpN' =  Λ-stepN scoping3 scoping2 (step1 next)

app-StepN : (trm : Term) → (arity : SuperArity trm ≡ just (+ zero)) → (isc : isCombinator trm ≡ true) →  StepN trm (AppFold trm arity isc)
app-StepN (trm1 · trm2) arity isc = step1 (appFold arity isc refl)

·-stepN : {M N M' N' : Term} → StepN M M' → StepN N N' → StepN (M · N) (M' · N') 
·-stepN {M} {N} {.M} {.N} (reflexive .M) (reflexive .N) = reflexive (M · N)
·-stepN {M} {N} {M'} {.N} (step1 {trm} {trm'} step2) (reflexive .N) = step1 (left-step step2)
·-stepN {M} {N} {M'} {.N} (step+ stpm next) (reflexive .N) = transitivity (·-stepN stpm (reflexive N)) (step1 (left-step next))
·-stepN {M} {N} {.M} {N'} (reflexive .M) (step1 step2) = step1 (right-step step2)
·-stepN {M} {N} {M'} {N'} (step1 step3) (step1 step2) = transitivity (·-stepN {M}{N}{M'}{N} (step1 step3) (reflexive N)) (·-stepN {M'}{N}{M'}{N'} (reflexive M') (step1 step2))
·-stepN {M} {N} {M'} {N'} (step+ {M}{trm''}{M'} stpm next) (step1 step2) = transitivity (·-stepN stpm (step1 step2)) (·-stepN (step1 next) (reflexive N'))
·-stepN {M} {N} {.M} {N'} (reflexive .M) (step+ {N}{trm'}{N'} stpn next) = transitivity (·-stepN (reflexive M) stpn) (·-stepN (reflexive M) (step1 next))
·-stepN {M} {N} {M'} {N'} (step1 step2) (step+ {N}{trm'}{N'} stpn next) = transitivity (·-stepN (step1 step2) stpn) (·-stepN (reflexive M') (step1 next))
·-stepN {M} {N} {M'} {N'} (step+ {M}{trm'}{M'} stpm next1) (step+ {N}{trm2'}{N'} stpn next2) = transitivity (·-stepN stpm  (reflexive N)) (transitivity (·-stepN (step1 next1) stpn) (·-stepN (reflexive M') (step1 next2)))

¬Λntrm→¬trm≡ : {n : ℕ}{trm : Term}{trm' : Term}{scoping : (Scope trm <= n) ≡ true} {scoping' : (Scope trm' <= n) ≡ true}
                  → ¬ (Λ n trm {scoping} ≡ Λ n trm' {scoping'}) → ¬ (trm ≡ trm')
¬Λntrm→¬trm≡ {n}{trm}{trm'} {scoping} {scoping'} neqn = λ x → neqn (trm1≡trm→Λntrm1≡Λmtrm2 refl x)

Step-Λ-lemma : {n : ℕ} {trm : Term}{scoping : (Scope trm <= n) ≡ true} → (M : Term) → Step (Λ n trm {scoping}) M → isLambda?n n M ≡ true
Step-Λ-lemma {n} {trm} {scoping} .(Λ n _) (Λ-step steplambda .scoping scoping') with ℕ-Dec n n 
... | yes refl = refl
... | no x = ⊥-elim (x refl)


-- A 0 or 1-step parallel reduction on Term -- 
data ->> : Term → Term → Set where
  reflexive : (trm : Term) → ->> trm trm
  node : (trm : Term) → (trm' : Term) → Step trm trm' → ->> trm trm'
  Λ-step : (n : ℕ) → (trm : Term) → (trm' : Term) → (scoping : (Scope trm <= n) ≡ true) → (scoping' : (Scope trm' <= n) ≡ true) → (arrow : ->> trm trm')
                   → ->> (Λ n trm {scoping}) (Λ n trm' {scoping'})
  ·-step : (trm1 : Term) → (trm1' : Term) → (trm2 : Term) → (trm2' : Term) → (legit1 : ->> trm1 trm1') → (legit2 : ->> trm2 trm2')
                   → ->> (trm1 · trm2) (trm1' · trm2')

Scope->>-lemma :  {trm : Term} → {trm' : Term} → (legit : ->> trm trm') → Scope trm ≡ Scope trm'
Scope->>-lemma {trm} {.trm} (reflexive .trm) = refl
Scope->>-lemma {trm} {trm'} (node .trm .trm' x) = ScopeStep-lemma x
Scope->>-lemma {.(Λ n trm)} {.(Λ n trm')} (Λ-step n trm trm' scoping scoping' legit) = refl
Scope->>-lemma {.(trm1 · trm2)} {.(trm1' · trm2')} (·-step trm1 trm1' trm2 trm2' legit legit₁) = A≡A'∧B≡B'→A⊔B≡A'⊔B' left-hlp right-hlp
                              where
                                left-hlp : Scope trm1 ≡ Scope trm1'
                                left-hlp = Scope->>-lemma legit
                                right-hlp : Scope trm2 ≡ Scope trm2'
                                right-hlp = Scope->>-lemma legit₁

Scope->>-lemma2 : {n : ℕ} {trm : Term}{trm' : Term} → (legit : ->> trm trm') →  ((Scope trm <= n) ≡ true) → ((Scope trm' <= n) ≡ true)
Scope->>-lemma2 {n}{trm}{trm'} legit scoping =  x<=n→xy→y<=n scoping (Scope->>-lemma {trm}{trm'} legit)

CongΛ->> : {n : ℕ} {trm trm' : Term} → (scoping : (Scope trm <= n) ≡ true) → (scoping' : (Scope trm' <= n) ≡ true) → (->> trm trm') → (->> (Λ n trm {scoping}) (Λ n trm' {scoping'})) 
CongΛ->> {n}{trm}{trm'} scoping scoping' arrow = Λ-step n trm trm' scoping scoping' arrow

->>ExtractΛtrm : {n : ℕ} {trm trm' : Term} → (scoping : (Scope trm <= n) ≡ true) → (scoping' : (Scope trm' <= n) ≡ true) → (->> (Λ n trm {scoping}) (Λ n trm' {scoping'})) → (->> trm trm')
->>ExtractΛtrm {n} {trm} {.trm} scoping .scoping (reflexive .(Λ n trm)) = reflexive _
->>ExtractΛtrm {n} {trm} {trm'} scoping scoping' (node .(Λ n trm) .(Λ n trm') x) = node _ _ (StepΛ-extract-lemma x)
->>ExtractΛtrm {n} {trm} {trm'} scoping scoping' (Λ-step .n .trm .trm' .scoping .scoping' arrow) = arrow

->>-SelfSub-lemma-left  : {n : ℕ} {trm1 trm1' trm2 : Term} → {scoping : (Scope trm1 <= n) ≡ true} → {scoping' : (Scope trm1' <= n) ≡ true} -> (steps : Step trm1 trm1') → ->> (SelfSub trm1 trm2) (SelfSub trm1' trm2) 
->>-SelfSub-lemma-left {n} {Self} {trm1'} {trm2} {refl} {scoping'} (appFold arity isc eqn) = ⊥-elim (false≡true→⊥ isc)
->>-SelfSub-lemma-left {n} {(! n₁)} {trm1'} {trm2} {refl} {scoping'} (appFold arity isc eqn) = ⊥-elim (just≢nothing (sym arity))
->>-SelfSub-lemma-left {n} {` x} {trm1'} {trm2} {scoping} {scoping'} (appFold arity isc eqn) =  ⊥-elim (false≡true→⊥ isc)
->>-SelfSub-lemma-left {n} {Λ n₁ trm1} {.(Λ n₁ _)} {Self} {refl} {refl} (Λ-step steps scoping' scoping'') = CongΛ->> scoping' scoping'' (node _ _ steps)
->>-SelfSub-lemma-left {n} {Λ n₁ trm1} {.(Λ n₁ _)} {(! n₂)} {refl} {refl} (Λ-step steps _ scoping'') = reflexive _
->>-SelfSub-lemma-left {n} {Λ n₁ trm1} {.(Λ n₁ _)} {` x} {refl} {refl} (Λ-step steps _ scoping'') = reflexive _
->>-SelfSub-lemma-left {n} {Λ n₁ trm1} {.(Λ n₁ _)} {Λ n₂ trm2} {refl} {refl} (Λ-step steps _ scoping'') = reflexive _
->>-SelfSub-lemma-left {n} {Λ n₁ trm1} {.(Λ n₁ _)} {trm2 · trm3} {refl} {refl} (Λ-step {_}{trm}{trm'} steps scoping' scoping'') = ·-step (SelfSub (Λ n₁ trm1) trm2) (SelfSub (Λ n₁ trm') trm2) (SelfSub (Λ n₁ trm1) trm3) (SelfSub (Λ n₁ trm') trm3) (->>-SelfSub-lemma-left {n}{Λ n₁ trm1}{Λ n₁ trm'}{trm2}{refl}{refl} (Λ-step steps scoping' scoping'')) (->>-SelfSub-lemma-left {n}{Λ n₁ trm1}{Λ n₁ trm'}{trm3}{refl}{refl} (Λ-step steps scoping' scoping''))
->>-SelfSub-lemma-left {n} {trm1 · trm3} {trm1'} {Self} {scoping} {scoping'} steps = node _ _ steps
->>-SelfSub-lemma-left {n} {trm1 · trm3} {trm1'} {(! n₁)} {scoping} {scoping'} steps = reflexive _
->>-SelfSub-lemma-left {n} {trm1 · trm3} {trm1'} {` x} {scoping} {scoping'} steps = reflexive _
->>-SelfSub-lemma-left {n} {trm1 · trm3} {trm1'} {Λ n₁ trm2} {scoping} {scoping'} steps = reflexive _
->>-SelfSub-lemma-left {n} {trm1 · trm3} {trm1'} {trm2 · trm4} {scoping} {scoping'} steps = ·-step (SelfSub (trm1 · trm3) trm2) (SelfSub trm1' trm2) (SelfSub (trm1 · trm3) trm4) (SelfSub trm1' trm4) (->>-SelfSub-lemma-left {n}{trm1 · trm3}{trm1'}{trm2}{scoping}{scoping'} steps) (->>-SelfSub-lemma-left {n}{trm1 · trm3}{trm1'}{trm4}{scoping}{scoping'} steps)

mutual 
 SuperArity-Step-lemma : {n : ℕ} {trm1 trm1' : Term} → SuperArity trm1 ≡ just (+ suc n) → (arrow : Step trm1 trm1' ) → SuperArity trm1' ≡ just (+ suc n)
 SuperArity-Step-lemma {.n₁} {Λ n₁ trm1 {scoping}} {trm1'} refl arrow = SuperArityΛ-Step arrow
 SuperArity-Step-lemma {n} {trm1 · trm2} {.(_ · trm2)} sa (left-step {trm1}{trm2}{trm1'} arrow) = ·SuperArity-suc-lemma {suc n}{trm1'}{trm2} hlp'
                       where
                         hlp : (SuperArity trm1) ≡ just +[1+ (suc n) ]
                         hlp = ·SuperArity-lemma' {suc n}{trm1}{trm1'} sa
                         hlp' : (SuperArity trm1') ≡ just +[1+ (suc n) ]
                         hlp' = SuperArity-Step-lemma hlp arrow
 SuperArity-Step-lemma {n} {trm1 · trm2} {.(trm1 · _)} sa (right-step arrow) = ·SuperArity-suc-lemma {suc n}{trm1}{trm2} hlp
                       where
                         hlp : (SuperArity trm1) ≡ just +[1+ (suc n) ]
                         hlp = ·SuperArity-lemma' {suc n}{trm1}{trm2} sa
 SuperArity-Step-lemma {n} {trm1 · trm2} {.(AppFold {0} (trm1 · trm2) arity isc)} sa (appFold arity isc refl) = ⊥-elim (just≢0 just-contra)
                       where
                         just-contra :  just +[1+ n ] ≡ just (+ zero)
                         just-contra = trans (sym sa) arity

 SuperArity->>-lemma : {n : ℕ} {trm1 trm1' : Term} → SuperArity trm1 ≡ just (+ suc n) → (arrow : ->> trm1 trm1' ) → SuperArity trm1' ≡ just (+ suc n)
 SuperArity->>-lemma {n} {trm1} {.trm1} sa (reflexive .trm1) = sa
 SuperArity->>-lemma {n} {trm1} {trm1'} sa (node .trm1 .trm1' x) = SuperArity-Step-lemma sa x
 SuperArity->>-lemma {n} {.(Λ n₁ trm)} {.(Λ n₁ trm')} sa (Λ-step n₁ trm trm' scoping scoping' arrow) = sa
 SuperArity->>-lemma {n} {.(trm1 · trm2)} {.(trm1' · trm2')} sa (·-step trm1 trm1' trm2 trm2' arrow1 arrow2) = ·SuperArity-suc-lemma {suc n}{trm1'}{trm2'} hlp'
                       where
                         hlp : (SuperArity trm1) ≡ just (+ (suc (suc n)))
                         hlp = ·SuperArity-lemma' {suc n}{trm1}{trm1'} sa
                         hlp' : (SuperArity trm1') ≡ just +[1+ (suc n) ]
                         hlp' = SuperArity->>-lemma {suc n}{trm1}{trm1'} hlp arrow1

·Step≢Λ-lemma : {trm1 arg trm' : Term} {scoping : (Scope trm' <= zero) ≡ true} → (cond : SuperArity trm1 ≢ just (+ 1)) → Step (trm1 · arg) (Λ 0 trm' {scoping}) → ⊥
·Step≢Λ-lemma {trm1} {arg} {trm'} {scoping} cond (appFold arity isc eqn) = ⊥-elim (cond (·SuperArity-lemma' {0}{trm1}{arg} arity))

·SuperArity->>-lemma : {trm1 trm1' trm2 trm2' : Term} → (arity : (SuperArity (trm1 · trm2)) ≡ just (+ zero)) → (arrow1 : ->> trm1 trm1') → (arrow2 : ->> trm2 trm2') → (SuperArity (trm1' · trm2')) ≡ just (+ zero)
·SuperArity->>-lemma {trm1}{trm1'}{trm2}{trm2'} arity arrow1 arrow2 = ·SuperArity-suc-lemma {0}{trm1'}{trm2'} hlp'
                            where
                              hlp : SuperArity trm1 ≡ just (+ suc 0)
                              hlp = ·SuperArity-lemma {_}{trm1}{trm2} arity
                              hlp' : SuperArity trm1' ≡ just (+ suc 0)
                              hlp' = SuperArity->>-lemma hlp arrow1

AppFold'->>-lemma-hlp2 : {x y arg : Term} → {scoping : (Scope (Substitute 1 x arg) <= 0) ≡ true} → {scoping' : (Scope y <= zero) ≡ true} → ->> (Substitute 1 x arg) y → ->> (Λ 0 (Substitute 1 x arg) {scoping}) (Λ zero y {scoping'})
AppFold'->>-lemma-hlp2 {x}{y}{arg} {scoping}{scoping'} arrow = Λ-step 0 ((Substitute 1 x arg)) y scoping scoping' arrow

AppFold'->>-lemma-hlp2' : {n : ℕ}{x y arg : Term} → {scoping : (Scope (Substitute (suc n) x arg) <= n) ≡ true} → {scoping' : (Scope y <= n) ≡ true} → ->> (Substitute (suc n) x arg) y → ->> (Λ n (Substitute (suc n) x arg) {scoping}) (Λ n y {scoping'})
AppFold'->>-lemma-hlp2' {n} {x}{y}{arg} {scoping}{scoping'} arrow = Λ-step n (Substitute (suc n) x arg) y scoping scoping' arrow

isCombinatorExpr->>invar : {trm trm' : Term} → (isc : isCombinator trm ≡ true) → (trmtrm' : ->> trm trm') → isCombinator trm' ≡ true
isCombinatorExpr->>invar {trm} {.trm} isc (reflexive .trm) = isc
isCombinatorExpr->>invar {trm} {trm'} isc (node .trm .trm' x) = isCombinatorExpr-Step-invar isc x
isCombinatorExpr->>invar {.(Λ n trm)} {.(Λ n trm')} isc (Λ-step n trm trm' scoping scoping' trmtrm') = refl
isCombinatorExpr->>invar {.(trm1 · trm2)} {.(trm1' · trm2')} isc (·-step trm1 trm1' trm2 trm2' trmtrm' trmtrm'') = ∧-intro (isCombinatorExpr->>invar (∧-elim-left isc) trmtrm') (isCombinatorExpr->>invar (∧-elim-right isc) trmtrm'')

->>Eq-lemma-right : {A B C : Term} → ->> A B → B ≡ C → ->> A C
->>Eq-lemma-right {A} {B} {.B} arrow refl = arrow

->>Eq-lemma-left : {A B C : Term} → ->> A B → A ≡ C → ->> C B
->>Eq-lemma-left {A} {B} {.A} arrow refl  = arrow

->>Eq-lemma : {A B C D : Term} → A ≡ C → B ≡ D → ->> A B → ->> C D
->>Eq-lemma {A} {B} {.A} {.B} refl refl arrow = arrow

SubΛ-base-AppFold-lemma : {trm1  : Term} {isc : isCombinator trm1 ≡ true} {arity : SuperArity trm1 ≡ just (+ zero)} {isl : isLambda? trm1 ≡ true} {isl' : isLambda? (AppFold trm1 arity isc) ≡ true} -> ->> (SubΛ-base trm1 isl) (SubΛ-base (AppFold trm1 arity isc) isl')
SubΛ-base-AppFold-lemma {Self} {isc} {arity} {()} {isl'}
SubΛ-base-AppFold-lemma {(! n)} {isc} {arity} {()} {isl'}
SubΛ-base-AppFold-lemma {` x} {isc} {arity} {()} {isl'}
SubΛ-base-AppFold-lemma {Λ n trm1 {scoping}} {isc} {()} {refl} {isl'}
SubΛ-base-AppFold-lemma {trm1 · trm2} {isc} {arity} {()} {isl'}

SelfTo!n→⊥ : {n : ℕ} → ->> Self (! n) → ⊥
SelfTo!n→⊥ {n} (node .Self .(! n) (appFold () isc eqn))

!nToSelf→⊥' : {n : ℕ} → ->> (! n) Self → ⊥
!nToSelf→⊥' {n} (node .(! n) .Self (appFold () isc eqn))

!nTo·→⊥ : {n : ℕ}{trm trm' : Term} → ->> (! n) (trm · trm') → ⊥
!nTo·→⊥ {n} {trm} {trm'} (node .(! n) .(trm · trm') (appFold () isc eqn))

SelfTo`x→⊥ : {x : ℕ} → ->> Self (` x) → ⊥
SelfTo`x→⊥ {x} (node .Self .(` x) (appFold () isc eqn))

`xToSelf→⊥' : {x : ℕ} → ->> (` x) Self  → ⊥
`xToSelf→⊥' {x} (node .(` x) .Self (appFold () isc eqn))

`xTo·→⊥ : {x : ℕ}{trm trm' : Term} → ->> (` x) (trm · trm')  → ⊥
`xTo·→⊥ {x} {trm} {trm'} (node .(` x) .(trm · trm') (appFold () isc eqn))

SelfToΛ→⊥ : {n : ℕ}{trm : Term}{scoping : (Scope trm <= n) ≡ true} → ->> Self (Λ n trm {scoping}) → ⊥
SelfToΛ→⊥ {n} {trm} {scoping} (node .Self .(Λ n trm) (appFold () isc eqn))

SelfTo·→⊥ : {trm : Term}{trm' : Term} → ->> Self (trm · trm') → ⊥
SelfTo·→⊥ {trm} {scoping} (node .Self .(trm · scoping) (appFold () isc eqn))

ΛToSelf→⊥ : {n : ℕ} {trm' : Term} {scoping : (Scope trm' <= n) ≡ true} → (arrow : ->> (Λ n trm' {scoping}) Self) → ⊥ 
ΛToSelf→⊥ {n} {trm'} {scoping} (node .(Λ n trm') .Self (appFold () isc eqn))

ΛTo·→⊥ : {n : ℕ} {trm trm' trm'' : Term}{scoping : (Scope trm <= n) ≡ true} → (arrow : ->> (Λ n trm {scoping}) (trm' · trm'')) → ⊥ 
ΛTo·→⊥ {n} {trm} {trm'} {trm''} {scoping} (node .(Λ n trm) .(trm' · trm'') (appFold () isc eqn))

Self-Step-n!→⊥ : {n : ℕ} → Step Self (! n) → ⊥
Self-Step-n!→⊥ {n} (appFold arity isc eqn) = ⊥-elim (false≡true→⊥ isc)

Self-Step-`x→⊥ : {x : ℕ} → Step Self (` x) → ⊥
Self-Step-`x→⊥ {x} (appFold arity isc eqn) = ⊥-elim (false≡true→⊥ isc)

Self-Step-Λ→⊥ : {n : ℕ} {x' : Term}{scoping : (Scope x' <= n) ≡ true} → Step Self (Λ n x' {scoping}) → ⊥
Self-Step-Λ→⊥ {n} {x'} {scoping} (appFold arity isc eqn) = ⊥-elim (false≡true→⊥ isc)

Self-Step·-→⊥ : {x' x'' : Term} → Step Self (x' · x'') → ⊥
Self-Step·-→⊥ {x'} {x''} (appFold arity isc eqn) = ⊥-elim (false≡true→⊥ isc)

Self->>n!→⊥ : {n : ℕ} → (arrow : ->> Self (! n)) → ⊥
Self->>n!→⊥ {n} (node .Self .(! n) x) = Self-Step-n!→⊥ x

Self->>`x→⊥ : {x : ℕ} → (arrow : ->> Self (` x)) → ⊥
Self->>`x→⊥ {x} (node .Self .(` x) x') = Self-Step-`x→⊥ x'

Self->>-Λ→⊥ : {n : ℕ} {x' : Term}{scoping : (Scope x' <= n) ≡ true} → ->> Self (Λ n x' {scoping}) → ⊥
Self->>-Λ→⊥ {n} {x'} {scoping} (node .Self .(Λ n x') x) = Self-Step-Λ→⊥ x

Self->>·-→⊥ : {x' x'' : Term} → ->> Self (x' · x'') → ⊥
Self->>·-→⊥ {x'} {x''} (node .Self .(x' · x'') x) = Self-Step·-→⊥ {x'}{x''} x

Self->>Self : {x' : Term} → (arrow : ->> Self x') → x' ≡ Self
Self->>Self {Self} arrow = refl
Self->>Self {(! n)} arrow = ⊥-elim (Self->>n!→⊥ {n} arrow)
Self->>Self {` x} arrow = ⊥-elim (Self->>`x→⊥ arrow)
Self->>Self {Λ n x' {scoping}} arrow = ⊥-elim (Self->>-Λ→⊥ arrow)
Self->>Self {x' · x''} arrow = ⊥-elim (Self->>·-→⊥ {x'}{x''} arrow)

Selfx'-lemma : {n : ℕ} {x' arg' : Term} → (arrow : ->> Self x') → ->> Self (Substitute n x' arg')
Selfx'-lemma {n} {Self} {arg'} arrow = reflexive Self
Selfx'-lemma {n} {(! n₁)} {arg'} arrow = arrow
Selfx'-lemma {n} {` x} {arg'} arrow with ℕ-Dec n x 
... | yes refl = ⊥-elim (Self->>`x→⊥ {x} arrow)
... | no y = arrow 
Selfx'-lemma {n} {Λ n₁ x' {scoping}} {arg'} arrow = arrow
Selfx'-lemma {n} {x' · x''} {arg'} arrow = ⊥-elim (Self->>·-→⊥ arrow)

·ToSelf→⊥ : {trm : Term}{trm' : Term} → ->> (trm · trm') Self → ⊥
·ToSelf→⊥ {trm} {trm'} (node .(trm · trm') .Self (appFold arity isc eqn)) = ⊥-elim (false≡true→⊥ (trans (sym Self-isc) (trans isc-eq hlp)))
                         where
                           Self-isc : isCombinator Self ≡ false
                           Self-isc = refl
                           apptrm : Σ[ x ∈ Term ] (isLambda?n 0 x ≡ true)
                           apptrm = AppFold' {zero} trm (·SuperArity-lemma' {0} {trm}{trm'} arity) (∧-elim-left isc) 
                           app : Term
                           app = isLambda?→inner (isLambda?n→isLambda? {0}{proj₁ apptrm} (proj₂ apptrm))
                           subapp : Term
                           subapp = Substitute zero app trm'
                           hlp : isCombinator subapp ≡ true
                           hlp = isCombinatorSubstitute-lemma' {trm} (·SuperArity-lemma' {0}{trm}{trm'} arity) (∧-elim-left isc) (∧-elim-right isc)
                           eqn' : Self ≡ subapp
                           eqn' = eqn
                           isc-eq : isCombinator Self ≡ isCombinator subapp
                           isc-eq = cong (λ w → isCombinator w) eqn

·ToΛ0 : {n : ℕ}{trm1 trm2 trm1' : Term}{scoping : (Scope trm1' <= n) ≡ true} → (arrow : ->> (trm1 · trm2) (Λ n trm1' {scoping})) → (SuperArity (trm1 · trm2)) ≡ just (+ 0) 
·ToΛ0 {n} {trm1} {trm2} {trm1'} {scoping} (node .(trm1 · trm2) .(Λ n trm1') (appFold arity isc eqn)) = arity

SelfSub-isc-lemma : {trm trm' : Term} → {isc : isCombinator trm' ≡ true} → SelfSub trm trm' ≡ trm'
SelfSub-isc-lemma {trm} {(! n)} {isc} = refl
SelfSub-isc-lemma {trm} {Λ n trm' {scoping}} {isc} = refl
SelfSub-isc-lemma {trm} {trm' · trm''} {isc} = cong₂ (λ x y → x · y) hlp-left hlp-right
                        where
                          hlp-left = SelfSub-isc-lemma {trm}{trm'} {∧-elim-left isc}
                          hlp-right = SelfSub-isc-lemma {trm}{trm''} {∧-elim-right isc}

SelfSubΛ-Step'-hlp : {n : ℕ} {trm1 trm' trm3 : Term}{scoping : (Scope trm1 <= n) ≡ true}{scoping' :  (Scope trm' <= n) ≡ true} → (steps1 : Step trm1 trm') → ->> (SelfSub (Λ n trm1 {scoping}) trm3) (SelfSub (Λ n trm' {scoping'}) trm3)
SelfSubΛ-Step'-hlp {n}{trm1} {trm'} {Self} {scoping} {scoping'} steps1 = Λ-step n trm1 trm' scoping scoping' (node _ _ steps1)
SelfSubΛ-Step'-hlp {m}{trm1} {trm'} {(! n)} {scoping} {scoping'} steps1 = reflexive _
SelfSubΛ-Step'-hlp {n}{trm1} {trm'} {` x} {scoping} {scoping'} steps1 = reflexive _
SelfSubΛ-Step'-hlp {m}{trm1} {trm'} {Λ n trm3} {scoping} {scoping'} steps1 = reflexive _
SelfSubΛ-Step'-hlp {n}{trm1} {trm'} {trm3 · trm4} {scoping} {scoping'} steps1 = ·-step (SelfSub (Λ n trm1 {scoping}) trm3) (SelfSub (Λ n trm' {scoping'}) trm3) (SelfSub (Λ n trm1 {scoping}) trm4) (SelfSub (Λ n trm' {scoping'}) trm4) hlp-left hlp-right
                        where
                         hlp-left : ->> (SelfSub (Λ n trm1 {scoping}) trm3) (SelfSub (Λ n trm' {scoping'}) trm3)
                         hlp-left = SelfSubΛ-Step'-hlp steps1
                         hlp-right : ->> (SelfSub (Λ n trm1 {scoping}) trm4) (SelfSub (Λ n trm' {scoping'}) trm4)
                         hlp-right = SelfSubΛ-Step'-hlp steps1 

SelfSubΛ->>'-hlp : {n : ℕ}{trm1 trm' trm3 : Term}{scoping : (Scope trm1 <= n) ≡ true}{scoping' :  (Scope trm' <= n) ≡ true} → (arrow1 : ->> trm1 trm') → ->> (SelfSub (Λ n trm1 {scoping}) trm3) (SelfSub (Λ n trm' {scoping'}) trm3)
SelfSubΛ->>'-hlp {n} {trm1} {trm'} {Self} {scoping} {scoping'} arrow1 = Λ-step n trm1 trm' scoping scoping' arrow1
SelfSubΛ->>'-hlp {m} {trm1} {trm'} {(! n)} {scoping} {scoping'} arrow1 = reflexive _
SelfSubΛ->>'-hlp {n} {trm1} {trm'} {` x} {scoping} {scoping'} arrow1 = reflexive _
SelfSubΛ->>'-hlp {m} {trm1} {trm'} {Λ n trm3 {scoping''}} {scoping} {scoping'} arrow1 = reflexive _
SelfSubΛ->>'-hlp {n} {trm1} {trm'} {trm3 · trm4} {scoping} {scoping'} arrow1 = ·-step (SelfSub (Λ n trm1 {scoping}) trm3) (SelfSub (Λ n trm' {scoping'}) trm3) (SelfSub (Λ n trm1 {scoping}) trm4) (SelfSub (Λ n trm' {scoping'}) trm4) hlp-left hlp-right
                        where
                          hlp-left : ->> (SelfSub (Λ n trm1 {scoping}) trm3) (SelfSub (Λ n trm' {scoping'}) trm3) 
                          hlp-left = SelfSubΛ->>'-hlp arrow1
                          hlp-right : ->> (SelfSub (Λ n trm1) trm4) (SelfSub (Λ n trm') trm4) 
                          hlp-right = SelfSubΛ->>'-hlp arrow1
                          
SelfSubΛ-Step' : {n : ℕ} {trm1 trm' trm2 trm2' : Term}{scoping : (Scope trm1 <= n) ≡ true}{scoping' : (Scope trm' <= n) ≡ true} → {scoping2 : (Scope trm2 <= n) ≡ true}{scoping2' : (Scope trm2' <= n) ≡ true} → Step trm1 trm' → Step trm2 trm2' → ->> (SelfSub (Λ n trm1 {scoping}) trm2) (SelfSub (Λ n trm' {scoping'}) trm2')
SelfSubΛ-Step' {n} {trm1} {trm'} {.(_ · _)} {.(_ · _)} {scoping} {scoping'} {scoping2} {scoping2'} steps1 (left-step {trm2}{trm3}{trm1'} steps2) = ·-step (SelfSub (Λ n trm1 {scoping}) trm2) (SelfSub (Λ n trm' {scoping'}) trm1') (SelfSub (Λ n trm1 {scoping}) trm3) (SelfSub (Λ n trm' {scoping'}) trm3) hlp1 hlp2
                         where
                           hlp1 : ->> (SelfSub (Λ n trm1 {scoping}) trm2) (SelfSub (Λ n trm' {scoping'}) trm1')  
                           hlp1 = SelfSubΛ-Step' {n} {trm1}{trm'}{trm2}{trm1'}{scoping}{scoping'}{x⊔y<=n-left-elim {Scope trm2}{Scope trm3}{n} scoping2}{x⊔y<=n-left-elim {Scope trm1'}{Scope trm3}{n} scoping2'} steps1 steps2
                           hlp2 : ->> (SelfSub (Λ n trm1 {scoping}) trm3) (SelfSub (Λ n trm' {scoping'}) trm3)
                           hlp2 = SelfSubΛ-Step'-hlp {n} steps1
SelfSubΛ-Step' {n} {trm1} {trm'} {.(_ · _)} {.(_ · _)} {scoping} {scoping'} {scoping2} {scoping2'} steps1 (right-step {trm2}{trm3}{trm2'} steps2) = ·-step (SelfSub (Λ n trm1 {scoping}) trm2) (SelfSub (Λ n trm' {scoping'}) trm2) (SelfSub (Λ n trm1 {scoping}) trm3) (SelfSub (Λ n trm' {scoping'}) trm2') hlp1 hlp2
                         where
                           hlp1 : ->> (SelfSub (Λ n trm1 {scoping}) trm2) (SelfSub (Λ n trm' {scoping'}) trm2)  
                           hlp1 = SelfSubΛ-Step'-hlp steps1  
                           hlp2 : ->> (SelfSub (Λ n trm1 {scoping}) trm3) (SelfSub (Λ n trm' {scoping'}) trm2')
                           hlp2 = SelfSubΛ-Step' {n} {trm1}{trm'}{trm3}{trm2'}{scoping}{scoping'} {x⊔y<=n-elim-right {Scope trm2}{Scope trm3}{n} scoping2}{x⊔y<=n-elim-right {Scope trm2}{Scope trm2'}{n} scoping2'} steps1 steps2               
SelfSubΛ-Step' {m} {trm1} {trm'} {.(Λ _ _)} {.(Λ _ _)} {scoping} {scoping'} {scoping2} {scoping2'} steps1 (Λ-step {n}{trm''}{trm'''} steps2 scoping₁ scoping'') = Λ-step _ trm'' trm''' scoping₁ scoping'' (node _ _ steps2)
SelfSubΛ-Step' {n} {trm1} {trm'} {trm2} {.(AppFold trm2 arity isc)} {scoping} {scoping'} {scoping2} {scoping2'} steps1 (appFold arity isc refl) = ->>Eq-lemma (sym hlp1) (sym hlp2) hlp3
                         where
                           hlp1 : (SelfSub (Λ n trm1 {scoping}) trm2) ≡ trm2
                           hlp1 = SelfSub-isc-lemma {Λ n trm1 {scoping}} {trm2} {isc} 
                           hlp2 : (SelfSub (Λ n trm' {scoping'}) (AppFold trm2 arity isc)) ≡  (AppFold trm2 arity isc)
                           hlp2 = SelfSub-isc-lemma {Λ n trm' {scoping'}}{AppFold trm2 arity isc}{isCombinatorExprAppFold {0}{trm2} arity isc}
                           hlp3 : ->> trm2 (AppFold trm2 arity isc)
                           hlp3 = node _ _ (appFold arity isc refl)

SelfSubΛ-Step'' : {trm1 trm' trm2 trm2' : Term}{scoping : (Scope trm1 <= zero) ≡ true}{scoping' : (Scope trm' <= zero) ≡ true} → Step trm1 trm' → Step trm2 trm2' → ->> (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm' {scoping'}) trm2')
SelfSubΛ-Step'' {trm1} {trm'} {.(_ · _)} {.(_ · _)} {scoping} {scoping'} steps1 (left-step {trm2}{trm3}{trm1'} steps2) = ·-step (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm' {scoping'}) trm1') (SelfSub (Λ 0 trm1 {scoping}) trm3) (SelfSub (Λ 0 trm' {scoping'}) trm3) hlp1 hlp2
                         where
                           hlp1 : ->> (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm' {scoping'}) trm1')  
                           hlp1 = SelfSubΛ-Step'' {trm1}{trm'}{trm2}{trm1'}{scoping}{scoping'} steps1 steps2 
                           hlp2 : ->> (SelfSub (Λ 0 trm1 {scoping}) trm3) (SelfSub (Λ 0 trm' {scoping'}) trm3)
                           hlp2 = SelfSubΛ-Step'-hlp steps1
SelfSubΛ-Step'' {trm1} {trm'} {.(_ · _)} {.(_ · _)} {scoping} {scoping'} steps1 (right-step {trm2}{trm3}{trm2'} steps2) = ·-step (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm' {scoping'}) trm2) (SelfSub (Λ 0 trm1 {scoping}) trm3) (SelfSub (Λ 0 trm' {scoping'}) trm2') hlp1 hlp2
                         where
                           hlp1 : ->> (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm' {scoping'}) trm2)  
                           hlp1 = SelfSubΛ-Step'-hlp steps1  
                           hlp2 : ->> (SelfSub (Λ 0 trm1 {scoping}) trm3) (SelfSub (Λ 0 trm' {scoping'}) trm2')
                           hlp2 = SelfSubΛ-Step'' {trm1}{trm'}{trm3}{trm2'} steps1 steps2 
SelfSubΛ-Step'' {trm1} {trm'} {.(Λ _ _)} {.(Λ _ _)} {scoping} {scoping'} steps1 (Λ-step {n}{trm''}{trm'''} steps2 scoping₁ scoping'') = Λ-step _ trm'' trm''' scoping₁ scoping'' (node _ _ steps2)
SelfSubΛ-Step'' {trm1} {trm'} {trm2} {.(AppFold trm2 arity isc)} {scoping} {scoping'} steps1 (appFold arity isc refl) = ->>Eq-lemma (sym hlp1) (sym hlp2) hlp3
                         where
                           hlp1 : (SelfSub (Λ 0 trm1 {scoping}) trm2) ≡ trm2
                           hlp1 = SelfSub-isc-lemma {Λ 0 trm1 {scoping}} {trm2} {isc} 
                           hlp2 : (SelfSub (Λ 0 trm' {scoping'}) (AppFold trm2 arity isc)) ≡  (AppFold trm2 arity isc)
                           hlp2 = SelfSub-isc-lemma {Λ 0 trm' {scoping'}}{AppFold trm2 arity isc}{isCombinatorExprAppFold {0}{trm2} arity isc}
                           hlp3 : ->> trm2 (AppFold trm2 arity isc)
                           hlp3 = node _ _ (appFold arity isc refl)

---------

SelfSubΛ·->>-lemma : {n : ℕ} {trm1 trm2 trm3 trm1' trm2' trm3' : Term} {scoping : ((Scope trm1 ⊔ Scope trm2) <= n) ≡ true} {scoping' : ((Scope trm1' ⊔ Scope trm2') <= n) ≡ true} → (arrow1 : ->> trm1 trm1') → (arrow2 : ->> trm2 trm2') → (arrow3 : ->> trm3 trm3') → ->> (SelfSub (Λ n (trm1 · trm2) {scoping}) trm3) (SelfSub (Λ n (trm1' · trm2') {scoping'}) trm3')
SelfSubΛ·->>-lemma {n} {trm1} {trm2} {trm3} {trm1'} {trm2'} {.trm3} {scoping} {scoping'} arrow1 arrow2 (reflexive .trm3) = SelfSubΛ->>'-hlp {n} (·-step trm1 trm1' trm2 trm2' arrow1 arrow2)
SelfSubΛ·->>-lemma {m} {trm1} {trm2} {.(Λ n trm)} {trm1'} {trm2'} {.(Λ n trm')} {scoping} {scoping'} arrow1 arrow2 (Λ-step n trm trm' scoping₁ scoping'' arrow3) = Λ-step n trm trm' scoping₁ scoping'' arrow3
SelfSubΛ·->>-lemma {n} {trm1} {trm2} {.(trm3 · trm4)} {trm1'} {trm2'} {.(trm1'' · trm2'')} {scoping} {scoping'} arrow1 arrow2 (·-step trm3 trm1'' trm4 trm2'' arrow3 arrow4) = ·-step (SelfSub (Λ n (trm1 · trm2) {scoping}) trm3) (SelfSub (Λ n (trm1' · trm2') {scoping'}) trm1'') (SelfSub (Λ n (trm1 · trm2) {scoping}) trm4) (SelfSub (Λ n (trm1' · trm2') {scoping'}) trm2'') hlp-left hlp-right
                        where
                          hlp-left : ->> (SelfSub (Λ n (trm1 · trm2) {scoping}) trm3) (SelfSub (Λ n (trm1' · trm2') {scoping'}) trm1'')
                          hlp-left = SelfSubΛ·->>-lemma arrow1 arrow2 arrow3
                          hlp-right : ->> (SelfSub (Λ n (trm1 · trm2) {scoping}) trm4) (SelfSub (Λ n (trm1' · trm2') {scoping'}) trm2'')
                          hlp-right = SelfSubΛ·->>-lemma arrow1 arrow2 arrow4
SelfSubΛ·->>-lemma {n} {trm1} {trm2} {.(_ · _)} {trm1'} {trm2'} {.(_ · _)} {scoping} {scoping'} arrow1 arrow2 (node .(_ · _) .(_ · _) (left-step {trm3}{trm4}{trm1''} x)) = ·-step (SelfSub (Λ n (trm1 · trm2) {scoping}) trm3) (SelfSub (Λ n (trm1' · trm2') {scoping'}) trm1'') (SelfSub (Λ n (trm1 · trm2) {scoping}) trm4) (SelfSub (Λ n (trm1' · trm2') {scoping'}) trm4) hlp-left hlp-right
                        where
                          hlp-left : ->> (SelfSub (Λ n (trm1 · trm2) {scoping}) trm3) (SelfSub (Λ n (trm1' · trm2') {scoping'}) trm1'')
                          hlp-left = SelfSubΛ·->>-lemma arrow1 arrow2 (node _ _ x)
                          hlp-right : ->> (SelfSub (Λ n (trm1 · trm2) {scoping}) trm4) (SelfSub (Λ n (trm1' · trm2') {scoping'}) trm4)
                          hlp-right = SelfSubΛ·->>-lemma arrow1 arrow2 (reflexive _)
SelfSubΛ·->>-lemma {n} {trm1} {trm2} {.(_ · _)} {trm1'} {trm2'} {.(_ · _)} {scoping} {scoping'} arrow1 arrow2 (node .(_ · _) .(_ · _) (right-step {trm3}{trm4}{trm2''} x)) = ·-step (SelfSub (Λ n (trm1 · trm2) {scoping}) trm3) (SelfSub (Λ n (trm1' · trm2') {scoping'}) trm3) (SelfSub (Λ n (trm1 · trm2) {scoping}) trm4) (SelfSub (Λ n (trm1' · trm2') {scoping'}) trm2'') hlp-left hlp-right
                        where
                          hlp-left : ->> (SelfSub (Λ n (trm1 · trm2) {scoping}) trm3) (SelfSub (Λ n (trm1' · trm2') {scoping'}) trm3)
                          hlp-left = SelfSubΛ·->>-lemma arrow1 arrow2 (reflexive _)
                          hlp-right : ->> (SelfSub (Λ n (trm1 · trm2) {scoping}) trm4) (SelfSub (Λ n (trm1' · trm2') {scoping'}) trm2'')
                          hlp-right = SelfSubΛ·->>-lemma arrow1 arrow2 (node _ _ x)                          
SelfSubΛ·->>-lemma {m} {trm1} {trm2} {.(Λ _ _)} {trm1'} {trm2'} {.(Λ _ _)} {scoping} {scoping'} arrow1 arrow2 (node .(Λ _ _) .(Λ _ _) (Λ-step {n}{trm}{trm'} x scoping₁ scoping'')) = Λ-step n trm trm' scoping₁ scoping'' (node _ _ x)
SelfSubΛ·->>-lemma {n} {trm1} {trm2} {trm3} {trm1'} {trm2'} {trm3'} {scoping} {scoping'} arrow1 arrow2 (node .trm3 .trm3' (appFold arity isc eqn)) = ->>Eq-lemma {trm3}{trm3'}{SelfSub (Λ n (trm1 · trm2) {scoping}) trm3} {SelfSub (Λ n (trm1' · trm2') {scoping'}) trm3'} (sym hlp1) (sym hlp2) trm33'
                         where
                           trm33' : ->> trm3 trm3'
                           trm33' = node trm3 trm3' (appFold arity isc eqn)
                           hlp1 : SelfSub (Λ n (trm1 · trm2) {scoping}) trm3 ≡ trm3
                           hlp1 = SelfSub-isc-lemma {Λ n (trm1 · trm2) {scoping}} {trm3} {isc}
                           iscapp : (isCombinator (AppFold trm3 arity isc)) ≡ true  
                           iscapp = isCombinatorExprAppFold {0}{trm3} arity isc
                           hlp2-hlp : isCombinator trm3' ≡ true
                           hlp2-hlp  = isCombinator≡ {AppFold trm3 arity isc} {trm3'} iscapp (sym eqn)
                           hlp2 : SelfSub (Λ n (trm1' · trm2') {scoping'}) trm3' ≡ trm3'
                           hlp2 = SelfSub-isc-lemma {Λ n (trm1' · trm2') {scoping'}} {trm3'} {hlp2-hlp} 

---------
mutual 
 SelfSubΛ->>-lemma-hlp : {trm1 trm' trm2 trm2' : Term}{scoping : (Scope trm1 <= zero) ≡ true}{scoping' : (Scope trm' <= zero) ≡ true} → ->> trm1 trm' → Step trm2 trm2' → ->> (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm' {scoping'}) trm2')
 SelfSubΛ->>-lemma-hlp {trm1} {trm'} {.(_ · _)} {.(_ · _)} {scoping} {scoping'} arrow1 (left-step {trm2}{trm3}{trm2'} steps) = ·-step (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm' {scoping'}) trm2') (SelfSub (Λ 0 trm1 {scoping}) trm3) (SelfSub (Λ 0 trm' {scoping'}) trm3) hlp-left hlp-right
                        where
                          hlp-left : ->> (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm' {scoping'}) trm2')
                          hlp-left = SelfSubΛ->>-lemma-hlp arrow1 steps
                          hlp-right : ->> (SelfSub (Λ 0 trm1 {scoping}) trm3) (SelfSub (Λ 0 trm' {scoping'}) trm3)
                          hlp-right = SelfSubΛ->>-lemma arrow1 (reflexive _) 
 SelfSubΛ->>-lemma-hlp {trm1} {trm'} {.(_ · _)} {.(_ · _)} {scoping} {scoping'} arrow1 (right-step {trm2}{trm3}{trm2'} steps) = ·-step (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm' {scoping'}) trm2) (SelfSub (Λ 0 trm1 {scoping}) trm3) (SelfSub (Λ 0 trm' {scoping'}) trm2') hlp-left hlp-right
                       where
                          hlp-left : ->> (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm' {scoping'}) trm2)
                          hlp-left = SelfSubΛ->>-lemma arrow1 (reflexive _)
                          hlp-right : ->> (SelfSub (Λ 0 trm1 {scoping}) trm3) (SelfSub (Λ 0 trm' {scoping'}) trm2') 
                          hlp-right = SelfSubΛ->>-lemma arrow1 (node _ _ steps)
 SelfSubΛ->>-lemma-hlp {trm1} {trm'} {.(Λ _ _)} {.(Λ _ _)} {scoping} {scoping'} arrow1 (Λ-step {n} {trm}{trm''} steps scoping₁ scoping'') = Λ-step n trm trm'' scoping₁ scoping'' (node _ _ steps)
 SelfSubΛ->>-lemma-hlp {trm1} {trm'} {trm2} {trm2'} {scoping} {scoping'} arrow1 (appFold arity isc eqn) = ->>Eq-lemma (sym hlp) (sym hlp') (node _ _ (appFold arity isc eqn))
                        where
                          hlp : (SelfSub (Λ 0 trm1 {scoping}) trm2) ≡ trm2
                          hlp = SelfSub-isc-lemma {Λ 0 trm1 {scoping}}{trm2} {isc}
                          hlp'-hlp : isCombinator trm2' ≡ true
                          hlp'-hlp = isCombinatorExpr->>invar {trm2}{trm2'} isc (node _ _ (appFold arity isc eqn))
                          hlp' : (SelfSub (Λ 0 trm' {scoping'}) trm2') ≡ trm2'
                          hlp' = SelfSub-isc-lemma {Λ 0 trm' {scoping'}}{trm2'} {hlp'-hlp}

 SelfSubΛ->>-lemma : {trm1 trm' trm2 trm2' : Term}{scoping : (Scope trm1 <= zero) ≡ true}{scoping' : (Scope trm' <= zero) ≡ true} -> ->> trm1 trm' → ->> trm2 trm2' → ->> (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm' {scoping'}) trm2')
 SelfSubΛ->>-lemma {trm1} {.trm1} {.Self} {.Self} {scoping} {scoping'} (reflexive .trm1) (reflexive Self) = Λ-step 0 trm1 trm1 scoping scoping' (reflexive _) 
 SelfSubΛ->>-lemma {trm1} {.trm1} {.(! n)} {.(! n)} {scoping} {scoping'} (reflexive .trm1) (reflexive (! n)) = reflexive _
 SelfSubΛ->>-lemma {trm1} {.trm1} {.(` x)} {.(` x)} {scoping} {scoping'} (reflexive .trm1) (reflexive (` x)) = reflexive _
 SelfSubΛ->>-lemma {trm1} {.trm1} {.(Λ n trm2)} {.(Λ n trm2)} {scoping}{scoping'}(reflexive .trm1) (reflexive (Λ n trm2 {scoping3})) = Λ-step n trm2 trm2 scoping3 scoping3 (reflexive _)
 SelfSubΛ->>-lemma {trm1} {.trm1} {.(trm2 · trm3)} {.(trm2 · trm3)} {scoping}{scoping'}(reflexive .trm1) (reflexive (trm2 · trm3)) = ·-step (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm1 {scoping'}) trm2) (SelfSub (Λ 0 trm1 {scoping}) trm3) (SelfSub (Λ 0 trm1 {scoping'}) trm3) hlp-left hlp-right
                        where
                          hlp-left : ->> (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm1 {scoping'}) trm2)
                          hlp-left = SelfSubΛ->>-lemma (reflexive _) (reflexive _)
                          hlp-right : ->> (SelfSub (Λ 0 trm1 {scoping}) trm3) (SelfSub (Λ 0 trm1 {scoping'}) trm3)
                          hlp-right = SelfSubΛ->>-lemma (reflexive _) (reflexive _)
 SelfSubΛ->>-lemma {trm1} {.trm1} {.(_ · _)} {.(_ · _)} {scoping}{scoping'} (reflexive .trm1) (node .(_ · _) .(_ · _) (left-step {trm2}{trm3}{trm1'} x)) =  ·-step (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm1 {scoping'}) trm1') (SelfSub (Λ 0 trm1 {scoping}) trm3) (SelfSub (Λ 0 trm1 {scoping'}) trm3) hlp-left hlp-right
                        where
                          hlp-left : ->> (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm1 {scoping'}) trm1')
                          hlp-left = SelfSubΛ->>-lemma (reflexive _) (node _ _ x)
                          hlp-right : ->> (SelfSub (Λ 0 trm1 {scoping}) trm3) (SelfSub (Λ 0 trm1 {scoping'}) trm3)
                          hlp-right = SelfSubΛ->>-lemma (reflexive _) (reflexive _)
 SelfSubΛ->>-lemma {trm1} {.trm1} {.(_ · _)} {.(_ · _)} {scoping} {scoping'} (reflexive .trm1) (node .(_ · _) .(_ · _) (right-step {trm2}{trm3}{trm2'} x)) = ·-step (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm1 {scoping'}) trm2) (SelfSub (Λ 0 trm1 {scoping}) trm3) (SelfSub (Λ 0 trm1 {scoping'}) trm2') hlp-left hlp-right
                        where
                          hlp-left : ->> (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm1 {scoping'}) trm2)
                          hlp-left = SelfSubΛ->>-lemma (reflexive _) (reflexive _)
                          hlp-right : ->> (SelfSub (Λ 0 trm1 {scoping}) trm3) (SelfSub (Λ 0 trm1 {scoping'}) trm2')
                          hlp-right = SelfSubΛ->>-lemma (reflexive _) (node _ _ x) 
 SelfSubΛ->>-lemma {trm1} {.trm1} {.(Λ _ _)} {.(Λ _ _)} {scoping} {scoping'} (reflexive .trm1) (node .(Λ _ _) .(Λ _ _) (Λ-step {n}{trm}{trm'} x scoping₁ scoping'')) = Λ-step n trm trm' scoping₁ scoping'' (node _ _ x)
 SelfSubΛ->>-lemma {trm1} {.trm1} {trm2} {trm2'} {scoping} {scoping'} (reflexive .trm1) (node .trm2 .trm2' (appFold arity isc eqn)) = ->>Eq-lemma (sym hlp1) (sym hlp2) trm22'
                        where
                          trm22' : ->> trm2 trm2'
                          trm22' = (node trm2 trm2' (appFold arity isc eqn))
                          hlp1 : (SelfSub (Λ 0 trm1 {scoping}) trm2) ≡ trm2
                          hlp1 = SelfSub-isc-lemma {Λ 0 trm1 {scoping}}{trm2}{isc}
                          hlp2 : (SelfSub (Λ 0 trm1 {scoping'}) trm2') ≡ trm2'
                          hlp2 = SelfSub-isc-lemma {Λ 0 trm1 {scoping'}} {trm2'} {isCombinator≡ (isCombinatorExprAppFold {0}{trm2} arity isc) (sym eqn)}
 SelfSubΛ->>-lemma {trm1} {.trm1} {.(Λ n trm)} {.(Λ n trm')} {scoping}{scoping'} (reflexive .trm1) (Λ-step n trm trm' scoping₁ scoping'' steps2) = Λ-step n trm trm' scoping₁ scoping'' steps2
 SelfSubΛ->>-lemma {trm1} {.trm1} {.(trm2 · trm3)} {.(trm1' · trm2')} {scoping}{scoping'} (reflexive .trm1) (·-step trm2 trm1' trm3 trm2' steps2 steps3) = ·-step (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm1 {scoping'}) trm1') (SelfSub (Λ 0 trm1 {scoping}) trm3) (SelfSub (Λ 0 trm1 {scoping'}) trm2') hlp-left hlp-right
                        where
                          hlp-left : ->> (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm1 {scoping'}) trm1')
                          hlp-left = SelfSubΛ->>-lemma (reflexive _) steps2
                          hlp-right : ->> (SelfSub (Λ 0 trm1 {scoping}) trm3) (SelfSub (Λ 0 trm1 {scoping'}) trm2')
                          hlp-right = SelfSubΛ->>-lemma (reflexive _) steps3
 SelfSubΛ->>-lemma {trm1} {trm'} {trm2} {.trm2} {scoping}{scoping'} (node .trm1 .trm' x) (reflexive .trm2) = SelfSubΛ->>'-hlp (node _ _ x)
 SelfSubΛ->>-lemma {trm1} {trm'} {trm2} {trm2'} {scoping}{scoping'} (node .trm1 .trm' x) (node .trm2 .trm2' x₁) =  SelfSubΛ-Step'' x x₁ 
 SelfSubΛ->>-lemma {trm1} {trm'} {.(Λ n trm)} {.(Λ n trm'')} {scoping} {scoping'} (node .trm1 .trm' x) (Λ-step n trm trm'' scoping₁ scoping'' steps2) = Λ-step n trm trm'' scoping₁ scoping'' steps2
 SelfSubΛ->>-lemma {trm1} {trm'} {.(trm2 · trm3)} {.(trm1' · trm2')} {scoping}{scoping'} (node .trm1 .trm' x) (·-step trm2 trm1' trm3 trm2' steps2 steps3) = ·-step (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm' {scoping'}) trm1') (SelfSub (Λ 0 trm1 {scoping}) trm3) (SelfSub (Λ 0 trm' {scoping'} ) trm2') hlp-left hlp-right
                        where
                          hlp-left : ->> (SelfSub (Λ 0 trm1 {scoping}) trm2) (SelfSub (Λ 0 trm' {scoping'}) trm1') 
                          hlp-left = SelfSubΛ->>-lemma (node _ _ x) steps2
                          hlp-right : ->> (SelfSub (Λ 0 trm1 {scoping}) trm3) (SelfSub (Λ 0 trm' {scoping'} ) trm2')
                          hlp-right = SelfSubΛ->>-lemma (node _ _ x) steps3
 SelfSubΛ->>-lemma {.(Λ n trm)} {.(Λ n trm')} {trm2} {.trm2} {scoping} {scoping'} (Λ-step n trm trm' scoping₁ scoping'' steps1) (reflexive .trm2) = SelfSubΛ->>'-hlp  (Λ-step n trm trm' scoping₁ scoping'' steps1)
 SelfSubΛ->>-lemma {.(Λ n trm)} {.(Λ n trm')} {trm2} {trm2'} {scoping} {scoping'} (Λ-step n trm trm' scoping₁ scoping'' steps1) (node .trm2 .trm2' x) = SelfSubΛ->>-lemma-hlp (Λ-step n trm trm' scoping₁ scoping'' steps1) x
 SelfSubΛ->>-lemma {.(Λ n trm)} {.(Λ n trm')} {.(Λ n₁ trm₁)} {.(Λ n₁ trm'')} {scoping}{scoping'} (Λ-step n trm trm' scoping₁ scoping'' steps1) (Λ-step n₁ trm₁ trm'' scoping₂ scoping''' steps2) = Λ-step n₁ trm₁ trm'' scoping₂ scoping''' steps2
 SelfSubΛ->>-lemma {.(Λ n trm)} {.(Λ n trm')} {.(trm1 · trm2)} {.(trm1' · trm2')} {scoping}{scoping'} (Λ-step n trm trm' scoping₁ scoping'' steps1) (·-step trm1 trm1' trm2 trm2' steps2 steps3) = ·-step (SelfSub (Λ 0 (Λ n trm {scoping₁}) {_}) trm1) (SelfSub (Λ 0 (Λ n trm' {scoping''}) {_}) trm1') (SelfSub (Λ 0 (Λ n trm {scoping₁}) {_}) trm2) (SelfSub (Λ 0 (Λ n trm' {scoping''}) {_}) trm2') hlp-left hlp-right
                        where
                          hlp-left : ->> (SelfSub (Λ 0 (Λ n trm {scoping₁}) {_}) trm1) (SelfSub (Λ 0 (Λ n trm' {scoping''}) {_}) trm1')
                          hlp-left = SelfSubΛ->>-lemma (Λ-step _ _ _ scoping₁ scoping'' steps1) steps2
                          hlp-right : ->> (SelfSub (Λ 0 (Λ n trm {scoping₁}) {_}) trm2) (SelfSub (Λ 0 (Λ n trm' {scoping''}) {_}) trm2')
                          hlp-right = SelfSubΛ->>-lemma (Λ-step _  _ _ scoping₁ scoping'' steps1) steps3
 SelfSubΛ->>-lemma {.(trm1 · trm3)} {.(trm1' · trm2'')} {trm2} {trm2'} {scoping}{scoping'} (·-step trm1 trm1' trm3 trm2'' steps1 steps3) steps2 = SelfSubΛ·->>-lemma steps1 steps3 steps2

SelfSubΛ-eq' : {n : ℕ} {trm1 trm' : Term}{scoping : (Scope trm1 <= n) ≡ true}{scoping' : (Scope trm' <= n) ≡ true} → ->> trm1 trm' → ->> (SelfSub (Λ n trm1 {scoping}) trm1) (SelfSub (Λ n trm' {scoping'}) trm')
SelfSubΛ-eq' {n}{trm1} {.trm1} {scoping} {scoping'} (reflexive .trm1) = SelfSubΛ->>'-hlp {n} (reflexive _)
SelfSubΛ-eq' {n}{trm1} {trm'} {scoping} {scoping'} (node .trm1 .trm' x) = SelfSubΛ-Step' {n} {_}{_}{_}{_}{scoping}{scoping'}{scoping}{scoping'} x x 
SelfSubΛ-eq' {m}{.(Λ n trm)} {.(Λ n trm')} {scoping} {scoping'} (Λ-step n trm trm' scoping₁ scoping'' arrow) = Λ-step n trm trm' scoping₁ scoping'' arrow
SelfSubΛ-eq' {n}{.(trm1 · trm2)} {.(trm1' · trm2')} {scoping} {scoping'} (·-step trm1 trm1' trm2 trm2' arrow arrow₁) =  ·-step _ _ _ _ hlp hlp'
                         where
                           hlp : ->> (SelfSub (Λ n (trm1 · trm2) {scoping}) trm1) (SelfSub (Λ n (trm1' · trm2') {scoping'}) trm1')                      
                           hlp = SelfSubΛ·->>-lemma {n} arrow arrow₁ arrow
                           hlp' : ->>  (SelfSub (Λ n (trm1 · trm2) {scoping}) trm2) (SelfSub (Λ n (trm1' · trm2') {scoping'}) trm2')
                           hlp' = SelfSubΛ·->>-lemma arrow arrow₁ arrow₁ 

SelfSubΛ-eq : {trm1 : Term}{scoping : (Scope trm1 <= zero) ≡ true}{scoping' : (Scope trm1 <= zero) ≡ true} → ->> (SelfSub (Λ 0 trm1 {scoping}) trm1) (SelfSub (Λ 0 trm1 {scoping'}) trm1)
SelfSubΛ-eq = SelfSubΛ-eq' {0} (reflexive _)

SubΛ-base->>-lemma : {trm1 trm' : Term} {scoping : (Scope trm1 <= zero) ≡ true}{scoping' : (Scope trm' <= zero) ≡ true} →  ->> trm1 trm' → ->> (SubΛ-base (Λ 0 trm1 {scoping}) refl) (SubΛ-base (Λ 0 trm' {scoping'}) refl)
SubΛ-base->>-lemma {trm1} {.trm1} {scoping} {scoping'} (reflexive .trm1) = Λ-step 0 (SelfSub (Λ 0 trm1 {scoping}) trm1) (SelfSub (Λ 0 trm1 {scoping'}) trm1) _ _ SelfSubΛ-eq
SubΛ-base->>-lemma {trm1} {trm'} {scoping} {scoping'} (node .trm1 .trm' x) = Λ-step 0 (SelfSub (Λ 0 trm1 {scoping}) trm1) (SelfSub (Λ 0 trm' {scoping'}) trm') _ _ (SelfSubΛ-eq' (node _ _ x))
SubΛ-base->>-lemma {.(Λ n trm1)} {.(Λ n trm')} {refl} {refl} (Λ-step n trm1 trm' scoping1' scoping'' arrow) = Λ-step 0 (Λ n trm1) (Λ n trm') refl refl (Λ-step n trm1 trm' scoping1' scoping'' arrow)
SubΛ-base->>-lemma {.(trm1 · trm2)} {.(trm1' · trm2')} {scoping} {scoping'} (·-step trm1 trm1' trm2 trm2' arrow arrow₁) = target
                    where
                      target : ->> (Λ 0 (SelfSub (Λ 0 (trm1 · trm2) {scoping}) trm1 · SelfSub (Λ 0 (trm1 · trm2) {scoping}) trm2) {_}) (Λ 0 (SelfSub (Λ 0 (trm1' · trm2') {scoping'}) trm1' · SelfSub (Λ 0 (trm1' · trm2') {scoping'}) trm2') {_})
                      target = Λ-step 0 (SelfSub (Λ 0 (trm1 · trm2)) trm1 · SelfSub (Λ 0 (trm1 · trm2)) trm2) (SelfSub (Λ 0 (trm1' · trm2')) trm1' · SelfSub (Λ 0 (trm1' · trm2')) trm2')
                               _ _
                               (·-step (SelfSub (Λ 0 (trm1 · trm2)) trm1) (SelfSub (Λ 0 (trm1' · trm2')) trm1') (SelfSub (Λ 0 (trm1 · trm2)) trm2) (SelfSub (Λ 0 (trm1' · trm2')) trm2')
                               (SelfSubΛ·->>-lemma arrow arrow₁ arrow) (SelfSubΛ·->>-lemma arrow arrow₁ arrow₁))

Step-·-left : {trm1 trm2 trm1' trm1'' : Term} → (superarity : SuperArity (trm1 · trm2) ≢ just (+ 0)) → (steps : Step (trm1 · trm2) (trm1' · trm1'')) → ->> trm1 trm1'
Step-·-left {trm1} {trm2} {trm1'} {.trm2} superarity (left-step steps) = node _ _ steps
Step-·-left {trm1} {trm2} {.trm1} {trm1''} superarity (right-step steps) = reflexive _
Step-·-left {trm1} {trm2} {trm1'} {trm1''} superarity (appFold arity isc eqn) = ⊥-elim (superarity arity)

->>-·-left : {trm1 trm2 trm1' trm1'' : Term} → (superarity : SuperArity (trm1 · trm2) ≢ just (+ 0)) → ->> (trm1 · trm2) (trm1' · trm1'') → ->> trm1 trm1'
->>-·-left {trm1} {trm2} {.trm1} {.trm2} superarity (reflexive .(trm1 · trm2)) = reflexive _
->>-·-left {trm1} {trm2} {trm1'} {trm1''} superarity (node .(trm1 · trm2) .(trm1' · trm1'') x) = Step-·-left superarity x
->>-·-left {trm1} {trm2} {trm1'} {trm1''} superarity (·-step .trm1 .trm1' .trm2 .trm1'' arrow arrow₁) = arrow

Step-·-right : {trm1 trm2 trm1' trm1'' : Term} → (superarity : SuperArity (trm1 · trm2) ≢ just (+ 0)) → (steps : Step (trm1 · trm2) (trm1' · trm1'')) → ->> trm2 trm1''
Step-·-right {trm1} {trm2} {trm1'} {.trm2} superarity (left-step steps) = reflexive _
Step-·-right {trm1} {trm2} {.trm1} {trm1''} superarity (right-step steps) = node _ _ steps
Step-·-right {trm1} {trm2} {trm1'} {trm1''} superarity (appFold arity isc eqn) = ⊥-elim (superarity arity)

->>-·-right : {trm1 trm2 trm1' trm1'' : Term} → (superarity : SuperArity (trm1 · trm2) ≢ just (+ 0)) → ->> (trm1 · trm2) (trm1' · trm1'') → ->> trm2 trm1''
->>-·-right {trm1} {trm2} {.trm1} {.trm2} superarity (reflexive .(trm1 · trm2)) = reflexive _
->>-·-right {trm1} {trm2} {trm1'} {trm1''} superarity (node .(trm1 · trm2) .(trm1' · trm1'') x) = Step-·-right superarity x
->>-·-right {trm1} {trm2} {trm1'} {trm1''} superarity (·-step .trm1 .trm1' .trm2 .trm1'' arrow arrow₁) = arrow₁

-------------------------------
-- Church-Rosser preliminaries
-------------------------------

Subst-arg-lemma : {n : ℕ}{arg arg' x : Term} → (arrow : ->> arg arg') → ->> (Substitute n x arg) (Substitute n x arg')
Subst-arg-lemma {n} {arg} {arg'} {Self} arrow = reflexive Self
Subst-arg-lemma {n} {arg} {arg'} {(! n₁)} arrow = reflexive _
Subst-arg-lemma {n} {arg} {arg'} {` x} arrow with ℕ-Dec n x 
... | yes y = arrow
... | no y = reflexive _
Subst-arg-lemma {n} {arg} {arg'} {Λ n₁ x} arrow = reflexive _
Subst-arg-lemma {n} {arg} {arg'} {x · x₁} arrow = ·-step (Substitute n x arg) (Substitute n x arg') (Substitute n x₁ arg) (Substitute n x₁ arg') (Subst-arg-lemma {n} {arg}{arg'} {x} arrow) (Subst-arg-lemma {n} {arg}{arg'} {x₁} arrow)

x≡Subst-x-lemma : {n : ℕ} {x arg : Term} → (isc : isCombinator x ≡ true) → x ≡ Substitute n x arg
x≡Subst-x-lemma {n} {(! n₁)} {arg} isc = refl
x≡Subst-x-lemma {n} {Λ n₁ x {scoping}} {arg} isc = refl
x≡Subst-x-lemma {n} {x · x₁} {arg} isc = cong₂ (λ x y → x · y) xsx xsx'
                 where
                  xsx : x ≡ Substitute n x arg
                  xsx = x≡Subst-x-lemma (∧-elim-left isc)
                  xsx' : x₁ ≡ Substitute n x₁ arg
                  xsx' = x≡Subst-x-lemma (∧-elim-right isc)

Subst-AppFold0-lemma-hlp : {x x' x₁ x₁' y y' : Term} → (x ≡ x') → (x₁ ≡ x₁') → (y ≡ y') → ->> (x · x₁) y → ->> (x' · x₁') y'
Subst-AppFold0-lemma-hlp {x} {.x} {x₁} {.x₁} {y} {.y} refl refl refl xxy = xxy

Subst-AppFold0-lemma : {n : ℕ}{x arg arg' : Term} {arity : SuperArity x ≡ just (+ 0)} {isc : isCombinator x ≡ true} → ->> (Substitute n x arg) (Substitute n (AppFold {0} x arity isc) arg')
Subst-AppFold0-lemma {n} {x · x'} {arg} {arg'} {arity} {isc} = hlp
      where
        apF = (AppFold' {0} x (·SuperArity-lemma' {0}{x}{x'} arity) (∧-elim-left isc))
        stepxx' : Step (x · x') (AppFold {0} (x · x') arity isc)
        stepxx' = appFold {x · x'} arity isc {AppFold {0} (x · x') arity isc} refl
        xx' : ->> (x · x') (AppFold {0} (x · x') arity isc)
        xx' = node (x · x') (AppFold {0} (x · x') arity isc) stepxx'
        iscApp : isCombinator (AppFold {0} (x · x') arity isc) ≡ true
        iscApp = isCombinatorExpr->>invar isc xx'
        iscx : isCombinator x ≡ true
        iscx = ∧-elim-left isc
        iscx' : isCombinator x' ≡ true
        iscx' = ∧-elim-right isc
        hlp : ->> ((Substitute n x arg) · (Substitute n x' arg))
                   (Substitute n (AppFold {0} (x · x') arity isc) arg')
        hlp = Subst-AppFold0-lemma-hlp {x}{_}{x'}{_}{AppFold {0} (x · x') arity isc}{_} (x≡Subst-x-lemma (∧-elim-left isc)) (x≡Subst-x-lemma (∧-elim-right isc)) (x≡Subst-x-lemma iscApp) xx' 

Subst-AppFoldΛ-lemma : {n : ℕ}{x arg arg' : Term} {arity : SuperArity x ≡ just (+ 0)} {isc : isCombinator x ≡ true}{islx : isLambda?n n x ≡ true}{islx' : isLambda?n n (AppFold x arity isc) ≡ true}{iscx : isCombinator arg ≡ true}{iscx' : isCombinator arg' ≡ true}  → ->> (SubstituteΛ {n} x islx arg iscx) (SubstituteΛ {n} (AppFold x arity isc) islx' arg' iscx')
Subst-AppFoldΛ-lemma {n} {Self} {arg} {arg'} {arity} {()} {islx} {islx'} {iscx} {iscx'}
Subst-AppFoldΛ-lemma {n} {(! n₁)} {arg} {arg'} {()} {refl} {islx} {islx'} {iscx} {iscx'}
Subst-AppFoldΛ-lemma {n} {` x} {arg} {arg'} {()} {isc} {islx} {islx'} {iscx} {iscx'}
Subst-AppFoldΛ-lemma {n} {Λ n₁ x {scoping}} {arg} {arg'} {()} {refl} {islx} {islx'} {iscx} {iscx'}
Subst-AppFoldΛ-lemma {n} {x1 · x2} {arg} {arg'} {arity} {isc} {()} {islx'} {iscx} {iscx'}

app≡app'-lemma : {M₂ : Term} {app app' : Σ[ x ∈ Term ] ((isLambda?n 0 x) ≡ true)} → (app≡app' : app ≡ app') →
                                     Substitute zero  (isLambda?→inner (isLambda?n→isLambda? {0} {proj₁ app'} (proj₂ app'))) M₂ ≡
                                     Substitute zero  (isLambda?→inner (isLambda?n→isLambda? {0} {proj₁ app} (proj₂ app))) M₂
app≡app'-lemma {M₂} {app} {.app} refl = refl

AppFold-eq-lemma : {n : ℕ} {trm : Term} {superarity : SuperArity trm ≡ just +[1+ n ]}{superarity' : SuperArity trm ≡ just +[1+ n ]}{isc : isCombinator trm ≡ true} → AppFold' {n} trm superarity isc ≡ AppFold' {n} trm superarity' isc
AppFold-eq-lemma {n} {trm}{superarity} {superarity'}{isc} = cong (λ w → AppFold' trm w isc) hlp 
                         where
                           hlp : superarity ≡ superarity'
                           hlp = K-Maybeℤ superarity superarity'

AppFold'-eq-lemma : {n : ℕ} {trm : Term} {superarity : SuperArity trm ≡ just +[1+ n ]}{superarity' : SuperArity trm ≡ just +[1+ n ]}{isc isc' : isCombinator trm ≡ true} → AppFold' {n} trm superarity isc ≡ AppFold' {n} trm superarity' isc' 
AppFold'-eq-lemma {n} {trm} {superarity} {superarity'} {isc} {isc'} = cong₂ (λ x y → AppFold' trm x y) (K-Maybeℤ superarity superarity') (K-bool' isc isc')

mutual
  Subst-Step-lemma : {n : ℕ}{x x' arg arg' : Term} → (arrow : Step x x') → (arrow' : ->> arg arg') → ->> (Substitute n x arg) (Substitute n x' arg')
  Subst-Step-lemma {n} {.(_ · _)} {.(_ · _)} {arg} {arg'} (left-step {trm1}{trm2}{trm1'} arrow) arrow' = ·-step (Substitute n trm1 arg) (Substitute n trm1' arg') (Substitute n trm2 arg) (Substitute n trm2 arg') (Subst-Step-lemma arrow arrow') ((Subst->>-lemma {n}{trm2}{trm2} (reflexive _) arrow'))
  Subst-Step-lemma {n} {.(_ · _)} {.(_ · _)} {arg} {arg'} (right-step {trm1}{trm2}{trm2'} arrow) arrow' = ·-step (Substitute n trm1 arg) (Substitute n trm1 arg') (Substitute n trm2 arg) (Substitute n trm2' arg') (Subst->>-lemma {n}{trm1}{trm1} (reflexive _) arrow') (Subst-Step-lemma arrow arrow')
  Subst-Step-lemma {n} {.(Λ _ _)} {.(Λ _ _)} {arg} {arg'} (Λ-step {_}{trm}{trm'} arrow scoping scoping') arrow' = Λ-step _ trm trm' scoping scoping' (node trm trm' arrow)
  Subst-Step-lemma {n} {x} {.(AppFold x arity isc)} {arg} {arg'} (appFold arity isc refl) arrow' = hlp 
                         where
                           hlp : ->> (Substitute n x arg) (Substitute n (AppFold {0} x arity isc) arg')
                           hlp = Subst-AppFold0-lemma {n}{x}{arg}{arg'} {arity} {isc}

  Subst->>-lemma : {n : ℕ}{x x' arg arg' : Term} → (arrow : ->> x x') → (arrow' : ->> arg arg') → ->> (Substitute n x arg) (Substitute n x' arg')
  Subst->>-lemma {n} {x} {.x} {arg} {arg'} (reflexive .x) arrow' = Subst-arg-lemma {n}{arg}{arg'}{x} arrow'
  Subst->>-lemma {n} {x} {x'} {arg} {arg'} (node .x .x' x₁) arrow' = Subst-Step-lemma x₁ arrow' 
  Subst->>-lemma {n} {.(Λ n₁ trm {scoping})} {.(Λ n₁ trm' {scoping'})} {arg} {arg'} (Λ-step n₁ trm trm' scoping scoping' arrow) arrow' = Λ-step n₁ trm trm' scoping scoping' arrow
  Subst->>-lemma {n} {.(trm1 · trm2)} {.(trm1' · trm2')} {arg} {arg'} (·-step trm1 trm1' trm2 trm2' arrow arrow₁) arrow' =  ·-step (Substitute n trm1 arg)(Substitute n trm1' arg')(Substitute n trm2 arg)(Substitute n trm2' arg') ( Subst->>-lemma arrow arrow') (Subst->>-lemma arrow₁ arrow')


Substitute->>-lemma-hlp : {n : ℕ}{x arg arg' : Term}{islx islx' : isLambda?n n x ≡ true}{iscx : isCombinator arg ≡ true}{iscx' : isCombinator arg' ≡ true} → (arrow' : ->> arg arg') → ->> (SubstituteΛ {n} x islx arg iscx) (SubstituteΛ {n} x islx' arg' iscx')
Substitute->>-lemma-hlp {zero} {Λ zero x {scoping}} {arg} {arg'} {islx} {islx'} {iscx} {iscx'} arrow' = Subst->>-lemma {0}{x}{x}{arg}{arg'} (reflexive _) arrow'
Substitute->>-lemma-hlp {suc n} {Λ (suc n₁) x {scoping}} {arg} {arg'} {islx} {islx'} {iscx} {iscx'} arrow' with ℕ-Dec n n₁ 
... | yes refl = Λ-step n (Substitute (suc n) x arg) (Substitute (suc n) x arg') _ _ (Subst->>-lemma {suc n} {x}{x}{arg}{arg'} (reflexive _) arrow')

Substitute-Step-lemma : {n : ℕ}{x x' arg arg' : Term}{islx : isLambda?n n x ≡ true}{islx' : isLambda?n n x' ≡ true}{iscx : isCombinator arg ≡ true}{iscx' : isCombinator arg' ≡ true} → (steps : Step x x') → (arrow' : ->> arg arg') → ->> (SubstituteΛ {n} x islx arg iscx) (SubstituteΛ {n} x' islx' arg' iscx')
Substitute-Step-lemma {zero} {.(Λ n₁ trm)} {.(Λ n₁ trm')} {arg} {arg'} {islx} {islx'} {iscx} {iscx'} (Λ-step {n₁} {trm} {trm'} steps scoping scoping') arrow2 with ℕ-Dec n₁ 0 
Substitute-Step-lemma {zero} {.(Λ n₁ trm)} {.(Λ n₁ trm')} {arg} {arg'} {islx} {islx'} {iscx} {iscx'} (Λ-step {n₁} {trm} {trm'} steps scoping scoping') arrow2 | yes refl = Subst-Step-lemma steps arrow2
Substitute-Step-lemma {zero} {.(Λ zero trm)} {.(Λ zero trm')} {arg} {arg'} {islx} {islx'} {iscx} {iscx'} (Λ-step {zero} {trm} {trm'} steps _ _) arrow2 | no x = ⊥-elim (x refl)
Substitute-Step-lemma {suc n} {.(Λ (suc n₁) trm)} {.(Λ (suc n₁) trm')} {arg} {arg'} {islx} {islx'} {iscx} {iscx'} (Λ-step {suc n₁} {trm} {trm'} steps scoping scoping') arrow2 with ℕ-Dec n n₁ 
... | yes refl = Λ-step n (Substitute (suc n) trm arg) (Substitute (suc n) trm' arg') (Substitute-lemma {n}{trm}{arg} iscx scoping) (Substitute-lemma {n}{trm'}{arg'} iscx' scoping') hlp
                                   where
                                     hlp : ->> (Substitute (suc n) trm arg) (Substitute (suc n) trm' arg')
                                     hlp = Subst-Step-lemma steps arrow2
Substitute-Step-lemma {n} {x} {.(AppFold x arity isc)} {arg} {arg'} {islx} {islx'} {iscx} {iscx'} (appFold arity isc refl) arrow2 = Subst-AppFoldΛ-lemma {n}{x}{arg}{arg'}{arity}{isc}{islx}{islx'}{iscx}{iscx'} 

Substitute->>-lemma : {n : ℕ}{x x' arg arg' : Term}{islx : isLambda?n n x ≡ true}{islx' : isLambda?n n x' ≡ true}{iscx : isCombinator arg ≡ true}{iscx' : isCombinator arg' ≡ true} → (arrow : ->> x x') → (arrow' : ->> arg arg') → ->> (SubstituteΛ {n} x islx arg iscx) (SubstituteΛ {n} x' islx' arg' iscx')
Substitute->>-lemma {n} {x} {.x} {arg} {arg'} {islx} {islx'} {iscx} {iscx'} (reflexive .x) arrow' = Substitute->>-lemma-hlp {n}{x}{arg}{arg'} arrow'
Substitute->>-lemma {n} {x} {x'} {arg} {arg'} {islx} {islx'} {iscx}{iscx'} (node .x .x' x₁) arrow' = Substitute-Step-lemma {n}{x}{x'} {arg}{arg'} x₁ arrow'
Substitute->>-lemma {zero} {.(Λ 0 trm {scoping})} {.(Λ 0 trm' {scoping'})} {arg} {arg'} {islx} {islx'} {iscx} {iscx'} (Λ-step 0 trm trm' scoping scoping' arrow) arrow' = Subst->>-lemma {0} {trm }{trm'}{arg}{arg'} arrow arrow'
Substitute->>-lemma {suc n} {.(Λ (suc n₁) trm)} {.(Λ (suc n₁) trm')} {arg} {arg'} {islx} {islx'} {iscx} {iscx'} (Λ-step (suc n₁) trm trm' scoping scoping' arrow) arrow' with ℕ-Dec n n₁ 
... | yes refl = Λ-step n (Substitute (suc n) trm arg) (Substitute (suc n) trm' arg') _ _ (Subst->>-lemma arrow arrow')
   

isLambda?n-Subst-lemma : {arg arg' : Term} → 
                         (app-trm :   Σ[ x ∈ Term ] ((isLambda?n 0 x) ≡ true)) → (app-trm' :  Σ[ x ∈ Term ] ((isLambda?n 0 x) ≡ true)) →
                         (arrow : ->> (proj₁ app-trm) (proj₁ app-trm')) → (arrow' : ->> arg arg') → 
                                  ->> (Substitute zero (isLambda?→inner (isLambda?n→isLambda? {0}{proj₁ app-trm} (proj₂ app-trm))) arg)
                                      (Substitute zero (isLambda?→inner (isLambda?n→isLambda? {0}{proj₁ app-trm'} (proj₂ app-trm'))) arg')
isLambda?n-Subst-lemma {arg} {arg'} (Λ 0 x {scoping} , isl) (Λ 0 .x {.scoping} , isl') (reflexive .(Λ zero x)) arrow' = Subst->>-lemma {0}{x}{x}{arg}{arg'} (reflexive _) arrow'
isLambda?n-Subst-lemma {arg} {arg'} (Λ 0 x {scoping} , isl) (Λ 0 x' {scoping'} , isl') (node .(Λ zero x) .(Λ zero x') y) arrow' = Subst->>-lemma {0}{x}{x'}{arg}{arg'} (node x x' hlp) arrow'
     where
       hlp : Step x x'
       hlp = StepΛ-extract-lemma {0}{0} {x}{x'}{scoping}{scoping'} y
isLambda?n-Subst-lemma {arg} {arg'} (Λ 0 x {scoping} , isl) (Λ 0 x' {scoping'} , isl') (Λ-step .zero .x .x' .scoping .scoping' arrow) arrow' = Subst->>-lemma arrow arrow'


AppFold'-eqn : {n : ℕ} {A B C trm1 trm1' trm2 trm2' : Term} {arity : (SuperArity (trm1 · trm2)) ≡ just (+ n)}{arity' : (SuperArity (trm1' · trm2')) ≡ just (+ n)} {isc :  isCombinator trm1 ∧ isCombinator trm2 ≡ true} {isc' :  isCombinator trm1' ∧ isCombinator trm2' ≡ true} -> (A ≡ (proj₁ (AppFold' {n} trm1 (·SuperArity-lemma {+ n} {trm1} {trm2} arity) (∧-elim-left isc)))) → (B ≡ (proj₁ (AppFold' {n} trm1' (·SuperArity-lemma {+ n} {trm1'} {trm2} arity') (∧-elim-left isc')))) → (C ≡ (proj₁ (AppFold' {n} trm1' (·SuperArity-lemma {+ n} {trm1'} {trm2'} arity') (∧-elim-left isc')))) → 
               (arrow : ->> A B) -> (->> A C)
AppFold'-eqn {n}{A}{B}{C}{trm1}{trm1'}{trm2}{trm2'}{arity}{arity'}{isc}{isc'} eqnA eqnB eqnC arrow1 = ->>Eq-lemma-right arrow1 hlp
             where
               hlp : B ≡ C
               hlp = trans eqnB (trans (cong (λ w → proj₁ w) (AppFold-eq-lemma {n}{trm1'}{·SuperArity-lemma {_}{trm1'}{trm2} arity'}{·SuperArity-lemma {_}{trm1'}{trm2'} arity'}{∧-elim-left isc'})) (sym eqnC))


SubstituteΛ≡1-lemma  : {n : ℕ} {arg : Term} {isc : isCombinator arg ≡ true} {app-inner : Term}{scope-app-inner : (Scope app-inner <= (suc n)) ≡ true} → (app : Σ[ x ∈ Term ] ((isLambda?n (suc n) x) ≡ true)) → (eqn1 : (proj₁ app) ≡  (Λ (suc n) app-inner {scope-app-inner})) → (SubstituteΛ {suc n} (proj₁ app) (proj₂ app) arg isc) ≡ SubstituteΛ {suc n} (Λ (suc n) app-inner {scope-app-inner}) (isLambda?nΛ {suc n}{Λ (suc n) app-inner {scope-app-inner}} refl) arg isc
SubstituteΛ≡1-lemma {n} {arg} {isc} {app-inner} {scope-app-inner} (.(Λ (suc n) app-inner {scope-app-inner}) , app2) refl with ℕ-Dec n n
... | yes refl = refl
                                       where
                                         eqn2-hlp : (Scope (Λ (suc n) app-inner {scope-app-inner}) <= (suc n)) ≡ true
                                         eqn2-hlp = refl
                                         eqn2 : (isLambda?nΛ {suc n} {Λ (suc n) app-inner {scope-app-inner}} eqn2-hlp) ≡ (isLambda?nΛ {suc n}{Λ (suc n) app-inner {scope-app-inner}} refl)
                                         eqn2 = refl
 
mutual
 ->>SubstituteΛ-lemma0 : {n : ℕ} {trm1 trm1' trm2 trm1'' : Term} {arity : SuperArity trm1 ≡ just +[1+ (suc n) ]} {arity' : SuperArity trm1' ≡ just +[1+ (suc n) ]} {isc : isCombinator trm1 ≡ true} {isc' : isCombinator trm1' ≡ true}{isc2 : isCombinator trm2 ≡ true}{isc2' : isCombinator trm1'' ≡ true} → (arrow1 : ->> trm1 trm1') → (arrow2 : ->> trm2 trm1'') → 
     ->> (SubstituteΛ {suc n}
           (proj₁ (AppFold' trm1 arity isc)) (proj₂ (AppFold' trm1 arity isc))
            trm2 isc2)
         (SubstituteΛ {suc n}
           (proj₁ (AppFold' trm1' arity' isc')) (proj₂ (AppFold' trm1' arity' isc'))
            trm1'' isc2')
 ->>SubstituteΛ-lemma0 {n} {trm1}{trm1'}{trm2}{trm1''}{arity}{arity'}{isc}{isc'}{isc2}{isc2'} arrow1 arrow2  = Substitute->>-lemma {suc n}{(proj₁ (AppFold' trm1 arity isc))}{ (proj₁ (AppFold' trm1' arity' isc'))}{trm2}{trm1''}{ (proj₂ (AppFold' trm1 arity isc))}{ (proj₂ (AppFold' trm1' arity' isc'))}{isc2} hlp arrow2
                        where
                          hlp :  ->> (proj₁ (AppFold' {suc n} trm1 arity isc)) (proj₁ (AppFold' {suc n} trm1' arity' isc'))
                          hlp = ->>-AppFold'-lemma0 arrow1

 Λ0SelfSub-lemma : {n : ℕ} {trm1 trm1' : Term}{scoping : (Scope trm1 <= n) ≡ true}{scoping' : (Scope trm1' <= n) ≡ true}{scoping2 : (Scope (SelfSub (Λ n trm1) trm1) <= n) ≡ true}{scoping2' : (Scope (SelfSub (Λ n trm1') trm1') <= n) ≡ true} → (arrow : ->> trm1 trm1') → ->> (Λ n (SelfSub (Λ n trm1 {scoping}) trm1) {scoping2}) (Λ n (SelfSub (Λ n trm1' {scoping'}) trm1') {scoping2'})
 Λ0SelfSub-lemma {n} {trm1}{trm1'}{scoping}{scoping'}{scoping2}{scoping2'} arrow  = hlp
                         where
                           hlp : ->> (Λ n (SelfSub (Λ n trm1 {scoping}) trm1) {scoping2}) (Λ n (SelfSub (Λ n trm1' {scoping'}) trm1') {scoping2'})
                           hlp = Λ-step n (SelfSub (Λ n trm1 {scoping}) trm1) (SelfSub (Λ n trm1' {scoping'}) trm1') scoping2 scoping2' (SelfSubΛ-eq' arrow)

 ->>-AppFold'-lemma0 : {n : ℕ} {trm1 trm1' : Term}{arity : (SuperArity trm1 ≡ just +[1+ n ])}{arity' : SuperArity trm1' ≡ just +[1+ n ]}{isc : isCombinator trm1 ≡ true}{isc' : isCombinator trm1' ≡ true} → (arrow1 : ->> trm1 trm1') → ->> (proj₁ (AppFold' {n} trm1 arity isc)) (proj₁ (AppFold' {n} trm1' arity' isc'))
 ->>-AppFold'-lemma0 {n} {Λ n₁ trm1 {scoping}} {Λ n₂ trm1' {scoping'}} {arity} {arity'} {isc} {isc'} arrow1 with ℕ-Dec n₁ n₂ | ℕ-Dec n n₁
 ... | yes refl | no x = ⊥-elim (x (just1+n≡m (sym arity)))
 ... | no x | v = ⊥-elim (x (just1+n≡m (trans arity (sym arity'))))
 ... | yes refl | yes refl with ℕ-Dec n n
 ->>-AppFold'-lemma0 {n₁} {Λ n₁ trm1 {scoping}} {Λ n₁ trm1' {scoping'}} {arity} {arity'} {isc} {isc'} arrow1 | yes refl | yes refl | no x = ⊥-elim (x refl)
 ->>-AppFold'-lemma0 {n₁} {Λ n₁ trm1 {scoping}} {Λ n₁ trm1' {scoping'}} {arity} {arity'} {isc} {isc'} arrow1 | yes refl | yes refl | yes refl = Λ0SelfSub-lemma (->>ExtractΛtrm scoping scoping' arrow1)

 ->>-AppFold'-lemma0 {n} {trm1 · trm2} {Λ n₁ trm1' {scoping'}} {arity} {arity'} {isc} {isc'} arrow1 = ⊥-elim (just≢ℕ contra)
                         where
                           hlp : (SuperArity (trm1 · trm2)) ≡ just (+ 0) 
                           hlp = ·ToΛ0 {n₁} arrow1
                           contra : just (+ (suc n)) ≡ just (+ 0)
                           contra = trans (sym arity) hlp
 ->>-AppFold'-lemma0 {n} {Λ n₁ trm1 {scoping}} {trm1' · trm1''} {arity} {arity'} {isc} {isc'} arrow1 = ⊥-elim (ΛTo·→⊥ arrow1)
 ->>-AppFold'-lemma0 {n} {trm1 · trm2} {trm1' · trm1''} {arity} {arity'} {isc} {isc'} arrow1 = hlp 
                         where
                           notn : (SuperArity (trm1 · trm2)) ≢ just (+ n)
                           notn = λ x → ⊥-elim (justn≢justn+1 (trans (sym x) arity))
                           not0 :  (SuperArity (trm1 · trm2)) ≢ just (+ 0)
                           not0 = λ x → just≢ℕ (trans (sym arity) x)
                           hlp : ->>
                                   (SubstituteΛ {suc n}
                                    (proj₁
                                    (AppFold' trm1 (·SuperArity-lemma' {suc n}{trm1}{trm2} arity) (∧-elim-left isc)))
                                        (proj₂
                                      (AppFold' trm1 (·SuperArity-lemma' {suc n}{trm1}{trm2} arity) (∧-elim-left isc)))
                                       trm2 (∧-elim-right isc) )
                                    (SubstituteΛ {suc n}
                                       (proj₁
                                    (AppFold' trm1' (·SuperArity-lemma' {suc n}{trm1'}{trm1''} arity') (∧-elim-left isc')))
                                      (proj₂
                                    (AppFold' trm1' (·SuperArity-lemma' {suc n}{trm1'}{trm1''} arity') (∧-elim-left isc')))
                                     trm1'' (∧-elim-right isc'))
                           hlp = ->>SubstituteΛ-lemma0 {n}{trm1}{trm1'}{trm2}{trm1''}
                                                       {·SuperArity-lemma' {suc n}{trm1}{trm2} arity}{·SuperArity-lemma' {suc n}{trm1'}{trm1''} arity'}
                                                       {∧-elim-left isc}{∧-elim-left isc'}{∧-elim-right isc}
                                                       (->>-·-left not0 arrow1) (->>-·-right not0 arrow1)          

->>-Diamond-hlp-hlp4 : {trm1 trm3 trm1' trm2 : Term}{arity : (SuperArity (trm1 · trm3 · trm2)) ≡ just (+ 0)}{arity' : SuperArity (trm1' · trm2) ≡ just (+ 0)}{isc : isCombinator trm1 ∧ isCombinator trm3 ≡ true}{isc' : isCombinator trm1' ≡ true} → (arrow1 : ->> (trm1 · trm3) trm1') → ->> (proj₁ (AppFold' {0} (trm1 · trm3) (·SuperArity-lemma' {0} {trm1 · trm3}{trm2} arity) isc)) (proj₁ (AppFold' {0} trm1' (·SuperArity-lemma' {0}{trm1'}{trm2} arity') isc'))
->>-Diamond-hlp-hlp4 {trm1} {trm3} {trm1'}{trm2}{arity}{arity'}{isc}{isc'} arrow1 = ->>-AppFold'-lemma0 arrow1                       --->>-Diamond-hlp-hlp5 arrow1 

->>-Diamond-hlp-hlp3 : {trm1 trm2 trm1' : Term}{arity : (SuperArity (trm1 · trm2)) ≡ just (+ 0)}{isc : isCombinator trm1 ≡ true}{arity' : (SuperArity (trm1' · trm2)) ≡ just (+ 0)}{isc' : isCombinator trm1' ≡ true} → ->> trm1 trm1' → ->> (proj₁ (AppFold' {0} trm1 (·SuperArity-lemma {+ 0} {trm1} {trm2} arity) (isc))) (proj₁ (AppFold' {0} trm1' (·SuperArity-lemma {+ 0} {trm1'} {trm2} arity') (isc')))
->>-Diamond-hlp-hlp3  {Λ 0 trm1 {scoping}} {trm2} {.(Λ 0 trm1)} {refl} {refl} {arity'} {isc'} (reflexive .(Λ 0 trm1)) = ->>Eq-lemma-left (reflexive _) refl
->>-Diamond-hlp-hlp3 {Λ .n trm1 {scoping}} {trm2} {.(Λ n _)} {refl} {refl} {arity'} {isc'} (node .(Λ n trm1 {scoping}) .(Λ n _) (Λ-step {n}{trm1}{trm'} x .scoping scoping')) =  Λ-step n (SelfSub (Λ n trm1 {scoping}) trm1) (SelfSub (Λ n trm' {scoping'}) trm') _ _ (SelfSubΛ-eq' {n}{trm1}{trm'} (node trm1 trm' x))
->>-Diamond-hlp-hlp3 {Λ 0 trm1 {scoping}} {trm2} {.(Λ 0 trm')} {refl} {refl} {arity'} {isc'} (Λ-step 0 .trm1 trm' .scoping scoping' arrow1) = hlp'
                     where
                       scoper : (Scope (SelfSub (Λ 0 trm1 {scoping}) trm1) <= 0) ≡ true
                       scoper = _
                       scoper' :  (Scope (SelfSub (Λ 0 trm' {scoping'}) trm') <= 0) ≡ true
                       scoper' = _
                       hlp' : ->> (Λ 0 (SelfSub (Λ 0 trm1 {scoping}) trm1) {scoper}) (Λ 0 (SelfSub (Λ 0 trm' {scoping'}) trm') {_})
                       hlp' = Λ-step 0 (SelfSub (Λ 0 trm1 {scoping}) trm1) (SelfSub (Λ 0 trm' {scoping'}) trm') scoper scoper' (SelfSubΛ-eq' arrow1)
->>-Diamond-hlp-hlp3  {trm1 · trm3} {trm2} {trm1'} {arity} {isc} {arity'} {isc'} arrow1 = target' 
                      where
                        arity13 : SuperArity (trm1 · trm3) ≡ just +[1+ 0 ]
                        arity13 = ·SuperArity-lemma' {0}{trm1 · trm3}{trm2} arity
                        app : Σ[ x ∈ Term ] ((isLambda?n (suc 0) x) ≡ true)
                        app = AppFold' {suc 0} trm1 (·SuperArity-lemma' {suc 0}{trm1}{trm3} arity13) (∧-elim-left isc)
                        islapp : isLambda?n (suc 0) (proj₁ app) ≡ true
                        islapp = proj₂ app
                        app-inner : Term
                        app-inner = isLambda?→inner {proj₁ app} (isLambda?n→isLambda? {(suc 0)} (proj₂ app))
                        scope-app-inner : (Scope app-inner <= (suc 0)) ≡ true
                        scope-app-inner = isLambda?-inner-Scope {(suc 0)}{proj₁ app} (proj₂ app)
                        app' :  Σ[ x ∈ Term ] ((isLambda?n 0 x) ≡ true)
                        app' =  AppFold' {0} trm1' (·SuperArity-lemma' {0}{trm1'}{trm2} arity') isc'
                        iscapp' : isCombinator (proj₁ app') ≡ true 
                        iscapp' = isCombinatorAppFold'-lemma {0} {trm1'} (·SuperArity-lemma { (+ 0) } {trm1'}{trm2}  arity') (isc')
                        islapp' : isLambda?n 0 (proj₁ app') ≡ true
                        islapp' = proj₂ app'
                        app'-inner : Term
                        app'-inner = isLambda?→inner {proj₁ app'} (isLambda?n→isLambda? (proj₂ app'))
                        scope-app'-inner : (Scope app'-inner <= 0) ≡ true
                        scope-app'-inner =  isLambda?-inner-Scope {0}{proj₁ app'} (proj₂ app')
                        iscarg : isCombinator trm3 ≡ true
                        iscarg = ∧-elim-right isc
                        app-inner-def' : (proj₁ app) ≡ Λ (suc 0) (isLambda?→inner {proj₁ app} (isLambda?n→isLambda? {suc 0} (proj₂ app))) {isLambda?-inner-Scope {suc 0}{proj₁ app} (proj₂ app)}
                        app-inner-def' = ΛisLambda?-def' app
                        app'-inner-def' : (proj₁ app') ≡ Λ 0 (isLambda?→inner {proj₁ app'} (isLambda?n→isLambda? {0} (proj₂ app'))) {isLambda?-inner-Scope {0}{proj₁ app'} (proj₂ app')}
                        app'-inner-def' = ΛisLambda?-def' {0} app'
                        app-inner-def : proj₁ app ≡ Λ (suc 0) app-inner {scope-app-inner}
                        app-inner-def = app-inner-def'
                        app'-inner-def : proj₁ app' ≡ Λ 0 app'-inner {scope-app'-inner}
                        app'-inner-def = app'-inner-def'
                        app-alt : (SubstituteΛ {suc 0} (proj₁ app) (proj₂ app) trm3 (∧-elim-right isc)) ≡
                                   SubstituteΛ {suc 0} (Λ (suc 0) app-inner {scope-app-inner}) (isLambda?nΛ {suc 0}{Λ (suc 0) app-inner {scope-app-inner}} refl) trm3 (∧-elim-right isc)
                        app-alt = SubstituteΛ≡1-lemma {0} {trm3} {∧-elim-right isc}{app-inner}{scope-app-inner} app app-inner-def  
                        appSublemma :  SubstituteΛ {suc 0} (Λ (suc 0) app-inner {scope-app-inner}) (isLambda?nΛ {suc 0}{Λ (suc 0) app-inner {scope-app-inner}} refl) trm3 (∧-elim-right isc) ≡ Λ 0 (Substitute (suc 0) app-inner trm3) {_}
                        appSublemma = refl
                        ScopeSub : (Scope (Substitute (suc 0) app-inner trm3) <= 0) ≡ true
                        ScopeSub =   ScopeSubstituteCombinator-lemma' {app-inner}{trm3} scope-app-inner iscarg
                        Sublambda : (SubstituteΛ {suc 0} (proj₁ app) (proj₂ app) trm3 (∧-elim-right isc)) ≡  Λ 0 (Substitute (suc 0) app-inner trm3) {_} 
                        Sublambda = trans app-alt appSublemma
                        SubLambda' : (SubstituteΛ {suc 0} (proj₁ app) (proj₂ app) trm3 (∧-elim-right isc)) ≡  Λ 0 (Substitute (suc 0) app-inner trm3) {ScopeSub}
                        SubLambda' = trans Sublambda trm1≡trm→Λntrm1≡Λmtrm2-hlp
                        appF'-lemma : ->> (proj₁ (AppFold' {0} (trm1 · trm3) (·SuperArity-lemma' {0} {trm1 · trm3}{trm2} arity) isc)) (proj₁ app')
                        appF'-lemma = ->>-Diamond-hlp-hlp4 arrow1
                        target' :  ->> (SubstituteΛ {suc 0} (proj₁ app) (proj₂ app) trm3 (∧-elim-right isc)) (proj₁ app')
                        target' = ->>Eq-lemma-left appF'-lemma refl
                     
->>-Diamond-hlp-hlp2 : {trm trm' trm1 trm1' trm2 trm2' : Term} {arity : SuperArity (trm1 · trm2) ≡ just (+ 0)}{arity' : SuperArity (trm1' · trm2') ≡ just (+ 0)}{isc : isCombinator trm1 ∧ isCombinator trm2 ≡ true}{isc' : isCombinator trm1' ∧ isCombinator trm2' ≡ true} →
     (arrow1 : ->> trm1 trm1') -> (arrow2 : ->> trm2 trm2') ->   
     (trm ≡ proj₁ (AppFold' {0} trm1 (·SuperArity-lemma {(+ zero)}{trm1}{trm2} arity) (∧-elim-left isc))) →
     (trm' ≡ proj₁ (AppFold' {0} trm1' (·SuperArity-lemma {(+ zero)}{trm1'}{trm2'} arity') (∧-elim-left isc'))) →
     (->> trm trm')
->>-Diamond-hlp-hlp2 {.(proj₁ (AppFold' trm1 (·SuperArity-lemma {+ 0}{trm1}{trm2} arity) (∧-elim-left isc)))} {.(proj₁ (AppFold' trm1' (·SuperArity-lemma {+ 0}{trm1'}{trm2'}  arity') (∧-elim-left isc')))} {trm1} {trm1'} {trm2} {trm2'} {arity} {arity'} {isc} {isc'} arrow1 arrow2 refl refl = hlp
                      where
                         hlp' : ->> (proj₁ (AppFold' {0} trm1 (·SuperArity-lemma {+ 0} {trm1} {trm2} arity) (∧-elim-left isc)))
                                    (proj₁ (AppFold' {0} trm1' (·SuperArity-lemma {+ 0} {trm1'} {trm2} arity') (∧-elim-left isc')))
                         hlp' = ->>-Diamond-hlp-hlp3 arrow1           
                         hlp : ->> (proj₁ (AppFold' {0} trm1 (·SuperArity-lemma {+ 0} {trm1} {trm2} arity) (∧-elim-left isc)))
                                   (proj₁ (AppFold' {0} trm1' (·SuperArity-lemma {+ 0} {trm1'} {trm2'} arity') (∧-elim-left isc')))
                         hlp = AppFold'-eqn {0}{_}{_}{_}{trm1}{trm1'}{trm2}{trm2'}  refl refl refl hlp' 
->>-Diamond-hlp-hlp : {trm1 trm2 trm1' trm2' : Term} → (->> trm1 trm1') → (->> trm2 trm2') →
                      (arity : SuperArity (trm1 · trm2) ≡ just (+ 0)) → (arity' : SuperArity (trm1' · trm2') ≡ just (+ 0)) →
                      (isc : isCombinator trm1 ∧ isCombinator trm2 ≡ true) → (isc' : isCombinator trm1' ∧ isCombinator trm2' ≡ true) → 
                      ->> (Substitute zero (isLambda?→inner (isLambda?n→isLambda? {0}
                            {proj₁ (AppFold' {0} trm1 (·SuperArity-lemma {(+ zero)}{trm1}{trm2} arity) (∧-elim-left isc))}
                            (proj₂ (AppFold' {0} trm1 (·SuperArity-lemma {(+ zero)}{trm1}{trm2} arity) (∧-elim-left isc)))))
                             trm2)
                          (AppFold {0} (trm1' · trm2') arity' isc')
->>-Diamond-hlp-hlp {trm1}{trm2}{trm1'}{trm2'} arrow arrow' arity arity' isc isc' = subst-lemma
                      where
                        app-hlp : Σ[ x ∈ Term ] ((isLambda?n 0 x) ≡ true)
                        app-hlp = AppFold' {0} trm1 (·SuperArity-lemma {(+ zero)}{trm1}{trm2} arity) (∧-elim-left isc)
                        app'-hlp :  Σ[ x ∈ Term ] ((isLambda?n 0 x) ≡ true)                     
                        app'-hlp = AppFold' {0} trm1' (·SuperArity-lemma {(+ zero)}{trm1'}{trm2'} arity') (∧-elim-left isc')
                        arrow'' : ->> (proj₁ app-hlp) (proj₁ app'-hlp)
                        arrow'' = ->>-Diamond-hlp-hlp2 {_}{_}{trm1}{trm1'}{trm2}{trm2'}{arity}{arity'}{isc}{isc'} arrow arrow' refl refl 
                        subst-lemma : ->> (Substitute zero (isLambda?→inner (isLambda?n→isLambda? {0}{proj₁ app-hlp} (proj₂ app-hlp))) trm2)
                                          (Substitute zero (isLambda?→inner (isLambda?n→isLambda? {0}{proj₁ app'-hlp} (proj₂ app'-hlp))) trm2')
                        subst-lemma = isLambda?n-Subst-lemma app-hlp app'-hlp arrow'' arrow'

mutual
 ->>-Diamond-hlp2 : {M M1 M2 : Term} → (leftstep : Step M M1) → (rightstep : Step M M2) → Σ[ M3 ∈ Term ] (( ->> M1 M3 ) × ( ->> M2 M3 ))
 ->>-Diamond-hlp2 {.(_ · _)} {.(_ · _)} {M2} (left-step {trm1}{trm2}{trm1'} leftstep) rightstep = (proj₁ hlp) , ((proj₂ (proj₂ hlp)) ,  (proj₁ (proj₂ hlp)))
                      where
                        hlp :  Σ[ M3 ∈ Term ] ((->> M2 M3) × (->> (trm1' · trm2) M3))
                        hlp = ->>-Diamond-hlp _ rightstep (node trm1 trm1' leftstep) (reflexive _)
 ->>-Diamond-hlp2 {.(_ · _)} {.(_ · _)} {M2} (right-step {trm1}{trm2}{trm1'} leftstep) rightstep = (proj₁ hlp) , ((proj₂ (proj₂ hlp)) , (proj₁ (proj₂ hlp)))
                      where
                        hlp : Σ[ M3 ∈ Term ] ((->> M2 M3) × (->> (trm1 · trm1') M3))
                        hlp = ->>-Diamond-hlp _ rightstep (reflexive _) (node _ _ leftstep)
 ->>-Diamond-hlp2 {.(Λ _ _)} {.(Λ _ _)} {M2} (Λ-step {n}{trm}{trm'} leftstep scoping scoping') rightstep with isLambda?n n M2 in isl 
 ->>-Diamond-hlp2 {.(Λ _ _)} {.(Λ _ _)} {M2} (Λ-step {n}{trm}{trm'} leftstep scoping scoping') rightstep | false = ⊥-elim (false≡true→⊥ (trans (sym isl) (Step-Λ-lemma _ rightstep)))
 ->>-Diamond-hlp2 {.(Λ n _ )} {.(Λ n _)} {Λ n M2 {scoping}} (Λ-step {.n} {.trm} {trm''} leftstep scoping' scoping'') (Λ-step {n}{trm}{trm'} rightstep _ _) | true  = Λ n M3-inner {Scope-M3-inner} , Λ-step _ trm'' M3-inner scoping'' Scope-M3-inner (proj₁ (proj₂ hlp)) , Λ-step _ M2 M3-inner scoping Scope-M3-inner (proj₂ (proj₂ hlp))
                      where
                        hlp : Σ[ M3-inner ∈ Term ] (( ->> trm'' M3-inner ) × (->> M2 M3-inner)) 
                        hlp = ->>-Diamond (node _ _ leftstep) (node _ _ rightstep)
                        M3-inner : Term
                        M3-inner = proj₁ hlp
                        Scope-M3-inner :  (Scope M3-inner <= n) ≡ true
                        Scope-M3-inner = Scope->>-lemma2 {n}{trm''}{_} (proj₁ (proj₂ hlp)) scoping''
 ->>-Diamond-hlp2 {M₁ · M₂} {.(AppFold (M₁ · M₂) arity isc)} {.(_ · M₂)} (appFold {M₁ · M₂} arity isc refl) (left-step {trm1}{trm2}{trm1'} rightstep) = target
                      where
                        leftstep : Step (M₁ · M₂) (AppFold (M₁ · M₂) arity isc)
                        leftstep =  appFold {M₁ · M₂} arity isc refl
                        app : Σ[ x ∈ Term ] ((isLambda?n 0 x) ≡ true)
                        app = AppFold' {0} M₁ (·SuperArity-lemma' {0}{M₁}{M₂} arity) (∧-elim-left isc)
                        target : Σ[ M3 ∈ Term ] ( (->> (Substitute zero (isLambda?→inner {proj₁ app} (isLambda?n→isLambda? {0}{proj₁ app} (proj₂ app))) M₂) M3) × (->> (trm1' · M₂) M3) )
                        target = ->>-Diamond-hlp {M₁}{M₂}{trm1'}{M₂} (Substitute zero (isLambda?→inner {proj₁ app} (isLambda?n→isLambda? {0}{proj₁ app} (proj₂ app))) M₂)
                                                  leftstep (node _ _ rightstep) (reflexive _)   --step0 steps1 steps2
                                                  
 ->>-Diamond-hlp2 {M₁ · M₂} {.(AppFold (M₁ · M₂) arity isc)} {.(M₁ · _)} (appFold {trm} arity isc refl) (right-step {trm1}{trm2}{trm2'} rightstep) = target
                      where
                        leftstep : Step (M₁ · M₂) (AppFold (M₁ · M₂) arity isc)
                        leftstep =  appFold {M₁ · M₂} arity isc refl
                        app : Σ[ x ∈ Term ] ((isLambda?n 0 x) ≡ true)
                        app = AppFold' {0} M₁ (·SuperArity-lemma' {0}{M₁}{M₂} arity) (∧-elim-left isc)
                        target : Σ[ M3 ∈ Term ] ( (->> (Substitute zero (isLambda?→inner {proj₁ app} (isLambda?n→isLambda? {0}{proj₁ app} (proj₂ app))) M₂) M3) × (->> (M₁ · trm2') M3) )
                        target = ->>-Diamond-hlp {M₁} {M₂} {M₁} {trm2'} _ leftstep (reflexive _) (node _ _ rightstep)  
 ->>-Diamond-hlp2 {M₁ · M₂} {.(AppFold (M₁ · M₂) arity isc)} {M2} (appFold arity isc refl) (appFold arity₁ isc₁ eqn) = myfunc
                      where
                        m1 : Step (M₁ · M₂) (AppFold (M₁ · M₂) arity isc)
                        m1 = appFold arity isc refl
                        app : Σ[ x ∈ Term ] ((isLambda?n 0 x) ≡ true)
                        app = (AppFold' {0} M₁ (·SuperArity-lemma' {zero}{M₁}{M₂} arity) (∧-elim-left isc))
                        app' :  Σ[ x ∈ Term ] ((isLambda?n 0 x) ≡ true)
                        app' = (AppFold' {0} M₁ (·SuperArity-lemma' {zero}{M₁}{M₂} arity₁) (∧-elim-left isc₁))
                        app≡app' : app ≡ app'
                        app≡app' = AppFold'-eq-lemma {0} {M₁} {·SuperArity-lemma' {zero}{M₁}{M₂} arity}{·SuperArity-lemma' {zero}{M₁}{M₂} arity₁}{∧-elim-left isc}{∧-elim-left isc₁}
                        islappapp' : Substitute zero  (isLambda?→inner (isLambda?n→isLambda? {0} {proj₁ app'} (proj₂ app'))) M₂ ≡
                                     Substitute zero  (isLambda?→inner (isLambda?n→isLambda? {0} {proj₁ app} (proj₂ app))) M₂
                        islappapp' = app≡app'-lemma app≡app'            
                        myfunc' : Σ[ M3 ∈ Term ] (( ->> (Substitute zero (isLambda?→inner {proj₁ app'} (isLambda?n→isLambda? {0}{proj₁ app'} (proj₂ app'))) M₂) M3) × ( ->> M2 M3 ))
                        myfunc' = ->>-Diamond {AppFold (M₁ · M₂) arity₁ isc₁}{ (Substitute zero (isLambda?→inner {proj₁ app'} (isLambda?n→isLambda? {0}{proj₁ app'} (proj₂ app'))) M₂)}{M2} (reflexive _) (->>Eq-lemma-left (reflexive M2) eqn)
                        myfunc : Σ[ M3 ∈ Term ] (( ->> (Substitute zero (isLambda?→inner {proj₁ app} (isLambda?n→isLambda? {0}{proj₁ app} (proj₂ app))) M₂) M3) × ( ->> M2 M3 ))
                        myfunc = ->>-Diamond {AppFold (M₁ · M₂) arity isc}{ (Substitute zero (isLambda?→inner {proj₁ app} (isLambda?n→isLambda? {0}{proj₁ app} (proj₂ app))) M₂)}{M2} (reflexive _) (->>Eq-lemma-left (reflexive M2) (trans eqn islappapp'))
  
 ->>-Diamond-hlp : {trm1 trm2 trm1' trm2' : Term} → (M1 : Term) → (step0 : Step (trm1 · trm2) M1)  → (steps1 : ->> trm1 trm1') → (steps2 : ->> trm2 trm2') →  Σ[ M3 ∈ Term ] ((->> M1 M3) × (->> (trm1' · trm2') M3))
 ->>-Diamond-hlp {trm1} {trm2} {trm1'} {trm2'} .(_ · trm2) (left-step {trm1}{_}{trm1''} x) steps1 steps2 = M3' · trm2' , ·-step trm1'' M3' trm2 trm2' (proj₂ (proj₂ M3'-hlp)) steps2 , ·-step trm1' M3' trm2' trm2' (proj₁ (proj₂ M3'-hlp)) (reflexive trm2')
                              where
                                M3'-hlp : Σ[ M3' ∈ Term ] ((->> trm1' M3') × (->> trm1'' M3'))
                                M3'-hlp = ->>-Diamond steps1 (node trm1 trm1'' x)                             
                                M3' : Term
                                M3' = proj₁ M3'-hlp
 ->>-Diamond-hlp {trm1} {trm2} {trm1'} {trm2'} .(trm1 · trm3''') (right-step {trm1}{trm2}{trm3'''} x) steps1 steps2 = (trm1' · M3') , (·-step trm1 trm1' trm3''' M3' steps1 (proj₁ (proj₂ M3'-hlp)) , (·-step trm1' trm1' trm2' M3' (reflexive trm1') (proj₂ (proj₂ M3'-hlp))))
                              where
                                M3'-hlp : Σ[ M3' ∈ Term ] ((->> trm3''' M3') × (->> trm2' M3'))
                                M3'-hlp = ->>-Diamond (node trm2 trm3''' x) steps2                            
                                M3' : Term
                                M3' = proj₁ M3'-hlp
 ->>-Diamond-hlp {trm1} {trm2} {trm1'} {trm2'} .(AppFold (trm1 · trm2) arity isc) (appFold {trm1 · trm2} arity isc refl) steps1 steps2 = hlp
                              where
                                isc' : isCombinator trm1' ∧ isCombinator trm2' ≡ true
                                isc' = ∧-intro (isCombinatorExpr->>invar (∧-elim-left isc) steps1) (isCombinatorExpr->>invar (∧-elim-right isc) steps2)  
                                arity' : (SuperArity (trm1' · trm2')) ≡ just (+ zero)
                                arity' = ·SuperArity->>-lemma arity steps1 steps2
                                app'-hlp : Σ[ x ∈ Term ] ((isLambda?n 0 x) ≡ true)
                                app'-hlp = (AppFold' {0} trm1 (·SuperArity-lemma {(+ zero)}{trm1}{trm2} arity) (∧-elim-left isc))
                                app-hlp' : Term
                                app-hlp' = AppFold {0} (trm1' · trm2') arity' (∧-intro (isCombinatorExpr->>invar (∧-elim-left isc) steps1)
                                                                                       (isCombinatorExpr->>invar (∧-elim-right isc) steps2))
                                M3 : Term
                                M3 = app-hlp'
                                hlp : Σ[ M3 ∈ Term ] ((->> (Substitute zero (isLambda?→inner {proj₁ app'-hlp} (isLambda?n→isLambda? {0}{proj₁ app'-hlp} (proj₂ app'-hlp))) trm2) M3) × (->> (trm1' · trm2') M3))
                                hlp = M3 , ->>-Diamond-hlp-hlp {trm1}{trm2}{trm1'}{trm2'} steps1 steps2 arity arity' isc ((∧-intro (isCombinatorExpr->>invar (∧-elim-left isc) steps1) (isCombinatorExpr->>invar (∧-elim-right isc) steps2))) , node (trm1' · trm2') M3 (appFold {trm1' · trm2'} arity' (∧-intro (isCombinatorExpr->>invar (∧-elim-left isc) steps1) (isCombinatorExpr->>invar (∧-elim-right isc) steps2)) refl)

 ->>-Diamond : {M M1 M2 : Term} → (leftstep : ->> M M1) → (rightstep : ->> M M2) → Σ[ M3 ∈ Term ] (( ->> M1 M3 ) × ( ->> M2 M3 ))
 ->>-Diamond {M} {.M} {M2} (reflexive .M) rightstep = M2 , (rightstep , (reflexive M2))
 ->>-Diamond {M} {M1} {.M} (node .M .M1 x) (reflexive .M) = M1 , ((reflexive M1) , (node M M1 x))
 ->>-Diamond {M} {M1} {M2} (node .M .M1 x) (node .M .M2 y) = ->>-Diamond-hlp2 x y
 ->>-Diamond {.(Λ n trm)} {.(Λ n _)} {.(Λ n trm')} (node .(Λ n trm) .(Λ n _) (Λ-step {n}{trm}{trm''} x .scoping scoping'')) (Λ-step n trm trm' scoping scoping' rightstep) = Λ n M3' {M3'-scope}  , (CongΛ->> scoping'' M3'-scope (proj₁ (proj₂ inner-term)) , CongΛ->> scoping' M3'-scope (proj₂ (proj₂ inner-term)))
                    where
                      inner-term :  Σ[ M3' ∈ Term ] (( ->> trm'' M3' ) × ( ->> trm' M3' ))
                      inner-term = ->>-Diamond (node trm trm'' x) rightstep
                      M3' : Term
                      M3' = proj₁ inner-term
                      M3'-scope :  (Scope M3' <= n) ≡ true
                      M3'-scope = Scope->>-lemma2 {n}{trm''}{M3'} (proj₁ (proj₂ inner-term)) scoping''
 ->>-Diamond {.(trm1 · trm2)} {M1} {.(trm1' · trm2')} (node .(trm1 · trm2) .M1 x) (·-step trm1 trm1' trm2 trm2' rightstep rightstep₁) = ->>-Diamond-hlp M1 x rightstep rightstep₁
 ->>-Diamond {.(Λ n trm)} {.(Λ n trm')} {.(Λ n trm)} (Λ-step n trm trm' scoping scoping' leftstep) (reflexive .(Λ n trm)) = (Λ n trm' {scoping'}) , ((reflexive _) , Λ-step n trm trm' scoping scoping' leftstep)
 ->>-Diamond {.(Λ n trm)} {.(Λ n trm')} {.(Λ n _)} (Λ-step n trm trm' scoping scoping' leftstep) (node .(Λ n trm) .(Λ n _ ) (Λ-step {_}{trm}{trm''} x .scoping scoping'')) = Λ n (proj₁ M3') {M3'-scope} , (Λ-step n trm' (proj₁ M3') scoping' M3'-scope trm'M3') , Λ-step n trm'' (proj₁ M3') scoping'' M3'-scope trm''M3'
            where
              M3' :  Σ[ M3' ∈ Term ] (( ->> trm' M3' ) × ( ->> trm'' M3' ))
              M3' = ->>-Diamond leftstep (node trm trm'' x)
              M3'-scope :  (Scope (proj₁ M3') <= n) ≡ true
              M3'-scope = Scope->>-lemma2 (proj₁ (proj₂ M3')) scoping'
              trm'M3' : ->> trm' (proj₁ M3')
              trm'M3' = proj₁ (proj₂ M3')
              trm''M3' : ->> trm'' (proj₁ M3')
              trm''M3' = proj₂ (proj₂ M3')
 ->>-Diamond {.(Λ n trm)} {.(Λ n trm')} {.(Λ n trm'')} (Λ-step n trm trm' scoping scoping' leftstep) (Λ-step .n .trm trm'' .scoping scoping'' rightstep) = (Λ n (proj₁ M3') {M3'-scope}) , Λ-step n trm' (proj₁ M3') scoping' M3'-scope (proj₁ (proj₂ M3')) , Λ-step n trm'' (proj₁ M3') scoping'' M3'-scope (proj₂ (proj₂ M3'))
            where
              M3' :  Σ[ M3' ∈ Term ] (( ->> trm' M3' ) × ( ->> trm'' M3' ))
              M3' = ->>-Diamond leftstep rightstep
              M3'-scope : (Scope (proj₁ M3') <= n) ≡ true
              M3'-scope =  Scope->>-lemma2 (proj₁ (proj₂ M3')) scoping'
 ->>-Diamond {.(trm1 · trm2)} {.(trm1' · trm2')} {.(trm1 · trm2)} (·-step trm1 trm1' trm2 trm2' leftstep leftstep₁) (reflexive .(trm1 · trm2)) = (trm1' · trm2') , ((reflexive _) , (·-step trm1 trm1' trm2 trm2' leftstep leftstep₁))
 ->>-Diamond {.(trm1 · trm2)} {.(trm1' · trm2')} {M2} (·-step trm1 trm1' trm2 trm2' leftstep leftstep₁) (node .(trm1 · trm2) .M2 x) = (proj₁ hlp) , (proj₂ (proj₂ hlp)) , (proj₁ (proj₂ hlp))
            where
              hlp : Σ[ M3 ∈ Term ] (->> M2 M3) × (->> (trm1' · trm2') M3) 
              hlp = ->>-Diamond-hlp _ x leftstep leftstep₁
 ->>-Diamond {.(trm1 · trm2)} {.(trm1' · trm2')} {.(trm1'' · trm2'')} (·-step trm1 trm1' trm2 trm2' leftstep leftstep₁) (·-step .trm1 trm1'' .trm2 trm2'' rightstep rightstep₁) = M3a · M3b , ·-step trm1' (proj₁ M3a') trm2' (proj₁ M3b') (proj₁ (proj₂ M3a')) (proj₁ (proj₂ M3b')) , (·-step trm1'' (proj₁ M3a') trm2'' (proj₁ M3b') (proj₂ (proj₂ M3a')) (proj₂ (proj₂ M3b')))
            where
              M3a' : Σ[ M3a ∈ Term ] (( ->> trm1' M3a ) × ( ->> trm1'' M3a ))
              M3a' = ->>-Diamond leftstep rightstep
              M3a = proj₁ M3a'
              M3b' : Σ[ M3b ∈ Term ] (( ->> trm2' M3b ) × ( ->> trm2'' M3b ))
              M3b' = ->>-Diamond {trm2} leftstep₁ rightstep₁
              M3b = proj₁ M3b'

->>ToStepN : {trm trm' : Term} → (arrow : ->> trm trm') → StepN trm trm'
->>ToStepN {trm} {.trm} (reflexive .trm) = reflexive trm
->>ToStepN {trm} {trm'} (node .trm .trm' x) = step1 x
->>ToStepN {.(Λ n trm {scoping})} {.(Λ n trm' {scoping'})} (Λ-step n trm trm' scoping scoping' arrow) = Λ-stepN scoping scoping' hlp'
                      where
                        hlp : ->> (Λ n trm {scoping})  (Λ n trm' {scoping'})
                        hlp = Λ-step n trm trm' scoping scoping' arrow
                        hlp' : StepN trm trm'
                        hlp' = ->>ToStepN arrow
->>ToStepN {.(trm1 · trm2)} {.(trm1' · trm2')} (·-step trm1 trm1' trm2 trm2' arrow arrow₁) = ·-stepN hlp-left hlp-right
                      where
                        hlp-left : StepN trm1 trm1'
                        hlp-left = ->>ToStepN arrow
                        hlp-right : StepN trm2 trm2'
                        hlp-right = ->>ToStepN arrow₁

data ->>N# : ℕ → Term → Term → Set where
  embed# : (trm trm' : Term) → ->> trm trm' → ->>N# 1 trm trm'
  step# : {n : ℕ}{trm  trm' trm'' : Term} → ->>N# n trm trm' → ->> trm' trm'' → ->>N# (suc n) trm trm''

extract->> : {trm trm' : Term} → ->>N# 1 trm trm' → ->> trm trm'
extract->> {trm} {trm'} (embed# .trm .trm' x) = x

->>N#→StepN : {n : ℕ} {trm trm' : Term} → ->>N# n trm trm' → StepN trm trm'
->>N#→StepN {n} {trm} {trm'} (embed# .trm .trm' x) = ->>ToStepN x
->>N#→StepN {.(suc n)} {trm} {trm'} (step# {n} {trm} {trm''} {trm'} arrow x) = transitivity (->>N#→StepN arrow) (->>ToStepN x)  

StepN→->>N# : {trm trm' : Term} → (arrow : StepN trm trm') → Σ[ n ∈ ℕ ] (->>N# n trm trm')
StepN→->>N# {trm} {.trm} (reflexive .trm) = 1 , (embed# trm trm (reflexive _))
StepN→->>N# {trm} {trm'} (step1 step2) = 1 , (embed# trm trm' (node _ _ step2))
StepN→->>N# {trm} {trm'} (step+ {trm}{trm''}{trm'} arrow next) = suc (proj₁ hlp) , step# (proj₂ hlp) (node _ _ next)
                       where
                         hlp : Σ[ n ∈ ℕ ] (->>N# n trm trm'')
                         hlp = (StepN→->>N# arrow) 

->>N#-Diamond-hlp :  {m : ℕ}{M M1 M2 : Term} → (leftstep : ->>N# 1 M M1) → (rightstep : ->>N# m M M2) → Σ[ M3 ∈ Term ] (( ->>N# m M1 M3 ) × ( ->>N# 1 M2 M3 ))
->>N#-Diamond-hlp {.1} {M₁} {M1} {M2} (embed# .M₁ .M1 x) (embed# .M₁ .M2 y) = (proj₁ hlp) , (embed# _ _ (proj₁ (proj₂ hlp)) , embed# _ _ (proj₂ (proj₂ hlp)))
                       where
                         hlp :  Σ[ M3 ∈ Term ] (( ->> M1 M3 ) × ( ->> M2 M3 ))
                         hlp = ->>-Diamond x y 
->>N#-Diamond-hlp {.(suc _)} {M} {M1} {M2} (embed# .M .M1 x) (step# {n}{M₁}{trm'}{M2} rightstep x₁) =  M4 , fst , snd
                       where
                         hlp : Σ[ M3 ∈ Term ] (( ->>N# n M1 M3 ) × ( ->>N# 1 trm' M3 ))
                         hlp = ->>N#-Diamond-hlp (embed# _ _ x) rightstep
                         trm'M2 : ->>N# 1 trm' M2
                         trm'M2 = embed# _ _ x₁
                         M3 : Term
                         M3 = proj₁ hlp
                         ->>trm'M3 : ->> trm' M3
                         ->>trm'M3 = extract->> (proj₂ (proj₂ hlp))
                         ->>diamond :  Σ[ M4' ∈ Term ] (( ->> M3 M4' ) × ( ->> M2 M4' ))
                         ->>diamond = ->>-Diamond ->>trm'M3 x₁
                         hlp' : Σ[ M4 ∈ Term ] (( ->>N# 1 M3 M4 ) × ( ->>N# 1 M2 M4 ))  
                         hlp' = (proj₁ ->>diamond) , ((embed# _ _ (proj₁ (proj₂ ->>diamond))) , (embed# _ _ (proj₂ (proj₂ ->>diamond)))) 
                         M4 : Term
                         M4 = proj₁ hlp'
                         fst : ->>N# (suc n) M1 M4
                         fst = step# (proj₁ (proj₂ hlp)) (extract->> (proj₁ (proj₂ hlp')))
                         snd : ->>N# 1 M2 M4
                         snd = proj₂ (proj₂ hlp') 

->>N#-Diamond : {n m : ℕ}{M M1 M2 : Term} → (leftstep : ->>N# n M M1) → (rightstep : ->>N# m M M2) → Σ[ M3 ∈ Term ] (( ->>N# m M1 M3 ) × ( ->>N# n M2 M3 ))
->>N#-Diamond {.1} {m} {M₁} {M1} {M2} (embed# .M₁ .M1 x) rightstep = ->>N#-Diamond-hlp (embed# M₁ M1 x) rightstep
->>N#-Diamond {.(2+ n)} {suc m} {M₁} {M1} {M2} (step# {suc n} {M₁} {trm'} leftstep x) rightstep = hlp'
                        where
                          hlp : Σ[ M3 ∈ Term ] (( ->>N# (suc m) trm' M3 ) × ( ->>N# (suc n) M2 M3 ))
                          hlp = ->>N#-Diamond leftstep rightstep
                          M3 : Term
                          M3 = proj₁ hlp
                          ind-step : Σ[ M4 ∈ Term ] (( ->>N# (suc m) M1 M4 ) × ( ->>N# 1 M3 M4 ))
                          ind-step = ->>N#-Diamond-hlp (embed# _ _ x) (proj₁ (proj₂ hlp))
                          M4 : Term
                          M4 = proj₁ ind-step
                          M2M4 : ->>N# (suc (suc n)) M2 M4
                          M2M4 = step# (proj₂ (proj₂ hlp)) (extract->> (proj₂ (proj₂ ind-step)))
                          hlp' :  Σ[ M4 ∈ Term ] (( ->>N# (suc m) M1 M4 ) × ( ->>N# (suc (suc n)) M2 M4 ))
                          hlp' = M4 , (proj₁ (proj₂ ind-step)) , M2M4


{-
->>N#-Diamond : {n m : ℕ}{M M1 M2 : Term} → (leftstep : ->>N# n M M1) → (rightstep : ->>N# m M M2) → Σ[ M3 ∈ Term ] (( ->>N# m M1 M3 ) × ( ->>N# n M2 M3 ))
->>N#-Diamond {.1} {.1} {M₁} {M1} {M2} (embed# .M₁ .M1 x) (embed# .M₁ .M2 y) = (proj₁ hlp) , (embed# _ _ (proj₁ (proj₂ hlp)) , embed# _ _ (proj₂ (proj₂ hlp)))
                       where
                         hlp :  Σ[ M3 ∈ Term ] (( ->> M1 M3 ) × ( ->> M2 M3 ))
                         hlp = ->>-Diamond x y
->>N#-Diamond {.1} {.(suc n)} {M₁} {M1} {M2} (embed# .M₁ .M1 x) (step# {n}{M₁}{trm'}{M2} rightstep x₁) = M4 , fst , snd
                       where
                         hlp : Σ[ M3 ∈ Term ] (( ->>N# n M1 M3 ) × ( ->>N# 1 trm' M3 ))
                         hlp = ->>N#-Diamond (embed# _ _ x) rightstep
                         trm'M2 : ->>N# 1 trm' M2
                         trm'M2 = embed# _ _ x₁
                         M3 : Term
                         M3 = proj₁ hlp
                         ->>trm'M3 : ->> trm' M3
                         ->>trm'M3 = extract->> (proj₂ (proj₂ hlp))
                         ->>diamond :  Σ[ M4' ∈ Term ] (( ->> M3 M4' ) × ( ->> M2 M4' ))
                         ->>diamond = ->>-Diamond ->>trm'M3 x₁
                         hlp' : Σ[ M4 ∈ Term ] (( ->>N# 1 M3 M4 ) × ( ->>N# 1 M2 M4 ))  
                         hlp' = (proj₁ ->>diamond) , ((embed# _ _ (proj₁ (proj₂ ->>diamond))) , (embed# _ _ (proj₂ (proj₂ ->>diamond)))) 
                         M4 : Term
                         M4 = proj₁ hlp'
                         fst : ->>N# (suc n) M1 M4
                         fst = step# (proj₁ (proj₂ hlp)) (extract->> (proj₁ (proj₂ hlp')))
                         snd : ->>N# 1 M2 M4
                         snd = proj₂ (proj₂ hlp') --proj₂ (proj₂ hlp')
->>N#-Diamond {.(suc n)} {m} {M} {M1} {M2} (step# {n} {M} {trm'} leftstep x) (rightstep) = {!!}
                       where
                         hlp :  Σ[ M3 ∈ Term ] (( ->>N# m trm' M3 ) × ( ->>N# n M2 M3 ))
                         hlp = ->>N#-Diamond leftstep rightstep
                         trm'M1 : ->>N# 1 trm' M1
                         trm'M1 = embed# _ _ x
                         M3 : Term
                         M3 = proj₁ hlp
                         ->>trm'M1 : ->> trm' M1
                         ->>trm'M1 = extract->> trm'M1
                         ->>diamond :  Σ[ M4' ∈ Term ] (( ->> M3 M4' ) × ( ->> {!!} M4' ))
                         ->>diamond = {!!} -}

{-hlp : Σ[ M3 ∈ Term ] (( ->>N# 1 trm' M3 ) × ( ->>N# n M2 M3 ))
                         hlp = ->>N#-Diamond leftstep (embed# _ _ x₁) 
                         trm'M1 : ->>N# 1 trm' M1
                         trm'M1 = embed# _ _ x
                         M3 : Term
                         M3 = proj₁ hlp
                         ->>trm'M3 : ->> trm' M3
                         ->>trm'M3 = extract->> (proj₁ (proj₂ hlp))
                         ->>diamond :  Σ[ M4' ∈ Term ] (( ->> M1 M4' ) × ( ->> M3 M4' ))
                         ->>diamond = ->>-Diamond x ->>trm'M3
                         hlp' : Σ[ M4 ∈ Term ] (( ->>N# 1 M1 M4 ) × ( ->>N# 1 M3 M4 ))  
                         hlp' = (proj₁ ->>diamond) , {!!} -- (proj₁ ->>diamond) , {!!} 
                         M4 : Term
                         M4 = proj₁ hlp'
                         fst : ->>N# 1 M1 M4
                         fst = proj₁ (proj₂ hlp')
                         snd :  ->>N# (suc n) M2 M4
                         snd = step# {!!}  {!!} -}

--->>N#-Diamond {.(suc n)} {.(suc _)} {M} {M1} {M2} (step# {n} {M} {trm'} leftstep x) (step# rightstep x₁) = {!!}
                   --    where
                   --       hlp :  Σ[ M3 ∈ Term ] (( ->>N# n M1 M3 ) × ( ->>N# 1 trm' M3 ))
                   --      hlp = ->>N#-Diamond (embed# _ _ x) rightstep
                   --      trm'M2 : ->>N# 1 trm' M2
                   --      trm'M2 = embed# _ _ x₁
                       {-  M3 : Term
                         M3 = proj₁ hlp
                         ->>trm'M3 : ->> trm' M3
                         ->>trm'M3 = extract->> (proj₂ (proj₂ hlp))
                         ->>diamond :  Σ[ M4' ∈ Term ] (( ->> M3 M4' ) × ( ->> M2 M4' ))
                         ->>diamond = ->>-Diamond ->>trm'M3 x₁
                         hlp' : Σ[ M4 ∈ Term ] (( ->>N# 1 M3 M4 ) × ( ->>N# 1 M2 M4 ))  
                         hlp' = (proj₁ ->>diamond) , ((embed# _ _ (proj₁ (proj₂ ->>diamond))) , (embed# _ _ (proj₂ (proj₂ ->>diamond)))) 
                         M4 : Term
                         M4 = proj₁ hlp'
                         fst : ->>N# (suc n) M1 M4
                         fst = step# (proj₁ (proj₂ hlp)) (extract->> (proj₁ (proj₂ hlp')))
                         snd : ->>N# 1 M2 M4
                         snd = proj₂ (proj₂ hlp') --proj₂ (proj₂ hlp') -}



StepN-Diamond : {M M1 M2 : Term} → (leftstep : StepN M M1) → (rightstep : StepN M M2) → Σ[ M3 ∈ Term ] (( StepN M1 M3 ) × ( StepN M2 M3 ))
StepN-Diamond {M}{M1}{M2} leftstep rightstep = (proj₁ diamond) , ((->>N#→StepN (proj₁ (proj₂ diamond))) , (->>N#→StepN (proj₂ (proj₂ diamond))))
                        where
                          left# : Σ[ n ∈ ℕ ] (->>N# n M M1)
                          left# = StepN→->>N# leftstep
                          right# : Σ[ m ∈ ℕ ] (->>N# m M M2)
                          right# = StepN→->>N# rightstep
                          diamond : Σ[ M3 ∈ Term ] (( ->>N# (proj₁ right#) M1 M3 ) × ( ->>N# (proj₁ left#) M2 M3 ))
                          diamond = ->>N#-Diamond (proj₂ left#) (proj₂ right#)
                         

{-
StepN→->>N# : {n : ℕ} {trm trm' : Term} → (arrow : StepN trm trm') → ->>N# n trm trm'
StepN→->>N# {trm} {.trm} (reflexive .trm) = embed# trm trm (reflexive _)
StepN→->>N# {trm} {trm'} (step1 step2) = embed# trm trm' (node _ _ step2)
StepN→->>N# {trm} {trm'} (step+ {trm}{trm''}{trm'} arrow next) = step# (StepN→->>N# arrow) (node _ _ next) 
-}
{-
->>N!-Diamond : {M M1 M2 : Term} → (leftstep : ->>N# M M1) → (rightstep : ->>N# M M2) → Σ[ M3 ∈ Term ] (( ->>N# M1 M3 ) × ( ->>N# M2 M3 ))
->>N!-Diamond 

-}

{-

data ->>N! : Term → Term → Set where
  embed! : (trm trm' : Term) → ->> trm trm' → ->>N! trm trm'
  step! : {trm  trm' trm'' : Term} → ->>N! trm trm' → Step trm' trm'' → ->>N! trm trm''

->>N!→StepN :  {trm trm' : Term} → ->>N! trm trm' → StepN trm trm'
->>N!→StepN {trm} {trm'} (embed! .trm .trm' x) = ->>ToStepN x
->>N!→StepN {trm} {trm'} (step! {trm}{trm''}{trm'} arrow x) = (step+ (->>N!→StepN arrow) x)  

StepN→->>N! : {trm trm' : Term} → (arrow : StepN trm trm') → ->>N! trm trm'
StepN→->>N! {trm} {.trm} (reflexive .trm) = embed! trm trm (reflexive _)
StepN→->>N! {trm} {trm'} (step1 step2) = embed! trm trm' (node _ _ step2)
StepN→->>N! {trm} {trm'} (step+ {trm}{trm''}{trm'} arrow next) = step! (StepN→->>N! arrow) next 
                  where
                   hlp : ->>N! trm trm''
                   hlp = StepN→->>N! arrow

->>N!-Diamond : {M M1 M2 : Term} → (leftstep : ->>N! M M1) → (rightstep : ->>N! M M2) → Σ[ M3 ∈ Term ] (( ->>N! M1 M3 ) × ( ->>N! M2 M3 ))
->>N!-Diamond {M₁} {M1} {M2} (embed! .M₁ .M1 x) (embed! .M₁ .M2 x₁) = (proj₁ hlp) , ((embed! _ _ (proj₁ (proj₂ hlp))) , (embed! _ _ (proj₂ (proj₂ hlp))))
                  where
                    hlp :  Σ[ M3 ∈ Term ] (( ->> M1 M3 ) × ( ->> M2 M3 ))
                    hlp = ->>-Diamond x x₁
->>N!-Diamond {M₁} {M1} {M2} (embed! .M₁ .M1 x) (step! {M₁}{trm'} rightstep x₁) = {!!}
                   where
                    hlp :  Σ[ M3 ∈ Term ] (( ->> M1 M3 ) × ( ->> M2 M3 ))
                    hlp = {!!}
->>N!-Diamond {M} {M1} {M2} (step! {M}{trm'} {M1} leftstep x) rightstep = {!!}
                  where
                    hlp :  Σ[ M3 ∈ Term ] (( ->>N! trm' M3 ) × ( ->>N! M2 M3 ))
                    hlp = ->>N!-Diamond leftstep rightstep
                    M3 : Term
                    M3 = proj₁ hlp
                
data ->>N' : Term → Term → Set where
  embed' : (trm trm' : Term) → ->> trm trm' → ->>N' trm trm'
  step' : {trm  trm' trm'' : Term} → Step trm trm' → ->>N' trm' trm'' → ->>N' trm trm''

--innerΛ-step : {n : ℕ} {trm trm' trm'' : Term} {scoping : (Scope trm <= n) ≡ true}{scoping' : (Scope trm' <= n) ≡ true} → ->> trm trm' → Step (Λ n trm' {scoping'}) trm'' → ->> (Λ n trm {scoping}) trm''
--innerΛ-step {n} {trm} {trm'} {.(Λ n _)} {scoping} {scoping'} arrow (Λ-step {n}{trm'}{trm''} steps .scoping' scoping'') = {!!}

+step' :  {trm  trm' trm'' : Term} → ->>N' trm trm' → Step trm' trm'' → ->>N' trm trm''
+step' {trm} {.trm} {trm''} (embed' .trm .trm (reflexive .trm)) steps = embed' _ _ (node _ _ steps)
+step' {trm} {trm'} {trm''} (embed' .trm .trm' (node .trm .trm' x)) steps = step' x (embed' _ _ (node _ _ steps))
+step' {.(Λ n trm)} {.(Λ n trm')} {trm''} (embed' .(Λ n trm) .(Λ n trm') (Λ-step n trm trm' scoping scoping' x)) steps =  {!!}
+step' {.(trm1 · trm2)} {.(trm1' · trm2')} {trm''} (embed' .(trm1 · trm2) .(trm1' · trm2') (·-step trm1 trm1' trm2 trm2' x x₁)) steps = {!!}
+step' {trm} {trm'} {trm''} (step' {trm}{trm'''}  x arrow) steps = {!!}

->>N'→StepN :  {trm trm' : Term} → ->>N' trm trm' → StepN trm trm'
->>N'→StepN {trm} {trm'} (embed' .trm .trm' x) = ->>ToStepN x
->>N'→StepN {trm} {trm'} (step' {trm}{trm''}{trm'} x arrow) = +step x (->>N'→StepN arrow)

StepN→->>N' : {trm trm' : Term} → (arrow : StepN trm trm') → ->>N' trm trm'
StepN→->>N' {trm} {.trm} (reflexive .trm) = embed' trm trm (reflexive _)
StepN→->>N' {trm} {trm'} (step1 step2) = embed' trm trm' (node _ _ step2)
StepN→->>N' {trm} {trm'} (step+ {trm}{trm''}{trm'} arrow next) = +step' (StepN→->>N' arrow)  next
                  where
                   hlp : ->>N' trm trm''
                   hlp = StepN→->>N' arrow

->>N'-Diamond : {M M1 M2 : Term} → (leftstep : ->>N' M M1) → (rightstep : ->>N' M M2) → Σ[ M3 ∈ Term ] (( ->>N' M1 M3 ) × ( ->>N' M2 M3 ))
->>N'-Diamond {M} {M1} {M2} (embed' .M .M1 x) rightstep = {!!}
->>N'-Diamond {M} {M1} {M2} (step' x leftstep) rightstep = {!!}

-}
{-
data ->>N : Term → Term → Set where
  embed : (trm trm' : Term) → ->> trm trm' → ->>N trm trm'
  transitive : {trm  trm' trm'' : Term} → ->>N trm trm' → ->>N trm' trm'' → ->>N trm trm''

->>N→StepN :  {trm trm' : Term} → ->>N trm trm' → StepN trm trm'
->>N→StepN {trm} {trm'} (embed .trm .trm' x) = ->>ToStepN x
->>N→StepN {trm} {trm''} (transitive {trm} {trm'} {trm''} (embed .trm .trm' x) arrow2) = transitivity (->>ToStepN x) hlp
                      where
                        hlp : StepN trm' trm''
                        hlp = ->>N→StepN arrow2
->>N→StepN {trm} {trm''} (transitive {trm} {trm'} {trm''} (transitive {trm}{trm'''}{trm'} arrow1 arrow3) arrow2) = transitivity {trm}{trm'}{trm''} (transitivity (->>N→StepN arrow1) (->>N→StepN arrow3)) (->>N→StepN arrow2)

StepN→->>N : {trm trm' : Term} → (arrow : StepN trm trm') → ->>N trm trm'
StepN→->>N {trm} {.trm} (reflexive .trm) = embed trm trm (reflexive trm)
StepN→->>N {trm} {trm'} (step1 step2) = embed trm trm' (node _ _ step2)
StepN→->>N {trm} {trm'} (step+ {trm}{trm''}{trm'} arrow next) = transitive (StepN→->>N arrow) (StepN→->>N (step1 next))
-}


{-


->>NWith->>-diamond' : {M M1 M2 : Term} → (leftstep : ->> M M1) → (rightstep : ->>N M M2) → Σ[ M3 ∈ Term ] (( ->>N M1 M3 ) × ( ->>N M2 M3 ))
->>NWith->>-diamond' {M} {.M} {M2} (reflexive .M) rightstep = {!!}
->>NWith->>-diamond' {M} {M1} {M2} (node .M .M1 x) rightstep = {!!}
->>NWith->>-diamond' {.(Λ n trm)} {.(Λ n trm')} {M2} (Λ-step n trm trm' scoping scoping' leftstep) rightstep = {!!}
->>NWith->>-diamond' {.(trm1 · trm2)} {.(trm1' · trm2')} {M2} (·-step trm1 trm1' trm2 trm2' leftstep leftstep₁) rightstep = {!!}




mutual

 ->>NWith->>-diamond : {M M1 M2 : Term} → (leftstep : ->> M M1) → (rightstep : ->>N M M2) → Σ[ M3 ∈ Term ] (( ->>N M1 M3 ) × ( ->>N M2 M3 ))
 ->>NWith->>-diamond {M} {M1} {M2} leftstep (embed .M .M2 x) = M3 , (embed M1 M3 fst) , (embed M2 M3 snd)
                      where
                        hlp : Σ[ M3 ∈ Term ] (( ->> M1 M3 ) × ( ->> M2 M3 ))
                        hlp = ->>-Diamond leftstep x
                        M3 : Term
                        M3 = proj₁ hlp
                        fst : ->> M1 M3
                        fst = proj₁ (proj₂ hlp)
                        snd : ->> M2 M3
                        snd = proj₂ (proj₂ hlp)
 ->>NWith->>-diamond {M} {M1} {M2} leftstep (transitive {M}{trm'}{M2} rightstep1 rightstep2) = ->>N-Diamond {!!} {!!}
                       where
                        hlp : Σ[ M3 ∈ Term ] (( ->>N M1 M3 ) × ( ->>N trm' M3 ))
                        hlp = ->>NWith->>-diamond leftstep rightstep1
                        

                     {- where
                       
                        M3 : Term
                        M3 = proj₁ hlp
                        hlp' : Σ[ M3' ∈ Term ] (( ->>N M2 M3' ) × ( ->>N M3 M3' ))
                        hlp' = ->>N-Diamond rightstep2 (proj₂ (proj₂ hlp)) -}
                        

 ->>N-Diamond : {M M1 M2 : Term} → (leftstep : ->>N M M1) → (rightstep : ->>N M M2) → Σ[ M3 ∈ Term ] (( ->>N M1 M3 ) × ( ->>N M2 M3 ))
 ->>N-Diamond {M₁} {M1} {M2} (embed .M₁ .M1 x) (embed .M₁ .M2 y) = (proj₁ hlp) , ((embed M1 (proj₁ hlp) (proj₁ (proj₂ hlp))) , (embed M2 (proj₁ hlp) (proj₂ (proj₂ hlp))))
                                where
                                  hlp : Σ[ M3 ∈ Term ] (( ->> M1 M3 ) × ( ->> M2 M3 ))
                                  hlp = ->>-Diamond x y
 ->>N-Diamond {M₁} {M1} {M2} (embed .M₁ .M1 x) (transitive {M₁} {trm'}{M2} rightstep1 rightstep2) = {!!} , {!!} --->>NWith->>-diamond x {!!}
                                where
                                  hlp : Σ[ M3 ∈ Term ] (( ->>N M1 M3 ) × ( ->>N trm' M3 ))
                                  hlp = ->>NWith->>-diamond x rightstep1
                                  hlp' :  Σ[ M3 ∈ Term ] (( ->>N M1 M3 ) × ( ->>N trm' M3 ))
                                  hlp' = ->>N-Diamond (embed _ _ x) rightstep1
                                  M3 : Term
                                  M3 = proj₁ hlp'
                                  part2 : Σ[ M4 ∈ Term ] (( ->>N M2 M4 ) × ( ->>N M3 M4 ))
                                  part2 = ->>N-Diamond rightstep2 (proj₂ (proj₂ hlp'))
                                  M4 : Term
                                  M4 = proj₁ part2
 ->>N-Diamond {M} {M1} {M2} (transitive {M}{trm'}{M1} leftstep1 leftstep2) (embed .M .M2 x) = {!!}
 ->>N-Diamond {M} {M1} {M2} (transitive leftstep1 leftstep2) (transitive {M}{trm''}{M2} rightstep1 rightstep2) = {!!}
                     

------------------------------------
--Church Rosser property proper
------------------------------------

StepN-Diamond : {M M1 M2 : Term} → (leftstep : StepN M M1) → (rightstep : StepN M M2) → Σ[ M3 ∈ Term ] (( StepN M1 M3 ) × ( StepN M2 M3 ))
StepN-Diamond {M₁} {.M₁} {.M₁} (reflexive .M₁) (reflexive .M₁) = M₁ , ((reflexive _) , (reflexive _)) 
StepN-Diamond {M₁} {.M₁} {M2} (reflexive .M₁) (step1 {M₁}{M2} step2) = M2 , ((step1 step2) , (reflexive _))
StepN-Diamond {M₁} {.M₁} {M2} (reflexive .M₁) (step+ {M₁}{trm'}{M2} rightstep next) = M2 , ((step+ rightstep next) , (reflexive _))
StepN-Diamond {M} {M1} {.M} (step1 {M} {M1} step2) (reflexive .M) = M1 , ((reflexive _) , (step1 step2))
StepN-Diamond {M} {M1} {M2} (step1 {M} {M1} step2) (step1 {M}{M2} step3) = proj₁ M3 , ->>ToStepN (proj₁ (proj₂ M3)) , ->>ToStepN (proj₂ (proj₂ M3))
                       where
                         ->>StepM→M2 : ->> M M2
                         ->>StepM→M2 = node _ _ step3
                         ->>StepM→M1 : ->> M M1
                         ->>StepM→M1 = node _ _ step2
                         M3 : Σ[ M3 ∈ Term ] (( ->> M1 M3 ) × ( ->> M2 M3 ))
                         M3 = ->>-Diamond ->>StepM→M1 ->>StepM→M2 
StepN-Diamond {M} {M1} {M2} (step1 {M} {M1} step2) (step+ {M}{trm'}{M2} rightstep next) = {!!}
                       where
                         ind-step :  Σ[ M4 ∈ Term ] (( StepN M1 M4 ) × ( StepN trm' M4 ))
                         ind-step =  StepN-Diamond (step1 step2) rightstep
                         M5' :  Σ[ M5 ∈ Term ] (( StepN M2 M5 ) × ( StepN trm' M5 ))
                         M5' = StepN-Diamond (step+ rightstep next) rightstep
StepN-Diamond {M} {M1} {M2} (step+ {M}{trm'}{M1} leftstep next) rightstep = {!!}

-}
------------------------------------
------------------------------------


{- -- Proof of diamond property for ->>T --

->>T-Diamond : {M M1 M2 : termTree} → (leftstep : ->>T M M1) → (rightstep : ->>T M M2) → Σ[ M3 ∈ termTree ] (( ->>T M1 M3 ) × ( ->>T M2 M3 ))
->>T-Diamond {.(node _)} {.(node _)} {.(node _)} (node->> {trm}{trm''} x) (node->> {trm}{trm'}  y) = {!!}
                                 where
                                   hlp : {!!}
                                   hlp = {!!}
->>T-Diamond {.(Λ* _ _ _)} {M1} {.(Λ* _ _ (->>T-scope-inv _ rightstep))} leftstep (Λ*->> rightstep) = {!!}
->>T-Diamond {.(·* _ _)} {M1} {.(·* _ _)} leftstep (·*->> rightstep rightstep₁) = {!!}
-}

{- {node trm} {.(node trm')} {.(node trm'')} () (node->> {trm} {trm''} {.(node trm)} refl x) = {!!}
->>T-Diamond {Λ* n M₁ scoping} {.(Λ* n trmT'' (->>T-scope-inv {n}{M₁} {trmT''} scoping leftstep))} {.(Λ* n trmT' (->>T-scope-inv {n}{M₁}{trmT'} scoping rightstep))}
             (Λ*->> {n} {M₁} {trmT''} {scoping} refl leftstep) (Λ*->> {.n} {.M₁} {trmT'} {.scoping} refl rightstep) = M3 , (hlp' , hlp)
                              where
                                subproblem :  Σ[ M3' ∈ termTree ] (( ->>T trmT'' M3' ) × ( ->>T trmT' M3' ))
                                subproblem = ->>T-Diamond leftstep rightstep
                                subproblem' :  Σ[ M3' ∈ termTree ] (( ->>T trmT' M3' ) × ( ->>T trmT'' M3' ))
                                subproblem' = ->>T-Diamond rightstep leftstep
                                M3-hlp : (ScopeT (proj₁ subproblem) <= n) ≡ true
                                M3-hlp =  (->>T-scope-inv (->>T-scope-inv scoping leftstep) (proj₁ (proj₂ subproblem)))
                                M3 : termTree
                                M3 = Λ* n (proj₁ subproblem) _
                                hlp : ->>T (Λ* n trmT' (->>T-scope-inv scoping rightstep)) M3
                                hlp = Λ*->> {n}{trmT'} {proj₁ subproblem} refl (proj₂ (proj₂ subproblem))
                                hlp'2 : ->>T trmT'' (proj₁ subproblem)
                                hlp'2 = proj₁ (proj₂ subproblem)
                                hlp'3 : ->>T (Λ* n trmT'' (->>T-scope-inv {n} {M₁}{trmT''} scoping leftstep))
                                             (Λ* n (proj₁ subproblem) (->>T-scope-inv (->>T-scope-inv scoping leftstep) (proj₁ (proj₂ subproblem)))) 
                                hlp'3 = Λ*->> {n}{trmT''}{proj₁ subproblem}{ ->>T-scope-inv {n}{M₁}{trmT''} scoping leftstep}
                                                                           {(Λ* n trmT'' (->>T-scope-inv {n} {M₁}{trmT''} scoping leftstep))} refl (proj₁ (proj₂ subproblem))
                                hlp' : ->>T (Λ* n trmT'' (->>T-scope-inv {n} {M₁}{trmT''} scoping leftstep))
                                            (Λ* n (proj₁ subproblem) (->>T-scope-inv (->>T-scope-inv scoping rightstep) (proj₂ (proj₂ subproblem))))
                                hlp' = ->>T-right≡-lemma {(Λ* n trmT'' (->>T-scope-inv {n} {M₁}{trmT''} scoping leftstep))}
                                                         {Λ* n (proj₁ subproblem) ( ->>T-scope-inv ( ->>T-scope-inv scoping leftstep)  (proj₁ (proj₂ subproblem)))}
                                                         {Λ* n (proj₁ subproblem) (->>T-scope-inv (->>T-scope-inv scoping rightstep) (proj₂ (proj₂ subproblem)))}
                                                          hlp'3 (trm1≡trm→Λ*ntrm1≡Λ*mtrm2 refl refl)  
-}

-- SHOW THAT 2 SCOPINGS ARE THE SAME IF THEY OUGHT TO BE __

--  {n : ℕ} → {trmT trmT' : termTree} → {scoping : ((ScopeT trmT) <= n) ≡ true} → {Λ*term : termTree} →  (eqn : Λ*term ≡ Λ* n trmT scoping) → (reduce : ->>T trmT trmT') → ->>T Λ*term (Λ* n trmT' (->>T-scope-inv scoping reduce))

--->>T-Diamond {.(·* lftT rgtT)} {M1} {.(·* lftT' rgtT')} leftstep (·*->> {lftT} {rgtT} {lftT'} {rgtT'} {.(·* lftT rgtT)} refl rightstep1 rightstep2) = {!!}






{-
->>TN-Diamond-hlp : {M M1 M2 : termTree} → (leftstep : ->>TN M M1) → (step : ->>T M M2)  → Σ[ M3 ∈ termTree ] (( ->>TN M1 M3 ) × ( ->>TN M2 M3 ))
->>TN-Diamond-hlp {M} {.M} {M2} (reflexiveT .M) step2 = M2 , (stepT1 step2) , (reflexiveT M2)
->>TN-Diamond-hlp {M} {M1} {M2} (stepT1 step3) step2 = proj₁ hlp , (stepT1 (proj₁ (proj₂ hlp))) , (stepT1 (proj₂ (proj₂ hlp)))
                                    where
                                      hlp : Σ[ M3 ∈ termTree ] (( ->>T M1 M3 ) × ( ->>T M2 M3 ))
                                      hlp = ->>T-Diamond step3 step2
->>TN-Diamond-hlp {.(node trm)} {M1} {.(node trm'')} (stepT+ {.(node trm)} {trmT} {M1} chain next) (node->> {trm} {trm''} {.(node trm)} refl x) = {!!}
                                    where
                                      hlp : Σ[ M3 ∈ termTree ] (( ->>TN trmT M3 ) × ( ->>TN (node trm'') M3 ))
                                      hlp = ->>TN-Diamond-hlp chain (node-lemma x)
                                      M3 : termTree
                                      M3 = proj₁ hlp
                                                                         
->>TN-Diamond-hlp {M} {M1} {.(Λ* _ _ (->>T-scope-inv _ step2))} (stepT+ {M} {trm'} {M1} chain next) (Λ*->> eqn step2) = {!!}
->>TN-Diamond-hlp {M} {M1} {.(·* _ _)} (stepT+ {M} {trm'} {M1} chain next) (·*->> eqn step2 step3) = {!!}

-}

{-


{-
->>TN-Diamond-hlp : {M M1 M2 : termTree} → (leftstep : ->>TN M M1) → (step : ->>T M M2)  → Σ[ M3 ∈ termTree ] (( ->>TN M1 M3 ) × ( ->>TN M2 M3 ))
->>TN-Diamond-hlp {M} {.M} {M2} (reflexiveT .M) step2 = M2 , (stepT1 step2) , (reflexiveT M2)
->>TN-Diamond-hlp {M} {M1} {M2} (stepT1 step3) step2 = proj₁ hlp , (stepT1 (proj₁ (proj₂ hlp))) , (stepT1 (proj₂ (proj₂ hlp)))
                                    where
                                      hlp : Σ[ M3 ∈ termTree ] (( ->>T M1 M3 ) × ( ->>T M2 M3 ))
                                      hlp = ->>T-Diamond step3 step2
->>TN-Diamond-hlp {M} {M1} {M2} (stepT+ {M} {trm'} {M1} chain next) step2 = {!!} -}


->>TN-Diamond : {M M1 M2 : termTree} → (leftstep : ->>TN M M1) → (rightstep : ->>TN M M2) → Σ[ M3 ∈ termTree ] (( ->>TN M1 M3 ) × ( ->>TN M2 M3 ))
->>TN-Diamond {M} {M1} {.M} leftstep (reflexiveT .M) = M1 , ((reflexiveT M1) , leftstep)
->>TN-Diamond {M} {M1} {M2} leftstep (stepT+ {M} {trm'} {M2} rightstep next) = (proj₁ hlp') , transitivityT (proj₁ (proj₂ hlp)) (proj₁ (proj₂ hlp')) , (proj₂ (proj₂ hlp'))
                                       where
                                         hlp : Σ[ M3 ∈ termTree ] (( ->>TN M1 M3) × ( ->>TN trm' M3))
                                         hlp = ->>TN-Diamond leftstep rightstep
                                         M3 : termTree
                                         M3 = proj₁ hlp
                                         next' : ->>TN trm' M2
                                         next' = stepT1 next
                                         hlp' : Σ[ M4 ∈ termTree ] (( ->>TN M3 M4) × ( ->>TN M2 M4))
                                         hlp' = ->>TN-Diamond (proj₂ (proj₂ hlp)) (stepT1 next)
->>TN-Diamond {M} {M1} {M2} leftstep (stepT1 step2) = ->>TN-Diamond-hlp leftstep step2                                   

StepN-Diamond : {M M1 M2 : Term} → (leftstep : StepN M M1) → (rightstep : StepN M M2) → Σ[ M3 ∈ Term ] (( StepN M1 M3 ) × ( StepN M2 M3 ))
StepN-Diamond {M}{M1}{M2} leftstep rightstep = {!!}


{-
 data termTree where
   node : (trm : Term) → termTree
   Λ* : (n : ℕ) → (trmT : termTree) → (scoping : ((ScopeT trmT) <= n) ≡ true) → termTree
   ·* : (lftT : termTree) → (rgtT : termTree) → termTree -}

{- cached ->>1-Diamond : {M M1 M2 : termTree} → (leftstep : ->>T M M1) → (rightstep : ->>T M M2) → Σ[ M3 ∈ termTree ] (( ->>T M1 M3 ) × ( ->>T M2 M3 ))
->>1-Diamond {node trm} {.(node trm'')} {.(node trm')} (node->> {.trm} {trm''} refl y) (node->> {trm} {trm'} {.(node trm)} refl x) = {!!}
->>1-Diamond {Λ* n M₁ scoping} {M1} {.(Λ* n trmT' (->>T-scope-inv scoping rightstep))} leftstep (Λ*->> {.n} {.M₁} {trmT'} {.scoping} refl rightstep) = {!!}
->>1-Diamond {.(·* lftT rgtT)} {M1} {.(·* lftT' rgtT')} leftstep (·*->> {lftT} {rgtT} {lftT'} {rgtT'} {.(·* lftT rgtT)} refl rightstep1 rightstep2) = {!!} -}

  






{- scoping'-hlp : {n : ℕ} → {trm : Term} → (superarity : SuperArity trm ≡ just (+ n)) → (isc : isCombinator trm ≡ true) → (Scope (AppFold {n} trm superarity isc) <= Scope trm) ≡ true
scoping'-hlp {.(suc m)} {Λ m trm {scoping}} refl refl = {!!} --SubΛ-base-lemma {Λ m trm {scoping}} refl
scoping'-hlp {n} {trm1 · trm2} superarity isc = {!!} {-trans<= {Scope (Substitute n ( (AppFold trm1 (trans (sym (ssuc'Pred'-id {trm1}{trm2})) (cong ssuc' superarity)) (∧-elim-left isc))) trm2)}
                                                        {(Scope ( (AppFold trm1 (trans (sym (ssuc'Pred'-id {trm1}{trm2})) (cong ssuc' superarity)) (∧-elim-left isc)))  ⊔ Scope trm2)}
                                                        {(Scope trm1 ⊔ Scope trm2)} step2 step5 -}
                 where
                   hlp : (Scope trm2) <= ((Scope trm1) ⊔ (Scope trm2)) ≡ true
                   hlp = x<=y→x<=n⊔y {Scope trm2}{Scope trm2}{Scope trm1} (x≡y→x<=y≡true {Scope trm2}{Scope trm2} refl)
                   step1 : (Scope (Substitute n trm1 trm2) <= (Scope trm1 ⊔ Scope trm2)) ≡ true
                   step1 = ScopeSubstitute {n} {trm1} {trm2} 
                   step2 : (Scope (Substitute n ( (AppFold trm1 (trans (sym (ssuc'Pred'-id {trm1}{trm2})) (cong ssuc' superarity)) (∧-elim-left isc))) trm2) <= (Scope ( (AppFold trm1 (trans (sym (ssuc'Pred'-id {trm1}{trm2})) (cong ssuc' superarity)) (∧-elim-left isc))) ⊔ Scope trm2)) ≡ true
                   step2 = ScopeSubstitute  {n} {(AppFold trm1 (trans (sym (ssuc'Pred'-id {trm1}{trm2})) (cong ssuc' superarity)) (∧-elim-left isc))} {trm2}
                   step3 : (Scope ( (AppFold trm1 (trans (sym (ssuc'Pred'-id {trm1}{trm2})) (cong ssuc' superarity)) (∧-elim-left isc)))) ≡ 0
                   step3 = ScopeAppFold0 {suc n} {trm1} (_) (∧-elim-left isc)
                   step4 : (Scope ( (AppFold trm1 (trans (sym (ssuc'Pred'-id {trm1}{trm2})) (cong ssuc' superarity)) (∧-elim-left isc))) ⊔ Scope trm2) ≡ 0 ⊔ Scope trm2 
                   step4 = cong (λ w → w  ⊔ Scope trm2) step3
                   step5 : (Scope ( (AppFold trm1 (trans (sym (ssuc'Pred'-id {trm1}{trm2})) (cong ssuc' superarity)) (∧-elim-left isc))) ⊔ Scope trm2) <= (Scope trm1 ⊔ Scope trm2) ≡ true
                   step5 = trans<= {(Scope ( (AppFold trm1 (trans (sym (ssuc'Pred'-id {trm1}{trm2})) (cong ssuc' superarity)) (∧-elim-left isc))) ⊔ Scope trm2)}
                                   {0 ⊔ Scope trm2}{Scope trm1  ⊔ Scope trm2}
                                   (x≡y→x<=y≡true {(Scope (AppFold trm1 (trans (sym (ssuc'Pred'-id {trm1}{trm2})) (cong ssuc' superarity)) (∧-elim-left isc))) ⊔ Scope trm2}
                                   {0 ⊔ Scope trm2} step4) hlp -}
                                   



--ParallelSteps : Terms →   


--lemma-xyz : Reconstruct {xs} trms 


--isCombinatorExprSubstitute-lemma {{!!}} {trm2} {!!} (∧-elim-right isc) --SubstituteΛ-lemma {ft isc))} {!!} trm2 (∧-elim-right isc)

--isCombinatorExprSubstituteScope-lemma {!!} (∧-elim-right isc)
{-

  -}                 
-- A lemma about the scopes of Λ-step :
{- Scoping' : {n : ℕ} → {trm : Term} → {trm' : Term} → (legit : Step trm trm') → (scoping : (Scope trm <= n) ≡ true) → (Scope trm' <= n) ≡ true
Scoping' {n} {.(_ · _)} {.(_ · _)} (left-step {trm1}{trm2}{trm1'} legit) scoping = ⊔Scoping {n}{trm1'}{trm2} (Scoping' legit (·Scoping-elim-left {n} {trm1}{trm2} scoping))  (·Scoping-elim-right {n} {trm1}{trm2} scoping)                      
Scoping' {n} {.(_ · _)} {.(_ · _)} (right-step {trm1}{trm2}{trm2'} legit) scoping =  ⊔Scoping {n}{trm1}{trm2'} (·Scoping-elim-left {n} {trm1}{trm2} scoping) (Scoping' legit (·Scoping-elim-right {n} {trm1}{trm2} scoping))
Scoping' {n} {.(Λ _ _)} {.(Λ _ _)} (Λ-step legit scoping1 scoping1') scoping = refl
Scoping' {n} {trm1 · trm2} {.(AppFold (trm1 · trm2) superarity isc)} (appFold superarity isc) scoping =  {!!} {-trans<=
                                 {(Scope (Substitute zero (AppFold trm1 (trans (sym (ssuc'Pred'-id {trm1}{trm2})) (cong ssuc' superarity)) (∧-elim-left isc)) trm2))}
                                 {(Scope ((AppFold trm1 (trans (sym (ssuc'Pred'-id {trm1}{trm2})) (cong ssuc' superarity)) (∧-elim-left isc))) ⊔ Scope trm2)}
                                 {n} hlp3 (trans<=
                                 {Scope ((AppFold trm1 (trans (sym (ssuc'Pred'-id {trm1}{trm2})) (cong ssuc' superarity)) (∧-elim-left isc))) ⊔ Scope trm2}
                                 {Scope trm1 ⊔ Scope trm2}
                                 {n} hlp4 scoping)  -}
          where
            hlp : (Scope trm1 <= n) ≡ true
            hlp = ·Scoping-elim-left {n}{trm1}{trm2} scoping
            hlp2 : (Scope (AppFold trm1 (trans (sym (ssuc'Pred'-id {trm1}{trm2})) (cong ssuc' superarity)) (∧-elim-left isc)) <= (Scope trm1)) ≡ true
            hlp2 = scoping'-hlp {_} {trm1} (trans (sym (ssuc'Pred'-id {trm1}{trm2})) (cong ssuc' superarity)) (∧-elim-left isc)
            hlp3 :  (Scope (Substitute zero (AppFold trm1 (trans (sym (ssuc'Pred'-id {trm1}{trm2})) (cong ssuc' superarity)) (∧-elim-left isc)) trm2)
                     <= (Scope ((AppFold trm1 (trans (sym (ssuc'Pred'-id {trm1}{trm2})) (cong ssuc' superarity)) (∧-elim-left isc))) ⊔ Scope trm2)) ≡ true
            hlp3 = ScopeSubstitute {_}{(AppFold trm1 (trans (sym (ssuc'Pred'-id {trm1}{trm2})) (cong ssuc' superarity)) (∧-elim-left isc))} {trm2}
            hlp4 : ((Scope (AppFold trm1 (trans (sym (ssuc'Pred'-id {trm1}{trm2})) (cong ssuc' superarity)) ((∧-elim-left isc))) ⊔ (Scope trm2)) <= (Scope trm1 ⊔ Scope trm2)) ≡ true
            hlp4 = x<=y→x⊔y⊔ {Scope (AppFold trm1 (trans (sym (ssuc'Pred'-id {trm1}{trm2})) (cong ssuc' superarity)) ((∧-elim-left isc)))} {Scope trm1} {Scope trm2} hlp2
-}

-- So scoping' in a Λ-step can be calculated automatically and the Λ-step more eeasily done as follows:
--Λ-step' : {n : ℕ} → {trm : Term} → {trm' : Term} → (legit : Step trm trm') → (scoping : (Scope trm <= n) ≡ true) → Step (Λ n trm {scoping}) (Λ n trm' {Scoping' legit scoping})
--Λ-step' {n} {trm} {trm'} legit scoping = Λ-step legit scoping (Scoping' legit scoping)



{-
---

-- Some proofs that may be needed --
-- This seems convoluted... --

data isStep : Set where
  left  : isStep
  right : isStep
  lambda : isStep
  appfold : isStep

StepIs? :  {trm : Term} {trm' : Term} → (legit : Step trm trm') → isStep
StepIs? {.(_ · _)} {.(_ · _)} (left-step legit) = left
StepIs? {.(_ · _)} {.(_ · _)} (right-step legit) = righty

StepIs? {.(Λ _ _)} {.(Λ _ _)} (Λ-step {n} {trm} {trm'} legit scoping scoping') = lambda
StepIs? {trm} {.(AppFold trm arity isc)} (appFold arity isc) = appfold

ΛisLambda : {n : ℕ} {trm : Term} {trm' : Term} {scoping1 : (Scope trm <= n) ≡ true} → (legit : Step (Λ n trm {scoping1}) (trm')) → StepIs? legit ≡ lambda
ΛisLambda {n} {trm} {.(Λ n _)} {scoping1} (Λ-step legit .scoping1 scoping') = refl

ΛisLambda' : {n m : ℕ} {trm : Term} {trm' : Term} {scoping1 : (Scope trm <= n) ≡ true}{scoping2 : (Scope trm' <= m) ≡ true} → (legit : Step (Λ n trm {scoping1}) (Λ m trm' {scoping2})) → StepIs? legit ≡ lambda
ΛisLambda' {n}{m}{trm}{trm'}{scoping1}{scoping2} legit =  ΛisLambda legit

StepIsΛ-def1 :  {trm1 : Term} {trm2 : Term} → (move : Step trm1 trm2) → StepIs? move ≡ lambda → Σ[ n ∈ ℕ ] (Σ[ trm1' ∈ Term ] (Σ[ scoping1 ∈ (((Scope trm1') <= n) ≡ true) ] (trm1 ≡ (Λ n trm1' {scoping1}))))
StepIsΛ-def1 {.(Λ n trm)} {.(Λ n trm')} (Λ-step {n} {trm} {trm'} move' scoping scoping') refl = n , (trm , (scoping , refl))

StepIsΛ-def2 :  {trm1 : Term} {trm2 : Term} → (move : Step trm1 trm2) → StepIs? move ≡ lambda → Σ[ n ∈ ℕ ] ( Σ[ (trm1' , trm2') ∈ (Term × Term) ] ( Σ[ (scoping1 , scoping2)  ∈ (((Scope trm1') <= n) ≡ true) × (((Scope trm2') <= n) ≡ true) ] ( (trm1 , trm2) ≡ ((Λ n trm1' {scoping1}) , (Λ n trm2' {scoping2})) ) )) 
StepIsΛ-def2 {.(Λ _ _)} {.(Λ _ _)} (Λ-step {n}{trm}{trm'} move' scoping scoping') istep = n , ((trm , trm') , (scoping , scoping') , refl)

Λ-Step-n≡m-lemma-hlp : {n m : ℕ} {trm1 : Term} {trm2 : Term} → (isLambda?n n trm1 ≡ true) → (isLambda?n m trm2 ≡ true) → (legit : Step trm1 trm2) → 
                       (working :  Σ[ n ∈ ℕ ] ( Σ[ (trm1' , trm2') ∈ (Term × Term) ] ( Σ[ (scoping1 , scoping2)  ∈ (((Scope trm1') <= n) ≡ true) × (((Scope trm2') <= n) ≡ true) ]
                                   ( (trm1 , trm2) ≡ ((Λ n trm1' {scoping1}) , (Λ n trm2' {scoping2})) ) )) ) → n ≡ m 
Λ-Step-n≡m-lemma-hlp {n} {m} {.(Λ n' trma {_})} {.(Λ n' trmb {_})} isl1 isl2 legit (n' , (trma , trmb) , (fst2 , snd) , refl) with ℕ-Dec m n' | ℕ-Dec n n' 
...                    | yes refl | yes refl = refl

Λ-Step-n≡m-lemma-hlp2 : {n : ℕ} {trm : Term}{scoping : (Scope trm <= n) ≡ true} → (isLambda?n n (Λ n trm {scoping})) ≡ true
Λ-Step-n≡m-lemma-hlp2 {n}{trm}{scoping} with ℕ-Dec n n 
...                 | yes x = refl
...                 | no x = ⊥-elim (x refl)

-- *
Λ-Step-n≡m-lemma : {n m : ℕ} {trm : Term} {trm' : Term} {scoping1 : (Scope trm <= n) ≡ true} {scoping2 : (Scope trm' <= m) ≡ true} → (legit : Step (Λ n trm {scoping1}) (Λ m trm' {scoping2})) → n ≡ m
Λ-Step-n≡m-lemma {n} {m} {trm} {trm'} {scoping1} {scoping2} legit = hlp2
         where
           hlp : StepIs? {Λ n trm {scoping1}}{Λ m trm' {scoping2}} legit ≡ lambda
           hlp = ΛisLambda {n}{trm}{Λ m trm' {scoping2}} legit
           hlp2 : n ≡ m
           hlp2 = Λ-Step-n≡m-lemma-hlp {n}{m}{Λ n trm {scoping1}}{Λ m trm' {scoping2}} (Λ-Step-n≡m-lemma-hlp2 {n}{trm}{scoping1}) (Λ-Step-n≡m-lemma-hlp2 {m}{trm'}{scoping2}) legit (StepIsΛ-def2 legit (ΛisLambda' legit)) 

Λ-Step-extract-inner : {trm1 trm2 : Term} → (legit : Step trm1 trm2) → (StepIs? {trm1} {trm2} legit) ≡ lambda → Σ[ (trm , trm') ∈ (Term × Term) ] (Step trm trm')
Λ-Step-extract-inner {.(Λ _ _)} {.(Λ _ _)} (Λ-step {n}{trm}{trm'} legit scoping scoping') steps = (trm , trm') , legit

Λ-Step-extract-inner'-hlp : {trm1 trm2 : Term} → (legit : Step trm1 trm2) → (steps : (StepIs? {trm1} {trm2} legit) ≡ lambda) → (isLambda? trm1 ≡ true) × (isLambda? trm2 ≡ true)
Λ-Step-extract-inner'-hlp {.(Λ _ _)} {.(Λ _ _)} (Λ-step legit scoping scoping') refl = refl , refl

Λ-Step-extract-inner' : {trm1 trm2 : Term} → (legit : Step trm1 trm2) → (steps : (StepIs? {trm1} {trm2} legit) ≡ lambda) → (Step (isLambda?→inner {trm1} (proj₁ (Λ-Step-extract-inner'-hlp legit steps))) (isLambda?→inner {trm2} (proj₂ (Λ-Step-extract-inner'-hlp legit steps))))
Λ-Step-extract-inner' {.(Λ n trm)} {.(Λ n trm')} (Λ-step {n} {trm} {trm'} legit scoping scoping') refl = legit

-- *
Λ-Step-trm-lemma :  {n m : ℕ} {trm : Term} {trm' : Term} {scoping1 : (Scope trm <= n) ≡ true} {scoping2 : (Scope trm' <= m) ≡ true} → (legit : Step (Λ n trm {scoping1}) (Λ m trm' {scoping2})) → Step trm trm'
Λ-Step-trm-lemma {n}{m}{trm}{trm'}{scoping1}{scoping2} legit with ℕ-Dec n m
Λ-Step-trm-lemma {n}{m}{trm}{trm'}{scoping1}{scoping2} legit | yes refl with ℕ-Dec n n
Λ-Step-trm-lemma {n} {n} {trm} {trm'} {scoping1} {scoping2} legit | yes refl | no x = ⊥-elim (x refl) 
Λ-Step-trm-lemma {n} {n} {trm1} {trm2} {scoping1} {scoping2} legit | yes refl | yes x =  Λ-Step-extract-inner' legit (ΛisLambda legit)
-- Λ-Step-extract-inner' {Λ n trm1 {scoping1}}{Λ n trm2 {scoping2}} legit (ΛisLambda legit)
Λ-Step-trm-lemma {n}{m}{trm}{trm'}{scoping1}{scoping2} legit | no x = ⊥-elim (x (Λ-Step-n≡m-lemma legit))

-}












-- The reflexive, transitive closure of Step (includes zero and multi-step reduction).
-- This might be seen as the 'reflexive transitive closure' of Step:
data StepR : Term → Term → Set where
  reflexive : (trm : Term) → StepR trm trm
  step1 : {trm : Term} → {trm' : Term} → (step1 : Step trm trm') → StepR trm trm'
  transitive : {trm trm' trm'' : Term} → (stepR1 : StepR trm trm') → (stepR2 : StepR trm' trm'') → (StepR trm trm'')


----------------------------------------

-- In the combinator context we need parallel substitutions:
data ->>1List : (trms : List Term) → (trms' : List Term) → Set where
  nostep : ->>1List [] []
  addstep : {x : Term} → {y : Term} → {xs : List Term} → {ys : List Term} →
             (x->>1y : ->>1 x y) → (xs->>ys : ->>1List xs ys) → ->>1List (x ∷ xs) (y ∷ ys)

-- A construction of a Term from a List of Terms.
mutual
 data Terms : List Term → Set  where
   left* : {xs : List Term} → (lft : Term) → (trms : Terms xs) → Terms (lft ∷ xs) 
   right* : {xs : List Term} → (rgt : Term) → (trms : Terms xs) → Terms (rgt ∷ xs)
   Λ* : {xs : List Term} → (n : ℕ) → (trms : Terms xs) → (scoping : ((Scope (Reconstruct {xs} trms)) <= n) ≡ true) → Terms xs

 Reconstruct : {xs : List Term} → Terms xs → Term
 Reconstruct {.(lft ∷ _)} (left* lft trms) = lft · (Reconstruct trms) 
 Reconstruct {.(rgt ∷ _)} (right* rgt trms) = (Reconstruct trms) · rgt
 Reconstruct {xs} (Λ* {xs} n trms scoping) = Λ n (Reconstruct trms) {scoping}

Terms[] : Terms [] -> ⊥
Terms[] (Λ* n null scoping) = ⊥-elim (Terms[] null)

TermsTail : {x : Term} → {xs : List Term} → Terms (x ∷ xs) → Terms xs
TermsTail {x} {xs} (left* .x trmxs) = trmxs
TermsTail {x} {xs} (right* .x trmxs) = trmxs
TermsTail {x} {xs} (Λ* n (left* .x trmxxs) scoping) = trmxxs
TermsTail {x} {xs} (Λ* n (right* .x trmxxs) scoping) = trmxxs
TermsTail {x} {xs} (Λ* n (Λ* n₁ trmxxs scoping₁) scoping) = TermsTail trmxxs
 
Terms->>1Terms :  {xs : List Term} → {ys : List Term} → (trms : Terms xs) → (xs->>Listys : ->>1List xs ys) → Terms ys
Terms->>1Terms {.(lft ∷ xs)} {.(lft' ∷ ys)} (left* {xs} lft trms) (addstep {lft} {lft'} {xs}{ys} x->>1y xs->>Listys) = left* {ys} lft' (Terms->>1Terms trms xs->>Listys)
Terms->>1Terms {.(rgt ∷ xs)} {.(rgt' ∷ ys)} (right* {xs} rgt trms) (addstep {rgt}{rgt'}{xs}{ys} x->>1y xs->>Listys) = right* {ys} rgt' (Terms->>1Terms trms xs->>Listys)
Terms->>1Terms {.[]} {.[]} (Λ* {.[]} n trms scoping) nostep = ⊥-elim (Terms[] trms)
Terms->>1Terms {.(x ∷ xs)} {.(y ∷ ys)} (Λ* {.(x ∷ xs)} n (left* .x trms) scoping) (addstep {x} {y} {xs} {ys} x->>1y xs->>Listys) = Λ* {y ∷ ys} n (left* y trmsys) {!!} 
                                                           where
                                                            trmsxs : Terms xs
                                                            trmsxs = TermsTail (left* x trms) -- change this for th eothers!
                                                            trmsys : Terms ys
                                                            trmsys = (Terms->>1Terms {xs} {ys} trmsxs xs->>Listys)
                                                            scp≡ : Scope x ≡ Scope y
                                                            scp≡ = Scope->>1-lemma x->>1y
                                                            hlp : ((Scope x ⊔ Scope (Reconstruct trms)) <= n) ≡ ((Scope y ⊔ Scope (Reconstruct trms)) <= n)
                                                            hlp = cong (λ w -> ((w ⊔ Scope (Reconstruct trms)) <= n)) scp≡
Terms->>1Terms {.(x ∷ xs)} {.(y ∷ ys)} (Λ* {.(x ∷ xs)} n (right* .x trms) scoping) (addstep {x} {y} {xs} {ys} x->>1y xs->>Listys) = {!!}
Terms->>1Terms {.(x ∷ xs)} {.(y ∷ ys)} (Λ* {.(x ∷ xs)} n (Λ* n₁ trms scoping₁) scoping) (addstep {x} {y} {xs} {ys} x->>1y xs->>Listys) = {!!}

-- Define parallel ->>1 reduction
data ->>P : Term → Term → Set where
  parallelStep : {xs : List Term} → {ys : List Term} → (->>1list : ->>1List xs ys) → (trms : Terms xs) → ->>P (Reconstruct {xs} trms) (Reconstruct {ys} (Terms->>1Terms trms ->>1list)) 

reflexive' : (trm : Term) → ->>P trm trm
reflexive' trm = {!!}
          where
            xs : List Term
            xs = trm ∷ []
            trms : Terms xs
            trms = {!!}
            hlp : trm ≡ Reconstruct {xs} trms
            hlp = {!!}

-- Relation ->>P satisfies the diamond property --
->>P-Diamond : {M M1 M2 : Term} → (leftstep : ->>1 M M1) → (rightstep : ->>P M M2) → Σ[ M3 ∈ Term ] (( ->>P M1 M3 ) × ( ->>P M2 M3 ))
->>P-Diamond {M} {.M} {M2} reflexive rightstep = M2 , (rightstep , {!!})
->>P-Diamond {M} {M1} {M2} (Λ-step .M .M1 isl isl' leftstep) rightstep = {!!}
->>P-Diamond {.(M₁ · N)} {.(M' · N')} {M2} (·step M₁ M' N N' leftstep leftstep₁) rightstep = {!!}
->>P-Diamond {M} {.(AppFold M arity isc)} {M2} (appFold .M arity isc) rightstep = {!!}



---------------------------------------

-- Relation ->>1 satisfies the diamond property --
-- (Analogous to a similar lemma in Barendregt) --

{-->>1-Diamond : {M M1 M2 : Term} → (leftstep : ->>1 M M1) → (rightstep : ->>1 M M2) → Σ[ M3 ∈ Term ] (( ->>1 M1 M3 ) × ( ->>1 M2 M3 ))
->>1-Diamond {M} {.M} {M2} reflexive rightstep = M2 , (rightstep , reflexive)
->>1-Diamond {M} {M1} {.M} (Λ-step .M .M1 isl isl' leftstep) reflexive = M1 , (reflexive , (Λ-step M M1 isl isl' leftstep))
->>1-Diamond {M} {M1} {M2} (Λ-step {n} .M .M1 isl isl' leftstep) (Λ-step {m} M M2 isl1 isl'' rightstep) with isLambda?n≡m-lemma {n}{m}{M}  isl isl1 
...                                                                                                     | refl  with isLambda?n≡-lemma {n} {M} isl isl1
->>1-Diamond {M} {M1} {M2} (Λ-step {n} .M .M1 isl isl' leftstep) (Λ-step {n} M M2 .isl isl'' rightstep) | refl | refl = ΛM3' , (Λ-step {n} M1 ΛM3' isl' hlp' (proj₁ (proj₂ hlp)) , Λ-step {n} M2 ΛM3' isl'' hlp' (proj₂ (proj₂ hlp))) 
    where
      M1' : Term
      M1' = (isLambda?→inner (isLambda?n→isLambda? {n}{M1} isl'))
      M2' : Term
      M2' =  (isLambda?→inner (isLambda?n→isLambda? {n}{M2} isl''))
      hlp : Σ[ M3' ∈ Term ] ->>1 M1' M3' × ->>1 M2' M3'
      hlp = ->>1-Diamond {isLambda?→inner (isLambda?n→isLambda? {n} {M} isl)}{isLambda?→inner (isLambda?n→isLambda? {n}{M1} isl')}{isLambda?→inner (isLambda?n→isLambda? {n}{M2} isl'')} leftstep rightstep
      M3' : Term
      M3' = proj₁ hlp
      scM1' : (Scope M1' <= n) ≡ true
      scM1' = isLambda?-inner-Scope {n}{M1} isl'
      scM3' : (Scope M3' <= n) ≡ true
      scM3' = ->>1-Scope-lemma {n}{M1'}{M3'} scM1' (Scope->>1-lemma (proj₁ (proj₂ hlp)))
      ΛM3' : Term
      ΛM3' =  Λ n (M3') {scM3'}
      hlp' : (isLambda?n n (Λ n M3' {scM3'})) ≡ true
      hlp' = isLambda?n-def' {n}{M3'} {scM3'} 
->>1-Diamond {M} {M1} {.(AppFold {0} M arity isc)} (Λ-step {n} .M .M1 isl isl' leftstep) (appFold _  arity isc) = ⊥-elim (isLambda?→SuperArity≢just0 {M} (isLambda?n→isLambda? {n}{M} isl) arity)
->>1-Diamond {.(M · N)} {.(M' · N')} {.(M · N)} (·step M M' N N' leftstep1 leftstep2) reflexive = ((M' · N')) , (reflexive , (·step M M' N N' leftstep1 leftstep2))
->>1-Diamond {.(M · N)} {.(M' · N')} {.(M'' · N'')} (·step M M' N N' leftstep1 leftstep2) (·step M M'' N N'' rightstep1 rightstep2) = (M3' · N3') , (·step _ _ _ _ (proj₁ (proj₂ left-hlp)) (proj₁ (proj₂ right-hlp))) , (·step _ _ _ _ (proj₂ (proj₂ left-hlp)) (proj₂ (proj₂ right-hlp)))
    where
      left-hlp : Σ[ M3 ∈ Term ] ->>1 M' M3 × ->>1 M'' M3
      left-hlp = ->>1-Diamond leftstep1 rightstep1
      right-hlp : Σ[ N3 ∈ Term ] ->>1 N' N3 × ->>1 N'' N3
      right-hlp =  ->>1-Diamond leftstep2 rightstep2
      M3' : Term
      M3' = proj₁ left-hlp
      N3' : Term
      N3' = proj₁ right-hlp
->>1-Diamond {.(Λ zero M₁ · N)} {.(M' · N')} {.(AppFold (Λ zero M₁ {scoping} · N) refl isc)} (·step (Λ zero M₁ {scoping}) M' N N' leftstep1 leftstep2) (appFold .(Λ zero M₁ {scoping} · N) refl isc) = {!!}
->>1-Diamond {.(M₁ · M₂ · N)} {.(Self · N')} {.(AppFold (M₁ · M₂ · N) arity isc)} (·step (M₁ · M₂) Self N N' leftstep1 leftstep2) (appFold .(M₁ · M₂ · N) arity isc) = {!!}
->>1-Diamond {.(M₁ · M₂ · N)} {.((! n) · N')} {.(AppFold (M₁ · M₂ · N) arity isc)} (·step (M₁ · M₂) (! n) N N' leftstep1 leftstep2) (appFold .(M₁ · M₂ · N) arity isc) = {!!}
->>1-Diamond {.(M₁ · M₂ · N)} {.((` x) · N')} {.(AppFold (M₁ · M₂ · N) arity isc)} (·step (M₁ · M₂) (` x) N N' leftstep1 leftstep2) (appFold .(M₁ · M₂ · N) arity isc) = {!!}
->>1-Diamond {.(M₁ · M₂ · N)} {.(Λ n M' · N')} {.(AppFold (M₁ · M₂ · N) arity isc)} (·step (M₁ · M₂) (Λ n M') N N' leftstep1 leftstep2) (appFold .(M₁ · M₂ · N) arity isc) = {!!}
->>1-Diamond {.(M₁ · M₂ · N)} {.(M' · M'' · N')} {.(AppFold (M₁ · M₂ · N) arity isc)} (·step (M₁ · M₂) (M' · M'') N N' leftstep1 leftstep2) (appFold .(M₁ · M₂ · N) arity isc) = {!!}
                                                                  --  (->>1-Substitute-lemma {M}{M'}{N}{N'} leftstep1 leftstep2 isc arity)
->>1-Diamond {M} {.(AppFold M arity isc)} {.M} (appFold _ arity isc) reflexive = (AppFold M arity isc) , reflexive , (appFold _ arity isc)
->>1-Diamond {M} {.(AppFold M arity isc)} {M2} (appFold _ arity isc) (Λ-step {n} _ _  isl isl' rightstep) =  ⊥-elim (isLambda?→SuperArity≢just0 {M} (isLambda?n→isLambda? {n}{M} isl) arity)
->>1-Diamond {.(M · N)} {.(AppFold {0} (M · N) arity isc)} {.(M' · N')} (appFold (M · N) arity isc) (·step M M' N N' rightstep1 rightstep2) = {!!} --({!!}) , {!!}
 --                                                                   (->>1-Substitute-lemma rightstep1 rightstep2 isc arity , reflexive)
->>1-Diamond {M} {.(AppFold M arity isc)} {.(AppFold M arity1 isc1)} (appFold M arity isc) (appFold M arity1 isc1)= (AppFold M arity isc) , hlp , hlp'
     where
       hlp : ->>1 (AppFold M arity isc)  (AppFold M arity isc)
       hlp = reflexive
       hlp' : ->>1 (AppFold M arity1 isc1)  (AppFold M arity isc)
       hlp' = ->>1-Diamond-App-hlp {M} {AppFold M arity isc} {arity} {isc} arity1 isc1 hlp
-}
{-

{-



                                                  


StepN→StepR : {trm trm' : Term} → StepN trm trm' → StepR trm trm'
StepN→StepR {trm} {.trm} (reflexive .trm) = reflexive trm
StepN→StepR {trm} {trm'} (step1 step2) = step1 step2
StepN→StepR {trm} {trm'} (step+ stpn next) = transitive (StepN→StepR stpn) (step1 next)

StepR→StepN : {trm trm' : Term} → StepR trm trm' → StepN trm trm'
StepR→StepN {trm} {.trm} (reflexive .trm) = reflexive trm
StepR→StepN {trm} {trm'} (step1 step2) = step1 step2
StepR→StepN {trm} {trm''} (transitive {trm}{trm'}{trm''} stpR1 stpR2) = transitivity (StepR→StepN stpR1) (StepR→StepN stpR2)

ScopeStepR-lemma :  {trm trm' : Term} → (steps : StepR trm trm') → Scope trm ≡ Scope trm'
ScopeStepR-lemma {trm} {.trm} (reflexive .trm) = refl
ScopeStepR-lemma {trm} {trm'} (step1 step2) = ScopeStep-lemma step2
ScopeStepR-lemma {trm} {trm'} (transitive {trm}{trm''}{trm'} steps1 steps2) = trans (ScopeStepR-lemma steps1) (ScopeStepR-lemma steps2)

R→N→R-id-hlp : {trm trm' trm'' : Term} {a b  : StepR trm trm'} → {c d : StepR trm' trm''} → (a ≡ b) → (c ≡ d) → transitive a c ≡ transitive b d
R→N→R-id-hlp {trm} {trm'} {trm''} {a} {.a} {c} {.c} refl refl = refl -- R-N-R-id in any case doesn't exist, so StepR and StepN are not 'iso'

-- But this is true, so we have one side of the 'iso':
N→R→N-id : {trm trm' : Term} → (stpn : StepN trm trm') → (StepR→StepN {trm}{trm'} (StepN→StepR {trm}{trm'} stpn)) ≡ stpn
N→R→N-id {trm} {.trm} (reflexive .trm) = refl
N→R→N-id {trm} {trm'} (step1 step2) = refl
N→R→N-id {trm} {trm'} (step+ stpn next) = cong (λ w → step+ w next) hlp
                             where
                               hlp : (StepR→StepN (StepN→StepR stpn)) ≡ stpn
                               hlp = N→R→N-id stpn

-- This section proves the Diamond Property-       --
-- Analogous to proof in Barendregt, though the    --
-- type theoretic proof is very different in style --










Λ-step-def : (ΛM : Term) → (ΛM' : Term) →  (isl : isLambda? ΛM ≡ true) → (isl' : isLambda? ΛM' ≡ true) → ->>1 ΛM ΛM' → (isLambda?→n isl ≡ isLambda?→n isl')
Λ-step-def (Λ n ΛM) .(Λ n ΛM) refl refl reflexive = refl
Λ-step-def (Λ n ΛM {scoping}) (Λ m ΛM' {scoping'}) refl refl (Λ-step {n'} .(Λ n ΛM) .(Λ m ΛM') isl2 isl2' MM') with ℕ-Dec n' m | ℕ-Dec n' n 
... | yes refl | yes refl = refl
Λ-step-def Self .(AppFold Self arity isc) isl isl' (appFold .Self arity isc) = ⊥-elim (false≡true→⊥ isl)
Λ-step-def (! n) .(AppFold (! n) arity isc) isl isl' (appFold .(! n) arity isc) =  ⊥-elim (false≡true→⊥ isl)
Λ-step-def (` x) .(AppFold (` x) arity isc) isl isl' (appFold .(` x) arity isc) =  ⊥-elim (false≡true→⊥ isl)
Λ-step-def (Λ n ΛM) .(AppFold (Λ n ΛM) arity isc) isl isl' (appFold .(Λ n ΛM) arity isc) = ⊥-elim (suc'+ℕ≢+0 (just-elim arity))
Λ-step-def (ΛM · ΛM₁) .(AppFold (ΛM · ΛM₁) arity isc) isl isl' (appFold .(ΛM · ΛM₁) arity isc) =  ⊥-elim (false≡true→⊥ isl)






isLambda?n-def : {n : ℕ} {M : Term} (scoping : (Scope M <= n) ≡ true) → (isLambda?n n (Λ n M {scoping})) ≡ true
isLambda?n-def {n}{M} scoping with ℕ-Dec n n 
... | yes x = refl
... | no x = ⊥-elim (x refl)







--->>1-Substitute-lemma : {M M' N  N' : Term} →  (->>1 M M') → (->>1 N N') → (isc : isCombinator M ∧ isCombinatorExpr N ≡ true) → (arity : (SuperArity (M · N) ≡ just (+ zero)))
                                           --                → ->>1 (Substitute zero (AppFold M (trans (sym (ssuc'Pred'-id {M}{N})) (cong ssuc' arity)) (∧-elim-left isc)) N) (M' · N')
--->>1-Substitute-lemma {M}{M'}{N}{N'} MM' NN' isc arity = {!!}

{- 

arity     : (SuperArity (M · N) | SuperArity M) ≡ just (+ zero) -}



-}    

{-where
        app1 : ->>1 M (AppFold M arity isc)
        app1 = appFold M arity isc -}

{-
-- ***DIAMOND PROPERTY FOR BETA REDUCTION*** --
StepN-Diamond : {M M1 M2 : Term} → (leftstep : StepN M M1) → (rightstep : StepN M M2) → Σ[ M3 ∈ Term ] (( StepN M1 M3 ) × ( StepN M2 M3 ))
StepN-Diamond {M}{M1}{M2} leftstep rightstep = DiamondLemma (StepN→->>1 leftstep) (StepN→->>1 rightstep) (->>1-Diamond (StepN→->>1 leftstep) (StepN→->>1 rightstep))
-}
--------------------------


{-
  left-step : {trm1 : Term} → {trm2 : Term} → {trm1' : Term} → (legit : Step trm1 trm1' ) → (trm1 · trm2) (trm1' · trm2)
  right-step : {trm1 : Term} → {trm2 : Term} → {trm2' : Term} → (legit : Step trm2 trm2') → Step01 (trm1 · trm2) (trm1 · trm2')
  Λ-step : {Λtrm : Term} → {Λtrm' : Term} → (isl : isLambda? Λtrm ≡ true) → (isl' : isLambda? Λtrm' ≡ true)
               → (legit : Step (isLambda?→inner {Λtrm} isl) (isLambda?→inner {Λtrm'} isl')) → Step01 Λtrm Λtrm'
  appFold : {trm : Term} → (arity : Arity' trm ≡ + zero) → (isc : isCombinator trm ≡ true) → Step01 trm (AppFold trm {arity} {isc})


EndBranch : {start : Term} → {end : Term} → (branch : StepN start end) → Term
EndBranch {start}{end} Branch = end

EndStep :  {start : Term} → {end : Term} → (step' : Step start end) → Term
EndStep {start}{end} step' = end

FlipDiamond : {left right : Term} → Σ[ end ∈ Term ] StepN left end × StepN right end → Σ[ end ∈ Term ] StepN right end × StepN left end
FlipDiamond {left} {right} (fst , snd1 , snd2) = fst , (snd2 , snd1)

{-

OneStep-Diamond : {start left right : Term} → (leftstep : Step start left) → (rightstep : Step start right) → Σ[ end ∈ Term ] StepN left end × StepN right end
--OneStep-Diamond {Self k} {left} {Self k'} (Λ-step isl isl' leftstep) rightstep = {!!}
OneStep-Diamond {Self k} {.(AppFold (Self k))} {Self k'} (appFold arity isc) rightstep = ⊥-elim (false≡true→⊥ isc)
--OneStep-Diamond {Self k} {left} {(! n)} (Λ-step isl isl' leftstep) rightstep = {!!}
--OneStep-Diamond {Self k} {.(AppFold (Self k))} {(! n)} (appFold arity isc) rightstep = {!!}
--OneStep-Diamond {Self k} {left} {` x} (Λ-step isl isl' leftstep) rightstep = {!!}
--OneStep-Diamond {Self k} {.(AppFold (Self k))} {` x} (appFold arity isc) rightstep = {!!}
--OneStep-Diamond {Self k} {left} {Λ n right} leftstep rightstep = {!!}
--OneStep-Diamond {Self k} {left} {right · right₁} leftstep rightstep = {!!}
--OneStep-Diamond {(! n)} {left} {right} (Λ-step isl isl' leftstep) rightstep = {!!}
OneStep-Diamond {(! n)} {.(AppFold (! n))} {right} (appFold arity isc) rightstep =  ⊥-elim (false≡true→⊥ isc)
--OneStep-Diamond {` x} {left} {right} leftstep rightstep = {!!}
OneStep-Diamond {Λ n start} {Λ m left} {Self k} (Λ-step isl isl' leftstep) rightstep = {!!} --imp
OneStep-Diamond {Λ n start} {Λ m left} {(! k)} (Λ-step isl isl' leftstep) rightstep = {!!}  --imp
OneStep-Diamond {Λ n start} {Λ m left} {` x} (Λ-step isl isl' leftstep) rightstep = {!!}  --imp
OneStep-Diamond {Λ zero start} {Λ m left} {Λ zero right} (Λ-step isl isl' leftstep') rightstep = {!!}
OneStep-Diamond {Λ zero start} {Λ m left} {Λ (suc k) right} (Λ-step isl isl' leftstep') rightstep = {!!} --imp
OneStep-Diamond {Λ (suc n) start} {Λ m left} {Λ k right} (Λ-step isl isl' leftstep') rightstep = {!!}  -- imp
OneStep-Diamond {Λ n start} {Λ m left} {right1 · right2} (Λ-step isl isl' leftstep') rightstep = {!!} --imp
OneStep-Diamond {start1 · start2} {.(_ · start2)} {Self k} (left-step leftstep') rightstep = {!!}
OneStep-Diamond {start1 · start2} {.(_ · start2)} {(! n)} (left-step leftstep') rightstep = {!!}
OneStep-Diamond {start1 · start2} {.(_ · start2)} {` x} (left-step leftstep') rightstep = {!!}
OneStep-Diamond {start1 · start2} {.(_ · start2)} {Λ n right} (left-step leftstep') rightstep = {!!}
OneStep-Diamond {start1 · start2} {.(_ · start2)} {right1 · right2} (left-step leftstep') rightstep = {!!}
OneStep-Diamond {start1 · start2} {.(start1 · _)} {Self k} (right-step leftstep') rightstep = {!!}
OneStep-Diamond {start1 · start2} {.(start1 · _)} {(! n)} (right-step leftstep') rightstep = {!!}
OneStep-Diamond {start1 · start2} {.(start1 · _)} {` x} (right-step leftstep') rightstep = {!!}
OneStep-Diamond {start1 · start2} {.(start1 · _)} {Λ n right} (right-step leftstep') rightstep = {!!}
OneStep-Diamond {start1 · start2} {.(start1 · _)} {right1 · right2} (right-step leftstep') rightstep = {!!}
OneStep-Diamond {start1 · start2} {.(AppFold (start1 · start2))} {Self k} (appFold arity isc) rightstep = {!!}
OneStep-Diamond {start1 · start2} {.(AppFold (start1 · start2))} {(! n)} (appFold arity isc) rightstep = {!!}
OneStep-Diamond {start1 · start2} {.(AppFold (start1 · start2))} {` x} (appFold arity isc) rightstep = {!!}
OneStep-Diamond {start1 · start2} {.(AppFold (start1 · start2))} {Λ n right} (appFold arity isc) rightstep = {!!}
OneStep-Diamond {start1 · start2} {.(AppFold (start1 · start2))} {right1 · right2} (appFold arity isc) rightstep = {!!} 


Diamond-Property-step : {start left right : Term} → (leftstep : Step start left) → (rightBranch : StepN start right) → Σ[ end ∈ Term ] StepN left end × StepN right end  
Diamond-Property-step {.(_ · _)} {.(_ · _)} {.(_ · _)} (left-step {trm1}{trm1'}{trm2} leftstep) (reflexive .(_ · _)) =  (trm2  · trm1') , (reflexive (trm2 · trm1') , step1 (left-step leftstep))
Diamond-Property-step {.(trm1 · trm2)} {.(trm1' · trm2)} {Self} (left-step {trm1} {trm2} {trm1'} leftstep) (step1 {.(trm1 · trm2)} {.(Self)} step2) = {!!}
Diamond-Property-step {.(trm1 · trm2)} {.(trm1' · trm2)} {(! n)} (left-step {trm1} {trm2} {trm1'} leftstep) (step1 {.(trm1 · trm2)} {.(! n)} step2) = {!!}
Diamond-Property-step {.(trm1 · trm2)} {.(trm1' · trm2)} {` x} (left-step {trm1} {trm2} {trm1'} leftstep) (step1 {.(trm1 · trm2)} {.(` x)} step2) = {!!}
Diamond-Property-step {.(trm1 · trm2)} {.(trm1' · trm2)} {Λ n right} (left-step {trm1} {trm2} {trm1'} leftstep) (step1 {.(trm1 · trm2)} {.(Λ n right)} step2) = {!!}
Diamond-Property-step {.(trm1 · trm2)} {.(trm1' · trm2)} {right1 · right2} (left-step {trm1} {trm2} {trm1'} leftstep) (step1 {.(trm1 · trm2)} {.(right1 · right2)} step2) = {!!}
Diamond-Property-step {.(_ · _)} {.(_ · _)} {right} (left-step {trm1}{trm2}{trm1'} leftstep) (step+ {trm}{trm'} rightstep next) = (proj₁ hlp2) , {!!}
                                                                        where
                                                                          hlp : Σ[ end ∈ Term ] (StepN (trm1' · trm2) end × StepN trm' end) 
                                                                          hlp = Diamond-Property-step {trm}{trm1' · trm2}{trm'} (left-step leftstep) rightstep
                                                                          hlp2 : Σ[ end' ∈ Term ] (StepN right end') × (StepN (proj₁ hlp) end') 
                                                                          hlp2 =  Diamond-Property-step {trm'} {right} {proj₁ hlp} next (proj₂ (proj₂ hlp))
Diamond-Property-step {.(_ · _)} {.(_ · _)} {right} (right-step leftstep) rightstep = {!!}
Diamond-Property-step {start} {left} {right} (Λ-step isl isl' leftstep) rightstep = {!!}
Diamond-Property-step {start} {.(AppFold start)} {right} (appFold arity isc) rightstep =  {!!}



-- freeze --
Diamond-Property-step : {start left right : Term} → (leftstep : Step start left) → (rightBranch : StepN start right) → Σ[ end ∈ Term ] StepN left end × StepN right end  
Diamond-Property-step {.(_ · _)} {.(_ · _)} {.(_ · _)} (left-step {trm1}{trm1'}{trm2} leftstep) (reflexive .(_ · _)) =  (trm2  · trm1') , (reflexive (trm2 · trm1') , step1 (left-step leftstep))
Diamond-Property-step {.(trm1 · trm2)} {.(trm1' · trm2)} {Self k} (left-step {trm1} {trm2} {trm1'} leftstep) (step1 {.(trm1 · trm2)} {.(Self k)} step2) = {!!}
Diamond-Property-step {.(trm1 · trm2)} {.(trm1' · trm2)} {(! n)} (left-step {trm1} {trm2} {trm1'} leftstep) (step1 {.(trm1 · trm2)} {.(! n)} step2) = {!!}
Diamond-Property-step {.(trm1 · trm2)} {.(trm1' · trm2)} {` x} (left-step {trm1} {trm2} {trm1'} leftstep) (step1 {.(trm1 · trm2)} {.(` x)} step2) = {!!}
Diamond-Property-step {.(trm1 · trm2)} {.(trm1' · trm2)} {Λ n right} (left-step {trm1} {trm2} {trm1'} leftstep) (step1 {.(trm1 · trm2)} {.(Λ n right)} step2) = {!!}
Diamond-Property-step {.(trm1 · trm2)} {.(trm1' · trm2)} {right1 · right2} (left-step {trm1} {trm2} {trm1'} leftstep) (step1 {.(trm1 · trm2)} {.(right1 · right2)} step2) = {!!}
Diamond-Property-step {.(_ · _)} {.(_ · _)} {right} (left-step leftstep) (step+ rightstep next) = {!!}
Diamond-Property-step {.(_ · _)} {.(_ · _)} {right} (right-step leftstep) rightstep = {!!}
Diamond-Property-step {start} {left} {right} (Λ-step isl isl' leftstep) rightstep = {!!}
Diamond-Property-step {start} {.(AppFold start)} {right} (appFold arity isc) rightstep =  {!!}
-}


{-with ((Arity' start1) ==' (+ 1))
... | true  = {!!}
... | false = {!!} -}

{-
 {start} {left} {.start} leftstep (reflexive .start) = left , (reflexive left , step1 leftstep)
Diamond-Property-step {start} {left} {right} leftstep (step1 step2) = {!!} , ({!!} , {!!})
Diamond-Property-step {start} {left} {right} leftstep (step+ rightBranch' next) = (proj₁ {!!}) , {!!} 
                          where
                            ind : Σ[ end1 ∈ Term ] StepN left end1 × StepN (EndBranch rightBranch') end1  
                            ind = Diamond-Property-step leftstep rightBranch'
                            ind+ :  Σ[ end2 ∈ Term ] StepN right end2 × StepN (proj₁ ind) end2
                            ind+ = Diamond-Property-step {EndBranch rightBranch'} {right}{proj₁ ind} next (proj₂ (proj₂ ind))
                            stpn' : StepN (EndBranch rightBranch') (proj₁ ind)
                            stpn' = proj₂ (proj₂ ind)
                            stpn : StepN right (proj₁ ind)
                            stpn = proj₁ (proj₂ (Diamond-Property-step {EndBranch rightBranch'} {right} {proj₁ ind} next {!!}))  -}

Diamond-PropertyN : {start : Term} → {left : Term} → {right : Term} → (leftBranch : StepN start left) → (rightBranch : StepN start right) → Σ[ end ∈ Term ] (StepN left end × StepN right end) 
Diamond-PropertyN {start} {.start} {right} (reflexive .start) rightBranch = right , rightBranch , (reflexive right)
Diamond-PropertyN {start} {left} {right} (step1 step2) rightBranch = {!!}
Diamond-PropertyN {start} {left} {right} (step+ leftBranch' next) rightBranch =
                                          proj₁ secondDiamond , (proj₁ (proj₂ secondDiamond) , transitivity (proj₂ (proj₂ firstDiamond)) (proj₂ (proj₂ secondDiamond)))
                                    where
                                      firstDiamond : Σ[ end1 ∈ Term ] (StepN (EndBranch leftBranch') end1 × StepN right end1)
                                      firstDiamond = Diamond-PropertyN {start}{EndBranch leftBranch'}{EndBranch rightBranch} leftBranch' rightBranch
                                      secondDiamond : Σ[ end2 ∈ Term ] StepN (EndStep next) end2 × StepN (proj₁ firstDiamond) end2
                                      secondDiamond = Diamond-PropertyN {EndBranch leftBranch'} {EndStep next} {proj₁ firstDiamond} (step1 next) (proj₁ (proj₂ firstDiamond))

Diamond-PropertyR : {start : Term} → {left : Term} → {right : Term} → (leftBranch : StepR start left) → (rightBranch : StepR start right) → Σ[ end ∈ Term ] (StepR left end × StepR right end) 
Diamond-PropertyR {start}{left}{right} leftBranch rightBranch = proj₁ hlp1 , (left' , right')
                          where
                            hlp1 : Σ[ end ∈ Term ] (StepN left end × StepN right end)
                            hlp1 = Diamond-PropertyN (StepR→StepN leftBranch) (StepR→StepN rightBranch)
                            left' : StepR left (proj₁ hlp1)
                            left' = StepN→StepR (proj₁ (proj₂ hlp1))
                            right' : StepR right (proj₁ hlp1)
                            right' = StepN→StepR (proj₂ (proj₂ hlp1))



{-                           


EndBranch : {start : Term} → {end : Term} → (branch : StepR start end) → Term
EndBranch {start}{end} Branch = end

Diamond-Property-step : {start left right : Term} → (leftstep : Step start left) → (rightBranch : StepR start right) → Σ[ end ∈ Term ] StepR left end × StepR right end  
Diamond-Property-step {start} {left} {right} leftstep (step step1) = {!!}
Diamond-Property-step {start} {left} {.start} leftstep (reflexive .start) = left , ((reflexive left) , (step leftstep))
Diamond-Property-step {start} {left} {right} leftstep (transitive (step step1) rightBranch2) = {!!}
Diamond-Property-step {start} {left} {right} leftstep (transitive (reflexive .start) rightBranch2) = {!!}
Diamond-Property-step {start} {left} {right} leftstep (transitive (transitive rightBranch1 rightBranch3) rightBranch2) = {!!}

Diamond-Property : {start : Term} → {left : Term} → {right : Term} → (leftBranch : StepR start left) → (rightBranch : StepR start right) → Σ[ end ∈ Term ] (StepR left end × StepR right end) 
Diamond-Property {start} {left} {right} (step step1) rightBranch = Diamond-Property-step step1 rightBranch
Diamond-Property {start} {.start} {right} (reflexive .start) rightBranch = right , rightBranch , (reflexive right)
Diamond-Property {start} {left} {right} (transitive leftBranch1 leftBranch2) rightBranch = proj₁ secondDiamond ,
                                                                                          (proj₁ (proj₂ secondDiamond) , transitive (proj₂ (proj₂ firstDiamond)) (proj₂ (proj₂ secondDiamond)))
                                    where
                                      firstDiamond : Σ[ end1 ∈ Term ] (StepR (EndBranch leftBranch1) end1 × StepR right end1)
                                      firstDiamond = Diamond-Property {start}{EndBranch leftBranch1}{EndBranch rightBranch} leftBranch1 rightBranch
                                      --firstDiamondleft : StepR (EndBranch leftBranch1) (proj₁ firstDiamond)
                                      --firstDiamondleft = proj₁ (proj₂ firstDiamond)
                                      secondDiamond : Σ[ end2 ∈ Term ] StepR (EndBranch leftBranch2) end2 × StepR (proj₁ firstDiamond) end2
                                      secondDiamond = Diamond-Property {EndBranch leftBranch1} {EndBranch leftBranch2} {proj₁ firstDiamond} leftBranch2 (proj₁ (proj₂ firstDiamond))


Diamond-Property-step' : {start left right : Term} → (leftstep : Step start left) → (rightstep : Step start right) → Σ[ end ∈ Term ] StepR left end × StepR right end  
Diamond-Property-step' = {!!}


Diamond-Property' : {start : Term} → {left : Term} → {right : Term} → (leftBranch : StepR start left) → (rightBranch : StepR start right) → Σ[ end ∈ Term ] (StepR left end × StepR right end) 
Diamond-Property' {start} {left} {right} (step step2) (step step1) = Diamond-Property-step' step2 step1
Diamond-Property' {start} {.start} {right} (reflexive .start) (step step1) = right , (step step1 , reflexive right)
Diamond-Property' {start} {left} {right} (transitive leftBranch1 leftBranch2) (step step1) =
              proj₁ secondDiamond , (proj₁ (proj₂ secondDiamond) , transitive (proj₂ (proj₂ firstDiamond)) (proj₂ (proj₂ secondDiamond)))
                                    where
                                      firstDiamond : Σ[ end1 ∈ Term ] (StepR (EndBranch leftBranch1) end1 × StepR right end1)
                                      firstDiamond = Diamond-Property {start}{EndBranch leftBranch1}{EndBranch (step step1)} leftBranch1 (step step1)
                                      --firstDiamondleft : StepR (EndBranch leftBranch1) (proj₁ firstDiamond)
                                      --firstDiamondleft = proj₁ (proj₂ firstDiamond)
                                      secondDiamond : Σ[ end2 ∈ Term ] StepR (EndBranch leftBranch2) end2 × StepR (proj₁ firstDiamond) end2
                                      secondDiamond = Diamond-Property {EndBranch leftBranch1} {EndBranch leftBranch2} {proj₁ firstDiamond} leftBranch2 (proj₁ (proj₂ firstDiamond))
Diamond-Property' {start} {left} {.start} leftBranch (reflexive .start) =  left , ((reflexive left) , leftBranch)
Diamond-Property' {start} {left} {right} (step step1) (transitive rightBranch1 rightBranch2) =  proj₁ secondDiamond , transitive (proj₂ (proj₂ firstDiamond)) (proj₂ (proj₂ secondDiamond)) , proj₁ (proj₂ secondDiamond)
                                    where
                                      firstDiamond : Σ[ end1 ∈ Term ] (StepR (EndBranch rightBranch1) end1 × StepR left end1)
                                      firstDiamond = Diamond-Property {start}{EndBranch rightBranch1}{EndBranch (step step1)} rightBranch1 (step step1)
                                      --firstDiamondleft : StepR (EndBranch rightBranch1) (proj₁ firstDiamond)
                                      --firstDiamondleft = proj₁ (proj₂ firstDiamond)
                                      secondDiamond : Σ[ end2 ∈ Term ] StepR (EndBranch rightBranch2) end2 × StepR (proj₁ firstDiamond) end2
                                      secondDiamond = Diamond-Property {EndBranch rightBranch1} {EndBranch rightBranch2} {proj₁ firstDiamond} rightBranch2 (proj₁ (proj₂ firstDiamond)) 
Diamond-Property' {start} {.start} {right} (reflexive .start) (transitive rightBranch1 rightBranch2) = right , (transitive rightBranch1 rightBranch2 , reflexive right)
Diamond-Property' {start} {left} {right} (transitive leftBranch1 leftBranch2) (transitive rightBranch1 rightBranch2) = {!!} , {!!}

--(proj₁ fourthDiamond) , (transitive (proj₁ (proj₂ secondDiamond)) (proj₁ (proj₂ fourthDiamond))) , {!!}  -- (transitive (proj₂ (proj₂ thirdDiamond)) (proj₂ (proj₂ fourthDiamond)))
                                    where
                                      firstDiamond : Σ[ end1 ∈ Term ] (StepR (EndBranch leftBranch1) end1 × StepR (EndBranch rightBranch1) end1)
                                      firstDiamond = Diamond-Property' leftBranch1 rightBranch1
                                      firstDiamondR : Σ[ end1R ∈ Term ] StepR (EndBranch leftBranch1) end1R × StepR (EndBranch rightBranch2) end1R
                                      firstDiamondR = Diamond-Property' leftBranch1 (transitive rightBranch1 rightBranch2)
                                      firstDiamondL : Σ[ end1L ∈ Term ] StepR (EndBranch leftBranch2) end1L × StepR (EndBranch rightBranch1) end1L
                                      firstDiamondL = Diamond-Property' (transitive leftBranch1 leftBranch2) rightBranch1
                                    --  secondDiamond : Σ[ end2 ∈ Term ] StepR (EndBranch leftBranch2) end2 × StepR (proj₁ firstDiamond) end2
                                    --  secondDiamond = Diamond-Property' leftBranch2 (proj₁ (proj₂ firstDiamond))
                                    --  thirdDiamond' : Σ[ end3 ∈ Term ] (StepR (proj₁ firstDiamond) end3) × (StepR (EndBranch rightBranch2) end3)
                                    --  thirdDiamond' = Diamond-Property' {!!} {!!}
                                      fourthDiamond : Σ[ end4 ∈ Term ] (StepR (proj₁ firstDiamondL) end4) × (StepR (proj₁ firstDiamondR) end4)
                                      fourthDiamond = Diamond-Property' {proj₁ firstDiamond} {proj₁ firstDiamondL}{proj₁ firstDiamondR} {!!} {!!} 
--Diamond-Property {!!} {!!}



-- A proof that a Step changes the Term --

--trm·trm-lemma : {trm' trm : Term} → trm' · trm ≢ trm
--trm·trm-lemma {trm'} {trm} ()

AppFold-Count-lemma-base : {m : ℕ} → {trm : Term} → (scoping : (Scope trm <= m) ≡ true) → (Application-Count (SubΛ-base (Λ m trm {scoping}) refl) <= 0) ≡ true
AppFold-Count-lemma-base {m} {Self} scoping = refl
AppFold-Count-lemma-base {m} {(! n)} scoping = refl
AppFold-Count-lemma-base {m} {` x} scoping = refl
AppFold-Count-lemma-base {m} {Λ n trm} scoping = refl
AppFold-Count-lemma-base {m} {trm1 · trm2} scoping = refl

AppFold-Count-lemma-Sub : {n m : ℕ} → {trm trm' : Term} → (arity : Arity trm ≡ suc m) → (Application-Count (Substitute n trm trm')) <= Application-Count trm ≡ true
AppFold-Count-lemma-Sub {n}{m} {Self} {trm'} arity = refl
AppFold-Count-lemma-Sub {n}{m} {(! n')} {trm'} arity = refl
AppFold-Count-lemma-Sub {n}{m} {` x} {trm'} arity with ℕ-Dec n x 
...                             | yes y = ⊥-elim (0≡Sucx→⊥ arity)
...                             | no y = refl
AppFold-Count-lemma-Sub {n}{m} {Λ n' trm} {trm'} arity = refl
AppFold-Count-lemma-Sub {n}{m} {trm1 · trm2} {trm'} arity = AppFold-Count-lemma-Sub {n}{suc m} {trm1}{trm'} (Predsuc-lemma arity)


--Scope-Application-lemma : {trm : Term} → (scoping : Scope trm <= zero ≡ true) → (arity : +[1+ zero ] ≡ +[1+ zero ]) → (isc : true ≡ true) → Application-Count (AppFold {1} (Λ zero trm {scoping}) {arity}{isc}) <= 0 ≡ true
--Scope-Application-lemma  = {!!}

{-AppFold-Count-lemma-Sub2 : {n m : ℕ} → {trm trm' : Term} → (arity : Arity trm ≡ suc m) → (Application-Count (Substitute n trm trm')) <= Application-Count trm ≡ true
AppFold-Count-lemma-Sub2 {n}{m} {Self} {trm'} arity = refl
AppFold-Count-lemma-Sub2 {n}{m} {(! n')} {trm'} arity = refl
AppFold-Count-lemma-Sub2 {n}{m} {` x} {trm'} arity with ℕ-Dec n x 
...                             | yes y = ⊥-elim (0≡Sucx→⊥ arity)
...                             | no y = refl
AppFold-Count-lemma-Sub2 {n}{m} {Λ n' trm} {trm'} arity = refl
AppFold-Count-lemma-Sub2 {n}{m} {trm1 · trm2} {trm'} arity = AppFold-Count-lemma-Sub {n}{suc m} {trm1}{trm'} (Predsuc-lemma arity) 


AppFold-Count-lemma-ind : {n : ℕ} → {trm trm' : Term} → (scoping : Arity' trm ≡ (+ n)) → (Application-Count (Substitute n trm trm')) <= Application-Count trm ≡ true
AppFold-Count-lemma-ind {n} {trm}{trm'} scoping = {!!}  

AppFold-Count-lemma : {n : ℕ}  → {trm trm' : Term} → (arity : Arity' trm ≡  + n)  → (isc : isCombinator trm ≡ true) → (Application-Count (AppFold {n} trm {arity} {isc})) <= Application-Count trm ≡ true
AppFold-Count-lemma {.(suc m)} {Λ m trm {scoping}} {trm'} refl refl = AppFold-Count-lemma-base {_}{trm} scoping
AppFold-Count-lemma {n} {trm1 · trm2} {trm'} arity isc = trans<= {(Application-Count (Substitute n (AppFold {suc n} trm1 {Suc'Pred'≡ arity}{∧-elim-left isc}) trm2))}
                                                                 {suc (Application-Count (AppFold {suc n} trm1 {Suc'Pred'≡ arity}{∧-elim-left isc}))}{suc (Application-Count trm1)} hlp hlp3
              where
                hlp : (Application-Count (Substitute n (AppFold {suc n} trm1 {Suc'Pred'≡ arity} {∧-elim-left isc}) trm2)) <= suc (Application-Count (AppFold {suc n} trm1 {Suc'Pred'≡ arity}{∧-elim-left isc})) ≡ true
                hlp =  <=suc {{!!}}{{!!}} (AppFold-Count-lemma-ind {{!!}}{trm1}{trm2} {!!})
                hlp2 : Application-Count (AppFold {suc n} trm1 {Suc'Pred'≡ arity}{∧-elim-left isc}) <= Application-Count trm1 ≡ true
                hlp2 = AppFold-Count-lemma {suc n}{trm1}{trm2} (Suc'Pred'≡ arity) (∧-elim-left isc)
                hlp3 : suc (Application-Count (AppFold {suc n} trm1 {Suc'Pred'≡ arity}{∧-elim-left isc})) <= suc (Application-Count trm1) ≡ true
                hlp3 = suc<=suc {Application-Count (AppFold {suc n} trm1 {Suc'Pred'≡ arity}{∧-elim-left isc})} {Application-Count trm1} hlp2 -}

--Application-Count-Sub-hlp : 

Arity-AppFold : {n m : ℕ} → {trm : Term} → {arity : Arity' trm ≡ + n} → {isc : isCombinator trm ≡ true} → Arity (AppFold {n} trm {arity}{isc}) ≡ suc m
Arity-AppFold = {!!}

Application-Count-Sub : {trm1 trm2 : Term} → (arity : Arity' trm1 ≡ (+ 1)) → (isc : isCombinator trm1 ≡ true)  → Application-Count (Substitute zero (AppFold {1} trm1 {arity}{isc}) trm2) <= Application-Count trm1 ≡ true
Application-Count-Sub {Λ zero trm {scoping}} {trm2} arity isc = trans<= {Application-Count (Substitute zero (AppFold {1} (Λ zero trm {scoping}) {arity}{isc}) trm2)}
                                                                         {Application-Count (AppFold {1} (Λ zero trm {scoping}) {arity}{isc})} {0}
                                                                         (AppFold-Count-lemma-Sub {0}{Arity (AppFold {1} (Λ zero trm {scoping}) {arity}{isc})} {AppFold {1} (Λ zero trm {scoping}) {arity}{isc}} {trm2} {!!}) (Scope-Application-lemma {trm} scoping arity isc) 
Application-Count-Sub {trm1 · trm3} {trm2} arity isc = {!!}

Application-Count≢ : {trm trm' trm2 : Term} → Application-Count trm <= Application-Count trm' ≡ true → trm ≢ trm' · trm2
Application-Count≢ {Self} {trm'} {trm2} apc = λ ()
Application-Count≢ {(! n)} {trm'} {trm2} apc = λ ()
Application-Count≢ {` x} {trm'} {trm2} apc = λ ()
Application-Count≢ {Λ n trm} {trm'} {trm2} apc = λ ()
Application-Count≢ {trm1 · trm3} {trm' · trm''} {trm2} apc = ·-intro-left-contra hlp
                         where
                           hlp : trm1 ≢ trm' · trm''
                           hlp = Application-Count≢ apc

Application-Count-AppFold-lemma : {n : ℕ} → {trm : Term} → (arity : Arity' trm ≡ + n) → (isc : isCombinator trm ≡ true) → (Application-Count (AppFold {n} trm {arity} {isc} ) <= Application-Count trm) ≡ true
Application-Count-AppFold-lemma  = {!!}

AppFold-lemma : {n : ℕ}  → {trm trm' : Term} → (arity : Arity' trm ≡ + n)  → (isc : isCombinator trm ≡ true) → AppFold {n} trm {arity} {isc} ≢ trm · trm'
AppFold-lemma {n} {trm}{trm'} arity isc = Application-Count≢ {!!} 

Substitute-lemma-hlp-Self2 : {n : ℕ} → {trm1 trm2 : Term} → Self ≡  Substitute zero trm1 trm2 → trm2 ≡ Self 
Substitute-lemma-hlp-Self2 {n} {Self} {trm1} stt = {!!}
Substitute-lemma-hlp-Self2 {n} {` zero} {Self} stt = {!!}
Substitute-lemma-hlp-Self2 {n} {` zero} {(! m)} stt = {!!}
Substitute-lemma-hlp-Self2 {n} {` suc x} {(! m)} stt = {!!}
Substitute-lemma-hlp-Self2 {n} {` x} {` y} stt = {!!}
Substitute-lemma-hlp-Self2 {n} {` x} {Λ m trm2} stt = {!!}
Substitute-lemma-hlp-Self2 {n} {` x} {trm2 · trm3} stt = {!!}

Substitute-lemma : {n : ℕ} → {trm1 trm1' trm2 : Term} →  trm1 · trm2 ≡ Substitute n trm1' trm2 → trm1 ≡ trm1'
Substitute-lemma {zero} {Self} {` zero} {trm2} tts = ⊥-elim (trm·trm-lemma tts)
Substitute-lemma {zero} {Self} {` suc x} {trm2} ()
Substitute-lemma {zero} {Self} {trm1' · trm1''} {trm2} tts = {!!} --⊥-elim (Substitute-lemma-hlp-Self2 {zero}{trm1'}{trm2} trm1'-hlp)
                                                 where
                                                   trm1'-hlp : Self ≡  Substitute zero trm1' trm2
                                                   trm1'-hlp = ·-elim-left tts
Substitute-lemma {zero} {(! n)} {` zero} {trm2} tts = {!!}
Substitute-lemma {zero} {(! n)} {` suc x} {trm2} tts = {!!}
Substitute-lemma {zero} {(! n)} {trm1' · trm1''} {trm2} tts = {!!}
Substitute-lemma {zero} {` x} {trm1'} {trm2} tts = {!!}
Substitute-lemma {zero} {Λ n trm1} {trm1'} {trm2} tts = {!!}
Substitute-lemma {zero} {trm1 · trm3} {trm1'} {trm2} tts = {!!}
Substitute-lemma {suc n} {trm1} {trm1'} {trm2} tts = {!!}

Step-def-hlp2 : {n : ℕ} → {trm1 trm2 : Term} -> (arity : Arity' trm1 ≡ + suc n) -> (isc : isCombinator trm1 ≡ true) -> trm1 · trm2 ≢ Substitute n trm1 trm2
Step-def-hlp2 {n} {Λ m trm1} {trm2} arity isc = {!!}
Step-def-hlp2 {n} {trm1 · trm3} {trm2} arity isc = {!!}

Step-def-hlp : {n : ℕ} → {trm1 trm2 : Term} -> (arity : Arity' trm1 ≡ + suc n) -> (isc : isCombinator trm1 ≡ true) -> trm1 · trm2 ≢ Substitute n (AppFold {suc n} trm1 {arity}{isc}) trm2
Step-def-hlp {n} {Λ .n Self} {Self} refl refl () -- =  {!!}
--Step-def-hlp {Λ .0 Self} {(! n)} refl refl = λ x → {!!}
--Step-def-hlp {Λ .0 Self} {` x} refl refl = λ x → {!!}
--Step-def-hlp {Λ .0 Self} {Λ n trm2} refl refl = λ x → {!!}
--Step-def-hlp {Λ .0 Self} {trm2 · trm3} refl refl = λ x → {!!}
--Step-def-hlp {Λ .0 (! n)} {trm2} refl refl = λ x → {!!}
--Step-def-hlp {Λ .0 (` x)} {trm2} refl refl = λ x → {!!}
--Step-def-hlp {Λ .0 (Λ n trm1)} {trm2} refl refl = λ x → {!!}
--Step-def-hlp {Λ .0 (trm1 · trm3)} {trm2} refl refl = λ x → {!!}
Step-def-hlp {n} {trm1 · trm1'} {trm2} arity isc x = {!!}
--⊥-elim (Step-def-hlp-hlp {!!})
                      where
                       Step-def-hlp-hlp : trm1 · trm1' ≢ Substitute (suc n) (AppFold {suc (suc n)} trm1 {(trans (sym suc'Pred'-id) (cong (λ w → suc' w) arity))}{∧-elim-left isc}) trm1'
                       Step-def-hlp-hlp = Step-def-hlp {suc n} {trm1}{trm1'} (trans (sym suc'Pred'-id) (cong (λ w → suc' w) arity)) (∧-elim-left isc)  
                       Step-def-hlp-contra :  trm1 · trm1' ≡ Substitute (suc n) (AppFold {suc (suc n)} trm1 {(trans (sym suc'Pred'-id) (cong (λ w → suc' w) arity))}{∧-elim-left isc}) trm1'
                       Step-def-hlp-contra = Substitute-lemma x


Step-def-hlp3 : {n : ℕ} → {trm1 trm2 trm' : Term} -> (arity : Arity' trm1 ≡ + suc n) -> (isc : isCombinator trm1 ≡ true) -> trm1 · trm2 ≡ Substitute zero trm' trm2 → trm' ≡ trm1 · (` 0)  ⊎ trm' ≡ trm1 · trm2 
Step-def-hlp3 {.m} {Λ m trm1'} {trm2} {` zero} refl isc tts = ⊥-elim (trm·trm-lemma tts)
Step-def-hlp3 {.m} {Λ m trm1'} {trm2} {` suc x} refl isc ()
Step-def-hlp3 {.m} {Λ m trm1'} {trm2} {trm' · trm''} refl isc tts = {!!}
Step-def-hlp3 {n} {trm1 · trm3} {trm2} {trm'} arity isc tts = {!!} 

Step-def : {trm trm' : Term} → Step trm trm' → trm ≢ trm'
Step-def {Self} {trm'} (Λ-step isl isl' stp) = ⊥-elim (false≡true→⊥ isl)
Step-def {Λ n trm {scoping}} {Λ m trm' {scoping'}} (Λ-step isl isl' stp) =  λ x → Step-def stp (Λtrm1≡Λtrm2→trm1≡trm2 x)
Step-def {trm1 · trm2} {(trm1' · trm2)} (left-step stp) = λ x → Step-def stp (·-elim-left {trm1}{trm2}{trm1'}{trm2} x)
Step-def {trm1 · trm2} {(trm1 · trm2')} (right-step stp) = λ x → Step-def stp (·-elim-right x)
Step-def {trm1 · trm2} {.(AppFold (trm1 · trm2))} (appFold arity isc) with ℕ-Dec (Arity (Substitute zero (AppFold {1} trm1 {Suc'Pred'≡ arity}{∧-elim-left isc}) trm2)) 0 
... | no x = λ w → x {!!}
... | yes x = λ w → {!!} 
-- sym' (Application-Count≢ {Substitute zero (AppFold trm1) trm2} {trm1} {trm2} (Application-Count-Sub {trm1}{trm2}  (Suc'Pred'≡ arity) (∧-elim-left isc))) 
           where


             hlp2 : Arity' trm1 ≡ + 1 
             hlp2 = Suc'Pred'≡ arity
             hlp3 : Application-Count (Substitute 1 (AppFold {1} trm1 {hlp2}{∧-elim-left isc}) trm2) <= Application-Count ((AppFold {1} trm1 {hlp2}{∧-elim-left isc})) ≡ true
             hlp3 = AppFold-Count-lemma-ind {1} {(AppFold {1} trm1 {hlp2}{∧-elim-left isc})} {trm2} (Suc'Pred'≡ {!arity!})
             hlp5 : Application-Count ((AppFold {1} trm1 {hlp2}{∧-elim-left isc})) <= (Application-Count trm1) ≡ true
             hlp5 = {!!}
             hlp4 : (Application-Count (Substitute 1 (AppFold {1} trm1 {hlp2}{∧-elim-left isc}) trm2) <= Application-Count trm1) ≡ true
             hlp4 = trans<= { Application-Count (Substitute 1 (AppFold {1} trm1 {hlp2}{∧-elim-left isc}) trm2)}
                            { Application-Count ((AppFold {1} trm1 {hlp2}{∧-elim-left isc}))} {Application-Count trm1} hlp3 hlp5 
             hlp : Substitute 1 (AppFold {1} trm1 {hlp2}{∧-elim-left isc}) trm2 ≢ trm1 · trm2
             hlp = Application-Count≢ hlp4 

-- AppFold-Count-lemma-ind : {n : ℕ} → {trm trm' : Term} → (scoping : Arity' trm ≡ (+ n)) → (Application-Count (Substitute n trm trm')) <= Application-Count trm ≡ true
--AppFold-Count-lemma-ind {n} {trm}{trm'} scoping = {!!}  

--------------------
-- Applying Steps --
--------------------

ApplyStep : (trm : Term) → {trm' : Term n} → (Step trm trm') → Term 
ApplyStep trm {trm'} stp' = trm'


-- That constants can be turned into variables by a function and that this commutes with Step:

Constants? : Term 0 → ℕ
Constants? trm = {!!}

Constants→Variables : Term 0 → Σ[ n ∈ ℕ ] Term n
Constants→Variables trm = {!!}

Strategy : Set
Strategy = {n : ℕ} → {trm : Term n} → Dec (Σ[ x ∈ Term n ] (Step trm x))

---------------------------------------------------------------
-- That SKI combinatorial logic is embedded in this calculus --
--                Turing Completeness results                --
---------------------------------------------------------------


-- It is also shown that the combinators S, K and I act as they should.
-- We therefore have a Turing complete calculus.

S* : Term 0
S* = proj₁ S

K* : Term 0
K* = proj₁ K

I* : Term 0
I* = proj₁ I

I*-proof : {n : ℕ} → {x : Term 0} → (trm' : Term 0) → Step (I* · x) trm' → (trm' ≡ x) ⊎ (trm' ≡ proj₁ (Σ[ x' ∈ Term 0 ] (I* · x'))) 
I*-proof {n} {x} .(_ · x) (left-step step) = {!!}
I*-proof {n} {x} .(I* · _) (right-step step) = {!!}
I*-proof {n} {x} .(Substitute I* x {arity1} ) (application .x arity1) = {!!}


ArityR2 : Arity (proj₁ R2) ≡ 2
ArityR2 = refl

R2-step1 : Step ((proj₁ R2) · (proj₁ K)  · (proj₁ I))  (((Λ {1} (` 1))) · (proj₁ K)) 
R2-step1 = application {(proj₁ R2) · (proj₁ K)} (proj₁ I) refl

R2-step2 : Step ((((Λ {1} (` 1))) · (proj₁ K)) · (proj₁ I))  (proj₁ K)
R2-step2 = application {(((Λ {1} (` 1))) · (proj₁ K))} (proj₁ I) refl 



Self-≡ : {self' : Term 1} → (legit : Step Self self' ) → Self ≡ self'
Self-≡ {self'} ()

Self-≡R  : {trm' : Term 1} → (legit : StepR Self trm' ) → Self ≡ trm'
Self-≡R {Self} (reflexive .Self) = refl
Self-≡R {Self} (transitive legit1 legit2) = refl
Self-≡R {` .0} (transitive legit1 legit2) =  {!!}
Self-≡R {  trm'} (transitive legit1 legit2) = {!!}
Self-≡R {trm' · trm''} (transitive legit1 legit2) = {!!}





One-Step : {n : ℕ} → Term n → Maybe (Term n)
One-Step {.(suc x)} (` x) = nothing
One-Step {.0} (! index) = nothing
One-Step {.0} (Λ trm) with One-Step trm 
...                     | nothing = nothing
...                     | just (` x) = just (Λ (` x))
...                     | just (  x) = just (Λ (  x))

...                     | just (x1 · x2) = just (Λ  (x1 · x2))
One-Step {.(suc _)} (  trm) with One-Step trm 
...                     | nothing = nothing
...                     | just x = just (  x) 
One-Step {n} (trm1 · trm2) with Is Term? {n} {trm1} | Is Term? {n} {trm2}
One-Step {n} (trm1 · trm2) | no x  | _ with (One-Step trm1)                               -- left-most trm1 not a combinator, so try to reduce it
One-Step {n} (trm1 · trm2) | no x  | _ | just trm1' = just (trm1' · trm2)                   -- success: non-combinator trm1 reduced
One-Step {n} (trm1 · trm2) | no x  | _ | nothing with (One-Step trm2)                       -- failure: so try to reduce trm2
...                                               | just trm2' = just (trm1 · trm2')          -- success: trm2 reduced
...                                               | nothing = nothing                         -- failure: no redex
One-Step {n} (trm1 · trm2) | yes x | no y with (One-Step trm2)                            -- left-most trm1 is a combinator but trm2 is not, so try to reduce trm2 
...                                        | just trm2' = just (trm1 · trm2')               -- success: trm2 reduced
...                                        | nothing with (One-Step trm2)                   -- failure: try to reduce combinator trm1
...                                                  | just trm1' = just (trm1' · trm2)       -- success: trm1 reduced
...                                                  | nothing = nothing                      -- failure: no redex 
One-Step {n} (trm1 · trm2) | yes x | yes y with  Termy (↓↓ x) (↓↓ y) {↓↓' x} {↓↓' y} -- try applying trm2 to trm1 (as both are combinators)
...                                        | just z = just (z    _)                         -- success: resulting combinator is lifted up to scope      
...                                        | nothing with One-Step trm1                     -- failure : try reducing left combinator 
...                                                   | just trm1' = just (trm1' · trm2)      -- success: trm1 reduced           
...                                                   | nothing with One-Step trm2            -- failure: try reducing trm2
...                                                         | just trm2' = just (trm1 · trm2')  -- success: trm2 reduced 
...                                                         | nothing = nothing                 -- failure: no redex

-------------------------------



--left-step-inv : {n : ℕ} → {trm1 : Term n} → {trm2 : Term n} → {trm1' : Term n} → Step (trm1 · trm2) (trm1' · trm2) → Step trm1 trm1' 
--left-step-inv {n}{trm1}{trm2}{trm1'} lm = {!!} -- problematic


Λ-step-lemma : {n : ℕ} → {trm : Term (suc n)} → {trm' : Term (suc n)} → One-Step trm ≡ just trm' → One-Step (Λ trm) ≡ just (Λ trm')
Λ-step-lemma {n}{trm}{trm'} ost with One-Step trm in os 
...                             | just (` .n) = cong (λ x → just (Λ x)) (Just-elim ost)
...                             | just (  x) =  cong (λ x → just (Λ x)) (Just-elim ost)
...                             | just (x1 · x2) = cong (λ x → just (Λ x)) (Just-elim ost)
...                             | nothing = ⊥-elim (nothing≢just ost)  

Λ-step-neg-lemma : {n : ℕ} → {trm : Term (suc n)} → {trm' : Term (suc n)} → ¬ (One-Step trm ≡ just trm') → ¬ (One-Step (Λ trm) ≡ just (Λ trm'))
Λ-step-neg-lemma {n}{trm}{trm'} ost with One-Step trm in os
...                                 | nothing = λ x → nothing≢just x
...                                 | just (` .n) = λ x → ost {!!}
...                                 | just (  w)  = {!!}
...                                 | just (w · w₁) = {!!}

Λ-step-lemma' : {n : ℕ} → {trm : Term (suc n)} → {trm' : Term (suc n)} → One-Step (Λ trm) ≡ just (Λ trm') → One-Step trm ≡ just trm'
Λ-step-lemma' {n}{trm}{trm'} ost = {!!}

!≢Λ-lemma : {index m : ℕ} {trm : Term (suc m)} → (! index) ≡ (Λ trm) → ⊥
!≢Λ-lemma {index}{m}= λ ()


-- In the case One-Step trm reduces, is it legit?
mutual
 One-Step-legit : ∀ {n : ℕ} {trm : Term n} → (step-occurs : Σ[ z ∈ Term n ] (One-Step {n} trm ≡ just z)) → Step {basis} {n} trm (proj₁ step-occurs)
 One-Step-legit {.0} {Λ {m} trm} (! index , OSJ) with One-Step trm in ost
 ...                  | nothing = ⊥-elim (nothing≢just OSJ)  
 ...                  | just trm' = ⊥-elim (step3 step4)
                            where
                              Step1 : (One-Step (Λ {m} trm)) ≡ just (! index) 
                              Step1 rewrite ost = OSJ
                              Step2 : One-Step (Λ {m} trm) ≡ just (Λ {m} trm')
                              Step2 = Λ-step-lemma {m} {trm}{trm'} ost
                              step3 : just (! index) ≢ just (Λ trm')
                              step3  = λ x → !≢Λ-lemma (Just-elim x)
                              step4 : just (! index) ≡ just (Λ trm')
                              step4 = trans (sym Step1) Step2
 One-Step-legit {.0} {Λ {n} trm} (Λ {m} z , OSJ) with ℕ-Dec n m 
 ... | no x = {!!}
 ... | yes x = change-scope-step x (Λ-step (Λ-step-inv (One-Step-justΛ-lemma x OSJ)))
 One-Step-legit {.0} {Λ trm} (z1 · z2 , OSJ) = {!!}
 One-Step-legit {.(suc _)} {  trm} (z , OSJ) = {!!}
 One-Step-legit {n} {trm1 · trm2} (z , OSJ) = {!!}

 One-Step-justΛ-lemma : {n m : ℕ} → {trm : Term (suc n)} → {z : Term (suc m)} → (nm : n ≡ m) → (eqn : One-Step (Λ trm) ≡ just (Λ z)) →  Step (Λ (change-scope trm (cong (λ x → suc x) nm))) (Λ z)
 One-Step-justΛ-lemma {n} {.n} {trm} {z} refl eqn = Λ-step (One-Step-legit {suc n} {trm} (z , (Λ-step-lemma' {n} {trm} {z} eqn)))




 {.0} {Λ {m} trm} (ltrm' , OSJ) with  One-Step trm in os1 | One-Step (Λ {m} trm) in os2
...                                              | nothing   | just _ = {!!}
...                                              | just trm' | nothing = {!!}
One-Step-legit {_} {Λ {m} trm} (ltrm' , OSJ)     | just trm' | just (! index) = {!!}
One-Step-legit {_} {Λ {m} trm} (ltrm' , OSJ)     | just trm' | just (Λ ltrm'') = {!!}
                                                 where
                                                      hlp : Step {0} (Λ {m} trm) (Λ {m} trm')
                                                      hlp = Λ-step (One-Step-legit (trm' , os1))
                                                      --    hlp2 : just ltrm'2 ≡ One-Step (Λ {m} trm')
                                                      --    hlp2 = {!!}
                                                      hlp4 : One-Step (Λ trm') ≡ just (Λ {m} {!!}) 
                                                      hlp4 = {!!}
                                                     -- hlp5 : ltrm'2 ≡ ltrm'
                                                     -- hlp5 = Just-elim {!!}

                                                      hlp3 : Step {0} (Λ {m} trm) (ltrm')
                                                      hlp3 = {!!}
One-Step-legit {_} {Λ {m} trm} (ltrm' , OSJ)     | just trm' | just (ltrm'2 · ltrm'3) = {!!}

                                                           
One-Step-legit {.(suc _)} {  trm} (z , OSJ) = {!!}
One-Step-legit {n} {trm1 · trm2} (z , OSJ) = {!!}   

-------------------------------

-- Tries upto n steps until no further progress can be made
do-n-Steps : (steps : ℕ) → {n : ℕ} → Term n → Maybe (Term n)
do-n-Steps 0 trm = just trm
do-n-Steps (suc n') trm with One-Step trm -- do-n-Steps (suc n') trm
...                            | nothing = just trm
...                            | just trm' = do-n-Steps n' trm'


data Equal : {n m : ℕ} → {trm1 : term n} -> {trm2 : term m} → Is Term trm1 → Is Term trm2 → Set with
  refl-eq : {n m : ℕ} → (trm1 : term n} → (trm1 : term m} → (isc : Is Term trm1) → (isc' : Is Term trm2) → (↓↓ trm1) ≡ (↓↓ trm2) → Equal isc isc'
  ext-eq : {n m : ℕ} → (trm1 : term n} → (trm1 : term m} → (isc : Is Term trm1) → (isc' : Is Term trm2) → (↓↓ trm1) arg) (↓↓ trm2) 

=<-hlp : {x : ℕ} → (mbtrm : Maybe (Σ[ y ∈ ℕ ] Term y)) → (trm : Term x) → Bool
=<-hlp {x} (just (y' , trm')) trm = y' <= (Scope trm)
=<-hlp {x} nothing trm = true

=<ℕ-hlp : (mbtrm : Maybe (Σ[ y ∈ ℕ ] Term y)) → (m : ℕ) → Bool
=<ℕ-hlp (just (x' , trm')) m = x' <= m
=<ℕ-hlp nothing m = true

=<ℕ-hlp-postulate : {n m : ℕ} → {trm1 : Term n} → {trm2 : Term m} → {proof : IsTerm0 (trm1 · trm2)} → (ineq :  Termy proof ≢ nothing) → Scope' ( Termy proof) ≡ just 0
=<ℕ-hlp-postulate {n} {m} {trm1} {trm2} {prf .(trm1 · trm2) {eqn}} ineq with  Termy (prf  (trm1 · trm2) {eqn}) in comb 
...                                     | nothing = ⊥-elim (ineq refl)
...                                     | just y = {!!}

=<ℕ-hlp-lemma : {n m : ℕ} → {trm1 : Term n} → {trm2 : Term m} → (proof : IsTerm0 (trm1 · trm2)) → =<ℕ-hlp ( Termy proof) 0 ≡ true
=<ℕ-hlp-lemma {n}{m}{trm1}{trm2} proof with  Termy proof in eq 
...                                    | nothing = refl
=<ℕ-hlp-lemma {n}{m}{trm1}{trm2} proof | just (x' , trm') = {!!}

=<ℕ-hlp-lemma-hlp :  {n m : ℕ} → {trm : Term n} → {trm' : Term m} → (proof : IsTerm0 (trm · trm')) → (mbtrm : Maybe (Σ[ y ∈ ℕ ] Term y)) → (mbtrm ≡  Termy proof)->  =<ℕ-hlp mbtrm 0 ≡ true
=<ℕ-hlp-lemma-hlp {n} {m} {trm} {trm'} (prf .(trm · trm') {eqn}) .( Termy (prf (trm · trm'))) refl = {!!}

data _=<_ : {x : ℕ} → (mbtrm : Maybe (Σ[ y ∈ ℕ ] Term y)) → Term x → Set where
  prf : {x : ℕ} → {mbtrm : Maybe (Σ[ y ∈ ℕ ] Term y)} → {trm : Term x} → (proof : (=<-hlp mbtrm trm) ≡ true) → (_=<_) mbtrm trm 

data _=<ℕ_ : (Maybe (Σ[ y ∈ ℕ ] Term y)) → (m : ℕ) → Set where
  prf : (mbtrm : Maybe (Σ[ y ∈ ℕ ] Term y)) → (m : ℕ) -> (proof : (=<ℕ-hlp mbtrm m) ≡ true) → (_=<ℕ_) mbtrm m  

 Termy-lemma : {n arg0 : ℕ} → {trm : Term n} → {arg : Term arg0} → (proof : IsTerm0 (trm · arg)) → ( Termy proof) =<ℕ 0 
 Termy-lemma {zero} {zero} {trm} {arg} proof = prf ( Termy proof) 0 (=<ℕ-hlp-lemma proof)
 Termy-lemma {suc n} {zero} {trm} {arg} proof = ⊥-elim (¬Term0 trm (· Terms-left proof))
 Termy-lemma {zero} {suc arg0} {trm} {arg} proof = prf ( Termy proof) 0 (=<ℕ-hlp-lemma proof)
 Termy-lemma {suc n} {suc arg0} {trm} {arg} proof = ⊥-elim (¬Term0 trm (· Terms-left proof))

 
One-StepΛ-lemma : {x : ℕ}  → (trm : Term (suc x)) -> (One-Step (Λ trm)) =<ℕ 0
One-StepΛ-lemma {x} trm = prf (One-Step (Λ trm)) 0 {!!}

One-Step-Monotonic-hlp1 : {x x' : ℕ} -> {y : Fin x'} -> {trm : Term x} -> One-Step trm ≡ just (x' , ` y) -> (x' <= Scope trm) ≡ true
One-Step-Monotonic-hlp1 {.0} {x'} {y} {Λ trm} onestep = {!!}
One-Step-Monotonic-hlp1 {.(Scope trm1 ⊔ Scope trm2)} {x'} {y} {trm1 · trm2} onestep = {!!}
One-Step-Monotonic-hlp1 {.(suc _)} {x'} {y} {  trm'} onestep = {!!}

One-Step-Monotonic :  {x : ℕ} → (trm : Term x) → (One-Step trm) =< trm 
One-Step-Monotonic {x} trm with (One-Step {Scope trm} trm) in onestep 
...                     | nothing = prf refl
...                     | just (x' , ` y) = prf {!!}
...                     | just (.0 , ! index) = prf refl
...                     | just (.0 , Λ trm') = prf refl
...                     | just (.(Scope trm' ⊔ Scope trm'') , trm' · trm'') = prf {!!}
...                     | just (.(suc (Scope trm')) , (  trm')) = prf {!!}

One-Step-Mono :  {x : ℕ} → (trm : Term x) → (One-Step trm) =< trm
One-Step-Mono {x} (` y) with (Is-nothing (One-Step (` y)))
...                     | _ = prf refl
One-Step-Mono {.0} (! index) with (Is-nothing (One-Step (! index)))
...                     | _ = prf refl
One-Step-Mono {.0} (Λ trm) with (One-Step (Λ trm)) in trm'-eq
...                        | nothing = prf refl 
...                        | just (x' , trm') with (((suc (Scope trm)) ∸ x')) in eq 
One-Step-Mono {.0} (Λ trm) | just (x' , trm') | 0 = prf {!!}
...                                           | suc d =  {!!} 
One-Step-Mono {.(Scope trm1 ⊔ Scope trm2)} (trm1 · trm2) = {!!}
One-Step-Mono {.(suc (Scope trm'))} (  trm') with (One-Step (  trm')) in trms-eq
One-Step-Mono {.(suc (Scope trm'))} (  trm') | nothing = prf refl
One-Step-Mono {.(suc (Scope trm'))} (  trm') | just (x' , trm'') = prf {!!}

-- A single reduction for combinators only, including the case where the reduction remains unchanged
Reduce : (trm :  Term) →  Term
Reduce trm with (One-Step trm) -- {!!}
Reduce trm | nothing = trm
Reduce trm | just (zero , trm') = trm'
Reduce trm | just (suc x' , trm') =  {!!}

test-combinators : One-Step (K · I · S) ≡ just (0 , I)
test-combinators = refl
-}


-}
-}




----------------------------------------

--main : IO ⊤
--main = putStrLn "Hello world!"



-}
