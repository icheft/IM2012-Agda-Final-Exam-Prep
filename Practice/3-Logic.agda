module 3-Logic where

-- In this practical we play around with Curry-Howard
-- isomorphism in Agda.

-- Implication is encoded by function space.

I : {P : Set} → P → P
I = {!   !}

K : {P Q : Set} → P → (Q → P)
K = {!   !}

S : {P Q R : Set} → (P → Q → R) → (P → Q) → P → R
S = {!   !}

-- True is encoded by the type ⊤, a type with exactly
-- one component tt.

data ⊤ : Set where
  tt : ⊤

-- False is represented by ⊥, a type having no terms.

data ⊥ : Set where

-- Negation of P is P → False.

¬ : Set → Set
¬ P = P → ⊥

-- Conjunction P ∧ Q is encoded by a pair P × Q.

data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

infixr 4 _,_
infixr 2 _∧_

fst : {A B : Set} → A ∧ B → A
fst (x , y) = x

snd : {A B : Set} → A ∧ B → B
snd (x , y) = y

-- Disjunction P ∨ Q is encoded by the sum type.

data _∨_ (A B : Set) : Set where
  inj₁ : A → A ∨ B
  inj₂ : B → A ∨ B

infixr 1 _∨_

-- Exercises from your Logic class!

∨-comm : {A B : Set} → (A ∨ B) → (B ∨ A)
∨-comm = {!   !}
  -- ∨ "\ v e e"      "\ o r"
  -- ∧ "\ w e d g e"  "\ a n d"

∧-comm : {A B : Set} → (A ∧ B) → (B ∧ A)
∧-comm = {!   !}

→-∨-weakening-r : {A B C : Set} → (A → B) → (A → (B ∨ C))
→-∨-weakening-r = {!   !}

→-∨-weakening-l : {A B C : Set} → ((A ∨ C) → B) → (A → B)
→-∨-weakening-l = {!   !}

→-∧-weakening-r1 : {A B C : Set} → (A → (B ∧ C)) → (A → B)
→-∧-weakening-r1 = {!   !}

→-∧-weakening-r2 : {A B C : Set} → (A → (B ∧ C)) → (A → C)
→-∧-weakening-r2 = {!   !}

→-∧-distr : {A B C : Set}
          → (A → (B ∧ C)) → ((A → B) ∧ (A → C))
→-∧-distr = {!   !}

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

resol : {A B : Set} → ((A ∨ B) ∧ ¬ B) → A
resol = {!   !}

¬¬ex-middle : {A : Set} → ¬ (¬ (A ∨ ¬ A))
¬¬ex-middle f = f (inj₂ (λ a → f (inj₁ a)))

{- However, we cannot prove that:

ex-middle : {A : Set} → A ∨ (¬ A)
ex-middle = ?
-}

A→¬¬A : {A : Set} → A → ¬ (¬ A)
A→¬¬A = {!   !}


{- However, we cannot prove that:

¬¬A→A : {A : Set} → ¬ (¬ A) → A
¬¬A→A = ?
-}

demorgan : {A B : Set} → (¬ A ∨ ¬ B) → ¬ (A ∧ B)
demorgan = {!   !}

{- However, we cannot prove that

demorgan' : {A B : Set} → ¬ (A ∧ B) → (¬ A ∨ ¬ B)
demorgan' = ?

-}

contra : {A B : Set} → (A → B) → (¬ B → ¬ A)
contra = {!   !}

{- However, we cannot prove that

contra' : {A B : Set} → (¬ B → ¬ A) → (A → B)
contra' = ?
-}

-- Some exercises from MLTT...

-- Π type.
  -- Π (x : A) B
  -- (x : A) → B

flip : {A B : Set} {C : A → B → Set}
     → ((x : A) → (y : B) → C x y)
     → (y : B) → (x : A) → C x y
flip = {!   !}

-- Recall Bool and ℕ, to be used in examples later.

data Bool : Set where
  false : Bool
  true : Bool

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


-- 以下為出現在 Σ 之後的，但不知道會不會考

→-∧-distr⇒ : {A : Set} {B C : A → Set}
          → ((x : A) → (B x ∧ C x))
          → ((y : A) → B y) ∧ ((z : A) → C z)
→-∧-distr⇒ = {!   !}

→-∧-distr⇐ : {A : Set} {B C : A → Set}
          → ((y : A) → B y) ∧ ((z : A) → C z)
          → ((x : A) → (B x ∧ C x))
→-∧-distr⇐ = {!   !}


→-∨-distr⇐ : {A : Set} {B C : A → Set}
           → ((y : A) → B y) ∨ ((z : A) → C z)
           → ((x : A) → (B x ∨ C x))
→-∨-distr⇐ = {!   !}

-- Can this be proved?
→-∨-distr⇒ : {A : Set} {B C : A → Set}
           → ((x : A) → (B x ∨ C x))
           → ((y : A) → B y) ∨ ((z : A) → C z)
→-∨-distr⇒ = {!   !}


absorb : {A B : Set} → (A ∧ (¬ A ∨ B)) → (A ∧ B)
absorb = {!   !}

∨-∧-distr : {A B C : Set} → (A ∨ (B ∧ C)) → (A ∨ B) ∧ (A ∨ C)
∨-∧-distr = {!   !}

∀mono : {A : Set} {P Q : A → Set}
      → ((x : A) → P x → Q x) → ((x : A) → P x)
      → (x : A) → Q x
∀mono = {!   !}
