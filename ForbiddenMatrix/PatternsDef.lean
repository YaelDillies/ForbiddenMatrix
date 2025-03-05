import Mathlib.LinearAlgebra.Matrix.Permutation

set_option linter.unusedTactic false
set_option maxHeartbeats 800000

open Finset Set
open OrderDual
open Equiv
--open Fin
attribute [local irreducible] OrderDual

-- def trivialPattern : (α → β → Prop) := [1, 1, 1]
-- λ x : nat ↦ x + 5
-- variable {n : ℕ }
-- ![![a, b, c], ![b, c, d]] : matrix (fin 2) (fin 3) α
-- see https://leanprover-community.github.io/theories/linear_algebra.html
-- λ (i : m) (j : n), (_ : α)
def HatPattern : Fin 2 → Fin 3 → Prop :=
  ![
    ![false, true, false],
    ![true, false, true]
   ]
def HatPatternD : Fin 3 → Fin 2 → Prop :=
  ![
    ![true, false],
    ![false, true],
    ![true, false]
   ]
def VerticalTwoPattern : Fin 2 → Fin 1 → Prop :=
  ![
    ![true],
    ![true]
   ]
def Horizontal2Pattern : Fin 1 → Fin 2 → Prop := ![![true, true]]
def Horizontal3Pattern : Fin 1 → Fin 3 → Prop := ![![true, true, true]]


def Horizontal3Patternt : Fin 1 → Fin 3 → Fin 2 := ![![1, 1, 1]]
--def HatPatternFin: Fin 2 → Fin 3 → Bool :=
-- ![
--   ![0, 1, 0],
--   ![1, 0, 1]
--  ]
--#check HatPatternFin
def IdentityFin (n : ℕ) (i j : Fin n) : Fin 2 := if i = j then 1 else 0


def horizontalkPattern (k : ℕ) (_ :Fin 1) (_ : Fin k) : Prop := true
def verticalkPattern (k : ℕ) (_ :Fin k) (_ : Fin 1) : Prop := true
def identityPattern (n : ℕ) (i j : Fin n) : Prop := i = j
def revIdentityPattern (n : ℕ) (i j : Fin n) : Prop := i + j = n
--def IdentityF (n : ℕ) (i j : Fin n) : Fin 2 := (i = j :)
def Perm (k : ℕ) (i j : Fin k) : Prop := i = j
def onePattern : Fin 1 → Fin 1 → Prop := fun _ : Fin 1 => fun _ : Fin 1 => true
def IdentityB (n : ℕ) (i j : Fin n) : Bool := i = j
def PatternOneB : Fin 1 → Fin 1 → Bool := fun _ : Fin 1 => fun _ : Fin 1 => true


--variable {α : Type*} [Preorder α]
--open scoped Classical in noncomputable
--def permPatternFin {k : ℕ} (σ : Equiv.Perm (Fin k)) := Equiv.Perm.permMatrix (Fin 2) σ

--def f : Fin 3 → Fin 3 := ![0, 2, 1 : Fin 3]

def permPatternFin {k : ℕ} (σ : Equiv.Perm (Fin k)) (i j : Fin k): Fin 2 :=
  Equiv.Perm.permMatrix (Fin 2) σ i j

def permPattern {k : ℕ} (σ : Equiv.Perm (Fin k)) (i j : Fin k): Prop :=
  Equiv.Perm.permMatrix ℕ σ i j = 1

--def identity (k :ℕ) (i : Fin k) : Fin k := i
--#eval  (One (Fin 2))
--def f : Fin 2 → Fin 2 := ![0, 1]
def permid : Equiv.Perm (Fin 3) := Equiv.refl (Fin 3)
