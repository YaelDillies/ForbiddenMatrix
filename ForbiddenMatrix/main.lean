import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Lattice
import Mathlib.Logic.Equiv.Fin

namespace Finset
variable {ι α : Type*} [CanonicallyLinearOrderedAddCommMonoid α] {s : Finset ι} {f : ι → α}

@[simp] lemma sup_eq_zero : s.sup f = 0 ↔ ∀ i ∈ s, f i = 0 := by simp [← bot_eq_zero']

end Finset

open Finset

section Contains
variable {α β γ δ : Type*} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]

def Contains (P : α → β → Prop) (M : γ → δ → Prop) : Prop :=
  ∃ f : α → γ, StrictMono f ∧ ∃ g : β → δ, StrictMono g ∧ ∀ a b, P a b → M (f a) (g b)

def ContainsB (P : α → β → Bool) (M : γ → δ → Bool) : Prop :=
  ∃ f : α → γ, StrictMono f ∧ ∃ g : β → δ, StrictMono g ∧ ∀ a b, P a b → M (f a) (g b)

instance [Fintype α] [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : γ → γ → Prop)] {f : α → γ} :
  Decidable (StrictMono f) := inferInstanceAs (Decidable (∀ _ _, _ → _))

instance {P : α → β → Bool} {M : γ → δ → Bool}
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    [DecidableRel (· < · : γ → γ → Prop)] [DecidableRel (· < · : δ → δ → Prop)]
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [DecidableEq α] [DecidableEq β] :
    Decidable (ContainsB P M) :=
  inferInstanceAs (Decidable (∃ f : α → γ, StrictMono f ∧ ∃ g : β → δ, StrictMono g ∧ ∀ a b, P a b → M (f a) (g b)))

/- lemma reflectContain (M : γ → δ → Prop) : Contains M M :=
  ⟨_,_⟩
example (a b : ℕ ) : a + a *b = (b+1) * a := by
  rw [Nat.right_distrib]
-/
end Contains

variable {α β : Type*} [Preorder α] [Preorder β]
open scoped Classical in noncomputable def exRect (P : α → β → Prop) (n : ℕ) (m : ℕ) : ℕ :=
  sup {M : Fin n → Fin m → Prop | ¬ Contains P M} fun M ↦ card {(i,j): Fin n × Fin m | M i j}

def exRectB [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    (P : α → β → Bool) (n : ℕ) (m : ℕ) : ℕ :=
  sup {M : Fin n → Fin m → Bool | ¬ ContainsB P M} fun M ↦ card {ij : Fin n × Fin m | M ij.1 ij.2}

open scoped Classical in noncomputable def ex (P : α → β → Prop) (n : ℕ)  : ℕ := exRect P n n

def exB [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    (P : α → β → Bool) (n : ℕ) : ℕ :=
  exRectB P n n

-- def trivialPattern : (α → β → Prop)  := [1,1,1]
-- λ x : nat ↦ x + 5
-- variable {n : ℕ }
def Identity (n : ℕ ) (i j : Fin n) : Prop := i = j
def TwoOneY  (i _ : Fin 2) : Prop := i = 0
def PatternOne : Fin 1 → Fin 1 → Prop :=  fun _ : Fin 1 =>  fun _ : Fin 1 => true

def IdentityB (n : ℕ ) (i j : Fin n) : Bool := i = j
def PatternOneB : Fin 1 → Fin 1 → Bool :=  fun _ : Fin 1 =>  fun _ : Fin 1 => true

-- example : PatternOne = (Identity 1) := by

-- #eval exB PatternOneB 4
-- #eval exB (IdentityB 2) 4

lemma PatternOneIsIdentity : PatternOne = (Identity 1) := by
  ext -- apply function extensionality for all a F(a) = G(a) => F = G
  simp [Identity,PatternOne]
  exact Subsingleton.elim ..

lemma exPatternOne (n : ℕ ): ex PatternOne n = 0 := by
  rw [ex]
  rw [exRect]
  simp [filter_eq_empty_iff]
  intro M
  contrapose
  simp
  intro i j Mij
  simp [Contains]
  refine ⟨fun _ ↦ i, by simp [StrictMono], ![j], by simp [StrictMono], by simp [Mij]⟩

example (n : ℕ) : ex (Identity 1) n = 0 := by
    rw [← PatternOneIsIdentity]
    exact exPatternOne n

set_option diagnostics true
theorem exIdentity2 (n : ℕ) : ex (Identity 2) n ≤ 2 * n - 1 := by
  classical
  rw [ex]
  rw [exRect]
  simp
  intro M
  contrapose
  simp
  intro M_has_two_n_points

  let f : Fin n × Fin n → ℤ := fun ⟨i, j⟩ ↦ i - j
  let s : Finset (Fin n × Fin n) := {(i, j) : Fin n × Fin n | M i j}
  let t : Finset ℤ := Icc (-n + 1) (n - 1)
  let k := 1

  have hf ⦃a⦄ (ha : a ∈ s) : f a ∈ t := by simp [f, t]; omega

  have hn : t.card * k < s.card := by
    simp [k, s, t]
    cases n
    · contradiction
    simp
    rw [← Nat.cast_add_one, ← Nat.cast_add, Int.toNat_ofNat]
    omega

  have := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hn
  sorry

example (n k : ℕ) : ex (Identity k) n ≤ (2*n-1)*k := by sorry
