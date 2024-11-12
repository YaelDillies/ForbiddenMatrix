import ForbiddenMatrix.Containment
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Lattice

open Finset

variable {α β γ δ : Type*} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] {n m :ℕ}

open scoped Classical in
noncomputable def densityRect (M : Fin n → Fin m → Prop) : ℕ := #{(i, j) : Fin n × Fin m | M i j}

open scoped Classical in
noncomputable def density {n:ℕ} (M : Fin n → Fin n → Prop) : ℕ := #{(i, j) : Fin n × Fin n | M i j}

open scoped Classical in noncomputable
def row_density {n:ℕ } (M : Fin n → Fin n → Prop) (i : Fin n): ℕ := #{j | M i j}

open scoped Classical in noncomputable def exRect (P : α → β → Prop) (n : ℕ) (m : ℕ) : ℕ :=
  sup {M : Fin n → Fin m → Prop | ¬ contains P M} fun M ↦ densityRect M

def exRectB [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    (P : α → β → Bool) (n : ℕ) (m : ℕ) : ℕ :=
  sup {M : Fin n → Fin m → Bool | ¬ containsB P M} fun M ↦ # {ij : Fin n × Fin m | M ij.1 ij.2}

open scoped Classical in noncomputable
def ex (P : α → β → Prop) (n : ℕ) : ℕ := sup {M : Fin n → Fin n → Prop | ¬ contains P M} density

def exB [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    (P : α → β → Bool) (n : ℕ) : ℕ :=
  exRectB P n n

@[simp] lemma avoid_le_ex {n : ℕ} {P : α → β → Prop} (M : Fin n → Fin n → Prop) (AvoidP : ¬ contains P M)
: density M ≤ ex P n := by
  rw [ex]
  apply le_sup
  simpa only [mem_filter, Finset.mem_univ, true_and]

@[simp] theorem le_ex_iff (P : α → β → Prop) (P_nonempty : ∃ a b, P a b ) {a n : ℕ}
: a ≤ ex P n ↔ ∃ (M : Fin n → Fin n → Prop), ¬contains P M ∧ a ≤ density M := by
  cases a
  case zero => --zero is easy just take the zero matrix
    have : 0 ≤ ex P n := by simp only [zero_le]
    have : ∃ (M : Fin n → Fin n → Prop), ¬contains P M ∧ 0 ≤ density M := by
      let M (_ _ : Fin n) : Prop := false
      use M
      simp
      by_contra McontainP
      rw [contains] at McontainP
      obtain ⟨f, _, g, _, m⟩ := McontainP
      obtain ⟨a, b, Pab⟩ := P_nonempty
      have := m a b Pab
      have := M (f a) (g b)
      contradiction
    aesop
  case succ =>
    apply Iff.intro
    · -- (→)
      intro h1
      simp [ex] at h1
      exact h1
    · -- (←)
      intro ⟨M, avoids_P, has_a⟩
      rw [ex, Finset.le_sup_iff]
      use M
      aesop; aesop


--lemma rotationInvariant (P : α → β → Prop) := ex P n = ex rotate(P) n := by sorry
--#eval sup {j | false} id
theorem split_density {n : ℕ} (M : Fin n → Fin n → Prop) (Pred: Fin n → Fin n → Prop) :
let M1 (i j : Fin n) : Prop := M i j ∧   (Pred i j);
let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (Pred i j);
density M = density M1 + density M2 := by
  classical
  let M1 (i j : Fin n) : Prop := M i j ∧   (Pred i j);
  let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (Pred i j);
  let s1 : Finset (Fin n × Fin n) := {(i, j) | M1 i j}
  let s2 : Finset (Fin n × Fin n) := {(i, j) | M2 i j}
  let s  : Finset (Fin n × Fin n) := {(i, j) | M  i j}
  have seqs1s2: s = s1 ∪ s2 := by
    ext x
    constructor
    · -- (->)
      intro xins
      simp [s] at xins
      simp [s1, s2, M1, M2]
      tauto
    · -- (<-)
      intro xins1s2
      simp [s1, s2, M1, M2] at xins1s2
      simp [s]
      tauto
  have dm : density M = s.card := by simp [density]
  have dm1: density M1 = s1.card := by
    simp [density]
    convert rfl
  have dm2: density M2 = s2.card := by --
    simp [density, M2, s2, M1]
    convert rfl
  have s1eqs2card: (s1 ∪ s2).card = s1.card + s2.card := by
    apply card_union_of_disjoint
    simp [Disjoint]
    intro x h1 h2
    intro p hp
    simp only [Finset.not_mem_empty]
    have pins1 : p ∈ s1 := by
      apply h1
      exact hp
    have pins2: p ∈ s2 := by
      apply h2
      exact hp
    simp [M1, s1] at pins1
    simp [M2, s2] at pins2
    have:= pins1.right
    have:= pins2.right
    contradiction
  rw [← seqs1s2] at s1eqs2card
  aesop


--open scoped Classical in noncomputable
theorem split_density_to_rows {n:ℕ} (M : Fin n → Fin n → Prop) : density M = ∑ i,  row_density M i := by
  classical
  let s : Finset (Fin n × Fin n) := { (x, y)| M x y}
  let f : Fin n × Fin n → Fin n  := fun x ↦ x.1
  let t : Finset (Fin n) := Finset.univ
  have H : ∀ x ∈ s, f x ∈ t := by
    intro x _
    simp [f, t]
  have h_sum_card:= Finset.card_eq_sum_card_fiberwise H
  simp [f, t] at h_sum_card
  have: s.card = density M := by simp [s, density]
  rw [this] at h_sum_card
  have: ∀ k, (filter (fun x ↦ f x = k) s).card = row_density M k := ?proof_fiber_row_density
  simp only [this] at h_sum_card
  exact h_sum_card

  case proof_fiber_row_density =>
    intro k
    simp [row_density]
    apply Finset.card_bij (fun (a:Fin n × Fin n)  _ ↦ a.2 ) ?hi ?i_inj ?i_surj; aesop;aesop;aesop

    -- 30 lines --> 1 lines using apply (and lean will figure out what is needed.)

    /-let s := filter (fun x_1 ↦ x_1.1 = k) {(x, y)| M x y}
    let t := filter (fun j ↦ M k j) Finset.univ
    let i : (a :Fin n × Fin n) → a ∈ s → Fin n := fun a h ↦ a.2
    let hi : ∀ (a : Fin n × Fin n) (ha : a ∈ s), i a ha ∈ t := by
      intro a ha
      simp [i]
      simp [s] at ha
      refine mem_filter.mpr ?_
      constructor
      simp
      rw [ha.2] at ha
      exact ha.1
    let i_inj : ∀ (a₁ : Fin n × Fin n) (ha₁ : a₁ ∈ s) (a₂ : Fin n × Fin n) (ha₂ : a₂ ∈ s), i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂ := by
      intro a1 ha1 a2 ha2 H
      simp [i] at H
      simp [s] at ha1 ha2
      have : a1.1 = a2.1 := by omega
      exact Prod.ext this H
    let i_surj : ∀ b ∈ t, ∃ a, ∃ (ha : a ∈ s), i a ha = b :=  by
      intro b hb
      let a := (k, b)
      let ha : a ∈ s := by
        refine mem_filter.mpr ?_
        simp [t] at hb
        simp [mem_filter]
        exact hb
      use a
      use ha
    have:= Finset.card_bij i hi i_inj i_surj
    convert this
    done-/


--  classical
  --pairwise disjoint union is too hard

theorem density_by_rows_ub {n c:ℕ}  (M : Fin n → Fin n → Prop)
(h_row_density_bounded: ∀i, row_density M i ≤ c) : density M ≤  n * c  :=  calc
    density M = ∑ i,  row_density M i := split_density_to_rows M
    _         ≤ ∑ _, c := by
              apply Finset.sum_le_sum
              simp [mem_filter]
              exact h_row_density_bounded
    _         = n*c := by simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
