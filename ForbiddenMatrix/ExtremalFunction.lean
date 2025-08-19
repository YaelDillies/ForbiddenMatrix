import ForbiddenMatrix.Containment
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monoid.Canonical.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Lattice

open Finset

variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ] {m n : ℕ}
  {P : α → β → Prop}

open scoped Classical in
noncomputable def density (M : Fin m → Fin n → Prop) : ℕ := #{(i, j) : Fin m × Fin n | M i j}

lemma density_def {n : ℕ} (M : Fin n → Fin n → Prop) [DecidableRel M] :
    density M = #{(i, j) : Fin n × Fin n | M i j} := by unfold density; convert rfl

@[gcongr] lemma density_mono {M N : Fin m → Fin n → Prop} (h : ∀ i j, M i j → N i j) :
    density M ≤ density N := card_le_card fun _ ↦ by aesop

open scoped Classical in noncomputable
def row_density {n : ℕ} (M : Fin n → Fin n → Prop) (i : Fin n) : ℕ := #{j | M i j}

open scoped Classical in noncomputable
def col_density {n : ℕ} (M : Fin n → Fin n → Prop) (j : Fin n) : ℕ := #{i | M i j}

open scoped Classical in noncomputable
def ex (P : α → β → Prop) (n : ℕ) : ℕ := sup {M : Fin n → Fin n → Prop | ¬ Contains P M} density

@[simp] lemma ex_zero (P : α → β → Prop) : ex P 0 = 0 := by simp [ex, density]

theorem ex_le_iff {P : α → β → Prop} {m n : ℕ} :
    ex P n ≤ m ↔ ∀ (M : Fin n → Fin n → Prop), ¬ Contains P M → density M ≤ m:= by
  simp [ex]

theorem le_ex_iff (P : α → β → Prop) (P_nonempty : ∃ a b, P a b) {m n : ℕ} :
    m ≤ ex P n ↔ ∃ (M : Fin n → Fin n → Prop), ¬ Contains P M ∧ m ≤ density M := by
  obtain rfl | hm := eq_zero_or_pos m
  · simpa using ⟨_, not_contains_false P P_nonempty⟩
  · simp [ex, Finset.le_sup_iff hm]

lemma ex_le_sq {P : α → β → Prop} (n : ℕ) : ex P n ≤ n ^ 2 := by
  simpa [ex, density, sq] using fun M _ ↦ Finset.card_le_univ (α := Fin n × Fin n) _

lemma density_le_ex_of_not_contains (M : Fin n → Fin n → Prop) (AvoidP : ¬ Contains P M) :
    density M ≤ ex P n := by
  rw [ex]
  apply le_sup
  simpa only [mem_filter, Finset.mem_univ, true_and]

theorem split_density_to_rows {n : ℕ} (M : Fin n → Fin n → Prop) :
    density M = ∑ i, row_density M i := by
  simp [density, row_density, card_eq_sum_ones, -sum_const]
  exact Finset.sum_finset_product _ _ _ (by simp)

theorem density_by_rows_ub {n c : ℕ}  (M : Fin n → Fin n → Prop)
    (h_row_density_bounded : ∀ i, row_density M i ≤ c) : density M ≤ n * c := calc
    density M
  _ = ∑ i, row_density M i := split_density_to_rows M
  _ ≤ ∑ _, c := by gcongr; exact h_row_density_bounded _
  _ = n * c := by simp

theorem split_density_to_cols {n : ℕ} (M : Fin n → Fin n → Prop) :
    density M = ∑ i, col_density M i := by
  simp [density, col_density, card_eq_sum_ones, -sum_const]
  exact Finset.sum_finset_product_right _ _ _ (by simp)

theorem density_by_cols_ub {n c : ℕ}  (M : Fin n → Fin n → Prop)
    (h_col_bounded : ∀ i, col_density M i ≤ c) : density M ≤ n * c := calc
      density M
  _ = ∑ i, col_density M i := split_density_to_cols M
  _ ≤ ∑ _, c := by gcongr; exact h_col_bounded _
  _ = n * c := by simp

def rectPtset (n a₁ b₁ a₂ b₂ : ℕ) : Finset (Fin n × Fin n) :=
  ({a | ↑a ∈ Finset.Ico a₁ b₁} : Finset (Fin n)) ×ˢ ({a | ↑a ∈ Finset.Ico a₂ b₂} : Finset (Fin n))

open scoped Classical in noncomputable
def rectPtsetMatrix {n : ℕ}(M : Fin n → Fin n → Prop) (a₁ b₁ a₂ b₂ : ℕ) : Finset (Fin n × Fin n) :=
  {(a, b) | M a b ∧ (a, b) ∈ (rectPtset n a₁ b₁ a₂ b₂)}

open scoped Classical in noncomputable
def rectPtsetSubsetMatrix {n : ℕ}(M : Fin n → Fin n → Prop) (R C : Finset (Fin n)) :
    Finset (Fin n × Fin n) := {(a, b) | M a b ∧ (a, b) ∈ R ×ˢ C}

lemma card_interval {n : ℕ} (x y : ℕ) (hy : y ≤ n) :
    #{a : Fin n | ↑a ∈ Finset.Ico x y} = #(.Ico x y) := by
  apply Finset.card_bij (fun (a : Fin n) _ ↦ ↑a) (by aesop) (by aesop) ?_
  intro b hb
  simp at hb
  exact ⟨⟨b, by omega⟩, by simpa⟩

@[simp] lemma card_rectPtSet (n a₁ b₁ a₂ b₂ : ℕ) (h : b₁ ≤ n ∧ b₂ ≤ n) :
    #(rectPtset n a₁ b₁ a₂ b₂) = (b₁ - a₁) * (b₂ - a₂) := by
  simp only [rectPtset, card_product]
  suffices claim : ∀ x y, y ≤ n → #{a : Fin n | ↑a ∈ Finset.Ico x y} = #(.Ico x y) by aesop
  intro x y hy
  exact card_interval x y hy

@[simp] lemma card_rectPtsetSubsetMatrix {n : ℕ}(M : Fin n → Fin n → Prop) (R C : Finset (Fin n)) :
    #(rectPtsetSubsetMatrix M R C) ≤ #R * #C := by
  calc
    #(rectPtsetSubsetMatrix M R C)
      ≤ #(R ×ˢ C) := ?_
    _ = #R * #C := card_product R C
  gcongr
  simp only [rectPtsetSubsetMatrix, Prod.mk.eta, mem_product]
  intro a ha
  aesop

lemma density_mk_mem_product {n : ℕ} (I J : Finset (Fin n)) :
    density (fun i j ↦ (i, j) ∈ I ×ˢ J) = #I * #J := by simp [density_def, -mem_product]

theorem den_all1_matrix_row_subset {n : ℕ} (I : Finset (Fin n)) :
    let M (i j : Fin n) : Prop := (i, j) ∈ I ×ˢ  Finset.univ
    density M = n * #I := by
  extract_lets M
  let J : Finset (Fin n) := Finset.univ
  have := density_mk_mem_product I J
  simp at this
  rw [mul_comm]
  convert this <;> aesop

theorem den_all1_matrix_col_subset {n : ℕ} (I : Finset (Fin n)) :
    let M (i j : Fin n) : Prop := (i, j) ∈ Finset.univ ×ˢ I
    density M = n * #I := by
  simpa using density_mk_mem_product .univ I

theorem den_all1_matrix_column_interval {n : ℕ} (a b : Fin n) :
    let I := ({x | ↑x ∈ Finset.Icc a.1 b.1} : Finset (Fin n))
    let M (i j : Fin n) : Prop := (i, j) ∈ Finset.univ ×ˢ I
    density M = n * (b + 1 - a) := by
  extract_lets I M
  have h1 : #I = #(.Icc a.1 b.1) := by
    apply card_interval
    exact b.2
  observe h2 : #(.Icc a.1 b.1) = b.1 +1 - a.1
  calc
    density M = n * #I := by exact den_all1_matrix_col_subset I
    _ = n * #(.Icc a.1 b.1) := by exact congrArg (HMul.hMul n) h1
    _ = n * (b + 1 - a) := by exact congrArg (HMul.hMul n) h2

theorem den_all1_matrix_row_interval {n : ℕ} (a b : Fin n) :
    let I := ({x | ↑x ∈ Finset.Icc a.1 b.1} : Finset (Fin n))
    let M (i j : Fin n) : Prop := (i, j) ∈ I ×ˢ Finset.univ
    density M = n * (b + 1 - a) := by
  extract_lets I M
  have h1 : #I = #(.Icc a.1 b.1) := by
    apply card_interval
    exact b.2
  observe h2 : #(.Icc a.1 b.1) = b.1 +1- a.1
  calc
    density M = n * #I := by exact den_all1_matrix_row_subset I
    _ = n * #(.Icc a.1 b.1) := by exact congrArg (HMul.hMul n) h1
    _ = n * (b + 1 - a) := by exact congrArg (HMul.hMul n) h2

theorem den_all1_matrix_single_row {n : ℕ} (x : Fin n) :
    let M (i _ : Fin n) : Prop := i = x
    density M = n := by
  extract_lets M
  have := den_all1_matrix_row_interval x x
  simp [density] at this
  simp [density, M]
  convert this
  aesop

theorem den_all1_matrix_single_col {n : ℕ} (x : Fin n) :
    let M (_ j : Fin n) : Prop := j = x
    density M = n := by
  extract_lets M
  have := den_all1_matrix_column_interval x x
  simp [density] at this
  simp [density, M]
  convert this
  aesop

theorem le_ex_self_of_two_points (P : α → β → Prop) (n : ℕ)
    (hP : ∃ x y : (α × β), P x.1 x.2 ∧ P y.1 y.2 ∧ x ≠ y) : n ≤ ex P n := by
  obtain rfl | n_pos := eq_zero_or_neZero n
  · simp
  simp only [ne_eq, Prod.ext_iff, not_and_or] at hP
  obtain ⟨⟨a₁, b₁⟩, ⟨a₂, b₂⟩, h₁, h₂, ha | hb⟩ := hP
  · refine (le_ex_iff _ ⟨_, _, h₁⟩).2 ⟨fun i j ↦ i = 0, ?_, by simp [den_all1_matrix_single_row]⟩
    rintro ⟨f, hf, g, hg, hfg⟩
    exact ha <| hf.injective <| (hfg _ _ h₁).trans (hfg _ _ h₂).symm
  · refine (le_ex_iff _ ⟨_, _, h₁⟩).2 ⟨fun i j ↦ j = 0, ?_, by simp [den_all1_matrix_single_col]⟩
    rintro ⟨f, hf, g, hg, hfg⟩
    exact hb <| hg.injective <| (hfg _ _ h₁).trans (hfg _ _ h₂).symm

lemma exists_av_and_ex_eq {n : ℕ} {P : α → β → Prop} (P_nonempty : ∃ a b, P a b) :
    ∃ M : Fin n → Fin n → Prop, ¬ Contains P M ∧ ex P n = density M := by
  classical
  simpa using Finset.exists_mem_eq_sup {M : Fin n → Fin n → Prop | ¬ Contains P M}
    ⟨_, by simpa using not_contains_false P P_nonempty⟩ density

theorem split_density {n : ℕ} (M : Fin n → Fin n → Prop) (Pred : Fin n → Fin n → Prop) :
    let M1 (i j : Fin n) : Prop := M i j ∧  (Pred i j);
    let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (Pred i j);
    density M = density M1 + density M2 := by
  classical
  let M1 (i j : Fin n) : Prop := M i j ∧  (Pred i j);
  let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (Pred i j);
  let s1 : Finset (Fin n × Fin n) := {(i, j) | M1 i j}
  let s2 : Finset (Fin n × Fin n) := {(i, j) | M2 i j}
  let s : Finset (Fin n × Fin n) := {(i, j) | M  i j}
  have seqs1s2 : s = s1 ∪ s2 := by
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
  have dm : density M = s.card := by simp [density, s]
  have dm1 : density M1 = #s1 := by simp [density_def, s1]
  have dm2 : density M2 = #s2 := by simp [density_def, s2]
  have s1eqs2card : (s1 ∪ s2).card = s1.card + s2.card := by
    apply card_union_of_disjoint
    rw [disjoint_left]
    aesop
  rw [← seqs1s2] at s1eqs2card
  aesop
