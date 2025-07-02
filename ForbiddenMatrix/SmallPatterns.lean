import ForbiddenMatrix.ExtremalFunction
import ForbiddenMatrix.MatrixOperations
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Interval
import Mathlib.Logic.Equiv.Fin.Basic

open Finset Set

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-! ### Definitions -/

def IdentityPattern (n : ℕ) (i j : Fin n) : Prop := i = j

def AllPattern (m n : ℕ) : Fin m → Fin n → Prop := fun _ _ ↦ True
abbrev VerticalPattern (m : ℕ) : Fin m → Fin 1 → Prop := AllPattern m 1
abbrev HorizontalPattern (n : ℕ) : Fin 1 → Fin n → Prop := AllPattern 1 n
abbrev TrivialPattern : Fin 1 → Fin 1 → Prop := AllPattern 1 1

@[simp] lemma identityPattern_one : IdentityPattern 1 = TrivialPattern := by
  ext i j; simp [IdentityPattern, AllPattern, Subsingleton.elim i j]

def HatPattern : Fin 2 → Fin 3 → Prop :=
  ![
    ![False, True, False],
    ![True, False, True]
   ]

/-! ### Proofs -/

@[simp] lemma ex_of_isEmpty [IsEmpty α] [IsEmpty β] (P : α → β → Prop) (n : ℕ) : ex P n = 0 := by
  simp [ex]

@[simp] lemma ex_trivialPattern (n : ℕ) : ex TrivialPattern n = 0 := by
  simp only [ex, sup_eq_zero, mem_filter, Finset.mem_univ, true_and, density, card_eq_zero,
    not_imp_comm (a := Contains _ _), ← Finset.nonempty_iff_ne_empty, Finset.Nonempty, Prod.exists,
    forall_exists_index]
  exact fun M i j hij ↦ ⟨fun _ ↦ i, by simp [StrictMono], ![j], by simp [StrictMono], by simp [hij]⟩

@[simp] theorem ex_identityPattern_two (n : ℕ) : ex (IdentityPattern 2) n = 2 * n - 1 := by
  obtain rfl | hn := eq_zero_or_neZero n
  · simp
  apply ge_antisymm
  · refine (le_ex_iff _ ⟨0, 0, by simp [IdentityPattern]⟩).2 ⟨(· = 0 ∨ · = 0), ?_, ?_⟩
    · rintro ⟨f, hf, g, hg, pmap⟩
      have hf₀ : f 1 ≠ 0 := (hf Fin.zero_lt_one).ne_bot
      have hg₀ : g 1 ≠ 0 := (hg Fin.zero_lt_one).ne_bot
      simpa [IdentityPattern, hf₀, hg₀] using pmap 1
    calc
          2 * n - 1
        = #(.Ioo (-n : ℤ) n) := by simp; omega
      _ ≤ #{(i, j) : Fin n × Fin n | i = 0 ∨ j = 0} := by
        refine card_le_card_of_forall_subsingleton (fun z (i, j) ↦ z = i.val - j.val) ?_ ?_
        · simp only [Finset.mem_Ioo, mem_filter, Finset.mem_univ, true_and, or_and_right, exists_or,
            Prod.exists, exists_and_left, exists_eq_left, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
            CharP.cast_eq_zero, zero_sub, ← neg_eq_iff_eq_neg, sub_zero, and_imp]
          rintro (z | z) hnz hzn
          · exact .inr ⟨⟨z, by simpa using hzn⟩, rfl⟩
          · exact .inl ⟨⟨z + 1, by simp [Int.negSucc_eq] at hnz; omega⟩, rfl⟩
        · aesop (add simp [Set.Subsingleton])
      _ = density _ := by rw [density_def]
  classical
  simp only [ex, Finset.sup_le_iff, mem_filter, Finset.mem_univ, true_and]
  intro M
  contrapose
  simp [density]
  intro M_has_two_n_points

  let f : Fin n × Fin n → ℤ := fun ⟨i, j⟩ ↦ i - j
  let s := (filter (fun (i, j) ↦ M i j) univ)
  have : s.card > 2*n-1 := by aesop
  let t : Finset ℤ := Icc (-n + 1) (n - 1)
  have tcardeq2nm1 : t.card = 2*n -1 := by
    simp [t]
    cases n
    · contradiction
    simp
    omega
  let k := 1

  have hf ⦃a⦄ (_ : a ∈ s) : f a ∈ t := by simp [f, t]; omega

  have hn : t.card * k < s.card := by
    simp [k, s, t]
    cases n
    · contradiction
    simp
    omega

  obtain ⟨y, hy, hy'⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hn
  simp only [k] at hy'
  rw [one_lt_card] at hy'
  simp only [mem_filter, ne_eq] at hy'
  obtain ⟨a, ha, b, hb, hab⟩ := hy'
  obtain ⟨ha, ha'⟩ := ha
  obtain ⟨hb, hb'⟩ := hb

  have ⦃x⦄ (ha : x ∈ s) : M x.1 x.2 := by aesop
  have hmaa : M a.1 a.2 := by aesop
  have hmbb : M b.1 b.2 := by aesop
  have abneq : ¬ (a.1 = b.1 ∧ a.2 = b.2) := by aesop
  have dominance : (a.1 < b.1 ∧ a.2 < b.2) ∨ (a.1 > b.1 ∧ a.2 > b.2) := by
    rw [← ha'] at hb'
    simp only [f] at hb'
    rw [sub_eq_sub_iff_add_eq_add] at hb'
    omega
  simp [Contains]
  match dominance with
  | .inl ⟨hab₁, hab₂⟩ =>
      exact ⟨![a.1, b.1], by simpa [StrictMono, Fin.forall_fin_two], ![a.2, b.2], by
      simpa [StrictMono, Fin.forall_fin_two], by simp [Fin.forall_fin_two, IdentityPattern, *]⟩
  | .inr ⟨hab₁, hab₂⟩ =>
      exact ⟨![b.1, a.1], by simpa [StrictMono, Fin.forall_fin_two], ![b.2, a.2], by
      simpa [StrictMono, Fin.forall_fin_two], by simp [Fin.forall_fin_two, IdentityPattern, *]⟩

lemma ex_verticalPattern_two (n : ℕ) : ex (VerticalPattern 2) n = n := by
  classical
  refine le_antisymm ?_ ?_
  · rw [ex]
    simp
    intro M
    contrapose
    simp [density]
    intro more_than_n

    let f : Fin n × Fin n → ℕ := fun ⟨i, j⟩ ↦ j
    let s := (filter (fun (i, j) ↦ M i j) univ)
    have : s.card > n := by aesop
    let t : Finset ℕ := Finset.Iio n
    let k := 1
    have hf ⦃a⦄ (_ : a ∈ s) : f a ∈ t := by simp [f, t]
    have hn : t.card * k < s.card := by aesop
    obtain ⟨y, hy, hy'⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hn
    simp only [k] at hy'
    rw [one_lt_card] at hy'
    simp only [mem_filter, ne_eq] at hy'
    obtain ⟨a, ha, b, hb, hab⟩ := hy'
    obtain ⟨ha, ha'⟩ := ha
    obtain ⟨hb, hb'⟩ := hb
    rw [Contains]
    have : a.2 = b.2 := by
      simp [f] at ha' hb'
      rw [← ha'] at hb'
      omega

    have dominance : (a.1 < b.1) ∨ (b.1 < a.1) := by
      have : a.1 ≠ b.1 := ?_
      aesop
      by_contra a1b1
      apply hab
      aesop

    let g := ![a.2]
    have gmono : StrictMono g := by simp [StrictMono]

    cases dominance with
    | inl ab =>
      refine ⟨![a.1, b.1], by  simpa [f, StrictMono, Fin.forall_fin_two], g, gmono, ?_⟩
      simp [Fin.forall_fin_one, Fin.forall_fin_two, AllPattern, g]
      aesop
    | inr ba =>
      let f := ![b.1, a.1]
      refine ⟨![b.1, a.1], by  simpa [f, StrictMono, Fin.forall_fin_two], g, gmono, ?_⟩
      simp [Fin.forall_fin_one, Fin.forall_fin_two, AllPattern, g]
      aesop
  · obtain rfl | hn := eq_zero_or_neZero n
    · simp
    refine (le_ex_iff _ ⟨0, by simp [AllPattern]⟩).2 ⟨fun i j ↦ i = 0, ?_, ge_of_eq ?_⟩
    · rintro ⟨f, hf, g, hg, prop⟩
      simp [Fin.forall_fin_one, Fin.forall_fin_two, AllPattern] at prop
      exact (hf Fin.zero_lt_one).ne <| prop.1.trans prop.2.symm
    · calc
            density _
        _ = #{x : Fin n × Fin n | x.1 = 0} := density_def _
        _ = #({0} ×ˢ .univ : Finset <| Fin n × Fin n) := by congr; aesop
        _ = n := by simp

example (n : ℕ) : ex (HorizontalPattern 2) n ≤ n := by
  classical
  simp [ex]
  intro M noH2P
  let Pred_min_Ofrow := fun i j ↦ ∀ j', M i j' → j ≤ j'
  let M1 (i j : Fin n) : Prop := M i j ∧ Pred_min_Ofrow i j
  let M2 (i j : Fin n) : Prop := M i j ∧ ¬ Pred_min_Ofrow i j

  have dm1 : density M1 ≤ n := by
    have h_row_one i : row_density M1 i ≤ 1 := by
      by_contra H
      simp [row_density, one_lt_card_iff] at H
      obtain ⟨a, ha, b, hb, aneqb⟩ := H
      simp [M1, Pred_min_Ofrow] at ha
      simp [M1, Pred_min_Ofrow] at hb
      have : a = b := by
        refine Fin.le_antisymm ?h1 ?h2
        · -- a ≤ b
          apply ha.2
          exact hb.1
        · -- b ≤ a
          apply hb.2
          exact ha.1
      contradiction
    simpa using density_by_rows_ub M1 h_row_one
  have M2_avoids_trivial : ¬ Contains TrivialPattern M2 := by
    rintro ⟨f, hf, g, hg, prop⟩
    --  M2    g(0)
    -- f(0)    1
    simp [M2] at prop
    specialize prop 0 0
    simp [AllPattern, Pred_min_Ofrow] at prop
    obtain ⟨hfa, a, ha, ha2⟩ := prop
    --  M  a g(0)
    -- f(0) 1 1
    have : Contains (HorizontalPattern 2) M :=
      ⟨f, hf, ![a, g 0], by simpa [StrictMono, Fin.forall_fin_two], by
        simp [AllPattern, Fin.forall_fin_one, Fin.forall_fin_two, *]⟩
    contradiction
  have dm2 := calc
        density M2
    _ ≤ ex TrivialPattern n := density_le_ex_of_not_contains M2 M2_avoids_trivial
    _ = 0 := ex_trivialPattern n

  calc
        density M
    _ = density M1 + density M2 := split_density M Pred_min_Ofrow
    _ ≤ n + density M2 := by simp only [dm1, add_le_add_iff_right]
    _ ≤ n + 0 := by simp only [dm2, add_le_add_iff_left]
    _ ≤ n := by omega

theorem ex_horizontal (k n : ℕ) : ex (HorizontalPattern k) n ≤ n*(k-1) := by
  classical
  simp only [ex, Finset.sup_le_iff, mem_filter, Finset.mem_univ, true_and]
  intro M NoHPk
  refine density_by_rows_ub M fun i ↦ ?_
  contrapose! NoHPk
  simp [row_density] at NoHPk
  let s : Finset (Fin n) := {j | M i j}
  have h : k ≤ s.card := by simp [s]; omega
  let g := s.orderEmbOfCardLe h
  simp [Contains]
  refine ⟨![i], by simp [StrictMono], g, by simp [StrictMono, OrderEmbedding.lt_iff_lt], ?_⟩
  simp [AllPattern]
  intro j
  simpa [s] using s.orderEmbOfCardLe_mem h j

theorem ex_vertical (k n : ℕ) : ex (VerticalPattern k) n ≤ n*(k-1) := by
  classical
  calc
    ex (VerticalPattern k) n
    _ ≤ ex ( tranpose (VerticalPattern k)) n := ?exv
    _ = ex ( HorizontalPattern k) n := by rfl
    _ ≤ n*(k-1) := ex_horizontal k n

  case exv =>
    simp [ex]
    intro M hM
    rw [← ex]
    let M' := tranpose M
    have hM' : ¬ Contains (tranpose (VerticalPattern k)) M' := by
      by_contra H
      obtain ⟨f, hf, g, hg, emb_pat_to_M'⟩ := H
      have : Contains (VerticalPattern k) M := by
        refine ⟨g, hg, f, hf, by
          intro a b
          apply emb_pat_to_M'
        ⟩
      contradiction

    have dmeqdm' : density M = density M' := by
      apply Finset.card_bij (fun a _ ↦ (a.2, a.1)) ?hi ?i_inj ?i_surj; aesop;aesop;aesop

    calc
      density M = density M' := dmeqdm'
      _        ≤ ex (tranpose (VerticalPattern k)) n := (density_le_ex_of_not_contains M' hM')


theorem ex_hat (n : ℕ) : ex HatPattern n ≤ 3 * n := by
  classical
  simp [ex]
  intro M noHat

  let min_or_max_of_row := fun i j ↦ (∀ j', M i j' → j ≤ j') ∨ (∀ j', M i j' → j' ≤ j)
  let M1 (i j : Fin n) : Prop := M i j ∧ (min_or_max_of_row i j)
  let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (min_or_max_of_row i j)

  have M1_avoids_H3 : ¬ Contains (HorizontalPattern 3) M1 := by
    rintro ⟨f, _, g, g_mono, prop⟩
    simp [Fin.forall_fin_one, AllPattern] at prop
    -- prop :
    -- M1   g(0) g(1) g(2)
    -- f(0) 1   1   1
    simp [M1] at prop
    obtain ⟨_, h_min_max_g1⟩ : M (f 0) (g 1) ∧ min_or_max_of_row (f 0) (g 1) := prop 1
    -- since g(1) in M1, g(1) is either min or max
    cases h_min_max_g1 with
     | inl g1_min =>
      have : g 1 ≤ g 0 := by aesop (add simp g1_min)
      have : g 0 < g 1 := by aesop (add simp g_mono)
      omega
     | inr g1_max =>
      have : g 2 ≤ g 1 := by aesop (add simp g1_max)
      have : g 1 < g 2 := by aesop (add simp g_mono)
      omega
  have M2_avoids_V2 : ¬ Contains (VerticalPattern 2) M2 := by
    rintro ⟨f, hf, g, _, v2_to_M2⟩
    simp only [AllPattern, not_or, not_forall, Classical.not_imp, not_le, forall_const,
      Fin.forall_fin_one, Fin.isValue, Fin.forall_fin_two, M2, min_or_max_of_row] at v2_to_M2
    obtain ⟨⟨hib, -, -⟩, -, ⟨a, hja, hab⟩, c, hjc, hbc⟩ := v2_to_M2
    set b := g 0
    --      a b c
    -- f(0)   1
    -- f(1) 1   1
    exact noHat ⟨f, hf, ![a, b, c], by simp [StrictMono, Fin.forall_fin_succ, *, hab.trans hbc], by
      simp [HatPattern, Fin.forall_fin_succ, *]⟩
  have dm1 := calc
        density M1
    _ ≤ ex (HorizontalPattern 3) n := density_le_ex_of_not_contains M1 M1_avoids_H3
    _ ≤ n * 2 := ex_horizontal 3 n
  have dm2 := calc
        density M2
    _ ≤ ex (VerticalPattern 2) n := density_le_ex_of_not_contains M2 M2_avoids_V2
    _ = n := ex_verticalPattern_two n
  calc
        density M
    _ = density M1 + density M2 := split_density M min_or_max_of_row
    _ ≤ n * 2 + density M2 := by simp [dm1]
    _ ≤ n * 2 + n := by simp [dm2]
    _ ≤ 3 * n := by omega
