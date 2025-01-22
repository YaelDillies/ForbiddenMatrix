import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Order.Monoid.Canonical.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.Matrix.Permutation
import ForbiddenMatrix.Containment
import ForbiddenMatrix.PatternsDef
import ForbiddenMatrix.ExtremalFunction
import ForbiddenMatrix.MatrixOperations

open Finset Set

lemma PatternOneIsIdentity : onePattern = (identityPattern 1) := by
  ext -- apply function extensionality for all a F(a) = G(a) => F = G
  simp [identityPattern, onePattern]
  exact Subsingleton.elim ..

lemma exPatternOne (n : ℕ) : ex onePattern n = 0 := by
  rw [ex]
  simp [filter_eq_empty_iff]
  intro M
  contrapose
  simp
  intro Mnonzero
  simp only [density, card_eq_zero, filter_eq_empty_iff, Finset.mem_univ, true_implies, Prod.forall, not_forall,
  not_not] at Mnonzero
  obtain ⟨i, j, Mij⟩ := Mnonzero
  simp [contains]
  refine ⟨fun _ ↦ i, by simp [StrictMono], ![j], by simp [StrictMono], by simp [Mij]⟩

example (n : ℕ) : ex (identityPattern 1) n = 0 := by
  rw [← PatternOneIsIdentity]
  exact exPatternOne n

lemma injOn_aux (n : ℕ) [NeZero n] :
    InjOn (fun z : ℤ ↦ ((↑(z⁺), ↑(z⁻)) : Fin n × Fin n)) (Set.Ioo (-n) n : Set ℤ) :=
  ((CharP.intCast_injOn_Ico _ n).prodMap (CharP.intCast_injOn_Ico _ n)).comp
    posPart_negPart_injective.injOn fun z hz ↦
    ⟨⟨posPart_nonneg _, by simpa [NeZero.pos] using hz.2⟩,
      ⟨negPart_nonneg _, by simpa [NeZero.pos] using hz.1⟩⟩

--set_option diagnostics true
lemma  exIdentity2LB  (n : ℕ)[NeZero n]: 2*n-1 ≤ ex (identityPattern 2) n := by
  --The following code is a bad style: (a lot of unnecessary casting to deal with, e.g. double-casting)
  --let  M (i j : Fin n) : Prop := i.val = 0 ∨ j.val = 0
  --Better to use this one:
  let  M (i j : Fin n) : Prop := i = (0 : Fin n) ∨ j = (0 : Fin n)
  have : ¬contains (identityPattern 2) M := ?proof_of_M_avoids_I2
  have : 2*n -1 ≤ density M := ?proof_of_Mhastwon--(filter (fun x ↦ M x.1 x.2 : Fin n × Fin n → Prop) univ).card +1 := ?proof_of_Mhastwon
  -- Main proof starts here --
  rw [le_ex_iff]
  use M
  -- prove that (P is non-empty)
  case P_nonempty => simp [identityPattern]

  -- It remains to prove MavI2 and Mhastwon
  case proof_of_M_avoids_I2 =>
    by_contra h
    simp [contains] at h
    obtain ⟨f, hf, g, hg, pmap⟩ := h
    simp [M, identityPattern] at pmap
    simp [StrictMono] at hf hg
    have f1g0: 0 < f 1 := by
      by_contra f0
      simp at f0
      have fmono: f 0 < f 1 := by simp [hf]
      rw [f0] at fmono
      contradiction
    have g1g0: 0 < g 1 := by
      by_contra g0
      simp at g0
      have gmono: g 0 < g 1 := by simp [hg]
      rw [g0] at gmono
      contradiction
    specialize pmap 1
    cases' pmap
    aesop;aesop
  -- Now, we prove Mhastwon
  case proof_of_Mhastwon =>
    let t := (filter (fun x ↦ M x.1 x.2 : Fin n × Fin n → Prop) univ)
    simp only [density, ge_iff_le, M]
    let s : Finset ℤ := Ioo (-n) (n)
    let f : ℤ → Fin n × Fin n := fun (i) ↦ (↑(i⁺) , ↑(i⁻))
    have : s = (Set.Ioo (-n) n : Set ℤ) := by aesop
    have f_inj: InjOn f s := by simp [injOn_aux n, this, s, f]
    have hf : ∀ a ∈ s, f a ∈ t := by
      intro a ains
      simp [s] at ains
      simp [M, t]
      obtain hha | hha' := le_total a 0
      left
      have : a⁺ = 0 := by rwa [posPart_eq_zero]
      simp [this, s, f]
      -- use ful command rw [← Fin.val_zero' n, Fin.val_inj]--, Fin.natCast_eq_zero]
      right
      have : a⁻ = 0 := by rwa [negPart_eq_zero]
      simp [this, s, f]
    have: s.card ≤ t.card:= Finset.card_le_card_of_injOn f hf f_inj
    have: s.card = 2*n -1 := by
      simp [s]
      norm_cast
      rw [Int.toNat_ofNat]
      omega
    have: 2*n -1 ≤ t.card := by omega
    convert this



lemma exIdentity2UB (n : ℕ) : ex (identityPattern 2) n ≤ 2*n-1 := by
  classical
  rw [ex]
  simp
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
    rw [← Nat.cast_add_one, ← Nat.cast_add, Int.toNat_ofNat]
    omega
  let k := 1

  have hf ⦃a⦄ (_ : a ∈ s) : f a ∈ t := by simp [f, t]; omega

  have hn : t.card * k < s.card := by
    simp [k, s, t]
    cases n
    · contradiction
    simp
    rw [← Nat.cast_add_one, ← Nat.cast_add, Int.toNat_ofNat]
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
  simp [contains]

  cases dominance with
  | inl halb =>
    obtain ⟨a1leqb1, a2leqb2⟩ := halb
    let fM : Fin 2 → Fin n := ![a.1, b.1]
    let gM : Fin 2 → Fin n := ![a.2, b.2]
    have monof : StrictMono fM := by
      simp [StrictMono]
      intro a_fM b_fM aleqb_fM
      simp [fM]
      have abeqfm : a_fM = 0 ∧ b_fM = 1 := by omega
      obtain ⟨a_fM_eq_zero, b_fM_eq_one⟩ := abeqfm
      simp [a_fM_eq_zero, b_fM_eq_one, a1leqb1]
    have monog : StrictMono gM := by
      simp [StrictMono]
      intro a_fM b_fM aleqb_fM
      simp [gM]
      have abeqfm : a_fM = 0 ∧ b_fM = 1 := by omega
      obtain ⟨a_fM_eq_zero, b_fM_eq_one⟩ := abeqfm
      simp [a_fM_eq_zero, b_fM_eq_one, a2leqb2]

    refine ⟨fM, monof, gM, monog, by
    intro a' b' idab
    simp [identityPattern] at idab
    rw [idab]
    simp [fM, gM]
    subst b'
    fin_cases a';simp
    exact hmaa
    exact hmbb
   ⟩
  | inr hbla =>
    obtain ⟨a1leqb1, a2leqb2⟩ := hbla
    let fM : Fin 2 → Fin n := ![b.1, a.1]
    let gM : Fin 2 → Fin n := ![b.2, a.2]
    have monof : StrictMono fM := by
      simp [StrictMono]
      intro a_fM b_fM aleqb_fM
      simp [fM]
      have abeqfm : a_fM = 0 ∧ b_fM = 1 := by omega
      obtain ⟨a_fM_eq_zero, b_fM_eq_one⟩ := abeqfm
      simp [a_fM_eq_zero, b_fM_eq_one, a1leqb1]
    have monog : StrictMono gM := by
      simp [StrictMono]
      intro a_fM b_fM aleqb_fM
      simp [gM]
      have abeqfm : a_fM = 0 ∧ b_fM = 1 := by omega
      obtain ⟨a_fM_eq_zero, b_fM_eq_one⟩ := abeqfm
      simp [a_fM_eq_zero, b_fM_eq_one, a2leqb2]

    refine ⟨fM, monof, gM, monog, ?_⟩
    intro a' b' idab
    simp [identityPattern] at idab
    rw [idab]
    simp [fM, gM]
    subst b'
    fin_cases a';simp
    exact hmbb
    exact hmaa

theorem exIdentity2  (n : ℕ)[NeZero n]: 2*n-1 = ex (identityPattern 2) n :=
  Eq.symm (Nat.le_antisymm  (exIdentity2UB n) (exIdentity2LB n))

lemma exVerticalTwoPattern (n : ℕ) [NeZero n] : ex VerticalTwoPattern n = n := by
  have UB: ex VerticalTwoPattern n ≤ n := ?Proof_UB
  have LB: n ≤ ex VerticalTwoPattern n := ?Proof_LB
  exact Nat.le_antisymm UB LB

  case Proof_LB =>
    let  M (i j : Fin n) : Prop := i = (0 : Fin n)
    have : ¬contains VerticalTwoPattern M := ?proof_of_M_avoids_VerticalTwoPattern
    have : n ≤ density M := ?proof_of_Mhasn
  -- Main proof starts here --
    rw [le_ex_iff]
    use M
    case P_nonempty => simp [VerticalTwoPattern]; exact ⟨0, by simp⟩

    case proof_of_Mhasn =>
      rw [density]
      simp [M]
      let s : Finset (Fin n × Fin n) := (filter (fun x : Fin n × Fin n ↦ x.1 = 0) univ)
      let f : ℕ → Fin n × Fin n := fun (j) ↦ ( 0 , j)

      have f_inj : ∀ i < n, ∀ j < n, f i = f j → i = j := by
        intro i hi j hj fieqfj
        simp [f] at fieqfj

        have natCast_injOn_Fin := CharP.natCast_injOn_Iio (Fin n) n -- coercion N -> Fin n is only injective on [0, n[
        apply natCast_injOn_Fin at fieqfj; simpa;simpa;simpa
        -- Daniel Weber said that the problem is that (5 : Fin 3) = (8 : Fin 3), so you need h1 and h2 to remove the cast.
        -- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Casting.20Fin.20n.20to.20Nat/near/474463179
        --apply_fun Fin.val at fieqfj
        --rwa [Fin.val_cast_of_lt hi, Fin.val_cast_of_lt hj] at fieqfj

      refine le_card_of_inj_on_range f ?_ f_inj
      intro i hi
      simp [f]

    case proof_of_M_avoids_VerticalTwoPattern =>
      by_contra cont
      rw [contains, VerticalTwoPattern] at cont
      obtain ⟨f, hf, g, hg, prop⟩ := cont
      simp [StrictMono] at hf hg
      simp at prop
      specialize prop 1
      have fmono: f 0 < f 1 := by simp [hf]
      rw [prop] at fmono
      contradiction
      exact 0
      simp

  case Proof_UB =>
    classical
    rw [ex]
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
    rw [contains]
    have: a.2 = b.2 := by
      simp [f] at ha' hb'
      rw [← ha'] at hb'
      omega

    have dominance : (a.1 < b.1) ∨ (b.1 < a.1) := by
      have: a.1 ≠ b.1 := ?_
      aesop
      by_contra a1b1
      apply hab
      aesop

    let g := ![a.2]
    have gmono : StrictMono g := by simp [StrictMono]

    cases dominance with
    | inl ab =>
      let f := ![a.1, b.1]
      have fmono : StrictMono f := by
        simp [f, StrictMono]
        intro i j hij
        have abeqfm : i = 0 ∧ j = 1 := by omega
        obtain ⟨hi', hj'⟩ := abeqfm
        simp [hi', hj', ab]

      refine⟨f, fmono, g, gmono, ?_⟩
      simp [VerticalTwoPattern]
      intro a b
      fin_cases a;aesop;aesop
    | inr ba =>
      let f := ![b.1, a.1]
      have fmono : StrictMono f := by
        simp [f, StrictMono]
        intro i j hij
        have abeqfm : i = 0 ∧ j = 1 := by omega
        obtain ⟨hi', hj'⟩ := abeqfm
        simp [hi', hj', ba]
      refine⟨f, fmono, g, gmono, ?_⟩
      simp [VerticalTwoPattern]
      intro a b
      fin_cases a;aesop;aesop

-- Finset.card_disjiUnion
-- open BigOperators
example (n :ℕ) : ex Horizontal2Pattern n ≤ n := by
  classical
  simp [ex]
  intro M noH2P
  let Pred_min_Ofrow := fun i j ↦ ∀ j', M i j' → j ≤ j'
  let M1 (i j : Fin n) : Prop := M i j ∧  (Pred_min_Ofrow i j)
  let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (Pred_min_Ofrow i j)

  have dm1: density M1 ≤ n:= ?proof_dm1
  have M2_avoids_trivial : ¬ contains onePattern M2 := ?proof_M2_av_trivial
  have dm2: density M2 ≤ 0 := calc
    density M2 ≤ ex onePattern n := avoid_le_ex M2 M2_avoids_trivial
    _ = 0 := exPatternOne n

  calc
    density M = density M1 + density M2 := split_density M Pred_min_Ofrow
    _        ≤ n + density M2      := by simp only [dm1, add_le_add_iff_right]
    _        ≤ n + 0              := by simp only [dm2, add_le_add_iff_left]
    _        ≤ n                  := by omega

  ---
  case proof_M2_av_trivial =>
    by_contra contains_one
    simp [contains] at contains_one
    obtain ⟨f, hf, g, hg, prop⟩ := contains_one
      --  M2    g(0)
      -- f(0)    1
    simp [M2] at prop
    specialize prop 0 0
    simp [onePattern, Pred_min_Ofrow] at prop
    obtain ⟨a, ha, ha2⟩ := prop.2
       --  M  a g(0)
      -- f(0) 1 1
    have : contains Horizontal2Pattern M := by
      let g' := ![a, g 0]
      have hg' : StrictMono g' := by
        simp [StrictMono];
        intro x y hxy;
        fin_cases x <;> fin_cases y <;> all_goals (aesop)
      rw [contains]
      refine ⟨f, hf, g', hg', by
        -- show embedding of [1 1] pattern
        intro a b _
        fin_cases a ; fin_cases b <;> all_goals (aesop)
      ⟩
    contradiction

  case proof_dm1 =>
    have h_row_one: ∀ i, row_density M1 i ≤ 1 := by
      intro i
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

    have:= density_by_rows_ub M1 h_row_one; simp at this
    exact this

theorem ex_horizontal (k n: ℕ) : ex (horizontalkPattern k) n ≤ n*(k-1) := by
  classical
  simp only [ex, Finset.sup_le_iff, mem_filter, Finset.mem_univ, true_and]
  intro M NoHPk
  have h_row_k: ∀ i, row_density M i ≤ k-1 := ?proof_h_row_k
  exact density_by_rows_ub M h_row_k

  case proof_h_row_k =>
    intro i
    by_contra H
    simp at H
    simp [row_density] at H
    let s : Finset (Fin n) := {j | M i j}
    have h: k ≤ s.card := by simp [s]; omega
    let g := s.orderEmbOfCardLe h
    have: contains (horizontalkPattern k) M := ?proof_HPk
    contradiction
    case proof_HPk =>
      simp [contains]
      refine ⟨![i], by simp [StrictMono], g, by simp [StrictMono, OrderEmbedding.lt_iff_lt], ?EmbedPatttern⟩
      · -- Proof of Embed Pattern
        simp [horizontalkPattern]
        intro j
        have: g j ∈ s := s.orderEmbOfCardLe_mem h j
        simp [s] at this
        exact this

theorem ex_vertical (k n : ℕ) : ex (verticalkPattern k) n ≤ n*(k-1) := by
  classical
  have: ex (verticalkPattern k) n ≤ ex ( tranpose (verticalkPattern k)) n := ?exv

  calc
    ex (verticalkPattern k) n ≤ ex ( tranpose (verticalkPattern k)) n := this
    _                        = ex ( horizontalkPattern k) n := by rfl
    _                        ≤ n*(k-1) := ex_horizontal k n

  case exv =>
    simp [ex]
    intro M hM
    rw [← ex]
    let M' := tranpose M
    have hM': ¬ contains (tranpose (verticalkPattern k)) M' := by
      by_contra H
      obtain ⟨f, hf, g, hg, emb_pat_to_M'⟩ := H
      have: contains (verticalkPattern k) M := by
        refine ⟨g, hg, f, hf, by
          intro a b
          apply emb_pat_to_M'
        ⟩
      contradiction

    have dmeqdm' : density M = density M' := by
      apply Finset.card_bij (fun a _ ↦ (a.2, a.1)) ?hi ?i_inj ?i_surj; aesop;aesop;aesop

    calc
      density M = density M' := dmeqdm'
      _        ≤ ex (tranpose (verticalkPattern k)) n := (avoid_le_ex M' hM')


theorem ex_hat (n : ℕ) [NeZero n] : ex HatPattern n ≤ 3*n := by
  classical
  simp [ex]
  intro M noHat

  let min_or_max_of_row := fun i j ↦ (∀ j', M i j' → j ≤ j') ∨ (∀ j', M i j' → j' ≤ j)
  let M1 (i j : Fin n) : Prop := M i j ∧  (min_or_max_of_row i j)
  let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (min_or_max_of_row i j)

  have M1_avoids_H3 : ¬ contains (horizontalkPattern 3) M1  := ?proof_M1_avoids_H3
  have M2_avoids_V2 : ¬ contains VerticalTwoPattern M2      := ?proof_M2_avoids_V2

  have dm1: density M1 ≤ n*2 := calc
     density M1 ≤ ex  (horizontalkPattern 3) n := avoid_le_ex M1 M1_avoids_H3
     _         ≤ n*2                         := ex_horizontal 3 n

  have dm2: density M2 ≤ n := calc
    density M2 ≤ ex VerticalTwoPattern n := avoid_le_ex M2 M2_avoids_V2
    _         = n                      := exVerticalTwoPattern  n

  calc
    density M = density M1 + density M2 := split_density M min_or_max_of_row
    _        ≤ n*2 + density M2      := by simp [dm1]
    _        ≤ n*2 + n              := by simp [dm2]
    _        ≤ 3*n                  := by omega

  --
  case proof_M1_avoids_H3 =>
    by_contra containsH3
    simp [contains] at containsH3
    obtain ⟨f, _, g, g_mono, prop⟩ :
      ∃ f, StrictMono f ∧
      ∃ g, StrictMono g ∧
      ∀ (a : Fin 1) (b : Fin 3),
        horizontalkPattern 3 a b → M1 (f a) (g b)
      := containsH3
    simp [horizontalkPattern] at prop
    -- prop:
    -- M1   g(0) g(1) g(2)
    -- f(0) 1   1   1
    simp [M1] at prop
    obtain ⟨_, h_min_max_g1⟩ : M (f 0) (g 1) ∧ min_or_max_of_row (f 0) (g 1) := prop 0 1
    -- since g(1) in M1, g(1) is either min or max
    cases h_min_max_g1 with
     | inl g1_min =>
      have: g 1 ≤ g 0 := by aesop (add simp g1_min)
      have: g 0 < g 1 := by aesop (add simp g_mono)
      omega
     | inr g1_max =>
      have: g 2 ≤ g 1 := by aesop (add simp g1_max)
      have: g 1 < g 2 := by aesop (add simp g_mono)
      omega

  case proof_M2_avoids_V2 =>
    by_contra containsV2
    simp [contains] at containsV2
    obtain ⟨f, hf, g, _, v2_to_M2⟩ :
      ∃ f, StrictMono f ∧
      ∃ g, StrictMono g ∧
      ∀ (a : Fin 2) (b : Fin 1),
      VerticalTwoPattern a b → M2 (f a) (g b)
      := containsV2
    simp [VerticalTwoPattern, M2] at v2_to_M2

    -- v2_to_M2:
    -- M2  g(0)
    -- f(0) 1
    -- f(1) 1

    let i := f 1
    let j := g 0

    obtain ⟨_, h_non_min_max⟩ := v2_to_M2 1 0 (by simp)
    simp [min_or_max_of_row] at h_non_min_max
    obtain ⟨⟨a, ha1, ha2⟩, ⟨b, hb1, hb2⟩⟩ : (∃ a, M i a ∧ a < j) ∧ (∃ b, M i b ∧ j < b) := h_non_min_max

    --  M   a j b
    -- f(0)    1
    --  i   1    1

    let g' : Fin 3 → Fin n:= ![ a, j , b]
    have monog' : StrictMono g' := by
      simp [StrictMono]
      intro x y _
      fin_cases x <;> fin_cases y <;> simp [g'] <;> all_goals (first| contradiction | omega)

    have : contains HatPattern M := by
      rw [contains]
      refine ⟨f, hf, g', monog', by
        intro x y _
        fin_cases x <;> fin_cases y <;> all_goals (aesop (add simp HatPattern))
      ⟩
    contradiction
