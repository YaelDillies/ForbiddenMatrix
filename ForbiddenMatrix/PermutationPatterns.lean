import ForbiddenMatrix.SmallPatterns
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.Qify

attribute [gcongr] Nat.sub_lt_sub_right

instance Fin.instNontrivial {n : ℕ} [Fact <| 2 ≤ n] : Nontrivial (Fin n) :=
  nontrivial_iff_two_le.2 Fact.out

@[simp, norm_cast] lemma Fin.natCast_val_eq_zmodFinEquiv {n : ℕ} [NeZero n] (a : Fin n) :
    a = ZMod.finEquiv n a := by
  obtain _ | n := n
  · obtain ⟨_, ⟨⟩⟩ := a
  · change (⟨_, _⟩ : ZMod (n + 1)) = ⟨_, _⟩
    congr
    simp

open Finset Set OrderDual Equiv

variable {k n q : ℕ}

/-! ### Definitions -/

def PermPattern (σ : Equiv.Perm (Fin n)) (i j : Fin n) : Prop := σ i = j

@[simp] lemma permPattern_one (n : ℕ) :
    PermPattern (1 : Equiv.Perm (Fin n)) = IdentityPattern n := rfl

@[simp] lemma permPattern_refl (n : ℕ) :
    PermPattern (.refl _ : Equiv.Perm (Fin n)) = IdentityPattern n := rfl

/-! ### Proofs -/

theorem ex_identityPattern_le (k n : ℕ) : ex (IdentityPattern k) n ≤ (2 * n - 1) * (k - 1) := by
  obtain rfl | hn := eq_zero_or_neZero n
  · simp
  classical
  simp only [ex, Finset.sup_le_iff, mem_filter, Finset.mem_univ, true_and]
  intro M avoid_Ik
  by_contra! M_large_density
  let d : Fin n × Fin n → ℤ := fun ⟨i, j⟩ ↦ i - j
  let s : Finset (Fin n × Fin n) := {(i, j) : Fin n × Fin n | M i j}
  let t : Finset ℤ := Icc (-n + 1) (n - 1)
  obtain ⟨p, hp, hp'⟩ : ∃ p ∈ t, k - 1 < #{x ∈ s | d x = p} := by
    apply exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    · simp [s, d, t]; omega
    convert M_large_density
    simp [t]
    omega
  let fiber : Finset (Fin n × Fin n) := {x ∈ s | d x = p}
  let fiberSnd : Finset (Fin n) := {x.2 | x ∈ fiber}
  have card_fiber : #fiber = #fiberSnd := by apply card_bij fun a _ ↦ a.2 <;> aesop
  have le_card_fiberSnd : k ≤ #fiberSnd := by simp [← card_fiber, fiber]; omega
  let g := fiberSnd.orderEmbOfCardLe le_card_fiberSnd
  let f (i : Fin k) : Fin n := (ZMod.finEquiv n).symm p + g i
  have f_spec a (a' : Fin n) (ha : a' - g a = p) : f a = a' := by simp [f, ← ha]
  have mono_f : StrictMono f := fun a b hab ↦ by
    have hga : g a ∈ fiberSnd := fiberSnd.orderEmbOfCardLe_mem _ a
    have hgb : g b ∈ fiberSnd := fiberSnd.orderEmbOfCardLe_mem _ b
    simp [fiberSnd, fiber, d] at hga hgb
    obtain ⟨a', -, ha'⟩ := hga
    obtain ⟨b', -, hb'⟩ := hgb
    have hgab : g a < g b := by simpa
    have hab' : a' < b' := by omega
    simpa [f_spec _ _ ha', f_spec _ _ hb'] using hab'
  refine avoid_Ik ⟨f, mono_f, g, by simp [StrictMono], ?_⟩
  simp [IdentityPattern]
  intro a
  have hga : g a ∈ fiberSnd := fiberSnd.orderEmbOfCardLe_mem _ a
  simp [fiberSnd, fiber, d, s] at hga
  obtain ⟨a', hfa', ha'⟩ := hga
  simpa [f_spec _ _ ha'] using hfa'

/-! ### Marcus Tardos' theorem -/

@[simp] private
lemma le_mul_div_add_one {n q : ℕ} (p : Fin n) (h : 0 < q) : p < q * (p / q + 1) := by
  rw [Nat.mul_comm]
  exact Nat.lt_mul_of_div_lt (Nat.lt_add_one _) h

def rectPtsetq (n q i j : ℕ) := rectPtset n (q * i) (q * (i+1)) (q * j) (q * (j+1))

open scoped Classical in noncomputable
def rectPtsetqMatrix (M : Fin n → Fin n → Prop) (q i j : ℕ) : Finset (Fin n × Fin n) :=
  {(a, b) | M a b ∧ (a, b) ∈ rectPtsetq n q i j}

@[simp] private lemma card_intervalq (n q i : ℕ) (hn : 0 < n) (hq : q ∣ n) (h : i < n / q) :
    #{a : Fin n | ↑a ∈ Finset.Ico (q * ↑i) (q * (↑i + 1))} = q := by
  have hy : q * (i + 1) ≤ n := by
    observe h1 : q * (n / q - 1) = q * (n / q) - q
    observe h2 : q * (n / q) = n
    observe : i ≤ n / q - 1
    observe h3 : q * i ≤ q * (n / q - 1)
    calc
          q * (i+1)
      _ = q * i + q := rfl
      _ ≤ q * (n / q -1) + q := Nat.add_le_add_right h3 q
      _ = (q * (n / q) - q) + q := Nat.add_right_cancel_iff.mpr h1
      _ = n := by
        rw [h2]
        have : n - q + q = n + q - q := by
          have := Nat.le_of_dvd hn hq
          omega
        rw [this]
        exact Eq.symm (Nat.eq_sub_of_add_eq rfl)
  calc
     #{a : Fin n | ↑a ∈ Finset.Ico (q * ↑i) (q * (↑i + 1))}
      = #(.Ico (q * ↑i) (q * (↑i + 1))) := card_interval (q * i) (q * (i + 1)) hy
     _ = (q * (↑i + 1)) - (q * ↑i) := Nat.card_Ico (q * i) (q * (i + 1))
     _ = q := Nat.sub_eq_of_eq_add' rfl

@[simp] private lemma card_rectPtsetq (n q i j : ℕ) (hq : q ∣ n) (h : i < n / q ∧ j < n / q) :
    #(rectPtsetq n q i j) = q * q := by
  simp [rectPtsetq]
  convert card_rectPtSet n (q * i) (q * (i+1)) (q * j) (q * (j+1)) _
  · exact Nat.eq_sub_of_add_eq' rfl
  · exact Nat.eq_sub_of_add_eq' rfl
  obtain ⟨hi, hj⟩ := h
  constructor
  · calc
      q * (i+1) ≤ q * (n / q) := Nat.mul_le_mul_left q hi
      _     = n    := Nat.mul_div_cancel' hq
  · calc
      q * (j+1) ≤ q * (n / q) := Nat.mul_le_mul_left q hj
      _     = n    := Nat.mul_div_cancel' hq

@[simp] private lemma card_rectPtsetqMatrix (M : Fin n → Fin n → Prop) (hq : q ∣ n) (i j : ℕ)
    (h : i < n / q ∧ j < n / q) : #(rectPtsetqMatrix M q i j) ≤ q * q := by
  calc
    #(rectPtsetqMatrix M q i j)
    _ ≤ #(rectPtsetq n q i j) := ?_
    _ = q * q := card_rectPtsetq n q i j hq h
  -- proof of the claim
  refine Finset.card_le_card ?_
  simp only [rectPtsetqMatrix, rectPtsetq, Prod.mk.eta]
  intro p h
  simp at h
  exact h.2

def blkMatrix (M : Fin n → Fin n → Prop) (q : ℕ) : Fin (n / q) → Fin (n / q) → Prop :=
  fun i j ↦ ∃ p : Fin n × Fin n, M p.1 p.2 ∧ p ∈ rectPtsetq n q i j

open scoped Classical in noncomputable
def blk_den (M : Fin n → Fin n → Prop) (i j : Fin (n / q)) : ℕ := #(rectPtsetqMatrix M q i j)

@[simp] private lemma p_to_pq {p : Fin n × Fin n} (hq : q ≠ 0) :
    p ∈ rectPtset n (q * (p.1 / q)) (q * (p.1 / q + 1)) (q * (p.2 / q)) (q * (p.2 / q + 1)) := by
  simp only [rectPtset, Finset.mem_Ico, mem_product, mem_filter, Finset.mem_univ, true_and]
  constructor <;> exact ⟨Nat.mul_div_le .., le_mul_div_add_one _ <| by omega⟩

open scoped Classical
theorem den_eq_sum_blk_den (M : Fin n → Fin n → Prop) (hqn : q ∣ n) :
    let B := blkMatrix M q
    density M = ∑ ⟨i, j⟩ : Fin (n / q) × Fin (n / q) with B i j, blk_den M i j := by
  obtain rfl | hn := eq_zero_or_neZero n
  · simp [density, blkMatrix]
  obtain rfl | hq := eq_zero_or_neZero q
  · simp [NeZero.ne n] at hqn
  let B := blkMatrix M q
  let Q := Fin (n / q) × Fin (n / q)
  let N := Fin n × Fin n
  let fq (x : Fin n) : Fin (n / q) := ⟨x / q, Nat.div_lt_div_of_lt_of_dvd hqn x.isLt⟩
  let s : Finset N := {(x, y)| M x y}
  let f : N → Q := fun (i, j) ↦ (fq i, fq j)
  let t : Finset Q := {(i, j)| B i j}
  have H : ∀ x ∈ s, f x ∈ t := by
    intro p hp
    simp only [mem_filter, Finset.mem_univ, true_and, s] at hp
    simp only [mem_filter, Finset.mem_univ, true_and, t, B, blkMatrix]
    refine ⟨p, hp, p_to_pq ?_⟩
    rintro rfl
    obtain rfl : n = 0 := by simpa using hqn
    obtain ⟨_, ⟨⟩⟩ := p.1
  have h_sum_card := Finset.card_eq_sum_card_fiberwise H
  suffices claim : ∀ k, #{x ∈ s | f x = k} = blk_den M k.1 k.2 by simpa [← claim]
  -- proof of the last claim
  intro k
  dsimp [blk_den, rectPtsetMatrix]
  apply Finset.card_bij (fun (p : Fin n × Fin n) _ ↦ p) ?hi ?i_inj ?i_surj
  · intro p hp
    simp only [mem_filter, Finset.mem_univ, true_and, s] at hp
    simp only [rectPtsetqMatrix, rectPtsetq, Prod.mk.eta, mem_filter, Finset.mem_univ, true_and]
    have := NeZero.ne q
    aesop
  · -- i_inj
    aesop
  -- i_surj : ∀ b ∈ t, ∃ a, ∃ (ha : a ∈ s), i a ha = b
  intro p hp
  simp only [Prod.mk.eta, mem_filter, Finset.mem_univ, true_and, rectPtsetqMatrix, rectPtsetq]
    at hp
  simp only [mem_filter, Finset.mem_univ, true_and, exists_prop, exists_eq_right, s]
  refine ⟨hp.1, ?_⟩
  replace hp := hp.2
  simp [rectPtset] at hp
  obtain ⟨⟨p1l, p1h⟩, p2l, p2h⟩ := hp
  simp [f, fq]
  ext
  · simp
    have : ↑p.1 / q = k.1 := by apply Nat.div_eq_of_lt_le; rwa [mul_comm]; rwa [mul_comm]
    aesop
  · simp
    have : ↑p.2 / q = k.2 := by apply Nat.div_eq_of_lt_le; rwa [mul_comm]; rwa [mul_comm]
    aesop

private lemma f_pt_to_blk {n q : ℕ} (hqn : q ∣ n) {i j : Fin (n / q)} {a b : Fin n}
    (H : (a, b) ∈ rectPtsetq n q i j) :
    let fq (x : Fin n) : Fin (n / q) := ⟨x / q, Nat.div_lt_div_of_lt_of_dvd hqn x.isLt⟩
    fq a = i ∧ fq b = j := by
  extract_lets fq
  simp [rectPtsetq, rectPtset] at H
  obtain ⟨⟨la, ua⟩, lb, ub⟩ := H
  simp [fq]
  constructor
  · suffices ↑a / q = i from by exact Fin.eq_of_val_eq this
    apply Nat.div_eq_of_lt_le
    · rwa [mul_comm]
    · rwa [mul_comm]
  · suffices ↑b / q = j from by exact Fin.eq_of_val_eq this
    apply Nat.div_eq_of_lt_le
    · rwa [mul_comm]
    · rwa [mul_comm]

lemma den_submatrix_eq_sum_blk_den (M : Fin n → Fin n → Prop)
    (hqn : q ∣ n) (f1 : Fin (n / q) → Fin (n / q) → Prop) :
    let B := blkMatrix M q
    let B1 (i j : Fin (n / q)) : Prop := B i j ∧ f1 i j
    let fq (x : Fin n) : Fin (n / q) := ⟨x / q, Nat.div_lt_div_of_lt_of_dvd hqn x.isLt⟩
    let M1 (i j : Fin n) : Prop := M i j ∧ B1 (fq i) (fq j);
    let Q := Fin (n / q) × Fin (n / q)
    density M1 = ∑ ⟨i, j⟩ : Q with B1 i j, blk_den M i j := by

  extract_lets B B1 fq M1 Q
  have B1_eq_blockM1 : B1 = blkMatrix M1 q := by
    simp! [B1, B, blkMatrix, M1]
    ext i j
    constructor
    · rintro ⟨⟨a, b, Hab, Hab2⟩, h_f1ij⟩
      simp [blkMatrix]
      use a, b
      obtain ⟨fqa, fqb⟩ : fq a = i ∧ fq b = j := f_pt_to_blk hqn Hab2
      rw [fqa, fqb]
      refine ⟨⟨Hab, ?_, h_f1ij⟩, Hab2⟩
      use a, b
    · intro h
      simp [blkMatrix] at h
      obtain ⟨a, b, ⟨h1, _, h2⟩ , r⟩ := h
      obtain ⟨fqa, fqb⟩ : fq a = i ∧ fq b = j := f_pt_to_blk hqn r
      rw [fqa, fqb] at h2
      refine ⟨?_, h2⟩
      use a, b

  have h_only_M1 :
      ∑ ⟨i, j⟩ : Q with B1 i j, blk_den M i j = ∑ ⟨i, j⟩ : Q with B1 i j, blk_den M1 i j := by
    suffices ∀ p : Q, B1 p.1 p.2 → (blk_den M p.1 p.2 = blk_den M1 p.1 p.2) by
      let s : Finset Q := {p : Q | B1 p.1 p.2}
      show ∑ p ∈ s, blk_den M p.1 p.2 = ∑ p ∈ s, blk_den M1 p.1 p.2
      rw [Finset.sum_eq_sum_iff_of_le];aesop;aesop
    intro p hp
    simp [blk_den]
    suffices rectPtsetqMatrix M q p.1 p.2 = rectPtsetqMatrix M1 q p.1 p.2 by rw [this]
    simp [M1]
    simp [B1, B, blkMatrix] at hp
    obtain ⟨⟨a, b, _, H⟩, _⟩ := hp
    ext x
    simp only [rectPtsetqMatrix,  Prod.mk.eta, mem_filter, Finset.mem_univ, true_and,
      and_congr_left_iff, iff_self_and]
    intro hx hx2
    simp [B1, B, blkMatrix]
    obtain ⟨lx, rx⟩ : fq x.1 = p.1 ∧ fq x.2 = p.2 := f_pt_to_blk hqn hx
    constructor
    · use a, b
      aesop
    · aesop

  simp at h_only_M1
  have := den_eq_sum_blk_den M1 hqn; simp at this
  simp [B1]
  conv at this =>
    conv =>
      enter [2, 1, 1]
      intro
      rw [← B1_eq_blockM1]
    right
    rw [← h_only_M1]
  exact this

lemma split_density_blk {n q : ℕ} (hqn : q ∣ n) (M : Fin n → Fin n → Prop)
    (f1 f2 : Fin (n / q) → Fin (n / q) → Prop) :
    let Q := Fin (n / q) × Fin (n / q)
    let f3 := fun i j ↦ (¬ f1 i j) ∧ ¬ (f2 i j)
    let B := blkMatrix M q
    let B1 (i j : Fin (n / q)) : Prop := B i j ∧ f1 i j
    let B2 (i j : Fin (n / q)) : Prop := B i j ∧ f2 i j
    let N  (i j : Fin (n / q)) : Prop := B i j ∧ f3 i j

    density M ≤ ∑ ⟨i, j⟩ : Q with B1 i j, blk_den M i j +
                ∑ ⟨i, j⟩ : Q with B2 i j, blk_den M i j +
                ∑ ⟨i, j⟩ : Q with N i j, blk_den M i j
            := by
  obtain rfl | hn := eq_zero_or_neZero n
  · simp [density, blkMatrix]
  obtain rfl | hq := eq_or_ne q 0
  · simp [NeZero.ne n] at hqn
  extract_lets Q f3 B B1 B2 N

  let fq (x : Fin n) : Fin (n / q) := ⟨x / q, Nat.div_lt_div_of_lt_of_dvd hqn x.isLt⟩
  let P1 (i j : Fin n) : Prop := B1 (fq i) (fq j)
  let P2 (i j : Fin n) : Prop := B2 (fq i) (fq j)
  let P3 (i j : Fin n) : Prop := N (fq i) (fq j)

  let M1 (i j : Fin n) : Prop := M i j ∧ P1 i j
  let M2 (i j : Fin n) : Prop := M i j ∧ P2 i j
  let M3 (i j : Fin n) : Prop := M i j ∧ P3 i j

  suffices density M ≤ density M1 + density M2 + density M3 from by
    have : density M1 = ∑ ⟨i, j⟩ : Q with B1 i j, blk_den M i j := by
      convert den_submatrix_eq_sum_blk_den M hqn f1
    have : density M2 = ∑ ⟨i, j⟩ : Q with B2 i j, blk_den M i j := by
      convert den_submatrix_eq_sum_blk_den M hqn f2
    have : density M3 = ∑ ⟨i, j⟩ : Q with N i j , blk_den M i j := by
      convert den_submatrix_eq_sum_blk_den M hqn f3
    omega

  let M1' (i j : Fin n) : Prop := M i j ∧ ¬ P1 i j
  let M2' (i j : Fin n) : Prop := M1' i j ∧ P2 i j
  let M3' (i j : Fin n) : Prop := M1' i j ∧ ¬P2 i j

  have h2 : density M1' = density M2' + density M3' := by exact split_density M1' P2
  have h3 : density M3' = density M3 := by
    suffices M3' = M3 by aesop
    ext i j
    simp [M3', M1']
    rw [and_assoc]
    simp [M3]
    intro Mij
    simp [P3, P1, P2, N, B1, B2, f3]
    suffices B (fq i) (fq j) by tauto
    simp [B, blkMatrix, rectPtsetq, fq]
    exact ⟨i, j, Mij, p_to_pq (p := (i, j)) hq⟩

  have : density M2' ≤ density M2 := by
    simp [density, M2', M2, M1']
    apply Finset.card_le_card
    intro p a
    simp_all

  calc
    density M = density M1 + density M1' := split_density M P1
    _        = density M1 + density M2' + density M3' := by omega
    _         ≤ density M1 + density M2' + density M3 := by omega
    _         ≤ density M1 + density M2 + density M3 := by omega

theorem sum_blk_den_le_mul_den_blk {c : ℕ} (M : Fin n → Fin n → Prop)
    (B : Fin (n / q) → Fin (n / q) → Prop) (h : ∀ i j, B i j → blk_den M i j ≤ c) :
    ∑ ⟨i, j⟩ : Fin (n / q) × Fin (n / q) with B i j, (blk_den M i j) ≤ c* density B := by
  let Q := Fin (n / q) × Fin (n / q)
  calc
    ∑ ⟨i, j⟩ : Q with B i j, blk_den M i j
    _ ≤ ∑ ⟨i, j⟩ : Q with B i j, c := by apply Finset.sum_le_sum;intros p hp; aesop
    _ = #{(i, j) | B i j }*c := sum_const_nat fun x ↦ congrFun rfl
    _ = c * density B := Nat.mul_comm ..

lemma av_perm_contract_av_perm (q : ℕ) (σ : Perm (Fin k)) (M : Fin n → Fin n → Prop)
    (hM : ¬ Contains (PermPattern σ) M) : ¬ Contains (PermPattern σ) (blkMatrix M q) := by
  by_contra H
  simp [Contains] at H
  obtain ⟨f, hf, g, hg, h⟩ := H
  simp only [PermPattern, blkMatrix, rectPtsetq, rectPtset, Finset.mem_Ico, mem_product, mem_filter,
    Finset.mem_univ, true_and, forall_eq'] at h
  choose fg hfg using h
  --           . . g (i) . .  |    . . g (σ i) . .
  -- .                         | .
  -- .                         | .
  -- f (σ⁻¹ i)        1        | f i        1
  -- .                         | .
  -- .                         | .
  refine hM ⟨Prod.fst ∘ fg, ?_, Prod.snd ∘ fg ∘ ↑σ⁻¹, ?_, ?_⟩
  · intro a b hab
    obtain ⟨A, ⟨B, ca_ub⟩, C, D⟩ := hfg a
    obtain ⟨E, ⟨cb_lb, F⟩, G, H⟩ := hfg b
    calc
      (fg a).1 < q * (f a + 1) := ca_ub
      _  ≤ q * f b := by gcongr; exact hf hab
      _  ≤ (fg b).1 := cb_lb
  · intro a b hab
    obtain ⟨A, B, C, ca_ub⟩ := hfg (σ⁻¹ a)
    obtain ⟨D, E, cb_lb, F⟩ := hfg (σ⁻¹ b)
    calc
      (fg <| σ⁻¹ a).2 < q * (g a + 1) := by simpa using ca_ub
      _  ≤ q * g b := by gcongr; exact hg hab
      _  ≤ (fg <| σ⁻¹ b).2 := by simpa using cb_lb
  · rintro i j rfl
    simpa using (hfg i).1

lemma density_WB {n k : ℕ} (h_n : 0 < n) (h_k : k ^ 2 ∣ n) (M : Fin n → Fin n → Prop)
     {σ : Perm (Fin k)} (M_avoid_perm : ¬ Contains (PermPattern σ) M) :
    let q := k ^ 2
    let B := blkMatrix M q
    let W (i j : Fin (n / q)) : Prop := k ≤ #{c | ∃ r, (r, c) ∈ rectPtsetqMatrix M q i j}
    let WB : Fin (n / q) → Fin (n / q) → Prop := fun i j ↦ W i j ∧ B i j
    density WB ≤ n / k ^ 2 * (k * (k ^ 2).choose k) := by

  extract_lets q B W WB

  suffices ∀ i, col_density WB i ≤ k * q.choose k from density_by_cols_ub WB this
  intro j
  by_contra! h_contra

  let C : Finset (Fin n) := {a : Fin n | ↑a ∈ Finset.Ico (q * j) (q * (j+1))}

  have WB_k_col i (hi : WB i j) :
      ∃ s ⊆ ({c | ∃ r, (r, c) ∈ rectPtsetqMatrix M q i j} : Finset (Fin n)), #s = k := by
    apply Finset.exists_subset_card_eq
    simp_all [WB, W]

  let f : Fin (n / q) → Finset (Fin n) := fun i ↦ if h : WB i j then (WB_k_col i h).choose else ∅
  let s := ({i | WB i j} : Finset (Fin (n / q))) -- all wide blocks
  let t := Finset.powersetCard k C -- all subset of the column of size k

  obtain ⟨S, hs, hs'⟩ : ∃ C' ∈ t, k - 1 < #{i ∈ s | f i = C'} := by
    apply exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    · --  ∀ a ∈ s, f a ∈ t
      simp [s, t, WB]
      intro i ha1 ha2
      observe h : WB i j
      observe : W i j ∧ B i j
      simp [f]
      constructor
      · -- ⊢ (if h : WB i j then ⋯.choose else ∅) ⊆ C
        intro x hx
        simp [C]
        simp only [this, and_self, ↓reduceDIte, WB] at hx
        have := (WB_k_col i h).choose_spec.1
        simp [rectPtsetqMatrix, rectPtsetq, rectPtset] at this

        rw [Finset.subset_iff] at this
        have :
          x ∈ ({c | ∃ r, M r c ∧
            (q * ↑i ≤ ↑r ∧ ↑r < q * (↑i + 1)) ∧ q * ↑j ≤ ↑c ∧ ↑c < q * (↑j + 1)} : Finset _) := by
          apply this
          convert hx
          simp only [rectPtsetqMatrix, rectPtsetq, rectPtset, Finset.mem_Ico, Prod.mk.eta,
            mem_product, mem_filter, Finset.mem_univ, true_and]
        simp at this
        obtain ⟨_, _, _, l, r⟩ := this
        exact ⟨l, r⟩
      · -- ⊢ #(if h : WB i j then ⋯.choose else ∅) =
        simp [WB, h]
        exact (WB_k_col i h).choose_spec.2
    · -- ⊢ #t * (k - 1) < #s
      have tcard_eq_qck : #t = (q.choose k) := by
        simp [t, q]
        suffices #C = k ^ 2 by rw [this]
        dsimp [C]
        refine card_intervalq n q ↑j h_n h_k ?h
        · -- ⊢ ↑j < n / q
          simp only [Fin.is_lt]

      calc
        #t * (k - 1)
        _ = (k - 1) * q.choose k := by rw [mul_comm, tcard_eq_qck]
        _ ≤ k * (q.choose k) := by gcongr; omega
        _ < col_density WB j := h_contra
        _ = #s := by simp [col_density, WB, s]; congr

  simp [mem_powersetCard, t] at hs
  obtain ⟨s_subset_C, s_card_k⟩ := hs
  -- simp [f] at hp'

  suffices Contains (PermPattern σ) M by contradiction
  simp [Contains]

  let RB := (filter (fun i ↦ f i = S) s)
  replace hs' : k ≤ #RB := by exact Nat.le_of_pred_lt hs'

  let g := S.orderEmbOfFin s_card_k
  observe g_mono : StrictMono g

  let f' := RB.orderEmbOfCardLe hs'
  have f'_prop i : ∃ p, M p.1 p.2 ∧ p ∈ rectPtsetq n q (f' i) j ∧ p.2 = g (σ i) := by
    have := RB.orderEmbOfCardLe_mem hs' i
    simp only [mem_filter, RB] at this
    obtain ⟨h1, h2⟩ := this
    replace h2 : f (f' i) = S := by congr
    replace h1 : f' i ∈ s := by congr
    simp only [f, WB] at h2
    simp only [mem_filter, Finset.mem_univ, true_and, s, WB] at h1
    obtain ⟨h4, h3⟩ := h1
    simp only [h4, h3, and_self, ↓reduceDIte] at h2
    observe h : WB (f' i) j
    have := (WB_k_col (f' i) h).choose_spec.1
    rw [h2] at this
    observe g_pi : g (σ i) ∈ S
    simp only [subset_iff, mem_filter, Finset.mem_univ, true_and] at this
    obtain ⟨r, hr⟩ : ∃ r, (r, (g (σ i))) ∈ rectPtsetqMatrix M q ↑(f' i) ↑j := this g_pi
    simp only [rectPtsetqMatrix, Prod.mk.eta, mem_filter, Finset.mem_univ, true_and] at hr
    obtain ⟨hr1, hr2⟩ := hr
    use (r, g (σ i))

  let f := fun i : Fin k ↦ (f'_prop i).choose.1

  have f_mono : StrictMono f := by
    simp only [StrictMono]
    intro a b hab
    have ha := (f'_prop a).choose_spec.2.1; simp [rectPtsetq, rectPtset] at ha
    have hb := (f'_prop b).choose_spec.2.1; simp [rectPtsetq, rectPtset] at hb
    obtain ⟨⟨X, ha_ub⟩, Y⟩ := ha
    obtain ⟨⟨hb_lb, XX⟩, YY⟩ := hb

    observe : f' a < f' b
    observe : ↑ (f' a : ℕ) +1 ≤ ↑(f' b : ℕ)

    calc
      f a < q * (↑(f' a) + 1) := by convert ha_ub; simp [rectPtsetq, rectPtset]
      _ ≤ q * ↑(f' b) := by exact Nat.mul_le_mul_left q this
      _ ≤ f b := by convert hb_lb; simp [rectPtsetq, rectPtset]

  refine ⟨f, f_mono, g, g_mono, ?_⟩

  · -- show embedding of permutation
    simp only [PermPattern, forall_eq', *]
    intro i
    obtain ⟨H, _, H'⟩ := (f'_prop i).choose_spec
    simp only [f]
    rwa [H'] at H

lemma density_TB {n k : ℕ} (h_n : 0 < n) (h_k : k ^ 2 ∣ n) (M : Fin n → Fin n → Prop)
    {σ : Perm (Fin k)} (M_avoid_perm : ¬ Contains (PermPattern σ) M) :
    let q := k ^ 2
    let B := blkMatrix M q
    let T (i j : Fin (n / q)) : Prop := k ≤ #{r | ∃ c, (r, c) ∈ rectPtsetqMatrix M q i j}
    let TB : Fin (n / q) → Fin (n / q) → Prop := fun i j ↦ T i j ∧ B i j
    density TB ≤ n / k ^ 2 * (k * (k ^ 2).choose k) := by

  let q := k ^ 2
  let B := blkMatrix M q
  let T (i j : Fin (n / q)) : Prop := k ≤ #{r | ∃ c, (r, c) ∈ rectPtsetqMatrix M q i j}
  let TB : Fin (n / q) → Fin (n / q) → Prop := fun i j ↦ T i j ∧ B i j

  suffices ∀ i, row_density TB i ≤ k * q.choose k from density_by_rows_ub TB this
  intro i
  by_contra! h_contra

  let R : Finset (Fin n) := {a : Fin n | ↑a ∈ Finset.Ico (q * i) (q * (i+1))}

  have TB_k_row j (_ : TB i j) :
      ∃ s ⊆ ({r | ∃ c, (r, c) ∈ rectPtsetqMatrix M q i j} : Finset (Fin n)), #s = k := by
    apply Finset.exists_subset_card_eq
    simp_all [TB, T]

  let f : Fin (n / q) → Finset (Fin n) := fun j ↦ if h : TB i j then (TB_k_row j h).choose else ∅
  let s := ({j | TB i j} : Finset (Fin (n / q))) -- all tall blocks
  let t := Finset.powersetCard k R -- all subset of the rows of size k

  obtain ⟨S, hs, hs'⟩ : ∃ C' ∈ t, k - 1 < #{i ∈ s | f i = C'} := by
    apply exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    · --  ∀ a ∈ s, f a ∈ t
      simp [s, t, TB]
      intro j ha1 ha2
      observe h : TB i j
      observe : T i j ∧ B i j
      simp [f]
      constructor
      · -- ⊢
        intro x hx
        simp [R]
        simp only [this, and_self, ↓reduceDIte, TB] at hx
        have := (TB_k_row j h).choose_spec.1
        simp [rectPtsetqMatrix, rectPtsetq, rectPtset] at this

        rw [Finset.subset_iff] at this
        have :
            x ∈ ({r | ∃ c, M r c ∧
              (q * ↑i ≤ ↑r ∧ ↑r < q * (↑i + 1)) ∧ q * ↑j ≤ ↑c ∧ ↑c < q * (↑j + 1)} : Finset _) := by
          apply this
          convert hx
          simp only [rectPtsetqMatrix, rectPtsetq, rectPtset, Finset.mem_Ico, Prod.mk.eta,
            mem_product, mem_filter, Finset.mem_univ, true_and]
        simp at this
        obtain ⟨_, _, l, _, _⟩ := this
        exact l
      · -- ⊢
        simpa [TB, h] using (TB_k_row j h).choose_spec.2
    · -- ⊢ #t * (k - 1) < #s
      have tcard_eq_qck : #t = (q.choose k) := by
        simp [t, q]
        suffices #R = k ^ 2 by rw [this]
        dsimp [R]
        refine card_intervalq n q ↑i h_n h_k ?h
        · -- ⊢ ↑j < n / q
          simp only [Fin.is_lt]

      calc
        #t * (k - 1)
        _ = (k - 1) * q.choose k := by rw [tcard_eq_qck, mul_comm]
        _ ≤ k * q.choose k := by gcongr; omega
        _ < row_density TB i := h_contra
        _ = #s := by simp [row_density, TB, s]; congr

  simp [mem_powersetCard, t] at hs
  obtain ⟨s_subset_R, s_card_k⟩ := hs

  suffices Contains (PermPattern σ) M by contradiction
  simp [Contains]

  let RB := (filter (fun i ↦ f i = S) s)
  replace hs' : k ≤ #RB := by exact Nat.le_of_pred_lt hs'

  let f' := S.orderEmbOfFin s_card_k
  observe f_mono : StrictMono f'
  let g' := RB.orderEmbOfCardLe hs'

  have g'_prop j : ∃ p, M p.1 p.2 ∧ p ∈ rectPtsetq n q i (g' j) ∧ p.1 = f' (σ⁻¹ j) := by
    have := RB.orderEmbOfCardLe_mem hs' j
    simp only [mem_filter, RB] at this
    obtain ⟨h1, h2⟩ := this
    replace h2 : f (g' j) = S := by congr
    replace h1 : g' j ∈ s := by congr
    simp only [f, TB] at h2
    simp only [mem_filter, Finset.mem_univ, true_and, s, TB] at h1
    obtain ⟨h4, h3⟩ := h1
    simp only [h4, h3, and_self, ↓reduceDIte] at h2
    observe h : TB i (g' j)
    have := (TB_k_row (g' j) h).choose_spec.1
    rw [h2] at this
    observe f'_pi : f' (σ⁻¹ j) ∈ S
    simp only [subset_iff, mem_filter, Finset.mem_univ, true_and] at this
    obtain ⟨c, hc⟩ : ∃ c, (f' (σ⁻¹ j), c) ∈ rectPtsetqMatrix M q ↑i  ↑(g' j) := this f'_pi
    simp only [rectPtsetqMatrix, Prod.mk.eta, mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨hr1, hr2⟩ := hc
    use (f' (σ⁻¹ j), c)

  let g := fun i : Fin k ↦ (g'_prop i).choose.2
  refine ⟨f', f_mono, g, ?_, ?_⟩
  · intro a b hab
    replace ha := (g'_prop a).choose_spec.2.1; simp [rectPtsetq, rectPtset] at ha
    replace hb := (g'_prop b).choose_spec.2.1; simp [rectPtsetq, rectPtset] at hb
    obtain ⟨_, _, ha_ub⟩ := ha
    obtain ⟨_, hb_lb, _⟩ := hb
    observe : g' a < g' b
    observe : (g' a : ℕ) + 1 ≤ (g' b : ℕ)
    calc
      g a < q * (g' a + 1) := by convert ha_ub; simp [rectPtsetq, rectPtset]
      _ ≤ q * g' b := by exact Nat.mul_le_mul_left q this
      _ ≤ g b := by convert hb_lb; simp [rectPtsetq, rectPtset]


  · -- show embedding of permutation
    simp only [PermPattern, forall_eq']
    have : (∀ a, M (f' (σ⁻¹ a)) (g a)) ↔ ∀ a, M (f' a) (g (σ a)) := σ⁻¹.forall_congr (by simp)
    rewrite [← this]
    intro j
    obtain ⟨H, _, H'⟩ := (g'_prop j).choose_spec
    simp only [g]
    rwa [H'] at H

lemma blk_den_SB {n : ℕ} (k : ℕ) (M : Fin n → Fin n → Prop) :
    let q := k ^ 2
    let B := blkMatrix M q
    let W (i j : Fin (n / q)) : Prop := k ≤ #{c | ∃ r, (r, c) ∈ rectPtsetqMatrix M q i j}
    let T (i j : Fin (n / q)) : Prop := k ≤ #{r | ∃ c, (r, c) ∈ rectPtsetqMatrix M q i j}
    let S : Fin (n / q) → Fin (n / q) → Prop := fun i j ↦ ¬ W i j ∧ ¬ T i j
    let SB : Fin (n / q) → Fin (n / q) → Prop := fun i j ↦ S i j ∧ B i j
    ∀ (i j : Fin (n / q)), SB i j → blk_den M i j ≤ (k - 1) ^ 2 := by

  extract_lets q B W T S SB
  intro i j hij
  simp [blk_den]
  simp [SB, S, W, T, B, blkMatrix]  at hij
  obtain ⟨⟨num_cols, num_rows⟩, _⟩ := hij
  let R := (filter (fun r ↦ ∃ c, (r, c) ∈ rectPtsetqMatrix M q ↑i ↑j) Finset.univ)
  let C := (filter (fun c ↦ ∃ r, (r, c) ∈ rectPtsetqMatrix M q ↑i ↑j) Finset.univ)
  have rc : #R ≤ k - 1 := Nat.le_sub_one_of_lt num_rows
  have cc : #C ≤ k - 1 := Nat.le_sub_one_of_lt num_cols
  suffices (rectPtsetSubsetMatrix M R C) = rectPtsetqMatrix M q ↑i ↑j by
    rw [← this]
    calc
          #(rectPtsetSubsetMatrix M R C)
        ≤ #R * #C := card_rectPtsetSubsetMatrix M R C
      _ ≤ (k - 1) * (k - 1) := Nat.mul_le_mul rc cc
      _ = (k - 1) ^ 2 := by rw [sq]
  show (rectPtsetSubsetMatrix M R C) = rectPtsetqMatrix M q ↑i ↑j
  · ext
    simp only [rectPtsetSubsetMatrix, Prod.mk.eta, mem_product, mem_filter,
      Finset.mem_univ, true_and, rectPtsetqMatrix, rectPtsetq, rectPtset, Finset.mem_Ico,
      and_congr_right_iff]
    intro hx
    simp only [rectPtsetqMatrix, rectPtsetq, rectPtset, Finset.mem_Ico, Prod.mk.eta,
      mem_product, mem_filter, Finset.mem_univ, true_and, R, C]
    aesop

private lemma blk_den_k4 (hkn : k ^ 2 ∣ n) (M : Fin n → Fin n → Prop) :
    let q := k ^ 2
    ∀ i j : Fin (n / q), blk_den M i j ≤ k ^ 4 := by
  extract_lets q
  observe hqn : q ∣ n
  intro i j
  have := card_rectPtsetqMatrix M hqn i j (by aesop)
  simp [blk_den]
  simp [q] at this
  simp [q]
  suffices k ^ 4 = k ^ 2 * k ^ 2 by rwa [this]
  simpa using Nat.pow_add k 2 2

private lemma k_pow_n_mul (hkn : k ^ 2 ∣ n) :
    let K := (k ^ 2).choose k
    k ^ 4 * (n / k ^ 2 * (k * K)) = n * k ^ 3 * K := by
  qify [hkn]
  ring_nf
  have := calc
        k ^ 5 * (n / k ^ 2)
    _ = k ^ 3 * (n / k ^ 2 * k ^ 2) := by group
    _ = k ^ 3 * n := by rw [Nat.div_mul_cancel ‹_›]
  qify at this
  rw [this, mul_right_comm]

lemma ex_perm_recurrence (σ : Perm (Fin k)) (n : ℕ) (hkn : k ^ 2 ∣ n) :
    ex (PermPattern σ) n
      ≤ (k - 1) ^ 2 * ex (PermPattern σ) (n / k ^ 2) + 2 * n * k ^ 3 * (k ^ 2).choose k := by
  obtain rfl | hn := eq_zero_or_neZero n
  · simp
  obtain rfl | hk := eq_zero_or_neZero k
  · simp [NeZero.ne n] at hkn
  obtain ⟨M, M_av_perm, M_max⟩ :
      ∃ M, ¬ Contains (PermPattern σ) M ∧ ex (PermPattern σ) n = density M := by
    apply exists_av_and_ex_eq; simp [PermPattern]

  let q : ℕ := k ^ 2
  let B := blkMatrix M q
  let Q := Fin (n / q) × Fin (n / q)

  let W (i j : Fin (n / q)) : Prop := k ≤ #{c | ∃ r, (r, c) ∈ rectPtsetqMatrix M q i j}
  let T (i j : Fin (n / q)) : Prop := k ≤ #{r | ∃ c, (r, c) ∈ rectPtsetqMatrix M q i j}
  let S (i j : Fin (n / q)) : Prop := ¬ W i j ∧ ¬ T i j
  let WB (i j : Fin (n / q)) : Prop := W i j ∧ B i j
  let TB (i j : Fin (n / q)) : Prop := T i j ∧ B i j
  let SB (i j : Fin (n / q)) : Prop := S i j ∧ B i j

  let K := (k ^ 2).choose k

  let sum_SB := ∑ ⟨i, j⟩ : Q with SB i j, blk_den M i j
  let sum_WB := ∑ ⟨i, j⟩ : Q with WB i j, blk_den M i j
  let sum_TB := ∑ ⟨i, j⟩ : Q with TB i j, blk_den M i j
  observe q_dvd_n : q ∣ n
  have den_le_sum : density M ≤ sum_WB + sum_TB + sum_SB := by
    simpa [WB, B, and_comm (a := blkMatrix ..), sum_SB, sum_WB, sum_TB]
      using split_density_blk q_dvd_n M W T
  have h_sum_SB : sum_SB ≤ (k - 1) ^ 2 * ex (PermPattern σ) (n / k ^ 2) := by
    show ∑ ⟨i, j⟩ : Q with SB i j, blk_den M i j ≤ (k - 1) ^ 2 * ex (PermPattern σ) (n / k ^ 2)
    have h1 : ∀ (i j : Fin (n / q)), SB i j → blk_den M i j ≤ (k - 1) ^ 2 := by
      convert blk_den_SB k M
    have h2 : density SB ≤ ex (PermPattern σ) (n / q) := by
      suffices ¬ Contains (PermPattern σ) SB from density_le_ex_of_not_contains SB this
      show ¬ Contains (PermPattern σ) SB
      · by_contra!
        simp only [Contains, SB] at this
        obtain ⟨f, hf, g, hg, H⟩ := this
        refine av_perm_contract_av_perm q _ M M_av_perm ?_
        simp only [Contains]
        refine ⟨f, hf, g, hg, ?_⟩
        show ∀ (a b : Fin k), PermPattern σ a b → blkMatrix M q (f a) (g b)
        intros
        simp_all only [- M_av_perm, ge_iff_le, not_le, and_imp, q, SB, S, W, T, B]
    calc
      ∑ ⟨i, j⟩ : Q with SB i j, blk_den M i j ≤ (k - 1) ^ 2 * density SB := by
        convert sum_blk_den_le_mul_den_blk M SB h1
      _ ≤ (k - 1) ^ 2 * ex (PermPattern σ) (n / q) := Nat.mul_le_mul_left ((k - 1) ^ 2) h2
  have : sum_WB ≤ n * k ^ 3 * K := by
    show  ∑ ⟨i, j⟩ : Q with WB i j, blk_den M i j ≤ n * k ^ 3 * K
    have blk_den_trivial : ∀ (i j : Fin (n / q)), blk_den M i j ≤ k ^ 4 := by
      apply blk_den_k4
      simp_all

    observe h1 : ∀ (i j : Fin (n / q)), WB i j → blk_den M i j ≤ k ^ 4

    calc
      ∑ ⟨i, j⟩ : Q with WB i j, blk_den M i j
        ≤ k ^ 4 * density WB := by convert sum_blk_den_le_mul_den_blk M WB h1
      _ ≤ k ^ 4 * ((n / k ^ 2) * (k * K)) := by
        gcongr
        exact density_WB (NeZero.pos _) hkn M M_av_perm
      _ = n * k ^ 3 * K := k_pow_n_mul hkn
  have : sum_TB ≤ n * k ^ 3 * K := by
    show ∑ ⟨i, j⟩ : Q with TB i j, blk_den M i j ≤ n * k ^ 3 * K
    have blk_den_trivial : ∀ (i j : Fin (n / q)), blk_den M i j ≤ k ^ 4 := by
      apply blk_den_k4
      simp_all
    observe h1 : ∀ (i j : Fin (n / q)), TB i j → blk_den M i j ≤ k ^ 4

    calc
      ∑ ⟨i, j⟩ : Q with TB i j, blk_den M i j
        ≤ k ^ 4 * density TB := by convert sum_blk_den_le_mul_den_blk M TB h1
      _ ≤ k ^ 4 * ((n / k ^ 2) * (k * K)) := by
        gcongr; exact density_TB (NeZero.pos _) hkn M M_av_perm
      _ = n * k ^ 3 * K := k_pow_n_mul hkn
  have h_sum_WB_TB : sum_WB + sum_TB ≤ 2 * (n * k ^ 3 * K) := by omega

  calc
    ex (PermPattern σ) n
    _ = density M := M_max
    _ ≤ sum_WB + sum_TB + sum_SB := den_le_sum
    _ ≤ 2 * (n * k ^ 3 * K) + sum_SB := Nat.add_le_add_right h_sum_WB_TB sum_SB
    _ ≤ 2 * (n * k ^ 3 * K) + (k - 1) ^ 2 * ex (PermPattern σ) (n/k ^ 2) := by gcongr
    _ = (k - 1) ^ 2 * ex (PermPattern σ) (n / k ^ 2) + 2 * n * k ^ 3 * K := by ring


private lemma ex_permutation_to_dvd (σ : Perm (Fin k)) (n : ℕ) (hkn : k ^ 2 < n) :
    let n' : ℕ := n - n % k ^ 2
    ex (PermPattern σ) n ≤ ex (PermPattern σ) n' + 2 * k ^ 2 * n := by
  obtain rfl | hk₁ := eq_zero_or_neZero k
  · simp [Subsingleton.elim σ (.refl _)]
  extract_lets n'
  observe : 0 < n
  observe o1 : k ^ 2 ∣ n'
  observe o_le : n' ≤ n
  observe : 0 < k ^ 2
  have n'_pos : 0 < n' := by
    observe o1 : n % k ^ 2 < k ^ 2
    calc
      0 < k ^ 2 - n % k ^ 2 := Nat.zero_lt_sub_of_lt o1
      _ < n - n % k ^ 2 := by gcongr; exact o1.le
      _ = n' := by simp [n']

  have h_nn' : n - n' ≤ k ^ 2 := by
    have h1 : n - n'= n % k ^ 2 := by simp [n', tsub_tsub_cancel_of_le <| Nat.mod_le ..]
    have h2 : n % k ^ 2 < k ^ 2 := by apply Nat.mod_lt n; trivial
    observe h3 : n % k ^ 2 ≤ k ^ 2
    calc
      n - n' = n % k ^ 2 := h1
      _ ≤ k ^ 2 := h3

  obtain ⟨M, M_av_perm, M_max⟩ :
      ∃ M, ¬ Contains (PermPattern σ) M ∧ ex (PermPattern σ) n = density M := by
    apply exists_av_and_ex_eq; simp [PermPattern]

  let I : Finset (Fin n) := {a | ↑a ∈ Finset.Ico n' n}
  have h_out i : i ∉ I → ↑i < n' := by contrapose!; simp [I, n']
  let T (i j : Fin n) : Prop := (i, j) ∈ Finset.univ ×ˢ I
  let W (i j : Fin n) : Prop := (i, j) ∈ I ×ˢ Finset.univ
  let P (i j : Fin n) : Prop := T i j ∨ W i j

  have denP : density P ≤ 2 * n * (n - n') := by
    simp [density, P, T, W]
    let s : Finset (Fin n × Fin n) := Finset.univ ×ˢ I
    let t : Finset (Fin n × Fin n) := I ×ˢ Finset.univ
    obtain ⟨s_card, t_card⟩ : #s = n * (n - n') ∧ #t = n * (n - n') := by
      constructor <;>
      · simp [s, t, mul_comm]
        left
        dsimp [I]
        have : #{a : Fin n | ↑a ∈ Finset.Ico n' n} = #(.Ico n' n) := by apply card_interval; rfl
        aesop
    let P_pts := filter (fun x : Fin n × Fin n ↦ x.2 ∈ I ∨ x.1 ∈ I) Finset.univ
    have : P_pts = (s ∪ t) := by aesop

    calc
      #P_pts = #(s ∪ t) := congrArg card this
      _ ≤ #s + #t := Finset.card_union_le s t
      _ = 2 * n * (n - n') := by rw [s_card, t_card, mul_assoc, two_mul]

  let M1 (i j : Fin n) : Prop := M i j ∧  P i j
  let M2 (i j : Fin n) : Prop := M i j ∧ ¬ P i j

  have dM1 := calc
        density M1
    _ ≤ density P := by gcongr; aesop
    _ ≤ 2 * n * (n - n') := denP
    _ ≤ 2 * k ^ 2 * n := by
      conv =>
        right
        conv =>
          rw [mul_assoc]
          right
          rw [mul_comm]
        rw [← mul_assoc]
      exact Nat.mul_le_mul_left (2 * n) h_nn'

  have dM2 : density M2 ≤ ex (PermPattern σ) n' := by
    let M' (i j : Fin n') : Prop := M (i.castLE ‹_›) (j.castLE ‹_›)
    let fr : Fin n → Fin n' := fun i ↦ if h : i ∉ I then ⟨i, h_out i h⟩ else ⟨0, n'_pos⟩
    suffices claim : ¬ Contains (PermPattern σ) M' by
      let s : Finset (Fin n × Fin n) := {(x, y)| M2 x y}
      let t : Finset (Fin n' × Fin n') := {(x, y)| M' x y}
      have card_st : #s = #t := by
        apply Finset.card_bij (fun a  _ ↦ (fr a.1, fr a.2)) ?hi ?i_inj ?i_surj
        · intro a ha
          simp [M', t]--, P, W, T, I]
          simp [s] at ha
          simp [M2, P, T, W] at ha
          obtain ⟨_, A, B⟩ := ha
          simpa [fr, A, B]
        · intro a ha b hb' H
          simp at H
          simp [s, M2, P, W, T] at ha hb'
          obtain ⟨l, r⟩ := H
          obtain ⟨_, a2, a1⟩ := ha
          obtain ⟨_, b2, b1⟩ := hb'
          simp [fr, a1, a2, b1, b2] at l r
          rw [@Fin.val_eq_val] at l r
          exact Prod.ext l r
        · intro b hb
          simp [M', t] at hb
          simp [s]
          use b.1.castLE ‹_›, b.2.castLE ‹_›
          simp [M2, P, T, W, fr, hb, I]

      calc
        density M2 = #s := by simp [density, s]; congr
        _ = #t := card_st
        _ = density M' := by simp [density, t]
        _ ≤ ex (PermPattern σ) n' := density_le_ex_of_not_contains M' claim

    by_contra!
    suffices Contains (PermPattern σ) M by contradiction
    obtain ⟨f, hf, g, hg, prop⟩ := this
    simp [Contains]
    simp [M'] at prop
    simp [StrictMono] at hf hg
    refine ⟨fun i ↦ (f i).castLE ‹_›, hf, fun i ↦ (g i).castLE ‹_›, hg, ?_⟩
    simpa [PermPattern] using prop
  calc
    ex (PermPattern σ) n = density M := M_max
    _ = density M1 + density M2 := split_density M P
    _ ≤ 2 * k ^ 2 * n + ex (PermPattern σ) n' := add_le_add dM1 dM2
    _ = ex (PermPattern σ) n' + 2 * k ^ 2 * n := by rw [Nat.add_comm]

theorem ex_permPattern_le (σ : Perm (Fin k)) (n : ℕ) :
    ex (PermPattern σ) n ≤ 2 * k ^ 4 * (k ^ 2).choose k * n := by
  obtain rfl | hk₁ := eq_or_ne k 0
  · simp [Subsingleton.elim σ (.refl _)]
  obtain rfl | hk₁ := eq_or_ne k 1
  · simp [Subsingleton.elim σ (.refl _)]
  induction' n using Nat.strong_induction_on with n ih
  observe : k ^ 2 > 0
  observe : 0 < k
  have : k ≤ k ^ 2 := by
    rw [Nat.pow_two]
    exact Nat.le_mul_of_pos_left k this

  let K := (k ^ 2).choose k
  observe : 0 < K

  obtain rfl | n_pos := eq_zero_or_pos n
  · simp
  obtain base | h_k := le_or_gt n (k ^ 2)
  · -- base case is trivial
    calc
      ex (PermPattern σ) n ≤ n^2 := ex_le_sq n
      _ ≤ k ^ 2 * n := by rw [Nat.pow_two]; exact Nat.mul_le_mul_right n base
      _ ≤ 2 * k ^ 4 * n := by
        have : k ^ 2 ≤ k ^ 4 := by gcongr <;> omega
        have : k ^ 2 ≤ 2 * k ^ 4 := by omega
        exact Nat.mul_le_mul_right n this
      _ ≤ 2 * k ^ 4* K * n := by aesop
  · let n' : ℕ := n - n % k ^ 2
    observe hkn : k ^ 2 < n
    observe n_non_zero : NeZero n
    observe o1 : k ^ 2 ∣ n'
    observe o_le : n' ≤ n
    have o2 : 0 < n' := by
      observe o1 : n % k ^ 2 < k ^ 2
      calc
        0 < k ^ 2 - n % k ^ 2 := Nat.zero_lt_sub_of_lt o1
        _ < n - n % k ^ 2 := by
          rw [Nat.sub_lt_sub_iff_right]
          exact h_k
          exact Nat.le_of_succ_le o1
        _ = n' := by simp [n']
    observe o3 : NeZero n'

    have o4 : n' / k ^ 2 < n := by
      have : 1 < k ^ 2 := by omega
      observe : n' / k ^ 2 < n'
      calc
        n' / k ^ 2 < n' := this
        _ ≤ n := o_le
    have ez_eq1 : 2 * k ^ 4 * K * (n' / k ^ 2) = 2 * (k ^ 2 * K * n') := by
      suffices k ^ 4 * K * (n' / k ^ 2) = k ^ 2 * K * n' by simpa [mul_assoc]
      have : k ^ 4 * (n' / k ^ 2) = k ^ 2 * n' := by
        suffices k ^ 4 * (n' / k ^ 2) = (k ^ 4/k ^ 2) * n' by
          rw [this]
          rw [Nat.pow_div (Nat.le.step (Nat.le.step Nat.le.refl))]
          trivial
        have : k ^ 2 ∣ k ^ 4 := pow_dvd_pow _ <| by omega
        rw [Nat.pow_div]
        simp
        rw [← Nat.mul_div_assoc (k ^ 4), mul_comm, Nat.mul_div_assoc n' this, Nat.pow_div]
        simp [mul_comm]
        all_goals trivial
      conv =>
        left
        conv =>
          left
          rw [mul_comm]
        rw [mul_assoc]
        rw [this]
        rw [← mul_assoc]
        left
        rw [mul_comm]

    have : (k - 1) ^ 2 + k + 1 ≤ k ^ 2 := by
      have : (k - 1) ^ 2 + k + 1 = k ^ 2 - k + 2 := by
        cases k
        trivial
        simp [pow_two, left_distrib]
        ring
      rw [this]
      observe : k ^ 2 - k + 2 = k ^ 2 + 2 - k
      rw [this]
      omega

    calc
      ex (PermPattern σ) n
        ≤ ex (PermPattern σ) n' + 2 * k ^ 2 * n := ex_permutation_to_dvd σ n hkn
      _ ≤ (k - 1) ^ 2 * ex (PermPattern σ) (n' / k ^ 2) + 2 * n' * k ^ 3 * K + 2 * k ^ 2 * n := by
        gcongr; exact ex_perm_recurrence σ n' o1
      _ ≤ (k - 1) ^ 2 * (2 * k ^ 4 * K * (n' / k ^ 2)) + 2 * n' * k ^ 3 * K + 2 * k ^ 2 * n := by
        simp; gcongr; exact ih (n' / k ^ 2) o4
      _ = (k - 1) ^ 2 * (2 * (k ^ 2 * K * n')) + 2 * n' * k ^ 3 * K + 2 * k ^ 2 * n := by
        rw [ez_eq1]
      _ ≤ (k - 1) ^ 2 * (2 * (k ^ 2 * K * n)) + 2 * n * k ^ 3 * K + 2 * k ^ 2 * n := by gcongr
      _ ≤ (k - 1) ^ 2 * (2 * (k ^ 2 * K * n)) + 2 * n * k ^ 3 * K + 2 * k ^ 2 * n * K := by
        aesop
      _ = (2 * k ^ 2 * n * K) * ((k - 1) ^ 2 + k + 1) := by ring
      _ ≤ (2 * k ^ 2 * n * K) * k ^ 2 := Nat.mul_le_mul_left (2 * k ^ 2 * n * K) this
      _ = 2 * k ^ 4 * K * n := by ring

theorem le_ex_permPattern (σ : Perm (Fin k)) (n : ℕ) (hk : 2 ≤ k) : n ≤ ex (PermPattern σ) n := by
  have : Fact (2 ≤ k) := ⟨hk⟩
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Fin k)
  exact le_ex_self_of_two_points _ _ ⟨(a, σ a), (b, σ b), rfl, rfl, by aesop⟩
