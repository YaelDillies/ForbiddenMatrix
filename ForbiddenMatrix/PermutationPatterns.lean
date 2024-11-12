import ForbiddenMatrix.ExtremalFunction
import ForbiddenMatrix.PatternsDef
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Combinatorics.Pigeonhole

set_option linter.unusedTactic false
set_option maxHeartbeats 800000

open Finset Set
open OrderDual
open Equiv
--open Fin

variable {α β γ δ : Type*} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]

theorem ex_identity (k n: ℕ) [NeZero n] : ex (identityPattern k) n ≤ (2*n-1)*(k-1) := by
  classical
  simp [ex]
  intro M avoid_Ik
  by_contra! M_large_density
  simp [density] at M_large_density

  let f : Fin n × Fin n → ℤ := fun ⟨i, j⟩ ↦ i-j
  let s := (filter (fun (i, j) ↦ M i j) univ)
  let t : Finset ℤ := Icc (-n + 1) (n - 1)

  obtain ⟨p, hp, hp'⟩ : ∃ p ∈ t, k-1 < #{x ∈ s | f x = p} := by
    apply exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    · simp [s, f, t]; omega;
    · simp [s, t]
      cases n
      · contradiction
      simp_all
      rw [← Nat.cast_add_one, ← Nat.cast_add, Int.toNat_ofNat]
      rename_i n _
      have: (n + 1 + n) = (2 * (n + 1) - 1) := by omega
      rw [this]
      omega

  let set_points_to_p : Finset (Fin n × Fin n):= (filter (fun x ↦ f x = p) s)
  let set_points_to_p_col : Finset (Fin n):= { x.2 | x ∈ set_points_to_p}

  have: set_points_to_p.card = set_points_to_p_col.card := by
    apply Finset.card_bij (fun a _ ↦ a.2) ?hi ?i_inj ?i_surj; aesop;aesop;aesop

  have pcardk: k ≤ set_points_to_p.card := by
    simp [set_points_to_p]
    omega

  have hcol: k ≤ set_points_to_p_col.card := by omega

  let g := set_points_to_p_col.orderEmbOfCardLe hcol
  let f' : Fin k → Fin n := fun i ↦ ↑( (p : ℤ) + ( (g i) : ℤ ))
  have mono_f : StrictMono f' := by
    intro a b hb
    simp [f']
    have : g a ∈ set_points_to_p_col := set_points_to_p_col.orderEmbOfCardLe_mem hcol a
    simp [set_points_to_p_col] at this
    obtain ⟨a', ha' ⟩ := this
    simp [set_points_to_p, f] at ha'
    have : g b ∈ set_points_to_p_col := set_points_to_p_col.orderEmbOfCardLe_mem hcol b
    simp [set_points_to_p_col] at this
    obtain ⟨b', hb' ⟩ := this
    simp [set_points_to_p, f] at hb'
    nth_rewrite 1 [← ha'.2]
    nth_rewrite 1 [← hb'.2]
    simp only [Int.cast_sub, Int.cast_natCast, Fin.cast_val_eq_self, sub_add_cancel, gt_iff_lt]

    have ha'' := ha'.2
    rw [← hb'.2] at ha''
    have : (a' : ℤ) = ↑↑b' - ↑↑(g b) + ↑↑(g a) := by omega
    have : g a < g b := by simpa [StrictMono]
    omega

  have: contains (identityPattern k) M := by
    refine ⟨f', mono_f, g, by simp [StrictMono], /- Embed Identity k to M-/ by
        intro x y H
        simp [identityPattern] at H
        rw [H]
        simp [f']
        have : g y ∈ set_points_to_p_col := set_points_to_p_col.orderEmbOfCardLe_mem hcol y
        simp [set_points_to_p_col] at this
        obtain ⟨a, ha⟩ := this
        simp [set_points_to_p, f] at ha
        obtain ⟨a1, ha1⟩ := ha
        simp [s] at a1
        rw [← ha1]
        simpa
      ⟩

  contradiction
  done

lemma le_mul_div_add_one {n q :ℕ} (p : Fin n) (h: 0 < q): p < q * (p / q + 1) := by
  rw [Nat.mul_comm]
  exact Nat.lt_mul_of_div_lt (Nat.lt_add_one _) h

def rectPtset (n a₁ b₁ a₂ b₂: ℕ) : Finset (Fin n × Fin n) :=
  ({ a | ↑a ∈ Finset.Ico a₁ b₁} : Finset (Fin n)) ×ˢ ({ a | ↑a ∈ Finset.Ico a₂ b₂} : Finset (Fin n))

open scoped Classical in noncomputable
def rectPtsetMatrix {n :ℕ }(M : Fin n → Fin n → Prop) (a₁ b₁ a₂ b₂: ℕ) : Finset (Fin n × Fin n) :=
  {(a, b) | M a b ∧ (a, b) ∈ (rectPtset n a₁ b₁ a₂ b₂)}

open scoped Classical in noncomputable
def rectPtsetSubsetMatrix {n :ℕ }(M : Fin n → Fin n → Prop) (R C : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  {(a, b) | M a b ∧ (a, b) ∈ R ×ˢ C}


def rectPtsetq (n q i j :ℕ) := rectPtset n (q * i) (q * (i+1)) (q * j) (q * (j+1))

open scoped Classical in noncomputable
def rectPtsetqMatrix {n:ℕ }(M : Fin n → Fin n → Prop) (q i j :ℕ) : Finset (Fin n × Fin n) := {(a, b) | M a b ∧ (a, b) ∈ rectPtsetq n q i j}

lemma card_rectPtSet (n a₁ b₁ a₂ b₂: ℕ) (h: b₁ ≤ n ∧ b₂ ≤ n): (rectPtset n a₁ b₁ a₂ b₂).card = (b₁ -a₁ )*(b₂ - a₂) := by
  simp only [rectPtset, card_product]
  suffices claim: ∀x y, y ≤ n → #{a : Fin n | ↑a ∈ Finset.Ico x y} = #(.Ico x y) by aesop
  -- proof of the claim
  intro x y hy
  apply Finset.card_bij (fun (a: Fin n) _ ↦ ↑a) ?hi ?i_inj ?i_surj;aesop;aesop
  · -- ?i_surj
    intro b hb
    simp at hb
    have: b < n := by omega
    use ⟨b, this⟩
    simp_all only [Finset.mem_Ico, mem_filter, Finset.mem_univ, and_self, exists_const]

lemma card_rectPtsetSubsetMatrix {n :ℕ }(M : Fin n → Fin n → Prop) (R C : Finset (Fin n)) :
    #(rectPtsetSubsetMatrix M R C) ≤ #R * #C := by
  calc
    #(rectPtsetSubsetMatrix M R C)
      ≤ (R ×ˢ C).card := ?_
    _ = #R * #C := card_product R C
  gcongr
  simp only [rectPtsetSubsetMatrix, Prod.mk.eta, mem_product]
  intro a ha
  aesop

lemma card_rectPtsetq (n q i j : ℕ) (hq: q ∣ n) (h: i < n/q ∧ j < n/q) : (rectPtsetq n q i j).card = q*q := by
  simp [rectPtsetq]
  have:= card_rectPtSet n (q * i) (q * (i+1)) (q * j) (q * (j+1)) ?_
  convert this
  exact Nat.eq_sub_of_add_eq' rfl
  exact Nat.eq_sub_of_add_eq' rfl
  obtain ⟨hi, hj⟩ := h
  constructor
  calc
    q*(i+1) ≤ q*(n/q) := Nat.mul_le_mul_left q hi
    _      = n       := Nat.mul_div_cancel' hq
  calc
    q*(j+1) ≤ q*(n/q) := Nat.mul_le_mul_left q hj
    _      = n       := Nat.mul_div_cancel' hq

--lemma card_rectPtsetq_subset (n q i j : ℕ) (hq: q ∣ n) (h: i < n/q ∧ j < n/q) : (rectPtsetq n q i j).card = q*q := sorry

lemma card_rectPtsetqMatrix {n q:ℕ }(M : Fin n → Fin n → Prop) (i j :ℕ) (hq: q ∣ n) (h: i < n/q ∧ j < n/q):
  (rectPtsetqMatrix M q i j).card ≤ q*q := by

  suffices claim: (rectPtsetqMatrix M q i j).card ≤ (rectPtsetq n q i j).card by calc
    (rectPtsetqMatrix M q i j).card ≤ (rectPtsetq n q i j).card := claim
    _                              = q* q := card_rectPtsetq n q i j hq h
  -- proof of the claim
  refine Finset.card_le_card ?_
  simp only [rectPtsetqMatrix, rectPtsetq, Prod.mk.eta]
  intro p h
  simp at h
  exact h.2

def blkMatrix {n : ℕ} (M : Fin n → Fin n → Prop) (q : ℕ ) : Fin (n/q) → Fin (n/q) → Prop :=
  fun i j ↦
  ∃ p : Fin n × Fin n, M p.1 p.2 ∧ p ∈ rectPtsetq n q i j

open scoped Classical in noncomputable
def blk_den {n q:ℕ } (M : Fin n → Fin n → Prop) (i j : Fin (n/q)):
  ℕ := (rectPtsetqMatrix M q i j).card

@[simp] lemma p_to_pq{n:ℕ} {p : Fin n × Fin n} {q : ℕ} [NeZero q]:
p ∈ rectPtset n (q * (↑p.1 / q)) (q * (↑p.1 / q + 1)) (q * (↑p.2 / q)) (q * (↑p.2 / q + 1)) := by
  simp only [rectPtset, Finset.mem_Ico, mem_product, mem_filter, Finset.mem_univ, true_and]
  have hq: 0 < q := NeZero.pos _
  refine ⟨⟨?_1a, ?_1b⟩, ⟨?_2a, ?_2b⟩⟩
  · exact Nat.mul_div_le (↑p.1) q
  · exact le_mul_div_add_one p.1 hq
  · exact Nat.mul_div_le (↑p.2) q
  · exact le_mul_div_add_one p.2 hq

open scoped Classical
theorem den_eq_sum_blk_den {n:ℕ} (M : Fin n → Fin n → Prop) (q : ℕ ) [NeZero q] (h_q_div_n: q ∣ n) :
let B := blkMatrix M q;
density M = ∑ ⟨i, j⟩ : Fin (n/q) × Fin (n/q) with B i j, blk_den M i j := by
  let B := blkMatrix M q
  let Q := Fin (n/q) × Fin (n/q)
  let N := Fin n × Fin n
  let fq : Fin n → Fin (n/q) := fun x ↦ ⟨x/q, by apply Nat.div_lt_div_of_lt_of_dvd h_q_div_n; exact x.isLt ⟩
  let s : Finset N := { (x, y)| M x y}
  let f : N → Q := fun (i, j) ↦ (fq i, fq j)
  let t : Finset Q := {(i, j)| B i j}
  have H : ∀ x ∈ s, f x ∈ t := by
    intro p hp
    simp only [mem_filter, Finset.mem_univ, true_and, s] at hp
    simp only [mem_filter, Finset.mem_univ, true_and, t, B, blkMatrix]
    use p
    refine ⟨hp, p_to_pq⟩
  have h_sum_card:= Finset.card_eq_sum_card_fiberwise H
  suffices claim: ∀ k, (filter (fun x ↦ f x = k) s).card = blk_den M k.1 k.2 by aesop
  -- proof of the last claim
  intro k
  dsimp [blk_den, rectPtsetMatrix]
  apply Finset.card_bij (fun (p:Fin n × Fin n) _ ↦ p ) ?hi ?i_inj ?i_surj
  · -- hi : ∀ (a : α) (ha : a ∈ s), i a ha ∈ t
    intro p hp
    simp only [mem_filter, Finset.mem_univ, true_and, s] at hp
    simp only [rectPtsetqMatrix, rectPtsetq, Prod.mk.eta, mem_filter, Finset.mem_univ, true_and]
    aesop
  · -- i_inj
    aesop
  · -- i_surj : ∀ b ∈ t, ∃ a, ∃ (ha : a ∈ s), i a ha = b
    intro p hp
    simp only [Prod.mk.eta, mem_filter, Finset.mem_univ, true_and, rectPtsetqMatrix, rectPtsetq] at hp
    simp only [mem_filter, Finset.mem_univ, true_and, exists_prop, exists_eq_right, s, fq]
    refine ⟨hp.1, ?_⟩
    replace hp := hp.2
    simp [rectPtset] at hp
    obtain ⟨⟨p1l, p1h⟩, p2l, p2h⟩ := hp
    simp [f, fq]
    refine Prod.ext ?i_surj.intro.intro.intro.fst ?i_surj.intro.intro.intro.snd
    · -- proving k.1
      simp
      have: ↑p.1 / q = k.1 := by apply Nat.div_eq_of_lt_le; rwa [mul_comm];rwa [mul_comm]
      aesop
    · -- proving k.2
      simp
      have: ↑p.2 / q = k.2 := by apply Nat.div_eq_of_lt_le;rwa [mul_comm];rwa [mul_comm]
      aesop
  done

theorem sum_blk_den_le_mul_den_blk {n q c:ℕ} (M : Fin n → Fin n → Prop) (B : Fin (n/q) → Fin (n/q) → Prop) (h: ∀ i j : Fin (n/q), B i j → blk_den M i j ≤ c):
--let B := blkMatrix M q;
∑ ⟨i, j⟩ : Fin (n/q) × Fin (n/q) with B i j, (blk_den M i j) ≤ c* density B := by
-- let B := blkMatrix M q
  let Q := Fin (n/q) × Fin (n/q)
  calc
    ∑ ⟨i, j⟩ : Q with B i j, blk_den M i j ≤ ∑ ⟨i, j⟩ : Q with B i j, c := by apply Finset.sum_le_sum;intros p hp; aesop
    _                                    = ({ (i, j) | B i j }: Finset Q).card*c := by exact sum_const_nat fun x ↦ congrFun rfl
    _                                    = c* density B := by apply Nat.mul_comm
  done


lemma av_perm_contract_av_perm {n k: ℕ} (q :ℕ) (σ : Perm (Fin k)) (M : Fin n → Fin n → Prop)
      (hM: ¬ contains (permPattern σ) M) : ¬ contains (permPattern σ) (blkMatrix M q) := by
  by_contra H
  simp [contains] at H
  obtain ⟨f, hf, g, hg, h⟩ := H
  simp only [blkMatrix, Finset.mem_Icc] at h
  simp only [permPattern, PEquiv.toMatrix_apply, toPEquiv, PEquiv.coe_mk, Function.comp_apply,
    Option.mem_def, Option.some.injEq, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not,
     forall_eq'] at h

  --     . . g (σ i) . .
  -- .
  -- .
  -- f i        1
  -- .
  -- .
  --#check (h ).choose
  simp only [rectPtsetq, rectPtset, Finset.mem_Ico, mem_product, mem_filter, Finset.mem_univ, true_and] at h
  let f' :Fin k → Fin n:= fun i ↦ (h i).choose.1

  have f'_mono: StrictMono f' := by
    simp [StrictMono, f']
    simp [StrictMono] at hf
    intro a b hab
    have spec_a:= (h a).choose_spec
    have spec_b:= (h b).choose_spec
    obtain ⟨A, ⟨B, ca_ub⟩, C, D⟩ := spec_a
    obtain ⟨E, ⟨cb_lb, F⟩, G, H⟩ := spec_b
    cases q
    · simp_all
    ·
      rename_i q
      simp_all
      calc
        f' a <  (q + 1) * (↑(f a) + 1) := ca_ub
        _  ≤ (q + 1) * ↑(f b) := by
            simp_arith
            exact hf hab
        _  ≤ f' b := cb_lb

  --           . . g (i) . .  |    . . g (σ i) . .
  -- .                         | .
  -- .                         | .
  -- f (σ⁻¹ i)        1        | f i        1
  -- .                         | .
  -- .                         | .

  let g' :Fin k → Fin n:= fun i ↦ (h (σ.invFun i)).choose.2

  have g'_mono: StrictMono g' := by
    simp [StrictMono]
    simp [StrictMono] at hg
    intro a b hab
    have spec_a:= (h (σ.invFun a)).choose_spec
    have spec_b:= (h (σ.invFun b)).choose_spec

    obtain ⟨A, B, C, ca_ub⟩ := spec_a
    obtain ⟨D, E, cb_lb, F⟩ := spec_b

    simp_all
    cases q
    · simp_all
    ·
      rename_i q
      calc
        g' a < (q + 1) * (↑(g a) + 1) := by simp_all [g']
        _  ≤ (q + 1) * (↑(g b) ) := by
            simp_arith
            exact hg hab
        _  ≤ g' b := by simp_all [g']

  have: contains (permPattern σ) M := by
    refine ⟨f', f'_mono, g', g'_mono,
      by
      intro i j hab
      simp only [permPattern, PEquiv.toMatrix_apply, toPEquiv, PEquiv.coe_mk, Function.comp_apply,
        Option.mem_def, Option.some.injEq, ite_eq_left_iff, zero_ne_one, imp_false,
        Decidable.not_not] at hab
      subst hab
      have := Classical.choose_spec (h i)
      simp [f', g']
      simp_all only [f']
    ⟩

  contradiction
  done


theorem split_density_blk {n q: ℕ} (M : Fin n → Fin n → Prop) (f1 f2: Fin (n/q) → Fin (n/q) → Prop) :
  --let M' := {(a, b) : Fin n × Fin n | M a b ∧ (a, b) ∈ rectPtsetq n q i j}
  let Q := Fin (n/q) × Fin (n/q)
  let f3 := fun i j ↦ (¬ f1 i j) ∧ ¬ (f2 i j)
  let B := blkMatrix M q
  let B1 (i j : Fin (n/q)) : Prop := B i j ∧ f1 i j
  let B2 (i j : Fin (n/q)) : Prop := B i j ∧ f2 i j
  let N (i j : Fin (n/q)) : Prop := B i j ∧ f3 i j

  density M ≤ ∑ ⟨i, j⟩ : Q with B1 i j, blk_den M i j +
              ∑ ⟨i, j⟩ : Q with B2 i j, blk_den M i j +
              ∑ ⟨i, j⟩ : Q with N i j, blk_den M i j
              := sorry


lemma density_WB {n k : ℕ}(M : Fin n → Fin n → Prop) {σ : Perm (Fin k)} (M_avoid_perm: ¬ contains (permPattern σ) M) (q :ℕ):
let B := blkMatrix M q
let W : Fin (n/q) → Fin (n/q) → Prop := fun i j ↦ ({ c | ∃ r, (r, c) ∈ rectPtsetqMatrix M q i j}: Finset (Fin n)).card ≥ k
let WB : Fin (n/q) → Fin (n/q) → Prop := fun i j ↦ W i j ∧ B i j
density WB ≤ n := sorry

lemma density_TB {n k : ℕ}(M : Fin n → Fin n → Prop) {σ : Perm (Fin k)} (M_avoid_perm: ¬ contains (permPattern σ) M) (q :ℕ):
let B := blkMatrix M q
let T : Fin (n/q) → Fin (n/q) → Prop := fun i j ↦ ({ r | ∃ c, (r, c) ∈ rectPtsetqMatrix M q i j}: Finset (Fin n)).card ≥ k
let TB : Fin (n/q) → Fin (n/q) → Prop := fun i j ↦ T i j ∧ B i j
density TB ≤ n := sorry

example {k : ℕ } [NeZero k] (σ : Perm (Fin k)) (n : ℕ) [NeZero n] (h_k_div_n: k*k ∣ n) : ex (permPattern σ) n ≤ n*k := by
  simp only [ex, Finset.sup_le_iff, mem_filter, Finset.mem_univ, true_and]

  have maxM : ∃ M : Fin n → Fin n → Prop, ¬ contains (permPattern σ) M ∧ ex (permPattern σ) n = density M := sorry
  let M := maxM.choose
  obtain ⟨M_avoid_perm, M_maximizer⟩ := maxM.choose_spec
  let q : ℕ := k*k
  let B := blkMatrix M q
  let Q := Fin (n/q) × Fin (n/q)

  have recurrence : ex (permPattern σ) n ≤ (k-1)*(k-1) * ex (permPattern σ) (n/(k*k)) + 2*n * k*k := by
    let W : Fin (n/q) → Fin (n/q) → Prop := fun i j ↦ ({ c | ∃ r, (r, c) ∈ rectPtsetqMatrix M q i j}: Finset (Fin n)).card ≥ k
    let T : Fin (n/q) → Fin (n/q) → Prop := fun i j ↦ ({ r | ∃ c, (r, c) ∈ rectPtsetqMatrix M q i j}: Finset (Fin n)).card ≥ k
    let S : Fin (n/q) → Fin (n/q) → Prop := fun i j ↦ ¬ W i j ∧ ¬ T i j

    let WB : Fin (n/q) → Fin (n/q) → Prop := fun i j ↦ W i j ∧ B i j
    let TB : Fin (n/q) → Fin (n/q) → Prop := fun i j ↦ T i j ∧ B i j
    let SB : Fin (n/q) → Fin (n/q) → Prop := fun i j ↦ S i j ∧ B i j
    let fk := k^4

    have sum_small_blks: ∑ ⟨i, j⟩ : Q with SB i j, blk_den M i j ≤ (k-1)*(k-1) * ex (permPattern σ) (n/(k*k)) := by
      have h1: ∀ (i j : Fin (n / q)), SB i j → blk_den M i j ≤ (k-1)*(k-1) := by
        intro i j hij
        simp [blk_den]
        simp [SB, S, W, T, B, blkMatrix]  at hij
        obtain ⟨⟨num_cols, num_rows⟩, _⟩ := hij
        let R := (filter (fun r ↦ ∃ c, (r, c) ∈ rectPtsetqMatrix M q ↑i ↑j) Finset.univ)
        let C := (filter (fun c ↦ ∃ r, (r, c) ∈ rectPtsetqMatrix M q ↑i ↑j) Finset.univ)
        have rc: R.card ≤ k - 1 := Nat.le_sub_one_of_lt num_rows
        have cc: C.card ≤ k - 1 := Nat.le_sub_one_of_lt num_cols
        suffices (rectPtsetSubsetMatrix M R C) = rectPtsetqMatrix M q ↑i ↑j by
          rw [← this]
          calc
            (rectPtsetSubsetMatrix M R C).card ≤ R.card * C.card := card_rectPtsetSubsetMatrix M R C
            _                                  ≤ (k - 1) * (k - 1) := Nat.mul_le_mul rc cc
        show (rectPtsetSubsetMatrix M R C) = rectPtsetqMatrix M q ↑i ↑j
        · ext x
          simp only [rectPtsetSubsetMatrix, Prod.mk.eta, mem_product, mem_filter,
            Finset.mem_univ, true_and, rectPtsetqMatrix, rectPtsetq, rectPtset, Finset.mem_Ico,
            and_congr_right_iff]
          intro hx
          simp only [rectPtsetqMatrix, rectPtsetq, rectPtset, Finset.mem_Ico, Prod.mk.eta,
            mem_product, mem_filter, Finset.mem_univ, true_and, R, C]
          clear! M_avoid_perm M_maximizer
          aesop
      have h2: density SB ≤ ex (permPattern σ) (n/q) := by
        suffices ¬ contains (permPattern σ) SB from avoid_le_ex SB this
        show ¬ contains (permPattern σ) SB
        · by_contra!
          simp only [contains, SB] at this
          obtain ⟨f, hf, g, hg, H⟩ := this
          refine av_perm_contract_av_perm q _ M M_avoid_perm ?_
          simp only [contains]
          refine ⟨f, hf, g, hg, ?_⟩
          show ∀ (a b : Fin k), permPattern σ a b → blkMatrix M q (f a) (g b)
          intros
          simp_all only [- M_avoid_perm, ge_iff_le, not_le, and_imp, q, SB, S, W, T, B]
      calc
        ∑ ⟨i, j⟩ : Q with SB i j, blk_den M i j ≤ (k-1)*(k-1) * density SB := by
          convert sum_blk_den_le_mul_den_blk M SB h1
        _ ≤ (k-1)*(k-1) * ex (permPattern σ) (n/q) := Nat.mul_le_mul_left ((k - 1) * (k - 1)) h2

    have sum_wide_blocks: ∑ ⟨i, j⟩ : Q with WB i j, blk_den M i j ≤ n * fk := by

      have h1: ∀ (i j : Fin (n / q)), WB i j → blk_den M i j ≤ fk := sorry
      have h2: density WB ≤ n := density_WB M M_avoid_perm q
      calc
        ∑ ⟨i, j⟩ : Q with WB i j, blk_den M i j ≤ fk * density WB := by convert sum_blk_den_le_mul_den_blk M WB h1
        _                                     ≤ fk * n := Nat.mul_le_mul_left fk h2
        _                                     = n * fk := Nat.mul_comm fk n

    have sum_tall_blocks: ∑ ⟨i, j⟩ : Q with TB i j, blk_den M i j ≤ n * k*k := sorry



    calc
      ex (permPattern σ) n = density M := M_maximizer
      _                    ≤ ∑ ⟨i, j⟩ : Q with WB i j, blk_den M i j +
                              ∑ ⟨i, j⟩ : Q with TB i j, blk_den M i j +
                              ∑ ⟨i, j⟩ : Q with SB i j, blk_den M i j := ?convert_split_density_blk
      _                    ≤ ∑ ⟨i, j⟩ : Q with WB i j, blk_den M i j +
                              ∑ ⟨i, j⟩ : Q with TB i j, blk_den M i j +
                              (k-1)*(k-1) * ex (permPattern σ) (n/(k*k)) := Nat.add_le_add_left sum_small_blks (∑ ⟨i, j⟩ : Q with WB i j, blk_den M i j + ∑ ⟨i, j⟩ : Q with TB i j, blk_den M i j)
      _                    ≤ n * k*k + n * k*k + (k-1)*(k-1) * ex (permPattern σ) (n/(k*k)) := by admit --by simp only [add_le_add_iff_right]; exact Nat.add_le_add sum_wide_blocks sum_tall_blocks
      _                    = (k-1)*(k-1) * ex (permPattern σ) (n/q) + 2*n * k*k := by ring

    case convert_split_density_blk =>
      convert split_density_blk M W T <;> all_goals (
        simp [WB, B]
        exact And.comm
      )

    done
  sorry



--theorem ex_permutation {k : ℕ } (σ : Perm (Fin k)) (n : ℕ) [NeZero n] [NeZero k] (h_k_div_n: k*k ∣ n) : ex (permPattern σ) n ≤ n*k := by sorry

--theorem ex_permutation {k : ℕ } (σ : Perm (Fin k)) (n : ℕ) : ex (permPattern σ) n ≤ n*k := sorry
