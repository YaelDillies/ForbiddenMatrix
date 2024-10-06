import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.ZMod.Defs
import Mathlib.Logic.Equiv.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Finset.Max



set_option linter.unusedTactic false

namespace Finset
variable {ι α : Type*} [CanonicallyLinearOrderedAddCommMonoid α] {s : Finset ι} {f : ι → α}

@[simp] lemma sup_eq_zero : s.sup f = 0 ↔ ∀ i ∈ s, f i = 0 := by simp [← bot_eq_zero']

end Finset

open Finset Set

-- def trivialPattern : (α → β → Prop) := [1, 1, 1]
-- λ x : nat ↦ x + 5
-- variable {n : ℕ }
-- ![![a, b, c], ![b, c, d]] : matrix (fin 2) (fin 3) α
-- see https://leanprover-community.github.io/theories/linear_algebra.html
-- λ (i : m) (j : n), (_ : α)
def HatPattern : Fin 2 → Fin 3 → Prop := ![![false, true, false], ![true, false, true]]
def VerticalTwoPattern : Fin 2 → Fin 1 → Prop := ![![true], ![true]]
def Horizontal3Pattern : Fin 1 → Fin 3 → Prop := ![![true,true,true]]
def Identity (n : ℕ) (i j : Fin n) : Prop := i = j
def TwoOneY (i _ : Fin 2) : Prop := i = 0
def PatternOne : Fin 1 → Fin 1 → Prop := fun _ : Fin 1 => fun _ : Fin 1 => true
def IdentityB (n : ℕ) (i j : Fin n) : Bool := i = j
def PatternOneB : Fin 1 → Fin 1 → Bool := fun _ : Fin 1 => fun _ : Fin 1 => true
--open Matrix
--section matrices

--def M : matrix (Fin 3) (Fin 3) Prop


section contains
variable {α β γ δ : Type*} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]

-- TODO: replace StrictMono f by StrictMonoOn {a ∣ ∃ b, P a b} f, and similarly for g to ignore blank rows/columns
def contains (P : α → β → Prop) (M : γ → δ → Prop) : Prop :=
  ∃ f : α → γ, StrictMono f ∧ ∃ g : β → δ, StrictMono g ∧ ∀ a b, P a b → M (f a) (g b)

def containsB (P : α → β → Bool) (M : γ → δ → Bool) : Prop :=
  ∃ f : α → γ, StrictMono f ∧ ∃ g : β → δ, StrictMono g ∧ ∀ a b, P a b → M (f a) (g b)

instance [Fintype α] [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : γ → γ → Prop)] {f : α → γ} :
  Decidable (StrictMono f) := inferInstanceAs (Decidable (∀ _ _, _ → _))

instance {P : α → β → Bool} {M : γ → δ → Bool}
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    [DecidableRel (· < · : γ → γ → Prop)] [DecidableRel (· < · : δ → δ → Prop)]
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [DecidableEq α] [DecidableEq β] :
    Decidable (containsB P M) :=
  inferInstanceAs (Decidable (∃ f : α → γ, StrictMono f ∧ ∃ g : β → δ, StrictMono g ∧ ∀ a b, P a b → M (f a) (g b)))

lemma reflectContain (M : γ → δ → Prop) : contains M M := by
  refine ⟨id, by simp [StrictMono],id, by simp [StrictMono], ?_ ⟩
  aesop

end contains




variable {α β γ δ : Type*} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]
open scoped Classical in noncomputable def densityRect {n m :ℕ} (M : Fin n → Fin m → Prop)  : ℕ :=  ({(i, j) : Fin n × Fin m | M i j} : Finset (Fin n × Fin m)).card
--open scoped Classical in noncomputable def density (M : α → β → Prop) : ℕ := card {(i, j) : α × β | M i j}
open scoped Classical in noncomputable def density {n:ℕ} (M : Fin n → Fin n → Prop)  : ℕ :=  ({(i, j) : Fin n × Fin n | M i j} : Finset (Fin n × Fin n)).card

open scoped Classical in noncomputable def exRect (P : α → β → Prop) (n : ℕ) (m : ℕ) : ℕ :=
  sup {M : Fin n → Fin m → Prop | ¬ contains P M} fun M ↦ densityRect M--card {(i, j) : Fin n × Fin m | M i j}

def exRectB [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    (P : α → β → Bool) (n : ℕ) (m : ℕ) : ℕ :=
  sup {M : Fin n → Fin m → Bool | ¬ containsB P M} fun M ↦ card {ij : Fin n × Fin m | M ij.1 ij.2}

open scoped Classical in noncomputable
def ex (P : α → β → Prop) (n : ℕ) : ℕ :=
   sup {M : Fin n → Fin n → Prop | ¬ contains P M} fun M ↦ density M

def exB [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    (P : α → β → Bool) (n : ℕ) : ℕ :=
  exRectB P n n

@[simp] lemma avoid_le_ex {n : ℕ} {P : α → β → Prop} (M : Fin n → Fin n → Prop) (AvoidP : ¬ contains P M)
: density M ≤ ex P n :=  by
  rw [ex]
  apply le_sup
  simpa only [mem_filter, Finset.mem_univ, true_and]

--@[simp]
--theorem ex.le_sup_iff {α : Type u_2} {ι : Type u_5} [linear_order α] [order_bot α] {s : finset ι} {f : ι → α} {a : α} (ha : ⊥ < a) :
--a ≤ s.sup f ↔ ∃ (b : ι) (H : b ∈ s), a ≤ f b :=
--let  M (i j : Fin n) :  Prop := i = (0 : Fin n) ∨ j = (0 : Fin n)
--have MavI2 : ¬contains (Identity 2) M := ?proof_of_MavI2
--have Mhastwon : 2*n  ≤ density n M +1 := ?proof_of_Mhastwon-

--(ha : ⊥ < a)
@[simp] theorem le_ex_iff (P : α → β → Prop) (P_nonempty : ∃ a b, P a b ) {a n : ℕ}
: a ≤ ex P n ↔ ∃ (M : Fin n → Fin n → Prop) , ¬contains P M ∧ a ≤ density M := by
  cases a
  case zero =>  --zero is easy just take the zero matrix
    have : 0 ≤ ex P n := by simp only [zero_le]
    have : ∃ (M : Fin n → Fin n → Prop) , ¬contains P M ∧ 0 ≤ density M := by
      let M (_ _ : Fin n) :  Prop := false
      use M
      simp
      by_contra McontainP
      rw [contains] at McontainP
      obtain ⟨f,_,g,_,m⟩ := McontainP
      obtain ⟨a,b,Pab⟩ := P_nonempty
      have := m a b Pab
      have := M (f a) (g b)
      contradiction
    aesop
    done
  case succ =>
    apply Iff.intro
    · -- (→)
      intro h1
      simp [ex] at h1
      exact h1
      done
    · -- (←)
      intro ⟨M,avoids_P,has_a⟩
      rw [ex, Finset.le_sup_iff]
      use M
      aesop; aesop
      done
    done


lemma PatternOneIsIdentity : PatternOne = (Identity 1) := by
  ext -- apply function extensionality for all a F(a) = G(a) => F = G
  simp [Identity, PatternOne]
  exact Subsingleton.elim ..

lemma exPatternOne (n : ℕ) : ex PatternOne n = 0 := by
  rw [ex]
  simp [filter_eq_empty_iff]
  intro M
  contrapose
  simp
  intro Mnonzero
  simp only [density, card_eq_zero, filter_eq_empty_iff, Finset.mem_univ, true_implies, Prod.forall, not_forall,
  not_not] at Mnonzero
  obtain ⟨i,j,Mij⟩ := Mnonzero
  simp [contains]
  refine ⟨fun _ ↦ i, by simp [StrictMono], ![j], by simp [StrictMono], by simp [Mij]⟩

example (n : ℕ) : ex (Identity 1) n = 0 := by
  rw [← PatternOneIsIdentity]
  exact exPatternOne n

lemma injOn_aux (n : ℕ) [NeZero n] :
    InjOn (fun z : ℤ ↦ ((↑(z⁺), ↑(z⁻)) : Fin n × Fin n)) (Set.Ioo (-n) n : Set ℤ) :=
  ((CharP.intCast_injOn_Ico _ n).prodMap (CharP.intCast_injOn_Ico _ n)).comp
    posPart_negPart_injective.injOn fun z hz ↦
    ⟨⟨posPart_nonneg _, by simpa [NeZero.pos] using hz.2⟩,
      ⟨negPart_nonneg _, by simpa [NeZero.pos] using hz.1⟩⟩

--set_option diagnostics true
lemma  exIdentity2LB  (n : ℕ )[NeZero n]: 2*n-1 ≤ ex (Identity 2) n  := by
  --The following code is a bad style: (a lot of unnecessary casting to deal with, e.g. double-casting)
  --let  M (i j : Fin n) :  Prop := i.val = 0  ∨ j.val = 0
  --Better to use this one:
  let  M (i j : Fin n) :  Prop := i = (0 : Fin n) ∨ j = (0 : Fin n)
  have : ¬contains (Identity 2) M := ?proof_of_M_avoids_I2
  have : 2*n -1 ≤ density M := ?proof_of_Mhastwon--(filter (fun x ↦ M x.1 x.2 : Fin n × Fin n → Prop) univ).card +1 := ?proof_of_Mhastwon
  -- Main proof starts here --
  rw [le_ex_iff]
  use M
  -- prove that (P is non-empty)
  case P_nonempty => simp [Identity]

  -- It remains to prove MavI2 and Mhastwon
  case proof_of_M_avoids_I2 =>
    by_contra h
    simp [contains] at h
    obtain ⟨ f,hf,g, hg, pmap ⟩ := h
    simp [M, Identity] at pmap
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
    let s : Finset ℤ := Ioo (-n ) (n)
    let f :  ℤ → Fin n × Fin n  := fun (i) ↦ (↑(i⁺) , ↑(i⁻))
    have : s = (Set.Ioo (-n) n : Set ℤ ) := by aesop
    have f_inj: InjOn f s := by simp [injOn_aux n,this]
    have hf :  ∀ a ∈ s, f a ∈ t := by
      intro a ains
      simp [s] at ains
      simp [M, t]
      obtain hha | hha' := le_total a 0
      left
      have : a⁺ = 0 := by rwa [posPart_eq_zero]
      simp [this]
      -- use ful command rw [← Fin.val_zero' n, Fin.val_inj]--, Fin.natCast_eq_zero]
      right
      have : a⁻ = 0 := by rwa [negPart_eq_zero]
      simp [this]
    have: s.card ≤ t.card:= Finset.card_le_card_of_injOn f hf f_inj
    have: s.card = 2*n -1 := by
      simp [s]
      norm_cast
      rw [Int.toNat_ofNat]
      omega
    have: 2*n -1 ≤ t.card := by aesop
    convert this



theorem exIdentity2UB (n : ℕ) : ex (Identity 2) n ≤ 2*n-1 := by
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
    simp [Identity] at idab
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

    refine ⟨fM, monof, gM, monog, by
      intro a' b' idab
      simp [Identity] at idab
      rw [idab]
      simp [fM, gM]
      subst b'
      fin_cases a';simp
      exact hmbb
      exact hmaa
    ⟩
  done

theorem  exIdentity2EQ  (n : ℕ )[hnz: NeZero n]: 2*n-1 = ex (Identity 2) n  := by
  have : 2*n-1 ≤ ex (Identity 2) n := exIdentity2LB n
  have : 2*n-1 ≥ ex (Identity 2) n := exIdentity2UB n
  omega
  done

theorem exVerticalTwoPattern (n : ℕ)  [NeZero n]  : ex VerticalTwoPattern n = n := by
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
    case P_nonempty => simp [VerticalTwoPattern]

    case proof_of_Mhasn =>
      rw [density]
      simp [M]
      let s : Finset (Fin n × Fin n) := (filter (fun x : Fin n × Fin n ↦ x.1 = 0) univ)
      let f :  ℕ → Fin n × Fin n  := fun (j) ↦ ( 0 , j)

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
      obtain ⟨f,hf,g,hg,prop⟩ := cont
      simp [StrictMono] at hf hg
      simp at prop
      specialize prop 1
      have fmono: f 0 < f 1 := by simp [hf]
      rw [prop] at fmono
      contradiction

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

      refine⟨f,fmono,g,gmono, ?_⟩
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
      refine⟨f,fmono,g,gmono, ?_⟩
      simp [VerticalTwoPattern]
      intro a b
      fin_cases a;aesop;aesop

--lemma rotationInvariant (P : α → β → Prop) := ex P n = ex rotate(P) n := by sorry
--#eval sup {j | false} id
theorem exHorizontal3Pattern (n :ℕ) [NeZero n] : ex Horizontal3Pattern n = 2*n := by sorry

theorem exHatPatternUB (n : ℕ)  [NeZero n] : ex HatPattern n ≤ 3*n  := by
  classical
  simp [ex]
  intro M noHat
  -- let f : Fin n × Fin n → ℕ := fun ⟨i, j⟩ ↦ j
  -- sup {M : Fin n → Fin n → Prop | ¬ contains P M} fun M ↦ density M
  -- let rightMostOfRow := fun i ↦ ({j: Fin n| M i j } : Finset (Fin n)).max
  -- let leftMostOfRow  := fun i ↦ ({j: Fin n| M i j } : Finset (Fin n)).min
  let Pred_min_or_max_Ofrow := fun i j ↦ (∀ j', M i j' → j ≤ j') ∨ (∀ j', M i j' → j' ≤ j)
  let M1 (i j : Fin n) : Prop := M i j ∧ (Pred_min_or_max_Ofrow i j)
  let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (Pred_min_or_max_Ofrow i j)
  have M2SubsetM: ∀ i j, M2 i j → M i j := by aesop
  have split_dm: density M = density M1 + density M2 := by
    let s1 : Finset (Fin n × Fin n):= {(i,j) | M1 i j}
    let s2 : Finset (Fin n × Fin n):= {(i,j) | M2 i j}
    let s : Finset (Fin n × Fin n) := {(i,j) | M i j}
    have seqs1s2: s = s1 ∪ s2 := by
      ext x
      constructor
      · -- (->)
        intro xins
        simp [s] at xins
        simp [s1,s2,M1,M2]
        tauto
      · -- (<-)
        intro xins1s2
        simp [s1,s2,M1,M2] at xins1s2
        simp [s]
        tauto
    have dm: density M = s.card := by simp [density]
    have dm1: density M1 = s1.card := by
      simp [density,s1,M1]
      convert
      --sorry
    have dm2: density M2 = s2.card := sorry --
     --simp [density,M2,s2,M1]
     -- convert
      --sorry
    have s1eqs2card: (s1 ∪ s2).card = s1.card + s2.card := by
      apply card_union_of_disjoint
      simp [Disjoint]
      intro x h1 h2
      intro p hp
      simp
      have pins1 : p ∈ s1 := by
        apply h1
        exact hp
      have pins2: p ∈ s2 := by
        apply h2
        exact hp
      simp [M1,s1] at pins1
      simp [M2,s2] at pins2
      have:= pins1.right
      have:= pins2.right
      contradiction

    --rw [← seqs1s2] at s1eqs2card
    --aesop

    --simp [M1,M2]
    --Learn injection,surjection,bijection of functions
  have M1_avoids_H3 : ¬ contains Horizontal3Pattern M1  := ?_
  have M2_avoids_V2 : ¬ contains VerticalTwoPattern M2  := by
    by_contra containsV2
    simp [contains] at containsV2
    obtain ⟨f,hf,g,hg,prop⟩ := containsV2
    -- M2  g(0)
    -- f(0) 1
    -- f(1) 1
    let i := f 1
    let j := g 0
    simp [VerticalTwoPattern] at prop
    have M2y : M2 i j := by apply prop
    simp [M2, M1,Pred_min_or_max_Ofrow] at M2y
    have H:  (∃ a, M i a ∧ a < j) ∧ (∃ b, M i b ∧ j < b)  := by exact M2y.2
    obtain ⟨a,ha1,ha2⟩ := H.left
    obtain ⟨b,hb1,hb2⟩ := H.right
    have alb : a < b := by omega
    let g' : Fin 3 → Fin n:= ![ a, g 0, b]
    have monog' : StrictMono g' := by
      simp [StrictMono, g']
      intro x y ha
      fin_cases x
      fin_cases y; contradiction; simp [ha2]   ; simp [alb]
      fin_cases y; contradiction; contradiction; simp [hb2]
      fin_cases y; contradiction; contradiction; contradiction

      --   M   a j/g(0) b
      --  f(0)     1
      -- i/f(1) 1  1  1

    have : contains HatPattern M  := by
      rw [contains]
      refine ⟨f,hf,g',monog', ?_⟩
      -- We prove forall a,b, HatPattern a b => M (f a) (g' b)
      intro i_row j_col H
      fin_cases i_row
      fin_cases j_col -- top part of hat pattern
      · contradiction
      ·
        simp [g']
        apply M2SubsetM (f 0) (g 0)
        apply prop 0 0
      · contradiction
      fin_cases j_col -- bottom part of hat pattern
      · simp [ha1,g']
      ·
        simp [g']
        apply M2SubsetM (f 1) (g 0)
        apply prop 1 0
      · simp [g', hb1]
    contradiction
    done

  have dm1: density M1 ≤ 2*n := by calc
    density M1 ≤ ex Horizontal3Pattern n := avoid_le_ex M1 M1_avoids_H3
    _ = 2*n  := exHorizontal3Pattern n
   -- simp [density, M1]
   -- simp [card_filter_le_iff]
   -- intro S hS

  have dm2: density M2 ≤ n := calc
    density M2 ≤ ex VerticalTwoPattern n := avoid_le_ex M2 M2_avoids_V2
    _ = n  := exVerticalTwoPattern n

  calc
    density M = density M1 + density M2 := split_dm
    _         ≤ 2*n + density M2      := by simp only [dm1, add_le_add_iff_right]
    _         ≤ 2*n + n               := by simp only [dm2, add_le_add_iff_left]
    _         ≤ 3*n                   := by omega



  --
  -- Fix M that avoids HatPattern
  --

theorem exIdentitykUB  (n k : ℕ) [NeZero n]  : ex (Identity k) n ≤ (2*n-1)*k := by sorry

--λ (i : m) (j : n), (_ : α)
