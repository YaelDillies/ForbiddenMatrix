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
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Synonym
import Mathlib.Data.Matrix.Basic


set_option linter.unusedTactic false
set_option maxHeartbeats 400000


namespace Finset
variable {ι α : Type*} [CanonicallyLinearOrderedAddCommMonoid α] {s : Finset ι} {f : ι → α}

@[simp] lemma sup_eq_zero : s.sup f = 0 ↔ ∀ i ∈ s, f i = 0 := by simp [← bot_eq_zero']

end Finset

open Finset Set
open OrderDual
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
def HatPatternD : Fin 3 → Fin 2 → Prop := ![![true, false], ![false, true], ![true, false]]
def VerticalTwoPattern : Fin 2 → Fin 1 → Prop := ![![true], ![true]]
def Horizontal2Pattern : Fin 1 → Fin 2 → Prop := ![![true,true]]
def Horizontal3Pattern : Fin 1 → Fin 3 → Prop := ![![true,true,true]]

def HorizontalkPattern (k : ℕ) (_ :Fin 1) (_ : Fin k) : Prop := true
def VerticalkPattern (k : ℕ) (_ :Fin k) (_ : Fin 1) : Prop := true
def Identity (n : ℕ) (i j : Fin n) : Prop := i = j
def TwoOneY (i _ : Fin 2) : Prop := i = 0
def PatternOne : Fin 1 → Fin 1 → Prop := fun _ : Fin 1 => fun _ : Fin 1 => true
def IdentityB (n : ℕ) (i j : Fin n) : Bool := i = j
def PatternOneB : Fin 1 → Fin 1 → Bool := fun _ : Fin 1 => fun _ : Fin 1 => true


--open Matrix
--section matrices



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

lemma reflect_contain (M : γ → δ → Prop) : contains M M := by
  refine ⟨id, by simp [StrictMono],id, by simp [StrictMono], ?_ ⟩
  aesop

end contains


variable {α β γ δ : Type*} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]
open scoped Classical in noncomputable
def densityRect {n m :ℕ} (M : Fin n → Fin m → Prop)  : ℕ :=  ({(i, j) : Fin n × Fin m | M i j} : Finset (Fin n × Fin m)).card
--open scoped Classical in noncomputable def density (M : α → β → Prop) : ℕ := card {(i, j) : α × β | M i j}
open scoped Classical in noncomputable
def density {n:ℕ} (M : Fin n → Fin n → Prop)  : ℕ := ({(i, j) : Fin n × Fin n | M i j} : Finset (Fin n × Fin n)).card

open scoped Classical in noncomputable
def row_density {n:ℕ } (M : Fin n → Fin n → Prop) (i : Fin n): ℕ := ({j | M i j} : Finset (Fin n)).card

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

--def Identity (n : ℕ) (i j : Fin n) : Prop := i = j


def L'' : Fin 2 → Fin 2 → Prop :=
  ![
    ![false, true],
    ![true, true]
  ]

def A' : Fin 2 → Fin 1 → Prop :=
  ![![true], ![false]]
def B' : Fin 2 → (Fin 1) → Prop :=
  ![![false], ![true]]

--def C' : (Fin 3)ᵒᵈ  → Bool := ![true,false,false]

--Matrix.of
--Fin.revOrderIso

def tranpose (M : α → β → Prop) : β → α  → Prop := fun x y ↦ M y x
def rev_all_rows (M : α → β → Prop) : α  → βᵒᵈ  → Prop :=  fun i ↦ (M i) ∘ ofDual
def rot_cw (M : α → β → Prop) :  β → α ᵒᵈ → Prop := (rev_all_rows ∘ tranpose) M

def rev_all_rows_via_list {n : ℕ} (M : α → Fin n → Prop) : α → Fin n → Prop :=
   fun i ↦
    let v := Mathlib.Vector.ofFn (M i)
    let rv := v.reverse
    fun j : Fin n ↦ rv.get j

--def tranpose (M : α → β → Prop) : β → α  → Prop := fun x y ↦ M y x
--#check rev_all_rows B
def L : Fin 2 → Fin 2 → Prop :=
  ![
    ![true, false],
    ![true, true]
   ]
def L' : Fin 2 → Fin 2 → Prop :=
  ![
    ![true, true],
    ![true, false]
  ]


def X : (Fin 3)ᵒᵈ → Bool := ![true,false,false] ∘ ofDual
def Y : Fin 3 → Bool := ![false,false,true]

def A : Fin 1 → Fin 2 → Prop := ![![true, false]]
def B : Fin 1 → (Fin 2)ᵒᵈ → Prop := ![![true, false]∘ ofDual]
def C : Fin 1 → (Fin 2) → Prop := ![![false, true]]

#check fun i ↦ (C i) ∘ Fin.revOrderIso
#check fun i ↦ (B i)

example : (fun i ↦ (C i) ∘ Fin.revOrderIso∘ toDual)  = fun i ↦ (rev_all_rows A i)∘ toDual := by
  ext i j
  simp [rev_all_rows,A,C]
  fin_cases i ; fin_cases j <;> simp [Fin.last,Fin.rev]

-- eample : B2 =    := by
--  ext
--  simp [rev_all_rows,A,B]

--def b : (Fin 2)ᵒᵈ → Bool := ![false, true] \comp ofDual
--#eval b (toDual 0)

-- the elements of (Fin 2)ᵒᵈ are, in order, toDual 1 and toDual 0
def a : Fin 2 → Bool := ![true, false]
-- b = rev_all_rows c
def c : Fin 2 → Bool := ![false, true]
def b : (Fin 2)ᵒᵈ → Bool := ![false, true]  ∘ ofDual

#eval  (a ∘ Fin.revOrderIso) (toDual 0) = b (toDual 0)
#eval  (a ∘ Fin.revOrderIso) (toDual 1) = b (toDual 1)


example : a ∘ Fin.revOrderIso  =  b  := by
  ext x
  --have:= OrderDual.toDual.surjective x
  --obtain ⟨y,h⟩  :=this
  --rw [← h]
  -- one line version of above
  obtain ⟨y, rfl⟩ := OrderDual.toDual.surjective x
  fin_cases y <;> rfl

example : a ∘ Fin.revOrderIso ∘ toDual =  b  ∘ toDual := by
  ext x
  fin_cases x <;> rfl


example : A = rev_all_rows_via_list C := by
  simp [A, C]
  ext a b
  rw [rev_all_rows_via_list]
  simp [Mathlib.Vector.ofFn]
  fin_cases a;
  fin_cases b; simp;
  exact trivial
  simp [Mathlib.Vector.ofFn];
  exact fun a ↦ a

-- example : HatPattern = (rot_cw ∘ rot_cw) HatPattern :=
--example : HatPattern = (rot_cw ∘ rot_cw ∘ rot_cw ∘ rot_cw) HatPattern := by
--  simp only [Function.comp_apply]
--  simp [rot_cw]
--  ext i j
--  fin_cases i; simp
--  fin_cases j; aesop; aesop; aesop
--  fin_cases j; aesop; aesop; aesop
--  done

--lemma vpk_eq_rot_hpk (k : ℕ): VerticalkPattern k = rot_cw (HorizontalkPattern k) := by
--  ext _ j
--  fin_cases j
--  rfl

---

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

theorem exIdentity2  (n : ℕ )[NeZero n]: 2*n-1 = ex (Identity 2) n  :=
  Eq.symm (Nat.le_antisymm  (exIdentity2UB n)  (exIdentity2LB n))

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
lemma split_density {n : ℕ} (M : Fin n → Fin n → Prop) (Pred: Fin n → Fin n → Prop) :
let M1 (i j : Fin n) : Prop := M i j ∧   (Pred i j);
let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (Pred i j);
density M = density M1 + density M2 := by
  classical
  let M1 (i j : Fin n) : Prop := M i j ∧   (Pred i j);
  let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (Pred i j);
  let s1 : Finset (Fin n × Fin n) := {(i,j) | M1 i j}
  let s2 : Finset (Fin n × Fin n) := {(i,j) | M2 i j}
  let s  : Finset (Fin n × Fin n) := {(i,j) | M  i j}
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
  have dm : density M = s.card := by simp [density]
  have dm1: density M1 = s1.card := by
    simp [density]
    convert rfl
  have dm2: density M2 = s2.card := by --
    simp [density,M2,s2,M1]
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
    simp [M1,s1] at pins1
    simp [M2,s2] at pins2
    have:= pins1.right
    have:= pins2.right
    contradiction
  rw [← seqs1s2] at s1eqs2card
  aesop


--open scoped Classical in noncomputable
lemma split_density_to_rows {n:ℕ} (M : Fin n → Fin n → Prop) : density M = ∑ i,  row_density M i := by
  classical
  let s : Finset (Fin n × Fin n) := { (x,y)| M x y}
  let f : Fin n × Fin n → Fin n  := fun x ↦ x.1
  let t : Finset (Fin n) := Finset.univ
  have H : ∀ x ∈ s, f x ∈ t := by
    intro x _
    simp [f,t]
  have h_sum_card:= Finset.card_eq_sum_card_fiberwise H
  simp [f,t] at h_sum_card
  have: s.card = density M := by simp [s,density]
  rw [this] at h_sum_card
  have: ∀ k, (filter (fun x ↦ f x = k) s).card = row_density M k := ?proof_fiber_row_density
  simp only [this] at h_sum_card
  exact h_sum_card

  case proof_fiber_row_density =>
    intro k
    simp [row_density]
    apply Finset.card_bij (fun (a:Fin n × Fin n)  _ ↦ a.2 ) ?hi ?i_inj ?i_surj; aesop;aesop;aesop

    -- 30 lines --> 1 lines using apply (and lean will figure out what is needed.)

    /-let s := filter (fun x_1 ↦ x_1.1 = k) {(x,y)| M x y}
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
      let a := (k,b)
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

lemma UB_density_by_rows {n c:ℕ}  (M : Fin n → Fin n → Prop)
(h_row_density_bounded: ∀i, row_density M i ≤ c) : density M ≤  n * c  :=  calc
    density M = ∑ i,  row_density M i := split_density_to_rows M
    _         ≤ ∑ _, c := by
              apply Finset.sum_le_sum
              simp [mem_filter]
              exact h_row_density_bounded
    _         = n*c := by simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

-- Finset.card_disjiUnion
-- open BigOperators
example (n :ℕ)  : ex Horizontal2Pattern n ≤ n := by
  classical
  simp [ex]
  intro M noH2P
  let Pred_min_Ofrow := fun i j ↦ ∀ j', M i j' → j ≤ j'
  let M1 (i j : Fin n) : Prop := M i j ∧   (Pred_min_Ofrow i j)
  let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (Pred_min_Ofrow i j)

  have dm1: density M1 ≤ n:= ?proof_dm1
  have M2_avoids_trivial : ¬ contains PatternOne M2 := ?proof_M2_av_trivial
  have dm2: density M2 ≤ 0 := calc
    density M2 ≤ ex PatternOne n := avoid_le_ex M2 M2_avoids_trivial
    _ = 0  := exPatternOne n

  calc
    density M = density M1 + density M2 :=  split_density M Pred_min_Ofrow
    _         ≤ n + density M2      := by simp only [dm1, add_le_add_iff_right]
    _         ≤ n + 0               := by simp only [dm2, add_le_add_iff_left]
    _         ≤ n                   := by omega

  ---
  case proof_M2_av_trivial =>
    by_contra contains_one
    simp [contains] at contains_one
    obtain ⟨f,hf,g,hg,prop⟩ := contains_one
      --   M2    g(0)
      --  f(0)     1
    simp [M2] at prop
    specialize prop 0 0
    simp [PatternOne, Pred_min_Ofrow] at prop
    obtain ⟨a,ha, ha2⟩ := prop.2
       --   M   a g(0)
      --  f(0)  1  1
    have : contains Horizontal2Pattern M  := by
      let g' := ![a, g 0]
      have hg' : StrictMono g' := by
        simp [StrictMono];
        intro x y hxy;
        fin_cases x <;> fin_cases y <;> all_goals (aesop)
      rw [contains]
      refine ⟨f,hf,g',hg', ?_⟩
      simp [g']
      intro a b ha'
      fin_cases a ; fin_cases b <;> all_goals (aesop)
    contradiction
    done

  case proof_dm1 =>
    have h_row_one: ∀ i, row_density M1 i ≤ 1 := by
      intro i
      by_contra H
      simp [row_density, one_lt_card_iff] at H
      obtain ⟨a,ha,b,hb,aneqb⟩ := H
      simp [M1,Pred_min_Ofrow] at ha
      simp [M1,Pred_min_Ofrow] at hb
      have : a = b := by
        refine Fin.le_antisymm ?h1 ?h2
        · -- a ≤ b
          apply ha.2
          exact hb.1
        · -- b ≤ a
          apply hb.2
          exact ha.1
      contradiction

    have:= UB_density_by_rows M1 h_row_one; simp at this
    exact this

theorem exHorizontalkPatternUB (k n: ℕ) : ex (HorizontalkPattern k) n ≤ n*(k-1) := by
  classical
  simp only [ex, Finset.sup_le_iff, mem_filter, Finset.mem_univ, true_and]
  intro M NoHPk
  have h_row_k: ∀ i, row_density M i ≤ k-1  := ?proof_h_row_k
  exact UB_density_by_rows M h_row_k

  case proof_h_row_k =>
    intro i
    by_contra H
    simp at H
    simp [row_density] at H
    let s : Finset (Fin n) := {j | M i j}
    have h: k ≤ s.card := by simp [s]; omega
    let g := s.orderEmbOfCardLe h
    have HPk : contains (HorizontalkPattern k) M := ?proof_HPk
    contradiction
    case proof_HPk =>
      simp [contains]
      refine ⟨![i], by simp [StrictMono],g, by simp [StrictMono, OrderEmbedding.lt_iff_lt], ?EmbedPatttern⟩
      · -- Proof of Embed Pattern
        simp [HorizontalkPattern]
        intro j
        have: g j ∈ s := s.orderEmbOfCardLe_mem h j
        simp [s] at this
        exact this

theorem exVerticalkPatternUB (k n : ℕ ) : ex (VerticalkPattern k) n ≤ n*(k-1) := by
  classical
  have: ex (VerticalkPattern k) n ≤ ex ( tranpose (VerticalkPattern k)) n := ?exv

  calc
    ex (VerticalkPattern k) n ≤ ex ( tranpose (VerticalkPattern k))  n := this
    _                         = ex ( HorizontalkPattern k )  n  := by rfl
    _                         ≤ n*(k-1) := exHorizontalkPatternUB k n

  case exv =>
    simp [ex]
    intro M hM
    rw [← ex]

    let M' := tranpose M
    have hM': ¬ contains (tranpose (VerticalkPattern k)) M' := by
      by_contra H
      simp [contains] at H
      obtain ⟨f,hf,g,hg,prop⟩ := H
      simp [M', tranpose, VerticalkPattern] at prop
      have: contains (VerticalkPattern k) M := by
        simp [contains]
        refine ⟨g,hg,f,hf, by
          simp [VerticalkPattern]
          intro a ha
          apply prop
        ⟩
      contradiction

    have dmeqdm' : density M = density M' :=  by
      apply Finset.card_bij (fun a _ ↦ (a.2,a.1)) ?hi ?i_inj ?i_surj; aesop;aesop;aesop

    calc
      density M = density M' := dmeqdm'
      _         ≤ ex (tranpose (VerticalkPattern k)) n := (avoid_le_ex M' hM')


theorem exHatPatternUB (n : ℕ)  [NeZero n] : ex HatPattern n ≤ 3*n  := by
  classical
  simp [ex]
  intro M noHat

  let min_or_max_of_row := fun i j ↦ (∀ j', M i j' → j ≤ j') ∨ (∀ j', M i j' → j' ≤ j)
  let M1 (i j : Fin n) : Prop := M i j ∧   (min_or_max_of_row i j)
  let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (min_or_max_of_row i j)

  have M1_avoids_H3 : ¬ contains (HorizontalkPattern 3) M1  := ?proof_M1_avoids_H3
  have M2_avoids_V2 : ¬ contains VerticalTwoPattern M2      := ?proof_M2_avoids_V2

  have dm1: density M1 ≤ n*2 := calc
     density M1 ≤ ex  (HorizontalkPattern 3) n := avoid_le_ex M1 M1_avoids_H3
     _          ≤ n*2                          := exHorizontalkPatternUB 3 n

  have dm2: density M2 ≤ n := calc
    density M2 ≤ ex VerticalTwoPattern n := avoid_le_ex M2 M2_avoids_V2
    _          = n                       := exVerticalTwoPattern n

  calc
    density M = density M1 + density M2 := split_density M min_or_max_of_row
    _         ≤ n*2 + density M2      := by simp [dm1]
    _         ≤ n*2 + n               := by simp [dm2]
    _         ≤ 3*n                   := by omega

  --
  case proof_M1_avoids_H3 =>
    by_contra containsH3
    simp [contains] at containsH3
    obtain ⟨f,hf,g,hg,prop⟩ := containsH3
    have M1_subset_M: ∀ i j, M1 i j → M i j := by aesop
    -- M1   g(0) g(1) g(2)
    -- f(0)  1    1    1
    have m1left: M1 (f 0) (g 0) := by apply prop; simp [HorizontalkPattern]
    have mleft: M (f 0) (g 0) := by apply M1_subset_M; exact m1left
    have mid : M1 (f 0) (g 1) := by apply prop; simp [HorizontalkPattern]
    have m1right: M1 (f 0) (g 2) := by apply prop; simp [HorizontalkPattern]
    have mright: M (f 0) (g 2) := by apply M1_subset_M; exact m1right
    simp [M1,min_or_max_of_row] at mid
    simp [StrictMono] at hg
    cases mid.right with
    | inl g1min =>
      have: g 1 ≤ g 0 := by apply g1min; exact mleft
      have: g 0 < g 1 := by simp [hg]
      omega
    | inr g1max =>
      have: g 2 ≤ g 1 := by apply g1max; exact mright
      have: g 1 < g 2 := by simp [hg]
      omega
    done

  case proof_M2_avoids_V2 =>
    by_contra containsV2
    simp [contains] at containsV2
    obtain ⟨f,hf,g,hg,v2_to_M2⟩ := containsV2

    -- M2  g(0)
    -- f(0) 1
    -- f(1) 1
    let i := f 1
    let j := g 0

    simp [VerticalTwoPattern] at v2_to_M2
    have M2y : M2 i j := by apply v2_to_M2
    simp [M2, M1,min_or_max_of_row] at M2y
    obtain ⟨⟨a,ha1,ha2⟩,⟨b,hb1,hb2⟩⟩ : (∃ a, M i a ∧ a < j) ∧ (∃ b, M i b ∧ j < b)  := M2y.2
    --have alb : a < b := by omega

    let g' : Fin 3 → Fin n:= ![ a, g 0, b]
    have monog' : StrictMono g' := by
      simp [StrictMono]
      intro x y _
      fin_cases x <;> fin_cases y <;> simp [g'] <;> all_goals (first| {aesop} | omega)
--      fin_cases x <;> fin_cases y <;> simp
--      contradiction; exact ha2   ; omega
--      contradiction; contradiction; exact hb2
--      contradiction; contradiction; contradiction

      --   M   a j/g(0) b
      --  f(0)     1
      -- i/f(1) 1     1

    have : contains HatPattern M  := by
      rw [contains]
      refine ⟨f,hf,g',monog', by
        -- We prove forall a,b, HatPattern a b => M (f a) (g' b)
        intro i_row j_col H
        fin_cases i_row <;> fin_cases j_col <;> simp [g'] <;> repeat (any_goals (first| exact ha1| exact hb1 | contradiction) )
        · -- i_row=0,j_col=1
          show M (f 0) j
          have M2_subset_M: ∀ i j, M2 i j → M i j := by aesop
          exact M2_subset_M (f 0) j (v2_to_M2 0 0)
      ⟩
    contradiction
    done

  /-  old long proof (it works but too long)
    have h_row_one: ∀ i, row_density M1 i ≤ 2 := by
      intro i
      by_contra H
      simp [row_density] at H
      have: ∃ u : Fin n, M1 i u ∧ ¬ (min_or_max_of_row i u) := ?proof_mid_point_exist
      simp [M1] at this
      obtain ⟨u, ⟨uinM,h1⟩ ,h2⟩ := this
      contradiction

      case proof_mid_point_exist =>
        simp [Finset.two_lt_card] at H
        obtain ⟨a,ha,b,hb,c,hc,anb,anc,bnc⟩ := H
        let s : Finset (Fin n):= {a,b,c}
        have h: s.card = 3 := by
          simp [s]
          rw [card_eq_three]
          use a,b,c
        let f := s.orderEmbOfFin h

        let x := f 0; have hx: x ∈ s := by simp [x,f]
        let y := f 1; have hy: y ∈ s := by simp [y,f]
        let z := f 2; have hz: z ∈ s := by simp [z,f]
        have: x < y ∧  y < z := by simp only [OrderEmbedding.lt_iff_lt, Fin.reduceLT, and_self, x, y, z]
        obtain ⟨xy,yz⟩ := this
        have M1ix : M1 i x := by
          simp [s] at hx
          rcases hx with h1 | h2 | h3
          · rwa [h1]
          · rwa [h2]
          · rwa [h3]
        have M1iy : M1 i y :=  by
          simp [s] at hy
          rcases hy with h1 | h2 | h3
          · rwa [h1]
          · rwa [h2]
          · rwa [h3]
        have M1iz : M1 i z :=  by
          simp [s] at hz
          rcases hz with h1 | h2 | h3
          · rwa [h1]
          · rwa [h2]
          · rwa [h3]
        have Mix : M i x := by
          apply M1_subset_M
          exact M1ix
        have Miz : M i z := by
          apply M1_subset_M
          exact M1iz
        -- main proof
        use y
        constructor
        · -- Proof: M1 i y
          exact M1iy
        · -- Proof: y not min nor max
          simp [min_or_max_of_row]
          constructor
          · -- Proof: y is not min
            use x
          · -- Proof: y is not max
            use z

    exact UB_density_by_rows M1 h_row_one-/

theorem exIdentitykUB  (n k : ℕ)  : ex (Identity k) n ≤ (2*n-1)*k := by sorry
