import Mathlib.Data.Fintype.Pi

variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ]

-- TODO: replace StrictMono f by StrictMonoOn {a ∣ ∃ b, P a b} f, and similarly for g to ignore blank rows/columns
def contains (P : α → β → Prop) (M : γ → δ → Prop) : Prop :=
  ∃ f : α → γ, StrictMono f ∧ ∃ g : β → δ, StrictMono g ∧ ∀ a b, P a b → M (f a) (g b)

def containsB (P : α → β → Bool) (M : γ → δ → Bool) : Prop :=
  ∃ f : α → γ, StrictMono f ∧ ∃ g : β → δ, StrictMono g ∧ ∀ a b, P a b → M (f a) (g b)

instance [Fintype α] [@DecidableRel α (· < ·)] [@DecidableRel γ (· < ·)] {f : α → γ} :
  Decidable (StrictMono f) := inferInstanceAs (Decidable (∀ _ _, _ → _))

instance {P : α → β → Bool} {M : γ → δ → Bool} [@DecidableRel α (· < ·)] [@DecidableRel β (· < ·)]
    [@DecidableRel γ (· < ·)] [@DecidableRel δ (· < ·)]
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [DecidableEq α] [DecidableEq β] :
    Decidable (containsB P M) :=
  inferInstanceAs <| Decidable <|
    ∃ f : α → γ, StrictMono f ∧ ∃ g : β → δ, StrictMono g ∧ ∀ a b, P a b → M (f a) (g b)

@[refl]
lemma contains_refl (M : γ → δ → Prop) : contains M M :=
  ⟨id, by simp [StrictMono], id, by simp [StrictMono], by aesop⟩

lemma contains_rfl {M : γ → δ → Prop} : contains M M := by rfl
