import StreamLogic.TutorialOne
open First

example (P : Prop) (h'₁ : P) : P := by
  assumption

example (P Q :Prop) (h'₁ : P) (h'₂ : Q) : P ∧ Q := by
  constructor
  repeat assumption 

example (P Q R S : Prop)(h'₁ : P)(h'₂ : Q)(h'₃ : R)(h'₄ : S) : (P ∧ Q) ∧ R ∧ S := by
  constructor
  repeat {constructor; assumption ;assumption}

example (P Q : Prop) (h : P ∧ Q) : P := by
  cases h
  assumption

example ( P Q R S : Prop ) (h1 : P ∧ Q) (h2 : R ∧ S) : P ∧ S := by
  constructor
  cases h1
  assumption
  cases h2
  assumption
variable (P Q : Prop)
example (h1: (Q ∧ (((Q ∧ P) ∧ Q) ∧ Q ∧ Q ∧ Q)) ∧ (Q ∧ Q) ∧ Q) : P := by
  exact h1.left.right.left.left.right

example (A C I O P S U : Prop)(h: ((P ∧ S) ∧ A) ∧ ¬I ∧ (C ∧ ¬O) ∧ ¬U) : A ∧ C ∧ P ∧ S := by
  exact ⟨h.left.right,⟨h.right.right.left.left,⟨h.left.left.left,h.left.left.right⟩⟩⟩


example (A C I O P S U : Prop)(h: ((P ∧ S) ∧ A) ∧ ¬I ∧ (C ∧ ¬O) ∧ ¬U) : A ∧ C ∧ P ∧ S := by
  obtain ⟨a,b⟩ := h
  obtain ⟨ps,a'⟩ := a
  obtain ⟨p,s⟩ := ps
  obtain ⟨_,co,_⟩ := b
  obtain ⟨c,_⟩ := co
  exact ⟨a',⟨c,⟨p,s⟩⟩⟩

example (C: Prop) : C → C := by
  exact λh ↦ h


example (I S: Prop) : I ∧ S → S ∧ I := by
  have h := λ h1 : I ∧ S ↦ and_intro h1.right h1.left
  exact h

example (A : Prop) (a : A ∧ A) : A := by
  cases a with | _ a b
  assumption


example (C A S: Prop) (h1 : C → A) (h2 : A → S) : C → S := by
  exact h2 ∘ h1

example (C A S: Prop) (h1 : C → A) (h2 : A → S) : C → S := 
  λ h' : C ↦ h2 (h1 h') 



example (P Q R S T U: Prop) (p : P) (h1 : P → Q) (h2 : Q → R) (h3 : Q → T) (h4 : S → T) (h5 : T → U) : U := by
  have h' := h5 ∘ h3 ∘ h1
  exact h' p

example (C D S: Prop) (h : C ∧ D → S) : C → D → S := by
  have h' := λ h1 : C ↦ λ h2 : D ↦ h (and_intro h1 h2)
  exact h'


example (C D S: Prop) (h : C → D → S) : C ∧ D → S := by
  have h' := λ h1 : C ∧ D ↦ h h1.left h1.right
  exact h'


example (C D S : Prop) (h : (S → C) ∧ (S → D)) : S → C ∧ D := by
  have h' := λ h1 :S ↦ and_intro (h.left h1) (h.right h1)
  exact h'


example (R S : Prop) : R → (S → R) ∧ (¬S → R) := by
  have h := λ r : R ↦ and_intro (λ s : S ↦ r) (λ ns :¬S ↦ r)
  exact h
