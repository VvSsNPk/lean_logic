-- this is the introduction
namespace First
variable (P Q R S U V W A I O U: Prop) 
example  (todo_list : P) : P := by
  exact todo_list

example : P → P := by
  intro h
  exact h

def and_intro : _A → _B → _A ∧ _B := And.intro
def and_left : _A ∧ _B → _A := And.left 
def and_right : _A ∧ _B → _B := And.right

example (p : P) (s: S) : P ∧ S := by
  exact and_intro p s

-- objective is to understand the precedence
example (a : A) (i : I) (o : O ) (u : U) : ((A ∧ I) ∧ (O ∧ U)) := by
  have ai := and_intro a i
  have aio := and_intro o u
  have ans := and_intro ai aio
  exact ans

example (a : A) (i : I) (o : O ) (u : U) : ((A ∧ I) ∧ (O ∧ U)) := by
  exact ⟨⟨a,i⟩,⟨o,u⟩⟩


example (vm : P ∧ S) : P := by
  exact vm.left

example (h : P ∧ Q) : Q := by
  exact and_right h

example (h1 : A ∧ I) (h2 : O ∧ U) : A ∧ U := by
  exact ⟨h1.left,h2.right⟩


example (C L : Prop)(h: (L ∧ (((L ∧ C) ∧ L) ∧ L ∧ L ∧ L)) ∧ (L ∧ L) ∧ L) : C := by
  exact h.left.right.left.left.right


example (A C I O P S U : Prop)(h: ((P ∧ S) ∧ A) ∧ ¬I ∧ (C ∧ ¬O) ∧ ¬U) : A ∧ C ∧ P ∧ S := by
  have p := h.left.left.left
  have c := h.right.right.left.left
  have a := h.left.right
  have s := h.left.left.right
  exact ⟨a,⟨c,⟨p,s⟩⟩⟩


--end of the first world
end First
