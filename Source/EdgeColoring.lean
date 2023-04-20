import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Tactic.LibrarySearch

universe u w

open SimpleGraph Hom Iso Embedding

variable {V : Type u} {G : SimpleGraph V} {α : Type v}

def closedNbhdSubgraph (v : V) : SimpleGraph {w | G.Adj v w ∨ w = v} where
  Adj := fun w₁ w₂ => G.Adj w₁ w₂ ∧ (w₁ = v ∨ w₂ = v)
  symm := by
    intro v₁ v₂ h
    constructor
    · apply G.symm <| h.left
    · match h.right with
      | .inl h => exact .inr h
      | .inr h => exact .inl h

def AdjacentAt (v : V) (e₁ e₂ : edgeSet G) : Prop := Sym2.Mem v e₁ ∧ Sym2.Mem v e₂

theorem AdjacentAt.symm {v : V} {e₁ e₂ : edgeSet G} (h : AdjacentAt v e₁ e₂) : AdjacentAt v e₂ e₁ := ⟨h.right, h.left⟩

def Adjacent (e₁ e₂ : edgeSet G) : Prop := ∃ v, AdjacentAt v e₁ e₂

@[symm, aesop unsafe 10% apply (rule_sets [SimpleGraph])]
theorem Adjacent.symm {e₁ e₂ : edgeSet G} (h : Adjacent e₁ e₂) : Adjacent e₂ e₁ := by
  obtain ⟨w,h'⟩ := h
  exact ⟨w,AdjacentAt.symm h'⟩

def lineGraph (G : SimpleGraph V) : SimpleGraph (edgeSet G) where
  Adj := fun e₁ e₂ => Adjacent e₁ e₂ ∧ e₁ ≠ e₂

variable (G)

abbrev EdgeColoring (α : Type v) := Coloring (lineGraph G) α

theorem EdgeColoring.valid {α : Type v} (G : SimpleGraph V)
    (c : EdgeColoring G α) {e₁ e₂ : edgeSet G} (h : e₁ ≠ e₂)
    (adj : Adjacent e₁ e₂ ) : c e₁ ≠ c e₂ :=
  Coloring.valid c ⟨adj,h⟩

noncomputable def edgeChromaticNumber : ℕ := chromaticNumber (lineGraph G)

variable (v : V) [F : Fintype (neighborSet G v)]
open Fintype Finset

def edgeSpan : Set (edgeSet G) := fun e => Sym2.Mem v e
def neighborSettoEdge (v' : neighborSet G v) : Sym2 V := ⟦(v,v')⟧


theorem other_not_eq_given {x y : V} (hne : x ≠ y)(h₁ : x ∈ ⟦(x, y)⟧) : (Sym2.Mem.other h₁) = y := by
  have h : x ∈ ⟦(x, y)⟧ :=
      Sym2.mem_iff.mpr <| .inl rfl
  have h' : (Sym2.Mem.other (h)) = x ∨ (Sym2.Mem.other (h)) = y := Sym2.mem_iff.mp (Sym2.other_mem h)
  have h'' : Sym2.Mem.other h ≠ x := by
      have H : ⟦(x, Sym2.Mem.other h)⟧ = Quotient.mk (Sym2.Rel.setoid V) (x, y) := Sym2.other_spec h
      have H' : y ∈ Quotient.mk (Sym2.Rel.setoid V) (x, y) := Sym2.mem_mk''_right x y
      rw [←H] at H'
      have H'' :  y ∈ Quotient.mk (Sym2.Rel.setoid V) (x, Sym2.Mem.other h) ↔ (y = x ∨ y = Sym2.Mem.other h) := Sym2.mem_iff
      rw [H''] at H'
      cases' H' with w w
      by_contra
      exact hne (Eq.symm w)
      cases' h' with X X
      by_contra
      rw [←X] at hne
      exact hne (_root_.id (Eq.symm w))
      rw [←X] at hne
      exact _root_.id (Ne.symm hne)
  cases' h' with Y Y
  by_contra
  exact h'' Y
  rw [Y]

noncomputable def neighborSetedgeSpanEquiv : (neighborSet G v) ≃ (edgeSpan G v) where
  toFun := fun ⟨v',hv'⟩ => by
    refine ⟨⟨⟦(v,v')⟧,hv'⟩,?_⟩
    · change v ∈ Quotient.mk (Sym2.Rel.setoid V) (v, ↑v')
      rw [Sym2.mem_iff]
      exact Or.inl rfl
  invFun := fun ⟨⟨e,he⟩,he'⟩ => by
    refine ⟨Sym2.Mem.other he',?_⟩
    dsimp [neighborSet]
    rw [←mem_edgeSet,Sym2.other_spec he']
    exact he
  left_inv := fun ⟨v',hv'⟩ => by
    dsimp
    congr
    apply other_not_eq_given (ne_of_adj G hv')
  right_inv := fun ⟨⟨e,he⟩,he'⟩ => by
    dsimp
    congr
    exact Sym2.other_spec he'

noncomputable instance : Fintype (edgeSpan G v) := by
  exact Fintype.ofEquiv (neighborSet G v) (neighborSetedgeSpanEquiv G v)

theorem something : edgeSpan G v = (edgeSpan G v).toFinset := by
  exact Eq.symm (Set.coe_toFinset (edgeSpan G v))

example (W : Type) (s : Set W) [Fintype s] : Finset W := s.toFinset
  -- @Finset.map s W ⟨(↑),Subtype.coe_injective⟩ elems

theorem edgeSpan_isClique : IsClique (lineGraph G) <| edgeSpan G v := fun _ he₁ _ he₂ ne => ⟨⟨v,⟨he₁,he₂⟩⟩,ne⟩

theorem degree_le_card_edgeColoring [Fintype α] (c : EdgeColoring G α) : G.degree v ≤ Fintype.card α := by
  change (neighborFinset G v).card ≤ Fintype.card α
  rw [neighborFinset]
  have X : Fintype.card ((neighborSet G v)) = Fintype.card ((edgeSpan G v)) := by
    apply Fintype.card_congr (neighborSetedgeSpanEquiv G v)

  repeat rw [←Set.toFinset_card] at X
  rw [X]

  refine @IsClique.card_le_of_coloring (edgeSet G) (lineGraph G) α (edgeSpan G v).toFinset ?_ _  ?_
  intro h₁ h₂ h₃ h₄ h₅
  constructor
  use v
  have H :  h₁ ∈ (edgeSpan G v) := Iff.mp Set.mem_toFinset h₂
  have H' :  h₃ ∈ (edgeSpan G v) := Iff.mp Set.mem_toFinset h₄
  have H'' : AdjacentAt v h₁ h₃ := by
    exact ⟨H,H'⟩
  exact H''

  exact h₅
  exact c
--
-- def restrictedColoring (c : EdgeColoring G α) : G.neighborSet v → α := sorry
--
theorem degree_le_coloring (n : ℕ) (c : EdgeColoring G (Fin n)) :
    G.degree v ≤ n := by
  rw [←Fintype.card_fin n]
  apply degree_le_card_edgeColoring _ _ c

theorem degree_le_colorable (n : ℕ) (h : (lineGraph G).Colorable n) :
    G.degree v ≤ n := by
  have ⟨c⟩ := h
  apply degree_le_coloring
  exact c

theorem degree_le_edgeChromaticNumber [Fintype (edgeSet G)] :
    G.degree v ≤ edgeChromaticNumber G:= by
  apply le_cinfₛ
  · apply colorable_set_nonempty_of_colorable
    apply colorable_of_fintype
  · intro b ⟨h⟩
    apply degree_le_coloring
    change Coloring (lineGraph G) (Fin b)
    apply h

-- Note: these should exist
-- instance [Fintype V] : Fintype (Sym2 V) := sorry
-- instance [Fintype V] : Fintype (edgeSet G) := sorry

theorem maxDegree_le_edgeChromaticNumber [Fintype V] [DecidableRel G.Adj] [Fintype (edgeSet G)] :
    maxDegree G ≤ edgeChromaticNumber G := by
  apply maxDegree_le_of_forall_degree_le
  intro v
  apply degree_le_edgeChromaticNumber G v

def insertEdges (t : Set (Sym2 V)) (G : SimpleGraph V) : SimpleGraph V :=
  fromEdgeSet (t ∪ edgeSet G)

instance : Insert (Sym2 V) (SimpleGraph V) where
  insert := fun e G => fromEdgeSet (insert e <| edgeSet G)

instance equivSimpleGraphNonDiagSym2 : Equiv (SimpleGraph V) { s : Set <| Sym2 V // s ∩ Sym2.IsDiag = ∅ } where
  toFun := fun G => by
    refine sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

-- example : [Fintype V] (s : Set (Sym2 V)) :
--     edgeChromaticNumber equivSimpleGraphNonDiagSym2 s ≤
--     maxDegee equiv
#check Equiv.forall_congr
theorem edgeChromaticNumber_le_succ_maxDegree [Fintype V] [Fintype (edgeSet G)] :
    edgeChromaticNumber G ≤ maxDegree G + 1 := by sorry
  -- rw [Equiv.forall_congr_left']
  -- let n := Fintype.card (edgeSet G)
  -- apply Fintype.induction_subsingleton_or_nontrivial
  -- · have : IsEmpty (edgeSet G) := sorry--  Fintype.card_eq_zero_iff.mp
  --   have : edgeChromaticNumber G = 0 := sorry
  --   rw [this]
  --   apply Nat.zero_le
  -- · sorry

