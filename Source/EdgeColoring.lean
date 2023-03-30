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

variable (v : V) [Fintype (neighborSet G v)]
open Fintype Finset

def edgeSpan : Set (edgeSet G) := fun e => Sym2.Mem v e

instance : Fintype (edgeSpan G v) := sorry

theorem something : edgeSpan G v = (edgeSpan G v).toFinset := sorry
#check edgeSet
def neighborSettoEdge (v' : neighborSet G v) : Sym2 V := ⟦(v,v')⟧
#print Subtype
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
  left_inv := fun v' => by sorry
  right_inv := sorry

example (W : Type) (s : Set W) [Fintype s] : Finset W := s.toFinset
  -- @Finset.map s W ⟨(↑),Subtype.coe_injective⟩ elems

theorem edgeSpan_isClique : IsClique (lineGraph G) <| edgeSpan G v := fun _ he₁ _ he₂ ne => ⟨⟨v,⟨he₁,he₂⟩⟩,ne⟩

#check IsClique.card_le_of_coloring

theorem degree_le_edgeColoring [Fintype α] (c : EdgeColoring G α) : G.degree v ≤ Fintype.card α := by
  change (neighborFinset G v).card ≤ Fintype.card α
  -- have : (edgeSpan G v).toFinset = neighborFinset G v := sorry
  -- refine @IsClique.card_le_of_coloring (edgeSet G) (lineGraph G) α (edgeSpan G v).toFinset ?_ _  ?_
  --
  sorry
  -- apply IsClique.card_le_of_coloring (G := lineGraph G)
  -- · exact edgeSpan_isClique G v
  -- · sorry

def restrictedColoring (c : EdgeColoring G α) : G.neighborSet v → α := sorry

theorem ge_degree_of_coloring (n : ℕ) (c : EdgeColoring G (Fin n)) :
    n ≥ G.degree v := by
  by_contra h
  sorry

theorem ge_degree_of_colorable (n : ℕ) (h : G.Colorable n) :
    n ≥ G.degree v := sorry

theorem edgeChromaticNumber_ge_degree :
    edgeChromaticNumber G ≥ G.degree v := by
  sorry
