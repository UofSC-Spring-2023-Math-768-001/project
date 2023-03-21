import Mathlib.Combinatorics.SimpleGraph.Coloring 

universe u w

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {α : Type v}

def closedNbhdSubgraph (v : V) : SimpleGraph {w | G.Adj v w ∨ w = v} where 
  Adj := fun w₁ w₂ => G.Adj w₁ w₂ ∧ (w₁ = v ∨ w₂ = v)
  symm := by
    intro v₁ v₂ h
    constructor
    · apply G.symm <| h.left
    · sorry

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

variable (v : V) [Fintype (G.neighborSet v)] 

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
