import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring 

#check SimpleGraph.Coloring

universe u w

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

def AdjacentAt (v : V) (e₁ e₂ : edgeSet G) : Prop := Sym2.Mem v e₁ ∧ Sym2.Mem v e₂

theorem AdjacentAt.symm {v : V} {e₁ e₂ : edgeSet G} (h : AdjacentAt v e₁ e₂) : AdjacentAt v e₂ e₁ := ⟨h.right, h.left⟩

def Adjacent (e₁ e₂ : edgeSet G) : Prop := ∃ v, AdjacentAt v e₁ e₂

@[symm, aesop unsafe 10% apply (rule_sets [SimpleGraph])]
theorem Adjacent.symm {e₁ e₂ : edgeSet G} (h : Adjacent e₁ e₂) : Adjacent e₂ e₁ := by 
  obtain ⟨w,h'⟩ := h
  exact ⟨w,AdjacentAt.symm h'⟩ 

def lineGraph (G : SimpleGraph V) : SimpleGraph (edgeSet G) where 
  Adj := fun e₁ e₂ => Adjacent e₁ e₂ ∧ e₁ ≠ e₂ 

abbrev EdgeColoring (α : Type) := Coloring (lineGraph G) α 
