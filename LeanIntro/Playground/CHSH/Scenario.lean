import LeanIntro.Playground.Hypergraph

/-!
# The CHSH measurement scenario and its cell category `ℳ`

Alice and Bob each choose one of two binary measurements. The jointly measurable sets — the
*contexts* — are the four pairs `{Aᵢ, Bⱼ}`. As a hypergraph these are 2-element edges, so the
context hypergraph is a graph, namely the 4-cycle

```
A₀ — B₀ — A₁ — B₁ — A₀
```

`Meas` lists the measurements in that cyclic order, which is what makes the rotation of
`Playground.CHSH.Aut` easy to write down.

`M` (written `ℳ` in the thesis) is the **face poset** of this hypergraph: the four measurements as
singleton cells together with the four contexts as edge cells, ordered by inclusion. A cellular
sheaf over the scenario is a functor out of `M`, with the restriction map `F_{v⊴e}` being the image
of the morphism `vertexCell v ⟶ edgeCell e`. Mathlib's `CategoryTheory.smallCategory` instance for
preorders supplies the category structure, so no bespoke category needs to be defined.
-/

namespace CHSH

/-- The four CHSH measurements, in cyclic order around the context cycle. -/
inductive Meas
  | A₀ | B₀ | A₁ | B₁
  deriving DecidableEq, Repr

namespace Meas

instance : Fintype Meas := ⟨{A₀, B₀, A₁, B₁}, fun x => by cases x <;> decide⟩

/-- Which party performs the measurement: `false` is Alice, `true` is Bob. -/
def party : Meas → Bool
  | A₀ | A₁ => false
  | B₀ | B₁ => true

end Meas

open Meas

/-- The four CHSH contexts: the jointly measurable pairs `{Aᵢ, Bⱼ}`. -/
def contexts : Finset (Finset Meas) := {{A₀, B₀}, {A₀, B₁}, {A₁, B₀}, {A₁, B₁}}

/-- The CHSH context hypergraph, as a Mathlib `Hypergraph`. -/
def chsh : Hypergraph Meas := Hypergraph.ofFinsetFamily contexts

@[simp] theorem card_contexts : contexts.card = 4 := by decide

/-- The scenario is 2-uniform: every context is a pair, so the context hypergraph is a graph. -/
theorem card_of_mem_contexts {e : Finset Meas} (he : e ∈ contexts) : e.card = 2 := by
  revert he; revert e; decide

/-- Every context holds exactly one measurement per party — the scenario is bipartite over
`Meas.party`, which is what makes each context jointly measurable. -/
theorem card_filter_party_of_mem_contexts {e : Finset Meas} (he : e ∈ contexts) :
    (e.filter fun v => v.party = false).card = 1 ∧
      (e.filter fun v => v.party = true).card = 1 := by
  revert he; revert e; decide

/-- The contexts are exactly the Alice/Bob pairs. In particular the same-party pairs `{A₀, A₁}` and
`{B₀, B₁}` are *not* contexts — that is what makes the context graph a 4-cycle rather than `K₄`. -/
theorem mem_contexts_iff (e : Finset Meas) :
    e ∈ contexts ↔ ∃ a b : Meas, a.party = false ∧ b.party = true ∧ e = {a, b} := by
  revert e; decide

/-- Every measurement lies in some context, so the vertex set of `chsh` really is all of `Meas` and
the `Set.univ` in `Hypergraph.ofFinsetFamily` is not an over-approximation. -/
theorem exists_mem_contexts (v : Meas) : ∃ e ∈ contexts, v ∈ e := by revert v; decide

/-- Each measurement lies in exactly two contexts: the context graph is 2-regular. -/
theorem card_filter_mem_contexts (v : Meas) : (contexts.filter fun e => v ∈ e).card = 2 := by
  revert v; decide

/-- Distinct contexts are incomparable. -/
theorem subset_iff_eq_of_mem_contexts {e f : Finset Meas} (he : e ∈ contexts)
    (hf : f ∈ contexts) : e ⊆ f ↔ e = f := by
  revert hf; revert f; revert he; revert e; decide

/-- No context sits below a measurement, so the incidence order has no inversions. -/
theorem not_subset_singleton_of_mem_contexts {e : Finset Meas} (he : e ∈ contexts) (v : Meas) :
    ¬ e ⊆ {v} := by revert he; revert e; revert v; decide

/-! ### The cell category `ℳ` -/

/-- The cells of the scenario: each measurement as a singleton, plus each context. -/
def cells : Finset (Finset Meas) :=
  (Finset.univ.image fun v : Meas => ({v} : Finset Meas)) ∪ contexts

@[simp] theorem card_cells : cells.card = 8 := by decide

/-- `ℳ`: the face poset of the CHSH context hypergraph, ordered by inclusion of cells.

The `PartialOrder` comes from `Subtype`, and `CategoryTheory.smallCategory` then makes this a
category whose morphisms `v ⟶ e` are exactly the incidences `v ⊴ e`. -/
abbrev M := {S : Finset Meas // S ∈ cells}

/-- The 0-cell of a measurement. -/
def vertexCell (v : Meas) : M := ⟨{v}, by revert v; decide⟩

/-- The 1-cell of a context. -/
def edgeCell {e : Finset Meas} (he : e ∈ contexts) : M :=
  ⟨e, Finset.mem_union_right _ he⟩

@[simp] theorem vertexCell_val (v : Meas) : (vertexCell v).val = {v} := rfl

@[simp] theorem edgeCell_val {e : Finset Meas} (he : e ∈ contexts) :
    (edgeCell he).val = e := rfl

/-- The order on `ℳ` is incidence: a measurement is below a context exactly when it belongs to it.
This is the relation the thesis writes `v ⊴ e`. -/
@[simp] theorem vertexCell_le_edgeCell {v : Meas} {e : Finset Meas} (he : e ∈ contexts) :
    vertexCell v ≤ edgeCell he ↔ v ∈ e := by
  change ({v} : Finset Meas) ≤ e ↔ v ∈ e
  simp [Finset.singleton_subset_iff]

/-- **`ℳ` is exactly the face poset.** Every morphism is either an identity or an incidence
`v ⊴ e`: there are no morphisms between distinct measurements, none between distinct contexts, and
none from a context down to a measurement. Without this, `ℳ` could carry extra morphisms that a
cellular sheaf over it would silently have to respect. -/
theorem M_le_iff (S T : M) :
    S ≤ T ↔ S = T ∨ ∃ v : Meas, S.val = {v} ∧ T.val ∈ contexts ∧ v ∈ T.val := by
  revert T; revert S; decide

/-! ### The context hypergraph is the 4-cycle

Every context is a pair, so the context hypergraph is a graph, and that graph is `C₄`. This is what
licenses the standard description of the CHSH symmetry group as the dihedral symmetry of a square —
`Playground.CHSH.Aut` proves `G ≃* DihedralGroup 4` directly and does not depend on this section. -/

/-- The graph induced by the contexts: two distinct measurements are adjacent when some context
contains both. -/
def chshGraph : SimpleGraph Meas where
  Adj v w := v ≠ w ∧ ∃ e ∈ contexts, v ∈ e ∧ w ∈ e
  symm := by
    constructor
    rintro v w ⟨hne, e, he, hv, hw⟩
    exact ⟨hne.symm, e, he, hw, hv⟩
  loopless := by
    constructor
    rintro v ⟨hne, -⟩
    exact hne rfl

instance : DecidableRel chshGraph.Adj := fun v w =>
  decidable_of_iff (v ≠ w ∧ ∃ e ∈ contexts, v ∈ e ∧ w ∈ e) Iff.rfl

/-- Measurements indexed by their position around the context cycle. -/
def cycleIndex : Meas ≃ Fin 4 where
  toFun := fun | A₀ => 0 | B₀ => 1 | A₁ => 2 | B₁ => 3
  invFun i := if i = 0 then A₀ else if i = 1 then B₀ else if i = 2 then A₁ else B₁
  left_inv x := by revert x; decide
  right_inv i := by revert i; decide

/-- **The CHSH context hypergraph is the 4-cycle** `A₀ — B₀ — A₁ — B₁ — A₀`. -/
def graphIso : chshGraph ≃g SimpleGraph.cycleGraph 4 where
  toEquiv := cycleIndex
  map_rel_iff' := by decide

/-- The induced graph carries exactly the hypergraph's information back: its edges are the
contexts. So `graphIso` is a statement about `chsh` and not merely about some auxiliary graph. -/
theorem adj_iff_mem_contexts (v w : Meas) :
    chshGraph.Adj v w ↔ ({v, w} : Finset Meas) ∈ contexts := by
  revert w; revert v; decide

/-- The graph is not complete: same-party measurements are non-adjacent. -/
theorem not_adj_same_party (v w : Meas) (hne : v ≠ w) (h : v.party = w.party) :
    ¬ chshGraph.Adj v w := by
  revert h; revert hne; revert w; revert v; decide
#print axioms Meas
#print axioms Meas.party
#print axioms contexts
#print axioms chsh
#print axioms card_contexts
#print axioms card_of_mem_contexts
#print axioms card_filter_party_of_mem_contexts
#print axioms mem_contexts_iff
#print axioms exists_mem_contexts
#print axioms card_filter_mem_contexts
#print axioms subset_iff_eq_of_mem_contexts
#print axioms not_subset_singleton_of_mem_contexts
#print axioms cells
#print axioms card_cells
#print axioms M
#print axioms vertexCell
#print axioms edgeCell
#print axioms vertexCell_val
#print axioms edgeCell_val
#print axioms vertexCell_le_edgeCell
#print axioms M_le_iff
#print axioms chshGraph
#print axioms cycleIndex
#print axioms graphIso
#print axioms adj_iff_mem_contexts
#print axioms not_adj_same_party

end CHSH
