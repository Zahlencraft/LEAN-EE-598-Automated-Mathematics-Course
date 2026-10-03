import Mathlib

/-!
# Automorphism groups of hypergraphs

Mathlib's `Hypergraph` (`Mathlib.Combinatorics.Hypergraph.Basic`) is `Set`-based and carries a
functorial `Hypergraph.image`, but has no notion of automorphism. We add one:

* `Hypergraph.autSubgroup H` — the vertex permutations `σ` with `H.image σ = H`, as a
  `Subgroup (Equiv.Perm α)`.

`Set`-based data is not computable, so a brute-force `decide` on `autSubgroup` is impossible as
stated. `Hypergraph.ofFinsetFamily` builds a hypergraph from a `Finset` family, and
`mem_autSubgroup_ofFinsetFamily` transports membership to an equality of `Finset`s — a decidable
proposition. That bridge is what lets the CHSH automorphism group be enumerated *by the kernel*,
while still stating the result about Mathlib's `Hypergraph`.
-/

namespace Hypergraph

variable {α β γ : Type*}

/-! ### `Hypergraph.image` is functorial -/

@[simp]
theorem image_id (H : Hypergraph α) : H.image id = H := by
  apply Hypergraph.ext <;> simp [image_vertexSet, image_edgeSet]

/-! ### The automorphism group -/

/-- The automorphism group of a hypergraph: the vertex permutations preserving it. -/
def autSubgroup (H : Hypergraph α) : Subgroup (Equiv.Perm α) where
  carrier := {σ | H.image σ = H}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change H.image ((a * b : Equiv.Perm α) : α → α) = H
    rw [show ((a * b : Equiv.Perm α) : α → α) = (a : α → α) ∘ (b : α → α) from rfl,
      ← image_image, hb, ha]
  inv_mem' := by
    intro a ha
    change H.image ((a⁻¹ : Equiv.Perm α) : α → α) = H
    replace ha : H.image ((a : Equiv.Perm α) : α → α) = H := ha
    calc H.image ((a⁻¹ : Equiv.Perm α) : α → α)
        = (H.image ((a : Equiv.Perm α) : α → α)).image ((a⁻¹ : Equiv.Perm α) : α → α) := by
          rw [ha]
      _ = H.image (((a⁻¹ : Equiv.Perm α) : α → α) ∘ ((a : Equiv.Perm α) : α → α)) :=
          image_image H
      _ = H := by
          rw [show ((a⁻¹ : Equiv.Perm α) : α → α) ∘ ((a : Equiv.Perm α) : α → α) = id from by
            funext x; simp]
          exact H.image_id

theorem mem_autSubgroup {H : Hypergraph α} {σ : Equiv.Perm α} :
    σ ∈ H.autSubgroup ↔ H.image σ = H := Iff.rfl

/-- An automorphism carries hyperedges to hyperedges. -/
theorem image_mem_edgeSet_of_mem_autSubgroup {H : Hypergraph α} {σ : Equiv.Perm α}
    (hσ : σ ∈ H.autSubgroup) {e : Set α} (he : e ∈ H.edgeSet) : σ '' e ∈ H.edgeSet := by
  have := image_mem_edgeSet_image (H := H) (f := (σ : α → α)) he
  rwa [mem_autSubgroup.mp hσ] at this

/-! ### Hypergraphs from a finite family, and decidability -/

/-- The hypergraph on all of `α` whose hyperedges are the members of a finite family. -/
def ofFinsetFamily (fam : Finset (Finset α)) : Hypergraph α where
  vertexSet := Set.univ
  edgeSet := (fun e : Finset α => (↑e : Set α)) '' ↑fam
  subset_vertexSet_of_mem_edgeSet' _ _ := Set.subset_univ _

@[simp]
theorem ofFinsetFamily_vertexSet (fam : Finset (Finset α)) :
    (ofFinsetFamily fam).vertexSet = Set.univ := rfl

@[simp]
theorem ofFinsetFamily_edgeSet (fam : Finset (Finset α)) :
    (ofFinsetFamily fam).edgeSet = (fun e : Finset α => (↑e : Set α)) '' ↑fam := rfl

/-- Coercing a finite family of finite sets to a set of sets is injective. -/
theorem coe_family_injective :
    Function.Injective fun F : Finset (Finset α) => (fun e : Finset α => (↑e : Set α)) '' ↑F := by
  intro F₁ F₂ h
  exact Finset.coe_inj.mp (Set.image_injective.mpr Finset.coe_injective h)

/-- The bridge that makes the automorphism group computable: preserving a hypergraph built from a
`Finset` family is the same as fixing that family under pointwise image. -/
theorem mem_autSubgroup_ofFinsetFamily [DecidableEq α] {fam : Finset (Finset α)}
    {σ : Equiv.Perm α} :
    σ ∈ (ofFinsetFamily fam).autSubgroup ↔ fam.image (Finset.image σ) = fam := by
  constructor
  · intro h
    apply coe_family_injective
    simpa [Finset.coe_image, Set.image_image] using congrArg Hypergraph.edgeSet h
  · intro h
    apply Hypergraph.ext
    · simp [image_vertexSet]
    · simpa [image_edgeSet, Finset.coe_image, Set.image_image] using
        congrArg (fun F : Finset (Finset α) => (fun e : Finset α => (↑e : Set α)) '' ↑F) h

instance [DecidableEq α] (fam : Finset (Finset α)) :
    DecidablePred (· ∈ (ofFinsetFamily fam).autSubgroup) := fun _ =>
  decidable_of_iff _ mem_autSubgroup_ofFinsetFamily.symm

#print axioms image_id
#print axioms autSubgroup
#print axioms mem_autSubgroup
#print axioms image_mem_edgeSet_of_mem_autSubgroup
#print axioms ofFinsetFamily
#print axioms ofFinsetFamily_vertexSet
#print axioms ofFinsetFamily_edgeSet
#print axioms coe_family_injective
#print axioms mem_autSubgroup_ofFinsetFamily
end Hypergraph
