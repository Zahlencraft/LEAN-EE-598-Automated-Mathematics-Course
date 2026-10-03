import LeanIntro.Playground.CHSH.Scenario

/-!
# The CHSH symmetry group `G` is the dihedral group of order 8

`G` is the automorphism group of the CHSH context hypergraph. The main result is
`CHSH.gEquivDihedral : G ≃* DihedralGroup 4` — an explicit group isomorphism, which is strictly
stronger than the cardinality statement `card_G : Nat.card G = 8`.

Note on conventions:

* Mathlib's `DihedralGroup n` has order `2 * n`, so the group of order 8 is `DihedralGroup 4`.
  Some authors write `D₈` for this group.
* `G` is the automorphism group of the *unlabelled* context hypergraph, so it contains the exchange
  of Alice and Bob (`swapParties_mem`). Requiring the party labelling to be preserved instead cuts
  `G` down to a subgroup of order 4 (`card_partyPreserving_aut`), which would change the
  representation theory downstream. This is a modelling choice, and it is the order-8 reading that
  matches the thesis.

Everything finite here is closed by `decide`, so it is checked by the Lean kernel. `native_decide`
is deliberately never used: it discharges goals via compiled code and the `Lean.ofReduceBool` axiom,
which would put the results outside the kernel.
-/

namespace CHSH

open Meas

/-- `G`: the symmetry group of the CHSH context hypergraph. -/
abbrev G : Subgroup (Equiv.Perm Meas) := chsh.autSubgroup

/-- Membership in `G` is decidable, via the `Finset` bridge for `Hypergraph.ofFinsetFamily`. This
instance is what allows the results below to be closed by `decide`. -/
instance : DecidablePred (· ∈ G) := fun σ =>
  decidable_of_iff _ (Hypergraph.mem_autSubgroup_ofFinsetFamily (fam := contexts) (σ := σ)).symm

/-! ### Generators -/

/-- Rotation of the context cycle: `A₀ → B₀ → A₁ → B₁ → A₀`. -/
def rot : Equiv.Perm Meas where
  toFun := fun | A₀ => B₀ | B₀ => A₁ | A₁ => B₁ | B₁ => A₀
  invFun := fun | A₀ => B₁ | B₀ => A₀ | A₁ => B₀ | B₁ => A₁
  left_inv := fun x => by cases x <;> rfl
  right_inv := fun x => by cases x <;> rfl

/-- Reflection of the context cycle through the `A₀ – A₁` axis: it swaps Bob's two measurements
and fixes Alice's. -/
def reflect : Equiv.Perm Meas := Equiv.swap B₀ B₁

theorem rot_mem : rot ∈ G := by decide

theorem reflect_mem : reflect ∈ G := by decide

theorem rot_pow_four : rot ^ 4 = 1 := by decide

theorem rot_pow_two_ne_one : rot ^ 2 ≠ 1 := by decide

theorem orderOf_rot : orderOf rot = 4 :=
  orderOf_eq_prime_pow (n := 1) (p := 2) rot_pow_two_ne_one (by simpa using rot_pow_four)

theorem reflect_sq : reflect * reflect = 1 := by decide

/-- The dihedral relation. -/
theorem reflect_mul_rot : reflect * rot = rot⁻¹ * reflect := by decide

/-! ### `G ≅ D₄` -/

/-- The permutation realising a dihedral group element. The `sr` case follows Mathlib's
`DihedralGroup` multiplication convention; `rot ^ i * reflect` would not be a homomorphism. -/
def toPerm : DihedralGroup 4 → Equiv.Perm Meas
  | .r i => rot ^ i.val
  | .sr i => reflect * rot ^ i.val

/-- `DihedralGroup 4` acting on the CHSH measurements. -/
def hom : DihedralGroup 4 →* Equiv.Perm Meas where
  toFun := toPerm
  map_one' := by decide
  map_mul' := by decide

@[simp] theorem hom_apply (d : DihedralGroup 4) : hom d = toPerm d := rfl

theorem hom_injective : Function.Injective hom := by decide

/-- Every dihedral element acts as a hypergraph automorphism, and every automorphism arises this
way — so the range of `hom` is exactly `G`. -/
theorem range_hom : hom.range = G := by
  refine le_antisymm ?_ ?_
  · rintro σ ⟨d, rfl⟩
    revert d
    decide
  · intro σ hσ
    have h : ∀ σ : Equiv.Perm Meas, σ ∈ G → ∃ d : DihedralGroup 4, toPerm d = σ := by decide
    obtain ⟨d, hd⟩ := h σ hσ
    exact ⟨d, hd⟩

/-- **The symmetry group of the CHSH context hypergraph is the dihedral group of order 8.**

This is the substantive form of the claim: an explicit isomorphism, not merely an equality of
cardinalities. -/
noncomputable def gEquivDihedral : G ≃* DihedralGroup 4 :=
  ((MonoidHom.ofInjective hom_injective).trans (MulEquiv.subgroupCongr range_hom)).symm

theorem card_G : Nat.card G = 8 := by
  rw [Nat.card_congr gEquivDihedral.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]

/-- Independent brute-force confirmation of `card_G`, not routed through the isomorphism: the
kernel enumerates all 24 permutations of the four measurements and keeps those preserving the
context set. -/
theorem card_G_by_enumeration : Fintype.card G = 8 := by decide

/-! ### `G` is the right group, and a proper non-trivial one

`card_G = 8` would also hold for various wrong definitions, so these pin down that `G` really is the
symmetry group of the CHSH scenario and not an artefact. -/

/-- `G` is also exactly the automorphism group of the context *graph*: nothing is lost or gained in
passing between the hypergraph `chsh` and the 4-cycle. -/
theorem mem_G_iff_graph_aut (σ : Equiv.Perm Meas) :
    σ ∈ G ↔ ∀ v w, chshGraph.Adj (σ v) (σ w) ↔ chshGraph.Adj v w := by
  revert σ; decide

/-- Some permutation of the measurements is not a symmetry, so `G ≠ ⊤`. -/
theorem exists_not_mem_G : ∃ σ : Equiv.Perm Meas, σ ∉ G := by decide

theorem G_ne_top : G ≠ ⊤ := by
  intro h
  obtain ⟨σ, hσ⟩ := exists_not_mem_G
  exact hσ (by rw [h]; exact Subgroup.mem_top σ)

theorem G_ne_bot : G ≠ ⊥ := by
  intro h
  have hrot : rot ∈ (⊥ : Subgroup (Equiv.Perm Meas)) := h ▸ rot_mem
  rw [Subgroup.mem_bot] at hrot
  exact absurd hrot (by decide)

/-! ### Why `G` has order 8 and not 4 -/

/-- Exchanging Alice and Bob is a hypergraph automorphism. -/
theorem swapParties_mem : (Equiv.swap A₀ B₀ * Equiv.swap A₁ B₁ : Equiv.Perm Meas) ∈ G := by
  decide

/-- Exchanging Alice and Bob does not preserve the party labelling, so it is exactly what
distinguishes `G` from its party-preserving subgroup. -/
theorem swapParties_not_partyPreserving :
    ¬ ∀ v : Meas, ((Equiv.swap A₀ B₀ * Equiv.swap A₁ B₁ : Equiv.Perm Meas) v).party = v.party := by
  decide

/-- The automorphisms that also preserve the Alice/Bob labelling number only 4: relabelling
Alice's two measurements and Bob's two measurements independently. Had the scenario been modelled
with the party partition fixed, `G` would be this order-4 group instead. -/
theorem card_partyPreserving_aut :
    ((Finset.univ : Finset (Equiv.Perm Meas)).filter fun σ =>
        σ ∈ G ∧ ∀ v : Meas, (σ v).party = v.party).card = 4 := by
  decide
#print axioms rot
#print axioms reflect
#print axioms rot_mem
#print axioms reflect_mem
#print axioms rot_pow_four
#print axioms rot_pow_two_ne_one
#print axioms orderOf_rot
#print axioms reflect_sq
#print axioms reflect_mul_rot
#print axioms toPerm
#print axioms hom
#print axioms hom_apply
#print axioms hom_injective
#print axioms range_hom
#print axioms gEquivDihedral
#print axioms card_G
#print axioms card_G_by_enumeration
#print axioms mem_G_iff_graph_aut
#print axioms exists_not_mem_G
#print axioms G_ne_top
#print axioms G_ne_bot
#print axioms swapParties_mem
#print axioms swapParties_not_partyPreserving
#print axioms card_partyPreserving_aut

end CHSH
