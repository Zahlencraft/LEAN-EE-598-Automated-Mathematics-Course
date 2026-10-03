import LeanIntro.Playground.CHSH.Aut

/-!
# The action `α : G × ℳ → ℳ` as a functor

`G` acts on the cell category `ℳ` by relabelling measurements. Each `g : G` acts by an
order-isomorphism of the face poset, hence by a functor `ℳ ⥤ ℳ`, and `g ↦ actFunctor g` is a monoid
homomorphism into `End (Cat.of ℳ)`. Applying `CategoryTheory.SingleObj.functor` turns that into a
single functor

```
α : SingleObj G ⥤ Cat
```

which is the precise sense in which the action is "a covariant functor": `SingleObj G` is the
delooping of `G` (one object, morphisms the group elements), so a functor out of it *is* an action,
with functoriality being exactly the two group-action axioms.

A remark on notation: the thesis writes `α : G × ℳ → ℳ`, which is the set-level action map. It is
not a functor out of the product category `SingleObj G × ℳ` — the object part of such a functor
could not depend on the group element, since group elements are *morphisms* of `SingleObj G`. The
functorial content is `SingleObj G ⥤ Cat`, given here as `CHSH.α`.
-/

namespace CHSH

open CategoryTheory

/-! ### `G` acts on the cells -/

/-- An automorphism of the context hypergraph permutes the cells of the face poset. -/
theorem image_mem_cells (σ : Equiv.Perm Meas) (hσ : σ ∈ G) {S : Finset Meas} (hS : S ∈ cells) :
    S.image σ ∈ cells := by
  revert hS; revert S; revert hσ; revert σ; decide

instance : SMul G M where
  smul g S := ⟨S.val.image (g : Equiv.Perm Meas), image_mem_cells _ g.2 S.2⟩

@[simp] theorem smul_val (g : G) (S : M) :
    (g • S).val = S.val.image (g : Equiv.Perm Meas) := rfl

instance : MulAction G M where
  one_smul S := by apply Subtype.ext; simp
  mul_smul g h S := by
    apply Subtype.ext
    simp [Finset.image_image, Equiv.Perm.coe_mul]

/-- The action sends the cell of a measurement to the cell of the relabelled measurement. -/
@[simp] theorem smul_vertexCell (g : G) (v : Meas) :
    g • vertexCell v = vertexCell ((g : Equiv.Perm Meas) v) := by
  apply Subtype.ext; simp [vertexCell]

/-- The action is faithful: distinct symmetries act differently on `ℳ`. -/
theorem faithful : Function.Injective (MulAction.toPermHom G M) := by
  intro g h hgh
  ext v
  have := congrArg (fun p => (p (vertexCell v)).val) hgh
  simpa [MulAction.toPermHom, vertexCell] using this

/-- The action respects cell dimension: measurements go to measurements and contexts to contexts.
A poset automorphism could not do otherwise, but stating it rules out a definition of `cells` that
accidentally conflated the two gradings. -/
theorem smul_mem_contexts (σ : Equiv.Perm Meas) (hσ : σ ∈ G) {e : Finset Meas}
    (he : e ∈ contexts) : e.image σ ∈ contexts := by
  revert he; revert e; revert hσ; revert σ; decide

theorem smul_singleton (σ : Equiv.Perm Meas) (v : Meas) :
    ({v} : Finset Meas).image σ = {σ v} := by simp

/-- The action is non-trivial: some symmetry moves some cell. Together with `faithful` this rules
out the action having been defined as the trivial one. -/
theorem exists_smul_ne : ∃ (g : G) (S : M), g • S ≠ S :=
  ⟨⟨rot, rot_mem⟩, vertexCell Meas.A₀, by decide⟩

/-! ### Each group element acts as a functor -/

theorem monotone_smul (g : G) : Monotone fun S : M => g • S := by
  intro S T hST
  exact Finset.image_subset_image hST

/-- The functor `ℳ ⥤ ℳ` given by relabelling along `g`. -/
def actFunctor (g : G) : M ⥤ M := (monotone_smul g).functor

@[simp] theorem actFunctor_obj (g : G) (S : M) : (actFunctor g).obj S = g • S := rfl

/-- Functor equality in `ℳ ⥤ ℳ` only needs agreement on objects: `ℳ` is a poset, so its hom types
are subsingletons. -/
theorem actFunctor_ext {F F' : M ⥤ M} (h : ∀ S, F.obj S = F'.obj S) : F = F' :=
  CategoryTheory.Functor.ext h fun _ _ _ => Subsingleton.elim _ _

/-- `act_identity`: the identity acts as the identity functor. -/
@[simp] theorem actFunctor_one : actFunctor 1 = 𝟭 M :=
  actFunctor_ext fun S => by simp [one_smul]

/-- `act_compose`: the action is functorial in the group. -/
theorem actFunctor_mul (g h : G) : actFunctor (g * h) = actFunctor h ⋙ actFunctor g :=
  actFunctor_ext fun S => by simp [mul_smul]

/-! ### The action as a single functor out of `SingleObj G` -/

/-- The action packaged as a monoid homomorphism into the endomorphism monoid of `ℳ` in `Cat`.

Note `End.mul_def : xs * ys = ys ≫ xs`, which is why `map_mul'` is discharged by `actFunctor_mul`
in the stated order. -/
def actHom : G →* End (Cat.of M) where
  toFun g := Cat.Hom.ofFunctor (actFunctor g)
  map_one' := by rw [actFunctor_one]; rfl
  map_mul' g h := by rw [actFunctor_mul]; rfl

/-- **The action of `G` on `ℳ` as a covariant functor.**

`SingleObj G` is the one-object category whose morphisms are the elements of `G`, so this functor
carries exactly the data of the action, and its functor laws are the group-action axioms. -/
def α : SingleObj G ⥤ Cat := SingleObj.functor actHom

@[simp] theorem α_map (g : G) : α.map (SingleObj.toEnd G g) = actHom g := rfl

@[simp] theorem α_map_toFunctor (g : G) :
    (α.map (SingleObj.toEnd G g)).toFunctor = actFunctor g := rfl

/-- `act_identity` for `α`: the group identity maps to the identity functor on `ℳ`. -/
theorem α_map_one : (α.map (SingleObj.toEnd G 1)).toFunctor = 𝟭 M := by
  rw [α_map_toFunctor, actFunctor_one]

/-- `act_compose` for `α`: the action is functorial in the group. -/
theorem α_map_mul (g h : G) :
    (α.map (SingleObj.toEnd G (g * h))).toFunctor = actFunctor h ⋙ actFunctor g := by
  rw [α_map_toFunctor, actFunctor_mul]

/-! ### Orbit data used downstream

The Equivariance Theorem and the Schur's-Lemma parameter count both depend on how `G` moves the
cells, so we record it explicitly. -/

/-- `G` acts transitively on the four context cells. -/
theorem transitive_on_contexts (e f : Finset Meas) (he : e ∈ contexts) (hf : f ∈ contexts) :
    ∃ σ : Equiv.Perm Meas, σ ∈ G ∧ e.image σ = f := by
  revert hf; revert f; revert he; revert e; decide

/-- `G` acts transitively on the four measurement cells. -/
theorem transitive_on_measurements (v w : Meas) :
    ∃ σ : Equiv.Perm Meas, σ ∈ G ∧ σ v = w := by
  revert w; revert v; decide

/-- The stabiliser of a context cell has order 2: having fixed a context, the only remaining
symmetry exchanges the two measurements in it. -/
theorem card_stabilizer_context :
    ((Finset.univ : Finset (Equiv.Perm Meas)).filter fun σ =>
        σ ∈ G ∧ ({Meas.A₀, Meas.B₀} : Finset Meas).image σ = {Meas.A₀, Meas.B₀}).card = 2 := by
  decide

#print axioms image_mem_cells
#print axioms smul_val
#print axioms smul_vertexCell
#print axioms faithful
#print axioms smul_mem_contexts
#print axioms smul_singleton
#print axioms exists_smul_ne
#print axioms monotone_smul
#print axioms actFunctor_obj
#print axioms actFunctor_ext
#print axioms actFunctor_one
#print axioms actFunctor_mul
#print axioms α_map
#print axioms α_map_toFunctor
#print axioms α_map_one
#print axioms α_map_mul
#print axioms transitive_on_contexts
#print axioms transitive_on_measurements
#print axioms card_stabilizer_context

end CHSH
