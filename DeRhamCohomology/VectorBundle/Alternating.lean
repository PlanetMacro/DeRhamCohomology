/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/

import Mathlib.Analysis.NormedSpace.Alternating.Basic
import Mathlib.Topology.VectorBundle.Basic

/-!
# The vector bundle of continuous alternating maps

We define the (topological) vector bundle of continuous alternating maps between two vector bundles
over the same base.

Given bundles `E₁ E₂ : B → Type*`, and normed spaces `F₁` and `F₂`, we define
`⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯` (notation for `Bundle.continuousAlternatingMap 𝕜 ι F₁ E₁ F₂ E₂ x`) to be
a type synonym for `fun x ↦ ⋀^ι⟮𝕜; E₁ x; E₂ x⟯`, the sigma-type of continuous alternating maps
fibrewise from `E₁ x` to `E₂ x`. If the `E₁` and `E₂` are vector bundles with model fibers `F₁` and
`F₂`, then this will be a vector bundle with model fiber `F₁ [⋀^ι]→L[𝕜] F₂`.

The topology is constructed from the trivializations for `E₁` and `E₂` and the norm-topology on the
model fiber `F₁ [⋀^ι]→L[𝕜] F₂` using the `vector_prebundle` construction.  This
is a bit awkward because it introduces a spurious (?) dependence on the normed space structure of
the model fiber.

Similar constructions should be possible (but are yet to be formalized) for bundles of continuous
symmetric maps, multilinear maps in general, and so on, where again the topology can be defined
using a norm on the fiber model if this helps.

## Main Definitions

* `Bundle.continuousAlternatingMap.vectorBundle`: continuous alternating maps between
  vector bundles form a vector bundle.  (FIXME Notation `⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯`.)

## Implementation notes

The development of the alternating bundle here is unsatisfactory because it is linear rather than
semilinear, so e.g. the bundle of alternating conjugate-linear maps, needed for Dolbeault
cohomology, is not constructed.

The wider development of linear-algebraic constructions on vector bundles (the hom-bundle, the
alternating-maps bundle, the direct-sum bundle, possibly in the future the bundles of multilinear
and symmetric maps) is also unsatisfactory, in that it proceeds construction by construction rather
than according to some generalization which works for all of them. But it is not clear what a
suitable generalization would be which also covers the semilinear case, as well as other important
cases such as fractional powers of line bundles (needed for the density bundle).
-/

noncomputable section

open Bundle Set ContinuousAlternatingMap

section defs
variable (𝕜 : Type*) [CommSemiring 𝕜] [TopologicalSpace 𝕜] (ι : Type*)
variable {B : Type*}

/- The bundle of continuous `ι`-slot alternating maps between the topological vector bundles `E₁`
and `E₂`. This is a type synonym for `⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯`.
We intentionally add `F₁` and `F₂` as arguments to this type, so that instances on this type
(that depend on `F₁` and `F₂`) actually refer to `F₁` and `F₂`. -/
@[nolint unusedArguments]
protected def Bundle.continuousAlternatingMap (F₁ : Type*) (E₁ : B → Type*)
    [Π x, AddCommMonoid (E₁ x)] [Π x, Module 𝕜 (E₁ x)] [Π x, TopologicalSpace (E₁ x)]
    (F₂ : Type*) (E₂ : B → Type*) [Π x, AddCommMonoid (E₂ x)] [Π x, Module 𝕜 (E₂ x)]
    [Π x, TopologicalSpace (E₂ x)] (x : B) : Type _ :=
  (E₁ x) [⋀^ι]→L[𝕜] (E₂ x)
-- deriving Inhabited FIXME

-- FIXME, notation more consistent with `F₁ [⋀^ι]→L[𝕜] F₂`?
notation3 "⋀^" ι "⟮" 𝕜 "; " F₁ ", " E₁ "; " F₂ ", " E₂ "⟯" => Bundle.continuousAlternatingMap 𝕜 ι F₁ E₁ F₂ E₂

variable (F₁ : Type*) (E₁ : B → Type*) [Π x, AddCommMonoid (E₁ x)] [Π x, Module 𝕜 (E₁ x)]
variable [Π x, TopologicalSpace (E₁ x)]
variable (F₂ : Type*) (E₂ : B → Type*) [Π x, AddCommMonoid (E₂ x)] [Π x, Module 𝕜 (E₂ x)]
variable [Π x, TopologicalSpace (E₂ x)]

variable [Π x, ContinuousAdd (E₂ x)]

instance (x : B) : AddCommMonoid (⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯ x) := by
  -- was `delta_instance bundle.continuousAlternatingMap`, FIXME
  dsimp [Bundle.continuousAlternatingMap]
  infer_instance

variable [∀ x, ContinuousSMul 𝕜 (E₂ x)]

instance (x : B) : Module 𝕜 (⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯ x) := by
  -- was delta_instance `Bundle.continuousAlternatingMap`, FIXME
  dsimp [Bundle.continuousAlternatingMap]
  infer_instance

end defs

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] (ι : Type*) [Fintype ι]

variable {B : Type*} [TopologicalSpace B]

variable (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  (E₁ : B → Type*) [Π x, AddCommMonoid (E₁ x)] [Π x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]
variable (F₂ : Type*) [NormedAddCommGroup F₂][NormedSpace 𝕜 F₂]
  (E₂ : B → Type*) [Π x, AddCommMonoid (E₂ x)] [Π x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]

variable {F₁ E₁ F₂ E₂}
variable (e₁ e₁' : Trivialization F₁ (π F₁ E₁)) (e₂ e₂' : Trivialization F₂ (π F₂ E₂))


namespace Pretrivialization

/-- Assume `eᵢ` and `eᵢ'` are trivializations of the bundles `Eᵢ` over base `B` with fiber `Fᵢ`
(`i ∈ {1,2}`), then `continuousAlternatingMapCoordChange σ e₁ e₁' e₂ e₂'` is the coordinate
change function between the two induced (pre)trivializations
`Pretrivialization.continuousAlternatingMap σ e₁ e₂` and
`Pretrivialization.continuousAlternatingMap σ e₁' e₂'` of `Bundle.ContinuousAlternatingMap`. -/
def continuousAlternatingMapCoordChange
    [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜] (b : B) :
    (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂) :=
  ((e₁'.coordChangeL 𝕜 e₁ b).symm.continuousAlternatingMapCongr (e₂.coordChangeL 𝕜 e₂' b) :
    (F₁ [⋀^ι]→L[𝕜] F₂) ≃L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))

variable {e₁ e₁' e₂ e₂'}
variable [Π x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁]
variable [Π x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]

section
variable (F₁ F₂)
variable [ContinuousSMul 𝕜 F₁] [ContinuousAdd F₁]

-- move this to `operator_norm`
/-- A linear isometry from a normed space `F` to a normed space `G` induces (by left-composition) a
linear isometry from operators into `F` to operators into `G`. -/
def _root_.LinearIsometry.compLeft {𝕜 : Type*} {𝕜₂ : Type*}
    {𝕜₃ : Type*} (E : Type*) {F : Type*} {G : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup G] [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃] [NormedSpace 𝕜 E]
    [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] (σ₁₂ : 𝕜 →+* 𝕜₂) {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃]
    [RingHomIsometric σ₁₃] (f : F →ₛₗᵢ[σ₂₃] G) :
    (E →SL[σ₁₂] F) →ₛₗᵢ[σ₂₃] (E →SL[σ₁₃] G) :=
  { ContinuousLinearMap.compSL _ _ _ _ _ f.toContinuousLinearMap with
    norm_map' := fun _ ↦ f.norm_toContinuousLinearMap_comp }

-- move this to `ContinuousMultilinearMap`
theorem _root_.ContinuousMultilinearMap.compContinuousLinearMapL_diag_continuous :
  Continuous (fun p : F₁ →L[𝕜] F₁ ↦
  (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : ι ↦ p) :
    ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂ →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂)) := by
  let φ : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁ →L[𝕜] F₁) _ :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : ι ↦ F₁) (fun _ : ι ↦ F₁) F₂
  show Continuous (fun p : F₁ →L[𝕜] F₁ ↦ φ (fun _ : ι ↦ p))
  apply Continuous.comp
  · apply ContinuousMultilinearMap.cont
  · apply continuous_pi
    intro _
    exact continuous_id

-- move this to `ContinuousAlternatingMap`
theorem _root_.ContinuousAlternatingMap.compContinuousLinearMapL_continuous :
    Continuous (fun p : F₁ →L[𝕜] F₁ ↦
    (ContinuousAlternatingMap.compContinuousLinearMapCLM p :
    (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) := by
  -- Composition with inclusion into multilinear maps
  let φ : (F₁ [⋀^ι]→L[𝕜] F₂) →ₗᵢ[𝕜] _ := toContinuousMultilinearMapLI
  let Φ : ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)) →ₗᵢ[𝕜] _ := φ.compLeft _ (RingHom.id _)
  rw [← Φ.comp_continuous_iff]
  -- Rewrite goal to using linear maps
  show Continuous (fun p : F₁ →L[𝕜] F₁ ↦
    (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ ↦ p) :
    ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂ →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂).comp
    (toContinuousMultilinearMapCLM 𝕜))
  -- Prove multilinear version of goal
  exact (ContinuousMultilinearMap.compContinuousLinearMapL_diag_continuous 𝕜 ι F₁ F₂).clm_comp
    continuous_const

end

theorem continuousOn_continuousAlternatingMapCoordChange
    [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
  ContinuousOn (continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂')
    ((e₁.baseSet ∩ e₂.baseSet) ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  have h₃ := (continuousOn_coordChange 𝕜 e₁' e₁)
  have h₄ := (continuousOn_coordChange 𝕜 e₂ e₂')
  let s (q : (F₁ →L[𝕜] F₁) × (F₂ →L[𝕜] F₂)) :
      (F₁ →L[𝕜] F₁) × ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)) :=
    (q.1, ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 F₁ F₂ F₂ q.2)
  have hs : Continuous s :=
    continuous_id.prodMap
      (ContinuousLinearMap.continuous (ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 F₁ F₂ F₂))
  -- note: the following `refine` worked in Lean 3; in Lean 4 this times out so has been replaced by
  -- the `have`/`exact` pair with an explicitly-provided `s` argument
  -- refine ((continuous_snd.clm_comp
  --   ((ContinuousAlternatingMap.compContinuousLinearMapL_continuous 𝕜 ι F₁ F₂).comp
  --   continuous_fst)).comp hs).comp_continuousOn ((h₃.mono ?_).prod (h₄.mono ?_))
  have' := ((continuous_snd.clm_comp
    ((ContinuousAlternatingMap.compContinuousLinearMapL_continuous 𝕜 ι F₁ F₂).comp
    continuous_fst)).comp hs).comp_continuousOn
    (s := (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet))) ((h₃.mono ?_).prod (h₄.mono ?_))
  · exact this
  · mfld_set_tac
  · mfld_set_tac

variable (e₁ e₁' e₂ e₂')
variable [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜]

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`,
`Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂` is the induced pretrivialization for the
continuous `ι`-slot alternating maps from `E₁` to `E₂`. That is, the map which will later become a
trivialization, after the bundle of continuous alternating maps is equipped with the right
topological vector bundle structure. -/
def continuousAlternatingMap : Pretrivialization (F₁ [⋀^ι]→L[𝕜] F₂)
    (π (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯) where
  toFun p := ⟨p.1, (e₂.continuousLinearMapAt 𝕜 p.1).compContinuousAlternatingMap <|
      p.2.compContinuousLinearMap <| e₁.symmL 𝕜 p.1⟩
  invFun p := ⟨p.1, (e₂.symmL 𝕜 p.1).compContinuousAlternatingMap <|
      p.2.compContinuousLinearMap <| e₁.continuousLinearMapAt 𝕜 p.1⟩
  source := (Bundle.TotalSpace.proj) ⁻¹' (e₁.baseSet ∩ e₂.baseSet)
  target := (e₁.baseSet ∩ e₂.baseSet) ×ˢ Set.univ
  map_source' _ h := ⟨h, Set.mem_univ _⟩
  map_target' _ h := h.1
  left_inv' := fun ⟨x, L⟩ ⟨h₁, h₂⟩ ↦ by
    rw [TotalSpace.mk_inj]
    dsimp [Bundle.continuousAlternatingMap]
    ext v
    refine (e₂.symmₗ_linearMapAt h₂ _).trans ?_
    dsimp
    congr
    ext i
    exact e₁.symmₗ_linearMapAt h₁ _
  right_inv' := fun ⟨x, f⟩ ⟨⟨h₁, h₂⟩, _⟩ ↦ by
    ext v
    dsimp
    refine (e₂.linearMapAt_symmₗ h₂ _).trans ?_
    dsimp
    congr
    ext i
    exact e₁.linearMapAt_symmₗ h₁ _
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).prod isOpen_univ
  baseSet := e₁.baseSet ∩ e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

instance continuousAlternatingMap.isLinear
    [Π x, ContinuousAdd (E₂ x)] [Π x, ContinuousSMul 𝕜 (E₂ x)] :
    (Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂).IsLinear 𝕜 where
  linear x _ :=
  { map_add := fun L L' ↦ by
      show ContinuousLinearMap.compContinuousAlternatingMapₗ 𝕜 _ _ _
        (e₂.continuousLinearMapAt 𝕜 x)
        (ContinuousAlternatingMap.compContinuousLinearMapₗ (e₁.symmL 𝕜 x) (L + L')) = _
      rw [_root_.map_add, _root_.map_add]
      rfl
    map_smul := fun c L ↦ by
      show ContinuousLinearMap.compContinuousAlternatingMapₗ 𝕜 _ _ _
        (e₂.continuousLinearMapAt 𝕜 x)
        (ContinuousAlternatingMap.compContinuousLinearMapₗ (e₁.symmL 𝕜 x) (c • L)) = _
      rw [map_smul, map_smul]
      rfl }

theorem continuousAlternatingMap_apply (p : TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯)) :
    (continuousAlternatingMap 𝕜 ι e₁ e₂) p =
    ⟨p.1, (e₂.continuousLinearMapAt 𝕜 p.1).compContinuousAlternatingMap <|
        p.2.compContinuousLinearMap <| e₁.symmL 𝕜 p.1⟩ :=
  rfl

theorem continuousAlternatingMap_symm_apply (p : B × (F₁ [⋀^ι]→L[𝕜] F₂)) :
    (continuousAlternatingMap 𝕜 ι e₁ e₂).toPartialEquiv.symm p =
    ⟨p.1, (e₂.symmL 𝕜 p.1).compContinuousAlternatingMap <|
      p.2.compContinuousLinearMap <| e₁.continuousLinearMapAt 𝕜 p.1⟩ :=
  rfl

@[simp] theorem baseSet_continuousAlternatingMap :
    (Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂).baseSet = e₁.baseSet ∩ e₂.baseSet :=
  rfl

variable [Π x, ContinuousAdd (E₂ x)]

theorem continuousAlternatingMap_symm_apply' {b : B} (hb : b ∈ e₁.baseSet ∩ e₂.baseSet)
    (L : (F₁ [⋀^ι]→L[𝕜] F₂)) :
    (continuousAlternatingMap 𝕜 ι e₁ e₂).symm b L =
    (e₂.symmL 𝕜 b).compContinuousAlternatingMap
    (L.compContinuousLinearMap <| e₁.continuousLinearMapAt 𝕜 b) := by
  rw [symm_apply]
  · rfl
  exact hb

theorem continuousAlternatingMapCoordChange_apply (b : B)
  (hb : b ∈ (e₁.baseSet ∩ e₂.baseSet) ∩ (e₁'.baseSet ∩ e₂'.baseSet)) (L : F₁ [⋀^ι]→L[𝕜] F₂) :
  continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂' b L =
  (continuousAlternatingMap 𝕜 ι e₁' e₂'
    (TotalSpace.mk b ((continuousAlternatingMap 𝕜 ι e₁ e₂).symm b L))).2 := by
  ext v
  have H : e₁'.coordChangeL 𝕜 e₁ b ∘ v = e₁.linearMapAt 𝕜 b ∘ e₁'.symm b ∘ v := by
    ext i
    dsimp
    rw [e₁'.coordChangeL_apply e₁ ⟨hb.2.1, hb.1.1⟩, e₁.coe_linearMapAt_of_mem hb.1.1]
  simp [Pretrivialization.continuousAlternatingMap_apply, continuousAlternatingMapCoordChange,
    Pretrivialization.continuousAlternatingMap_symm_apply' _ _ _ _ hb.1,
    e₂.coordChangeL_apply e₂' ⟨hb.1.2, hb.2.2⟩, H]
  rw [e₂'.coe_linearMapAt_of_mem hb.2.2]

  -- FIXME this could ideally be combined with the previous simp

end Pretrivialization

open Pretrivialization
variable (F₁ E₁ F₂ E₂)
variable [Π x : B, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
variable [Π x : B, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- Topology on the continuous `ι`-slot alternating_maps between the respective fibers at a point of
two "normable" vector bundles over the same base. Here "normable" means that the bundles have fibers
modelled on normed spaces `F₁`, `F₂` respectively.  The topology we put on the continuous `ι`-slot
alternating_maps is the topology coming from the norm on alternating maps from `F₁` to `F₂`. -/
instance (x : B) : TopologicalSpace (⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯ x) :=
  TopologicalSpace.induced
    ((Pretrivialization.continuousAlternatingMap 𝕜 ι
      (trivializationAt F₁ E₁ x) (trivializationAt F₂ E₂ x)) ∘ TotalSpace.mk' (F₁ [⋀^ι]→L[𝕜] F₂) x)
    inferInstance

variable [Π x, ContinuousAdd (E₂ x)] [Π x, ContinuousSMul 𝕜 (E₂ x)]

/-- The continuous `ι`-slot alternating maps between two topological vector bundles form a
`VectorPrebundle` (this is an auxiliary construction for the
`VectorBundle` instance, in which the pretrivializations are collated but no topology
on the total space is yet provided). -/
def _root_.Bundle.continuousAlternatingMap.vectorPrebundle :
    VectorPrebundle 𝕜 (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯ where
  pretrivializationAtlas :=
    {e |  ∃ (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
      e = Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂}
  pretrivialization_linear' := by
    rintro _ ⟨e₁, he₁, e₂, he₂, rfl⟩
    infer_instance
  pretrivializationAt x := Pretrivialization.continuousAlternatingMap 𝕜 ι
    (trivializationAt F₁ E₁ x) (trivializationAt F₂ E₂ x)
  mem_base_pretrivializationAt x :=
    ⟨mem_baseSet_trivializationAt F₁ E₁ x, mem_baseSet_trivializationAt F₂ E₂ x⟩
  pretrivialization_mem_atlas x :=
    ⟨trivializationAt F₁ E₁ x, trivializationAt F₂ E₂ x, inferInstance, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂',
      continuousOn_continuousAlternatingMapCoordChange 𝕜 ι,
      continuousAlternatingMapCoordChange_apply 𝕜 ι e₁ e₁' e₂ e₂'⟩
  totalSpaceMk_isInducing x := ⟨rfl⟩

/-- Topology on the total space of the continuous `ι`-slot alternating maps between two "normable"
vector bundles over the same base. -/
instance Bundle.continuousAlternatingMap.topologicalSpace_totalSpace :
    TopologicalSpace (TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯) :=
  (Bundle.continuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).totalSpaceTopology

/-- The continuous `ι`-slot alternating maps between two vector bundles form a fiber bundle. -/
instance _root_.Bundle.continuousAlternatingMap.fiberBundle :
    FiberBundle (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯ :=
  (Bundle.continuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).toFiberBundle

/-- The continuous `ι`-slot alternating maps between two vector bundles form a vector bundle. -/
instance _root_.Bundle.continuousAlternatingMap.vectorBundle :
    VectorBundle 𝕜 (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯ :=
  (Bundle.continuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).toVectorBundle

variable [he₁ : MemTrivializationAtlas e₁] [he₂ : MemTrivializationAtlas e₂] {F₁ E₁ F₂ E₂}

/-- Given trivializations `e₁`, `e₂` in the atlas for vector bundles `E₁`, `E₂` over a base `B`,
the induced trivialization for the continuous `ι`-slot alternating maps from `E₁` to `E₂`,
whose base set is `e₁.baseSet ∩ e₂.baseSet`. -/
def Trivialization.continuousAlternatingMap :
    Trivialization (F₁ [⋀^ι]→L[𝕜] F₂) (π (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯) :=
  VectorPrebundle.trivializationOfMemPretrivializationAtlas _ ⟨e₁, e₂, he₁, he₂, rfl⟩

instance _root_.Bundle.continuousAlternatingMap.memTrivializationAtlas :
    MemTrivializationAtlas (e₁.continuousAlternatingMap 𝕜 ι e₂ :
    Trivialization (F₁ [⋀^ι]→L[𝕜] F₂) (π (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯)) where
  out := ⟨_, ⟨e₁, e₂, inferInstance, inferInstance, rfl⟩, rfl⟩

@[simp] theorem Trivialization.baseSet_continuousAlternatingMap :
    (e₁.continuousAlternatingMap 𝕜 ι e₂).baseSet = e₁.baseSet ∩ e₂.baseSet :=
  rfl

theorem Trivialization.continuousAlternatingMap_apply
    (p : TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯) :
    e₁.continuousAlternatingMap 𝕜 ι e₂ p =
    ⟨p.1, (e₂.continuousLinearMapAt 𝕜 p.1).compContinuousAlternatingMap <|
      p.2.compContinuousLinearMap <| e₁.symmL 𝕜 p.1⟩ :=
  rfl

@[simp, mfld_simps]
theorem continuousAlternatingMap_trivializationAt_source (x₀ : B) :
    (trivializationAt (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯ x₀).source =
    π (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯ ⁻¹'
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

@[simp, mfld_simps]
theorem continuousAlternatingMap_trivializationAt_target (x₀ : B) :
    (trivializationAt (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯ x₀).target =
    ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) ×ˢ Set.univ :=
  rfl
