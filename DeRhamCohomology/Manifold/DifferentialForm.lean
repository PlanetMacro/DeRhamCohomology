import DeRhamCohomology.DifferentialForm
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import DeRhamCohomology.Manifold.VectorBundle.Alternating

open Bundle Set Function Filter
open scoped Topology Manifold ContDiff

noncomputable section

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  (IM : ModelWithCorners ℝ EM HM)
  (M : Type*) [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ⊤ M]
  {m n : ℕ} {k l : ℕ∞}

-- `TangentSpace IM x` is reducibly `EM`. Mathlib intentionally omits the normed-space instances on
-- `TangentSpace` to keep type-class search from guessing them; here we record the ones agreeing with
-- `EM`'s, so the instances inferred for `TangentSpace IM x` coincide with those used by
-- `writtenInExtChartAt`/`iprod`/`wedge_product` (which see the underlying `EM`).
local instance (x : M) : NormedAddCommGroup (TangentSpace IM x) := inferInstanceAs (NormedAddCommGroup EM)
local instance (x : M) : NormedSpace ℝ (TangentSpace IM x) := inferInstanceAs (NormedSpace ℝ EM)

-- Setup for Differential Form Space
notation "Ω^" k "," m "⟮" EM "," IM "," M "⟯" =>
  ContMDiffSection IM (EM [⋀^Fin m]→L[ℝ] ℝ) k
    (Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM : M → Type _) ℝ (Bundle.Trivial M ℝ))

namespace DifferentialForm

section mpullback

variable
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN]
  (IN : ModelWithCorners ℝ EN HN)
  (N : Type*) [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ⊤ N]

variable (α β : (x : N) → TangentSpace IN x [⋀^Fin m]→L[ℝ] Trivial N ℝ x)

/- The pullback of a differential form
Want to keep k-times differentiability away from it. Is this the way? -/
def mpullback (f : M → N) : (x : M) → TangentSpace IM x [⋀^Fin m]→L[ℝ] Trivial N ℝ (f x) :=
    fun x ↦ (α (f x)).compContinuousLinearMap (mfderiv IM IN f x)

theorem mpullback_zero (f : M → N) :
    mpullback IM M IN N (0 : (x : N) → TangentSpace IN x [⋀^Fin m]→L[ℝ] Trivial N ℝ x) f = 0 :=
  rfl

theorem mpullback_add (f : M → N) :
    mpullback IM M IN N (α + β) f = mpullback IM M IN N α f + mpullback IM M IN N β f :=
  rfl

theorem mpullback_sub (f : M → N) :
    mpullback IM M IN N (α - β) f = mpullback IM M IN N α f - mpullback IM M IN N β f :=
  rfl

theorem mpullback_neg (f : M → N) :
    - mpullback IM M IN N α f = mpullback IM M IN N (-α) f :=
  rfl

theorem mpullback_smul (f : M → N) (c : ℝ) :
    c • (mpullback IM M IN N α) f = mpullback IM M IN N (c • α) f :=
  rfl

end mpullback

section miprod

variable
  [ChartedSpace (EM [⋀^Fin (m + 1)]→L[ℝ] ℝ) 𝒜⟮ℝ,Fin (m + 1);EM,TangentSpace IM;ℝ,Trivial M ℝ⟯]

def miprod (α : Ω^k,m + 1⟮EM, IM, M⟯) (V : Π (x : M), TangentSpace IM x) :
    (x : M) → TangentSpace IM x [⋀^Fin m]→L[ℝ] Trivial M ℝ x :=
    fun x => iprod (writtenInExtChartAt IM (𝓘(ℝ, (EM [⋀^Fin (m + 1)]→L[ℝ] ℝ))) x
      (fun y ↦ TotalSpace.mk' (EM [⋀^Fin (m + 1)]→L[ℝ] ℝ) y (α.toFun y)))
        (writtenInExtChartAt IM 𝓘(ℝ, EM) x (fun (x : M) ↦ (V x : TangentSpace IM x)))
          (extChartAt IM x x)

end miprod

section mwedge_product

variable
  [ChartedSpace (EM [⋀^Fin m]→L[ℝ] ℝ) 𝒜⟮ℝ,Fin m;EM,TangentSpace IM;ℝ,Trivial M ℝ⟯] -- Shouldn't this just be true already?
  [ChartedSpace (EM [⋀^Fin n]→L[ℝ] ℝ) 𝒜⟮ℝ,Fin n;EM,TangentSpace IM;ℝ,Trivial M ℝ⟯] -- Shouldn't this just be true already?

/- Place for wedge product definitions -/
def mwedge_product (α : Ω^k,m⟮EM, IM, M⟯) (β : Ω^l,n⟮EM, IM, M⟯) :
    (x : M) → TangentSpace IM x [⋀^Fin (m + n)]→L[ℝ] Trivial M ℝ x :=
    fun x => wedge_product
      (ω₁ := (writtenInExtChartAt IM (𝓘(ℝ, (EM [⋀^Fin m]→L[ℝ] ℝ))) x
        (fun y ↦ TotalSpace.mk' (EM [⋀^Fin m]→L[ℝ] ℝ) y (α.toFun y))))
          (ω₂ := (writtenInExtChartAt IM (𝓘(ℝ, (EM [⋀^Fin n]→L[ℝ] ℝ))) x
            (fun y ↦ TotalSpace.mk' (EM [⋀^Fin n]→L[ℝ] ℝ) y (β.toFun y))))
              (ContinuousLinearMap.mul ℝ ℝ)
                (extChartAt IM x x)

end mwedge_product

section mederiv

variable
  [ChartedSpace (EM [⋀^Fin m]→L[ℝ] ℝ) 𝒜⟮ℝ,Fin m;EM,TangentSpace IM;ℝ,Trivial M ℝ⟯] -- Shouldn't this just be true already?
  (α : Ω^k,m⟮EM, IM, M⟯)

/- Definition of the manifold exterior derivative of differential form within a set -/
def mederivWithin (s : Set M) (x : M) : TangentSpace IM x [⋀^Fin (m + 1)]→L[ℝ] Trivial M ℝ x :=
    (ederivWithin (E := EM) (F := ℝ) (n := m) (writtenInExtChartAt IM (𝓘(ℝ, (EM [⋀^Fin m]→L[ℝ] ℝ))) x
      (fun y ↦ TotalSpace.mk' (EM [⋀^Fin m]→L[ℝ] ℝ) y (α.toFun y)))
        ((extChartAt IM x).symm ⁻¹' s ∩ range IM)) (extChartAt IM x x)

lemma mederivWithin_def (s : Set M) :
    mederivWithin IM M α s = fun x ↦ (ederivWithin (E := EM) (F := ℝ) (n := m)
      (writtenInExtChartAt IM (𝓘(ℝ, (EM [⋀^Fin m]→L[ℝ] ℝ))) x (fun y ↦ TotalSpace.mk' (EM [⋀^Fin m]→L[ℝ] ℝ) y (α.toFun y)))
        ((extChartAt IM x).symm ⁻¹' s ∩ range IM)) (extChartAt IM x x) :=
  rfl

lemma mederivWithin_apply (s : Set M) (x : M) :
    mederivWithin IM M α s x = (ederivWithin (E := EM) (F := ℝ) (n := m)
      (writtenInExtChartAt IM (𝓘(ℝ, (EM [⋀^Fin m]→L[ℝ] ℝ))) x (fun y ↦ TotalSpace.mk' (EM [⋀^Fin m]→L[ℝ] ℝ) y (α.toFun y)))
        ((extChartAt IM x).symm ⁻¹' s ∩ range IM)) (extChartAt IM x x) :=
  rfl

def mederiv (x : M) : TangentSpace IM x [⋀^Fin (m + 1)]→L[ℝ] Trivial M ℝ x :=
    mederivWithin IM M α univ x

lemma mederiv_def : mederiv IM M α = fun x ↦ mederiv IM M α x :=
  rfl

theorem mederivWithin_univ : mederivWithin IM M α univ = mederiv IM M α :=
  rfl

end mederiv
