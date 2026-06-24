import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Alternating.Basic
import Mathlib.Analysis.NormedSpace.Alternating.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.Mul

noncomputable section
suppress_compilation

namespace ContinuousLinearMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {ι : Type*} [Fintype ι]
  {ι' : Type*} [Fintype ι']

def _root_.LinearIsometryEquiv.flipAlternating :
    (M' →L[𝕜] (M [⋀^ι]→L[𝕜] N)) ≃ₗᵢ[𝕜] (M [⋀^ι]→L[𝕜] (M' →L[𝕜] N)) where
  toFun := ContinuousLinearMap.flipAlternating
  invFun g := LinearMap.mkContinuous
    { toFun := fun m' => (ContinuousLinearMap.apply 𝕜 N m').compContinuousAlternatingMap g
      map_add' := fun m₁ m₂ => by ext v; simp
      map_smul' := fun c m => by ext v; simp }
    ‖g‖
    (fun m' => by
      refine (ContinuousLinearMap.norm_compContinuousAlternatingMap_le _ g).trans ?_
      rw [mul_comm ‖g‖]
      gcongr
      exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg m') fun fL => by
        rw [ContinuousLinearMap.apply_apply]; exact (fL.le_opNorm m').trans_eq (mul_comm _ _))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by ext m' v; simp
  right_inv g := by ext v m'; simp
  norm_map' f := by
    show ‖ContinuousLinearMap.flipAlternating f‖ = ‖f‖
    refine le_antisymm ?_ ?_
    · refine ContinuousAlternatingMap.opNorm_le_bound _ (norm_nonneg f) fun v => ?_
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun m' => ?_
      rw [ContinuousLinearMap.flipAlternating_apply_apply]
      calc ‖(f m') v‖ ≤ ‖f m'‖ * ∏ i, ‖v i‖ := (f m').le_opNorm v
        _ ≤ (‖f‖ * ‖m'‖) * ∏ i, ‖v i‖ := by gcongr; exact f.le_opNorm m'
        _ = (‖f‖ * ∏ i, ‖v i‖) * ‖m'‖ := by ring
    · refine ContinuousLinearMap.opNorm_le_bound _
        (norm_nonneg (ContinuousLinearMap.flipAlternating f)) fun m' => ?_
      refine ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun v => ?_
      rw [show (f m') v = (ContinuousLinearMap.flipAlternating f) v m' from
            (ContinuousLinearMap.flipAlternating_apply_apply f v m').symm]
      calc ‖((ContinuousLinearMap.flipAlternating f) v) m'‖
            ≤ ‖(ContinuousLinearMap.flipAlternating f) v‖ * ‖m'‖ :=
              ((ContinuousLinearMap.flipAlternating f) v).le_opNorm m'
        _ ≤ (‖ContinuousLinearMap.flipAlternating f‖ * ∏ i, ‖v i‖) * ‖m'‖ := by
              gcongr; exact (ContinuousLinearMap.flipAlternating f).le_opNorm v
        _ = (‖ContinuousLinearMap.flipAlternating f‖ * ‖m'‖) * ∏ i, ‖v i‖ := by ring

-- TODO work out LinearIsometryEquiv from above to use here
def compContinuousAlternatingMap₂ (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') : M [⋀^ι]→L[𝕜] M' [⋀^ι']→L[𝕜] N'' :=
  (((ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 M' N' N'').flip h).comp
    f).compContinuousAlternatingMap g

theorem compContinuousAlternatingMap₂_apply (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') (m : ι → M) (m': ι' → M') :
    f.compContinuousAlternatingMap₂ g h m m' = f (g m) (h m') :=
  rfl

theorem compContinuousAlternatingMap₂_mul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] 𝕜) (m : ι → M) (m': ι' → M') :
    (ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) * (h m') :=
  rfl

theorem compContinuousAlternatingMap₂_lsmul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] N) (m : ι → M) (m': ι' → M') :
    (ContinuousLinearMap.lsmul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) • (h m') :=
  rfl

end ContinuousLinearMap

namespace ContinuousMultilinearMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {ι : Type*} [Fintype ι]
  {ι' : Type*} [Fintype ι']

def flipAlternating (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ M) (M' [⋀^ι']→L[𝕜] N)) :
    M' [⋀^ι']→L[𝕜] (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ M) N) :=
  AlternatingMap.mkContinuous
    { toFun := fun m =>
        MultilinearMap.mkContinuous
          { toFun := fun m' => f m' m
            map_update_add' := fun m' i x y => by rw [f.map_update_add m' i x y]; rfl
            map_update_smul' := fun m' i c x => by rw [f.map_update_smul m' i c x]; rfl }
          (‖f‖ * ∏ j, ‖m j‖)
          (fun m' => by
            calc ‖f m' m‖ ≤ ‖f m'‖ * ∏ j, ‖m j‖ := (f m').le_opNorm m
              _ ≤ (‖f‖ * ∏ i, ‖m' i‖) * ∏ j, ‖m j‖ := by gcongr; exact f.le_opNorm m'
              _ = (‖f‖ * ∏ j, ‖m j‖) * ∏ i, ‖m' i‖ := by ring)
      map_update_add' := fun m i x y => by ext m'; simp [(f m').map_update_add]
      map_update_smul' := fun m i c x => by ext m'; simp [(f m').map_update_smul]
      map_eq_zero_of_eq' := fun m i j h hij => by
        ext m'; simp [(f m').map_eq_zero_of_eq m h hij] }
    ‖f‖
    (fun m => ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m'' => by
      calc ‖f m'' m‖ ≤ ‖f m''‖ * ∏ j, ‖m j‖ := (f m'').le_opNorm m
        _ ≤ (‖f‖ * ∏ i, ‖m'' i‖) * ∏ j, ‖m j‖ := by gcongr; exact f.le_opNorm m''
        _ = (‖f‖ * ∏ j, ‖m j‖) * ∏ i, ‖m'' i‖ := by ring)

theorem flipAlternating_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ M) (M' [⋀^ι']→L[𝕜] N))
    (m : ι → M) (m' : ι' → M') : flipAlternating f m' m = f m m' :=
  rfl

end ContinuousMultilinearMap

namespace ContinuousAlternatingMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {ι ι' : Type*}

/-- This is the alternating version of `ContinuousMultilinearMap.domDomCongr`. -/
def domDomCongr (σ : ι ≃ ι') (f : M [⋀^ι]→L[𝕜] N) : M [⋀^ι']→L[𝕜] N :=
  { f.toContinuousMultilinearMap.domDomCongr σ with
    toFun := fun v => f (v ∘ σ)
    map_eq_zero_of_eq' := fun v i j hv hij =>
      f.map_eq_zero_of_eq (v ∘ σ) (i := σ.symm i) (j := σ.symm j)
        (by simpa using hv) (σ.symm.injective.ne hij) }

@[simp]
theorem domDomCongr_apply (σ : ι ≃ ι') (f : M [⋀^ι]→L[𝕜] N) (v : ι' → M) :
    (domDomCongr σ f) v = f (v ∘ σ) :=
  rfl

@[simp]
theorem domDomCongr_refl (f : M [⋀^ι]→L[𝕜] N) :
    domDomCongr (Equiv.refl ι) f = f :=
  rfl

variable
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  [Fintype ι] [Fintype ι']

def flipAlternating (f : M [⋀^ι]→L[𝕜] (M' [⋀^ι']→L[𝕜] N)) :
    M' [⋀^ι']→L[𝕜] M [⋀^ι]→L[𝕜] N :=
  AlternatingMap.mkContinuous
    { toFun := fun m =>
        AlternatingMap.mkContinuous
          { toFun := fun m' => f m' m
            map_update_add' := fun m' i x y => by rw [f.map_update_add m' i x y]; rfl
            map_update_smul' := fun m' i c x => by rw [f.map_update_smul m' i c x]; rfl
            map_eq_zero_of_eq' := fun m' i j h hij => by rw [f.map_eq_zero_of_eq m' h hij]; rfl }
          (‖f‖ * ∏ j, ‖m j‖)
          (fun m' => by
            calc ‖f m' m‖ ≤ ‖f m'‖ * ∏ j, ‖m j‖ := (f m').le_opNorm m
              _ ≤ (‖f‖ * ∏ i, ‖m' i‖) * ∏ j, ‖m j‖ := by gcongr; exact f.le_opNorm m'
              _ = (‖f‖ * ∏ j, ‖m j‖) * ∏ i, ‖m' i‖ := by ring)
      map_update_add' := fun m i x y => by ext m'; simp [(f m').map_update_add]
      map_update_smul' := fun m i c x => by ext m'; simp [(f m').map_update_smul]
      map_eq_zero_of_eq' := fun m i j h hij => by
        ext m'; simp [(f m').map_eq_zero_of_eq m h hij] }
    ‖f‖
    (fun m => ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun m'' => by
      calc ‖f m'' m‖ ≤ ‖f m''‖ * ∏ j, ‖m j‖ := (f m'').le_opNorm m
        _ ≤ (‖f‖ * ∏ i, ‖m'' i‖) * ∏ j, ‖m j‖ := by gcongr; exact f.le_opNorm m''
        _ = (‖f‖ * ∏ j, ‖m j‖) * ∏ i, ‖m'' i‖ := by ring)

theorem flipAlternating_apply (f : M [⋀^ι]→L[𝕜] (M' [⋀^ι']→L[𝕜] N))
    (m : ι → M) (m' : ι' → M') : flipAlternating f m' m = f m m' :=
  rfl
