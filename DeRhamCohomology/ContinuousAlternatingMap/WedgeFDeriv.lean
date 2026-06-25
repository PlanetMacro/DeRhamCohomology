import Mathlib.Analysis.Calculus.FDeriv.Mul
import DeRhamCohomology.ContinuousAlternatingMap.Wedge
import DeRhamCohomology.ContinuousAlternatingMap.FDeriv

/-!
# The wedge product as a bounded bilinear map and the Leibniz rule

This file bundles `ContinuousAlternatingMap.wedge_product g h f` (with the bilinear pairing `f`
fixed) as a continuous bilinear map `wedgeCLM f`, and uses it to differentiate
`x ↦ wedge_product (ω x) (τ x) f`.

It also proves the two algebraic "commutation" lemmas relating `uncurryFin` (the building block of
the exterior derivative) to the wedge product, which are the combinatorial core of the graded
Leibniz rule `ederiv_wedge`.
-/

noncomputable section
suppress_compilation

namespace ContinuousAlternatingMap

open scoped BigOperators

section bundle

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {m n : ℕ}

/-- The wedge product is linear in its left argument. -/
theorem smul_wedge_left (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') (c : 𝕜) :
    (wedge_product (c • g) h f) = c • (wedge_product g h f) := by
  ext x
  rw [smul_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  rw [uncurrySum.summand_mk, uncurrySum.summand_mk]
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply,
    ContinuousMultilinearMap.flipMultilinear_apply, coe_toContinuousMultilinearMap,
    ContinuousMultilinearMap.flipAlternating_apply,
    ContinuousLinearMap.compContinuousAlternatingMap₂_apply, smul_apply, map_smul,
    ContinuousLinearMap.smul_apply]
  rw [smul_comm]

/-- The wedge product is linear in its right argument. -/
theorem smul_wedge_right (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') (c : 𝕜) :
    (wedge_product g (c • h) f) = c • (wedge_product g h f) := by
  ext x
  rw [smul_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  rw [uncurrySum.summand_mk, uncurrySum.summand_mk]
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply,
    ContinuousMultilinearMap.flipMultilinear_apply, coe_toContinuousMultilinearMap,
    ContinuousMultilinearMap.flipAlternating_apply,
    ContinuousLinearMap.compContinuousAlternatingMap₂_apply, smul_apply, map_smul,
    ContinuousLinearMap.smul_apply]
  rw [smul_comm]

/-- Norm bound on a single summand of the (shuffle expansion of the) wedge product. -/
theorem norm_summand_compContinuousAlternatingMap₂_le
    (f : N →L[𝕜] N' →L[𝕜] N'') (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (σ : Equiv.Perm.ModSumCongr (Fin m) (Fin n)) (z : Fin (m + n) → M) :
    ‖uncurrySum.summand (f.compContinuousAlternatingMap₂ g h) σ (z ∘ finSumFinEquiv)‖
      ≤ ‖f‖ * ‖g‖ * ‖h‖ * ∏ k, ‖z k‖ := by
  induction σ using Quotient.inductionOn' with
  | _ σ₁ =>
    rw [uncurrySum.summand_mk'']
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
      Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply,
      ContinuousMultilinearMap.flipMultilinear_apply, coe_toContinuousMultilinearMap,
      ContinuousMultilinearMap.flipAlternating_apply,
      ContinuousLinearMap.compContinuousAlternatingMap₂_apply, norm_units_zsmul]
    refine (f.le_opNorm₂ _ _).trans ?_
    calc ‖f‖ * ‖g (fun i => z (finSumFinEquiv (σ₁ (Sum.inl i))))‖
            * ‖h (fun j => z (finSumFinEquiv (σ₁ (Sum.inr j))))‖
        ≤ ‖f‖ * (‖g‖ * ∏ i, ‖z (finSumFinEquiv (σ₁ (Sum.inl i)))‖)
            * (‖h‖ * ∏ j, ‖z (finSumFinEquiv (σ₁ (Sum.inr j)))‖) := by
          gcongr <;> [exact g.le_opNorm _; exact h.le_opNorm _]
      _ = ‖f‖ * ‖g‖ * ‖h‖
            * ((∏ i, ‖z (finSumFinEquiv (σ₁ (Sum.inl i)))‖)
              * ∏ j, ‖z (finSumFinEquiv (σ₁ (Sum.inr j)))‖) := by ring
      _ = ‖f‖ * ‖g‖ * ‖h‖ * ∏ k, ‖z k‖ := by
          congr 1
          rw [← Fintype.prod_sum_type fun s => ‖z (finSumFinEquiv (σ₁ s))‖,
              Equiv.prod_comp σ₁ fun s => ‖z (finSumFinEquiv s)‖,
              Equiv.prod_comp finSumFinEquiv fun k => ‖z k‖]

/-- The operator-norm bound on the wedge product, used to bundle it as a continuous bilinear map. -/
theorem norm_wedge_le (f : N →L[𝕜] N' →L[𝕜] N'') (g : M [⋀^Fin m]→L[𝕜] N)
    (h : M [⋀^Fin n]→L[𝕜] N') :
    ‖wedge_product g h f‖
      ≤ (Fintype.card (Equiv.Perm.ModSumCongr (Fin m) (Fin n)) : ℝ) * ‖f‖ * ‖g‖ * ‖h‖ := by
  refine opNorm_le_bound _ (by positivity) fun z => ?_
  rw [wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ σ : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
          ‖uncurrySum.summand (f.compContinuousAlternatingMap₂ g h) σ (z ∘ finSumFinEquiv)‖
      ≤ ∑ _σ : Equiv.Perm.ModSumCongr (Fin m) (Fin n), ‖f‖ * ‖g‖ * ‖h‖ * ∏ k, ‖z k‖ :=
        Finset.sum_le_sum fun σ _ =>
          norm_summand_compContinuousAlternatingMap₂_le f g h σ z
    _ = (Fintype.card (Equiv.Perm.ModSumCongr (Fin m) (Fin n)) : ℝ) * ‖f‖ * ‖g‖ * ‖h‖
          * ∏ k, ‖z k‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- The wedge product with respect to a fixed pairing `f`, bundled as a continuous bilinear map. -/
def wedgeCLM (f : N →L[𝕜] N' →L[𝕜] N'') :
    (M [⋀^Fin m]→L[𝕜] N) →L[𝕜] (M [⋀^Fin n]→L[𝕜] N') →L[𝕜] (M [⋀^Fin (m + n)]→L[𝕜] N'') :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜 (fun g h => wedge_product g h f)
      (fun g₁ g₂ h => add_wedge g₁ g₂ h f)
      (fun c g h => smul_wedge_left g h f c)
      (fun g h₁ h₂ => wedge_add g h₁ h₂ f)
      (fun c g h => smul_wedge_right g h f c))
    (Fintype.card (Equiv.Perm.ModSumCongr (Fin m) (Fin n)) * ‖f‖)
    fun g h => by
      rw [mul_assoc, mul_assoc]
      simpa only [mul_assoc] using norm_wedge_le f g h

@[simp]
theorem wedgeCLM_apply (f : N →L[𝕜] N' →L[𝕜] N'') (g : M [⋀^Fin m]→L[𝕜] N)
    (h : M [⋀^Fin n]→L[𝕜] N') :
    ((wedgeCLM f : (M [⋀^Fin m]→L[𝕜] N) →L[𝕜] (M [⋀^Fin n]→L[𝕜] N') →L[𝕜]
      M [⋀^Fin (m + n)]→L[𝕜] N'') g) h = wedge_product g h f :=
  rfl

end bundle

section fderiv

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {m n : ℕ}

/-- The Leibniz rule for the Fréchet derivative of a wedge product of (alternating-map valued)
functions: differentiating `x ↦ wedge_product (ω x) (τ x) f` follows the product rule of the
bounded bilinear map `wedgeCLM f`. The two summands are written via `precompR`/`precompL`, which
postcompose the bilinear map with the derivatives.

We go through `ContinuousLinearMap.fderiv_of_bilinear`, which differentiates the
`ContinuousAlternatingMap`-valued map `p ↦ wedgeCLM f p.1 p.2`; this avoids the normed-instance
diamond that arises when differentiating a `ContinuousLinearMap`-valued (curried) function. -/
theorem fderiv_wedge (f : N →L[𝕜] N' →L[𝕜] N'')
    {ω : E → M [⋀^Fin m]→L[𝕜] N} {τ : E → M [⋀^Fin n]→L[𝕜] N'} {x : E}
    (hω : DifferentiableAt 𝕜 ω x) (hτ : DifferentiableAt 𝕜 τ x) :
    fderiv 𝕜 (fun y => wedge_product (ω y) (τ y) f) x =
      (wedgeCLM (M := M) (m := m) (n := n) f).precompR E (ω x) (fderiv 𝕜 τ x)
        + (wedgeCLM (M := M) (m := m) (n := n) f).precompL E (fderiv 𝕜 ω x) (τ x) := by
  have h := (wedgeCLM (M := M) (m := m) (n := n) f).fderiv_of_bilinear
    (f := ω) (g := τ) hω hτ
  simpa only [wedgeCLM_apply] using h

end fderiv

section commute

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {m n : ℕ}

/-- `uncurryFin` (prepending a derivative slot) commutes with post-composition by a fixed
continuous linear map `L`. This is the quotient-free part of the wedge/uncurry interaction. -/
theorem uncurryFin_compContinuousAlternatingMapCLM (L : N →L[𝕜] G)
    (A : E →L[𝕜] (E [⋀^Fin m]→L[𝕜] N)) :
    uncurryFin ((ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E N G L).comp A) =
      L.compContinuousAlternatingMap (uncurryFin A) := by
  ext w
  simp only [uncurryFin_apply, ContinuousLinearMap.compContinuousAlternatingMap_coe,
    Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compContinuousAlternatingMapCLM_apply_apply]
  exact ((_root_.map_sum L _ _).trans
    (Finset.sum_congr rfl fun k _ => _root_.map_zsmul L _ _)).symm

/-- The wedge product, evaluated, as the shuffle sum over `ModSumCongr`. -/
theorem wedge_product_apply_sum (g : E [⋀^Fin m]→L[𝕜] N) (h : E [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') (w : Fin (m + n) → E) :
    wedge_product g h f w = ∑ σ : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
      uncurrySum.summand (f.compContinuousAlternatingMap₂ g h) σ (w ∘ finSumFinEquiv) := by
  rw [wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply]

/-- `compContinuousAlternatingMap₂ f g h` is post-composition of `g` by the fixed continuous
linear map `((compContinuousAlternatingMapCLM 𝕜 E N' N'').flip h).comp f`. This is definitional,
and it lets us feed `compContinuousAlternatingMap₂` to
`uncurryFin_compContinuousAlternatingMapCLM`. -/
theorem compContinuousAlternatingMap₂_eq_comp (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : E [⋀^Fin m]→L[𝕜] N) (h : E [⋀^Fin n]→L[𝕜] N') :
    f.compContinuousAlternatingMap₂ g h =
      (((ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E N' N'').flip h).comp
        f).compContinuousAlternatingMap g :=
  rfl

/-- Evaluation of a single `uncurrySum.summand` at a representative permutation `a₁`. -/
theorem summand_mk_eval
    {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (F : E [⋀^ι]→L[𝕜] (E [⋀^ι']→L[𝕜] G)) (a₁ : Equiv.Perm (ι ⊕ ι'))
    (w : ι ⊕ ι' → E) :
    uncurrySum.summand F (Quotient.mk'' a₁) w
      = Equiv.Perm.sign a₁ • F (fun i => w (a₁ (Sum.inl i))) (fun j => w (a₁ (Sum.inr j))) := by
  rw [uncurrySum.summand_mk'']
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply,
    ContinuousMultilinearMap.flipMultilinear_apply, coe_toContinuousMultilinearMap,
    ContinuousMultilinearMap.flipAlternating_apply]
  rfl

/-- The value-preserving relabelling `Fin (m+1) ⊕ Fin n ≃ Fin (m+n+1)`, used to lay out the
arguments of the right-hand side. -/
def insSumEquiv : Fin (m + 1) ⊕ Fin n ≃ Fin (m + n + 1) :=
  finSumFinEquiv.trans finAddFlipAssoc

/-- The equivalence `Option (Fin m) ⊕ Fin n ≃ Option (Fin m ⊕ Fin n)`:
`inl none ↦ none`, `inl (some k) ↦ some (inl k)`, `inr j ↦ some (inr j)`. -/
def optSumL : Option (Fin m) ⊕ Fin n ≃ Option (Fin m ⊕ Fin n) where
  toFun := Sum.elim (fun o => o.map Sum.inl) (fun j => some (Sum.inr j))
  invFun := fun o => o.elim (Sum.inl none) (Sum.elim (fun k => Sum.inl (some k)) Sum.inr)
  left_inv := by rintro ((_ | _) | _) <;> rfl
  right_inv := by rintro (_ | (_ | _)) <;> rfl

@[simp] theorem optSumL_inl_none : (optSumL (m := m) (n := n)) (Sum.inl none) = none := rfl
@[simp] theorem optSumL_inl_some (k : Fin m) :
    (optSumL (n := n)) (Sum.inl (some k)) = some (Sum.inl k) := rfl
@[simp] theorem optSumL_inr (j : Fin n) :
    (optSumL (m := m)) (Sum.inr j) = some (Sum.inr j) := rfl

/-- Drop the slot `i` from the left block: `Fin (m+1) ⊕ Fin n ≃ Option (Fin m ⊕ Fin n)`.
`inl i ↦ none`, `inl (i.succAbove k) ↦ some (inl k)`, `inr j ↦ some (inr j)`. -/
def dropL (i : Fin (m + 1)) : Fin (m + 1) ⊕ Fin n ≃ Option (Fin m ⊕ Fin n) :=
  (Equiv.sumCongr (finSuccEquiv' i) (Equiv.refl (Fin n))).trans optSumL

@[simp] theorem dropL_self (i : Fin (m + 1)) : (dropL (n := n) i) (Sum.inl i) = none := by
  simp [dropL]
@[simp] theorem dropL_succAbove (i : Fin (m + 1)) (k : Fin m) :
    (dropL (n := n) i) (Sum.inl (i.succAbove k)) = some (Sum.inl k) := by
  simp [dropL]
@[simp] theorem dropL_inr (i : Fin (m + 1)) (j : Fin n) :
    (dropL (m := m) i) (Sum.inr j) = some (Sum.inr j) := by
  simp [dropL]

@[simp] theorem optSumL_symm_none : (optSumL (m := m) (n := n)).symm none = Sum.inl none := rfl
@[simp] theorem optSumL_symm_some_inl (k : Fin m) :
    (optSumL (n := n)).symm (some (Sum.inl k)) = Sum.inl (some k) := rfl
@[simp] theorem optSumL_symm_some_inr (j : Fin n) :
    (optSumL (m := m)).symm (some (Sum.inr j)) = Sum.inr j := rfl

@[simp] theorem dropL_symm_none (i : Fin (m + 1)) :
    (dropL (n := n) i).symm none = Sum.inl i := by simp [dropL]
@[simp] theorem dropL_symm_some_inl (i : Fin (m + 1)) (k : Fin m) :
    (dropL (n := n) i).symm (some (Sum.inl k)) = Sum.inl (i.succAbove k) := by simp [dropL]
@[simp] theorem dropL_symm_some_inr (i : Fin (m + 1)) (j : Fin n) :
    (dropL (m := m) i).symm (some (Sum.inr j)) = Sum.inr j := by simp [dropL]

variable (G) in
/-- Given a target output position `x : Fin (m+n+1)` and a shuffle `σ : Perm (Fin m ⊕ Fin n)`,
the equivalence `Fin (m+1) ⊕ Fin n ≃ Fin (m+n+1)` that places the new (marked) left slot `inl 0`
at output position `x`, and lays out the remaining `m+n` slots through `σ` into the complement of
`x` (enumerated by `x.succAbove`). -/
def insHat (x : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Fin (m + 1) ⊕ Fin n ≃ Fin (m + n + 1) :=
  (dropL 0).trans <| (Equiv.optionCongr σ).trans <|
    (Equiv.optionCongr finSumFinEquiv).trans (finSuccEquiv' x).symm

theorem insHat_inl_zero (x : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    insHat x σ (Sum.inl 0) = x := by
  simp [insHat]

theorem insHat_inl_succ (x : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) (k : Fin m) :
    insHat x σ (Sum.inl k.succ) = x.succAbove (finSumFinEquiv (σ (Sum.inl k))) := by
  have hk : (Sum.inl k.succ : Fin (m + 1) ⊕ Fin n) = Sum.inl ((0 : Fin (m + 1)).succAbove k) := by
    rw [Fin.succAbove_zero]
  simp only [insHat, Equiv.trans_apply, hk, dropL_succAbove, Equiv.optionCongr_apply,
    Option.map_some, Function.comp_apply, finSuccEquiv'_symm_some]

theorem insHat_inr (x : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) (j : Fin n) :
    insHat x σ (Sum.inr j) = x.succAbove (finSumFinEquiv (σ (Sum.inr j))) := by
  simp [insHat]

theorem coe_insSumEquiv (z : Fin (m + 1) ⊕ Fin n) :
    (insSumEquiv z : ℕ) = (finSumFinEquiv z : ℕ) := by
  simp only [insSumEquiv, Equiv.trans_apply, finAddFlipAssoc, finCongr_apply_coe]

@[simp] theorem insSumEquiv_inl_zero : insSumEquiv (Sum.inl (0 : Fin (m + 1)) : Fin (m + 1) ⊕ Fin n)
    = 0 := by
  apply Fin.ext
  rw [coe_insSumEquiv]
  simp

theorem insSumEquiv_inl_succ (k : Fin m) :
    insSumEquiv (Sum.inl k.succ : Fin (m + 1) ⊕ Fin n)
      = (finSumFinEquiv (Sum.inl k) : Fin (m + n)).succ := by
  apply Fin.ext
  rw [coe_insSumEquiv]
  simp [Fin.val_succ]

theorem insSumEquiv_inr_eq_succ (j : Fin n) :
    insSumEquiv (Sum.inr j : Fin (m + 1) ⊕ Fin n)
      = (finSumFinEquiv (Sum.inr j) : Fin (m + n)).succ := by
  apply Fin.ext
  rw [coe_insSumEquiv]
  simp only [finSumFinEquiv_apply_right, Fin.coe_natAdd, Fin.val_succ]
  omega

/-- The permutation of `Fin (m+1) ⊕ Fin n` obtained from `insHat x σ` by reading the output
through `insSumEquiv`. Inserting the marked slot at `inl 0` mapping to output `x`. -/
def insPerm (x : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Equiv.Perm (Fin (m + 1) ⊕ Fin n) :=
  (insHat x σ).trans insSumEquiv.symm

/-- Inserting a fixed marked slot at output `0` does not change the sign. -/
theorem sign_insPerm_zero (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Equiv.Perm.sign (insPerm 0 σ) = Equiv.Perm.sign σ := by
  have key : insHat 0 σ
      = insSumEquiv.trans (Equiv.Perm.decomposeFin.symm (0, finSumFinEquiv.permCongr σ)) := by
    ext z
    rw [Equiv.trans_apply]
    rcases z with i | j
    · induction i using Fin.cases with
      | zero =>
        rw [insHat_inl_zero, insSumEquiv_inl_zero, Equiv.Perm.decomposeFin_symm_apply_zero]
      | succ k =>
        rw [insHat_inl_succ, insSumEquiv_inl_succ, Equiv.Perm.decomposeFin_symm_apply_succ,
          Equiv.swap_self, Equiv.refl_apply, Fin.succAbove_zero, Equiv.permCongr_apply,
          Equiv.symm_apply_apply]
    · rw [insHat_inr, insSumEquiv_inr_eq_succ, Equiv.Perm.decomposeFin_symm_apply_succ,
        Equiv.swap_self, Equiv.refl_apply, Fin.succAbove_zero, Equiv.permCongr_apply,
        Equiv.symm_apply_apply]
  rw [insPerm, key, Equiv.Perm.sign_trans_trans_symm, Equiv.Perm.decomposeFin.symm_sign,
    if_pos rfl, one_mul, Equiv.Perm.sign_permCongr]

/-- `insHat x σ` is `insHat 0 σ` followed by the cycle moving the output `0` to `x`. -/
theorem insHat_eq_trans_cycleRange (x : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    insHat x σ = (insHat 0 σ).trans x.cycleRange.symm := by
  have hsymm : (finSuccEquiv' x).symm
      = ((finSuccEquiv' (0 : Fin (m + n + 1))).symm).trans x.cycleRange.symm := by
    ext o
    rcases o with _ | p
    · simp [Fin.succAbove_zero]
    · simp [Fin.succAbove_zero, Fin.cycleRange_symm_succ]
  ext z
  simp only [insHat, Equiv.trans_apply, hsymm]

/-- The sign of the inserting permutation: inserting the marked slot at output position `x`
contributes the cyclic sign `(-1)^x`. -/
theorem sign_insPerm (x : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Equiv.Perm.sign (insPerm x σ) = (-1) ^ (x : ℕ) * Equiv.Perm.sign σ := by
  have hperm : insSumEquiv.permCongr (insPerm x σ)
      = x.cycleRange.symm * insSumEquiv.permCongr (insPerm 0 σ) := by
    ext y
    simp only [Equiv.permCongr_apply, insPerm, insHat_eq_trans_cycleRange x σ,
      Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.Perm.mul_apply, Equiv.apply_symm_apply]
  rw [← Equiv.Perm.sign_permCongr insSumEquiv (insPerm x σ), hperm, map_mul,
    Equiv.Perm.sign_symm, Fin.sign_cycleRange, Equiv.Perm.sign_permCongr, sign_insPerm_zero]

/-- The within-left-block permutation moving slot `0` to slot `i`. Lies in the range of
`sumCongrHom`, hence preserves the `ModSumCongr` class on right multiplication. -/
def slotMove (i : Fin (m + 1)) : Equiv.Perm (Fin (m + 1) ⊕ Fin n) :=
  Equiv.sumCongr i.cycleRange.symm (Equiv.refl (Fin n))

/-- The output position of the marked left slot `inl i` of a representative `τ`. -/
def markedOut (τ : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) (i : Fin (m + 1)) : Fin (m + n + 1) :=
  insSumEquiv (τ (Sum.inl i))

/-- The `Option`-encoded equivalence used to extract the "rest" shuffle from `τ` after marking
slot `i`. It fixes `none`. -/
def restOpt (τ : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) (i : Fin (m + 1)) :
    Option (Fin m ⊕ Fin n) ≃ Option (Fin (m + n)) :=
  (dropL i).symm.trans (τ.trans (insSumEquiv.trans (finSuccEquiv' (markedOut τ i))))

theorem restOpt_none (τ : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) (i : Fin (m + 1)) :
    restOpt τ i none = none := by
  simp only [restOpt, Equiv.trans_apply, dropL_symm_none, markedOut, finSuccEquiv'_at]

/-- The "rest" shuffle as an equivalence `Fin m ⊕ Fin n ≃ Fin (m+n)`. -/
def restHat (τ : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) (i : Fin (m + 1)) :
    Fin m ⊕ Fin n ≃ Fin (m + n) :=
  Equiv.removeNone (restOpt τ i)

/-- The "rest" shuffle as a permutation of `Fin m ⊕ Fin n`. -/
def restPerm (τ : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) (i : Fin (m + 1)) :
    Equiv.Perm (Fin m ⊕ Fin n) :=
  (restHat τ i).trans finSumFinEquiv.symm

/-- The key matching identity: laying out the marked layout of `τ` through `insSumEquiv`
recovers the `restHat` shuffle, shifted past the marked output `markedOut τ i`. -/
theorem succAbove_restHat (τ : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) (i : Fin (m + 1))
    (z : Fin m ⊕ Fin n) :
    (markedOut τ i).succAbove (restHat τ i z)
      = insSumEquiv (τ (Sum.map i.succAbove id z)) := by
  have hex : ∃ p, restOpt τ i (some z) = some p := by
    rcases h : restOpt τ i (some z) with _ | p
    · exact absurd (((restOpt τ i).injective (h.trans (restOpt_none τ i).symm))) (by simp)
    · exact ⟨p, rfl⟩
  have hsome : some (restHat τ i z) = restOpt τ i (some z) := Equiv.removeNone_some _ hex
  have hz : (dropL i).symm (some z) = Sum.map i.succAbove id z := by
    rcases z with k | j <;> simp
  simp only [restHat, restOpt, Equiv.trans_apply, hz] at hsome
  have := congrArg (finSuccEquiv' (markedOut τ i)).symm hsome
  rwa [finSuccEquiv'_symm_some, Equiv.symm_apply_apply] at this

@[simp] theorem slotMove_inl_zero (i : Fin (m + 1)) :
    (slotMove (n := n) i) (Sum.inl 0) = Sum.inl i := by simp [slotMove]
@[simp] theorem slotMove_inl_succ (i : Fin (m + 1)) (k : Fin m) :
    (slotMove (n := n) i) (Sum.inl k.succ) = Sum.inl (i.succAbove k) := by
  simp [slotMove, Fin.cycleRange_symm_succ]
@[simp] theorem slotMove_inr (i : Fin (m + 1)) (j : Fin n) :
    (slotMove (m := m) i) (Sum.inr j) = Sum.inr j := by simp [slotMove]

theorem finSumFinEquiv_restPerm (τ : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) (i : Fin (m + 1))
    (z : Fin m ⊕ Fin n) : finSumFinEquiv (restPerm τ i z) = restHat τ i z := by
  simp [restPerm]

/-- The inserting permutation built from `(markedOut τ i, restPerm τ i)` is exactly `τ` with the
marked left slot moved back from `0` to `i`. -/
theorem insPerm_markedOut_restPerm (τ : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) (i : Fin (m + 1)) :
    insPerm (markedOut τ i) (restPerm τ i) = τ * slotMove i := by
  ext z
  rw [insPerm, Equiv.trans_apply, Equiv.Perm.mul_apply]
  rcases z with I | j
  · induction I using Fin.cases with
    | zero =>
      rw [insHat_inl_zero, slotMove_inl_zero, markedOut, Equiv.symm_apply_apply]
    | succ k =>
      rw [insHat_inl_succ, slotMove_inl_succ, finSumFinEquiv_restPerm, succAbove_restHat]
      simp only [Sum.map_inl, id, Equiv.symm_apply_apply]
  · rw [insHat_inr, slotMove_inr, finSumFinEquiv_restPerm, succAbove_restHat (z := Sum.inr j)]
    simp only [Sum.map_inr, id, Equiv.symm_apply_apply]

@[simp] theorem sign_slotMove (i : Fin (m + 1)) :
    Equiv.Perm.sign (slotMove (n := n) i) = (-1) ^ (i : ℕ) := by
  rw [slotMove, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_symm, Fin.sign_cycleRange,
    Equiv.Perm.sign_refl, mul_one]

theorem slotMove_inv (i : Fin (m + 1)) :
    (slotMove (n := n) i)⁻¹ = Equiv.sumCongr i.cycleRange (Equiv.refl (Fin n)) := by
  rw [Equiv.Perm.inv_def, slotMove, Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.symm_symm]

/-- The representative-level sign identity at the heart of the shuffle/Pascal recursion. -/
theorem sign_restPerm (τ : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) (i : Fin (m + 1)) :
    (-1) ^ (markedOut τ i : ℕ) * Equiv.Perm.sign (restPerm τ i)
      = Equiv.Perm.sign τ * (-1) ^ (i : ℕ) := by
  have h := insPerm_markedOut_restPerm τ i
  apply_fun Equiv.Perm.sign at h
  rwa [sign_insPerm, map_mul, sign_slotMove] at h

/-- Descent: `insPerm x` carries within-block reshuffles of `σ` to within-block reshuffles of
`insPerm x σ`, hence descends to the `ModSumCongr` quotient. -/
theorem insPerm_mul_sumCongr (x : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (sl : Equiv.Perm (Fin m)) (sr : Equiv.Perm (Fin n)) :
    insPerm x (σ * Equiv.sumCongr sl sr)
      = insPerm x σ * Equiv.sumCongr (Equiv.Perm.decomposeFin.symm (0, sl)) sr := by
  ext z
  rw [Equiv.Perm.mul_apply, insPerm, Equiv.trans_apply, insPerm, Equiv.trans_apply]
  congr 1
  rcases z with I | j
  · induction I using Fin.cases with
    | zero =>
      rw [Equiv.sumCongr_apply, Sum.map_inl, Equiv.Perm.decomposeFin_symm_apply_zero,
        insHat_inl_zero, insHat_inl_zero]
    | succ k =>
      rw [Equiv.sumCongr_apply, Sum.map_inl, Equiv.Perm.decomposeFin_symm_apply_succ,
        Equiv.swap_self, Equiv.refl_apply, insHat_inl_succ, insHat_inl_succ,
        Equiv.Perm.mul_apply, Equiv.sumCongr_apply, Sum.map_inl]
  · simp only [Equiv.sumCongr_apply, Sum.map_inr, id_eq, insHat_inr, Equiv.Perm.mul_apply]

open Equiv.Perm in
theorem proj_spec (x : Fin (m + n + 1)) (a b : Equiv.Perm (Fin m ⊕ Fin n))
    (h : (QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range) a b) :
    (Quot.mk (⇑(QuotientGroup.leftRel (sumCongrHom (Fin (m + 1)) (Fin n)).range))
        (insPerm x a)) =
      (Quot.mk (⇑(QuotientGroup.leftRel (sumCongrHom (Fin (m + 1)) (Fin n)).range))
        (insPerm x b)) := by
  apply Quot.sound
  rw [QuotientGroup.leftRel_apply] at h ⊢
  obtain ⟨⟨sl, sr⟩, hb⟩ := h
  simp only [sumCongrHom_apply, MonoidHom.coe_mk, OneHom.coe_mk] at hb
  have hbb : b = a * Equiv.sumCongr sl sr := by
    rw [show Equiv.sumCongr sl sr = sl.sumCongr sr from rfl, hb, mul_inv_cancel_left]
  rw [hbb, insPerm_mul_sumCongr]
  refine ⟨(Equiv.Perm.decomposeFin.symm (0, sl), sr), ?_⟩
  simp only [sumCongrHom_apply]
  group

/-- The fibrewise projection sending a marked output position `x` together with a shuffle class of
`Fin m ⊕ Fin n` to the shuffle class of `Fin (m+1) ⊕ Fin n` obtained by inserting the marked slot
at `inl 0`. -/
def proj (p : Fin (m + n + 1) × Equiv.Perm.ModSumCongr (Fin m) (Fin n)) :
    Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n) :=
  Quotient.liftOn' p.2 (fun σ => Quotient.mk'' (insPerm p.1 σ)) (proj_spec p.1)

@[simp] theorem proj_mk (x : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    proj (x, Quotient.mk'' σ) = Quotient.mk'' (insPerm x σ) := rfl

theorem insHat_injective (x : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Function.Injective (insHat x σ) := (insHat x σ).injective

/-- `insPerm x` is injective in its shuffle argument. -/
theorem insPerm_left_injective (x : Fin (m + n + 1)) :
    Function.Injective (insPerm x : Equiv.Perm (Fin m ⊕ Fin n) → _) := by
  intro σ₁ σ₂ h
  have h' : insHat x σ₁ = insHat x σ₂ := by
    have := congrArg (fun e => e.trans insSumEquiv) h
    simpa only [insPerm, Equiv.symm_trans_self, Equiv.trans_refl, Equiv.trans_assoc] using this
  ext z
  rcases z with k | j
  · have := Equiv.congr_fun h' (Sum.inl k.succ)
    rw [insHat_inl_succ, insHat_inl_succ] at this
    have h2 := (Fin.succAbove_right_injective (p := x)) this
    exact finSumFinEquiv.injective h2
  · have := Equiv.congr_fun h' (Sum.inr j)
    rw [insHat_inr, insHat_inr] at this
    have h2 := (Fin.succAbove_right_injective (p := x)) this
    exact finSumFinEquiv.injective h2

/-- For fixed marked output `x`, the descended projection is injective on shuffle classes. -/
theorem proj_left_injective (x : Fin (m + n + 1)) (σ₁ σ₂ : Equiv.Perm (Fin m ⊕ Fin n))
    (h : Quotient.mk'' (insPerm x σ₁) =
      (Quotient.mk'' (insPerm x σ₂) : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n))) :
    (Quotient.mk'' σ₁ : Equiv.Perm.ModSumCongr (Fin m) (Fin n)) = Quotient.mk'' σ₂ := by
  rw [Quotient.eq''] at h
  rw [QuotientGroup.leftRel_apply] at h
  obtain ⟨⟨sl, sr⟩, hsl⟩ := h
  simp only [Equiv.Perm.sumCongrHom_apply] at hsl
  -- `insPerm x σ₂ = insPerm x σ₁ * sumCongr sl sr`
  have hmul : insPerm x σ₂ = insPerm x σ₁ * Equiv.sumCongr sl sr := by
    rw [show Equiv.sumCongr sl sr = sl.sumCongr sr from rfl, hsl, mul_inv_cancel_left]
  -- evaluating at `inl 0` forces `sl 0 = 0`
  have hsl0 : sl 0 = 0 := by
    have e2 : insSumEquiv (insPerm x σ₂ (Sum.inl 0)) = x := by
      rw [insPerm, Equiv.trans_apply, Equiv.apply_symm_apply, insHat_inl_zero]
    rw [hmul, Equiv.Perm.mul_apply, Equiv.sumCongr_apply, Sum.map_inl, insPerm,
      Equiv.trans_apply, Equiv.apply_symm_apply] at e2
    have : insHat x σ₁ (Sum.inl (sl 0)) = insHat x σ₁ (Sum.inl 0) := by
      rw [e2, insHat_inl_zero]
    exact Sum.inl_injective (insHat_injective x σ₁ this)
  -- a permutation of `Fin (m+1)` fixing `0` factors through `decomposeFin`
  set sl' := (Equiv.Perm.decomposeFin sl).2 with hsl'def
  have hsl_eq : sl = Equiv.Perm.decomposeFin.symm (0, sl') := by
    have hsplit : sl = Equiv.Perm.decomposeFin.symm (Equiv.Perm.decomposeFin sl) := by
      rw [Equiv.symm_apply_apply]
    have hp : (Equiv.Perm.decomposeFin sl).1 = 0 := by
      have h0 : Equiv.Perm.decomposeFin.symm (Equiv.Perm.decomposeFin sl) 0 = sl 0 := by
        rw [Equiv.symm_apply_apply]
      rw [Equiv.Perm.decomposeFin_symm_apply_zero] at h0
      rw [h0, hsl0]
    rw [hsplit]; congr 1; rw [← hp]
  rw [hsl_eq, ← insPerm_mul_sumCongr] at hmul
  have := insPerm_left_injective x hmul
  rw [Quotient.eq'', QuotientGroup.leftRel_apply]
  exact ⟨(sl', sr), by simp only [Equiv.Perm.sumCongrHom_apply]; rw [this]; group⟩

/-- The per-fibre identity: summing the left-hand side over the fibre of a fixed shuffle class
`[τ]` reconstructs the `summand` of `uncurryFin Φ` at `[τ]`. -/
theorem fibre_identity
    (Φ : E →L[𝕜] (E [⋀^Fin m]→L[𝕜] (E [⋀^Fin n]→L[𝕜] G)))
    (u : Fin (m + n + 1) → E) (τ : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    ∑ p ∈ Finset.univ.filter
        (fun p : Fin (m + n + 1) × Equiv.Perm.ModSumCongr (Fin m) (Fin n) =>
          proj p = Quotient.mk'' τ),
        (-1 : ℤ) ^ (p.1 : ℕ) • uncurrySum.summand (Φ (u p.1)) p.2
          ((Fin.removeNth p.1 u) ∘ ⇑finSumFinEquiv)
      = uncurrySum.summand (uncurryFin Φ) (Quotient.mk'' τ)
          ((u ∘ ⇑finAddFlipAssoc) ∘ ⇑finSumFinEquiv) := by
  -- evaluate the right-hand summand, then `uncurryFin`
  rw [summand_mk_eval, uncurryFin_apply]
  have hw : ((u ∘ ⇑finAddFlipAssoc) ∘ ⇑finSumFinEquiv)
      = (u ∘ ⇑(insSumEquiv : Fin (m + 1) ⊕ Fin n ≃ Fin (m + n + 1))) := by
    ext z; rfl
  rw [hw, ContinuousAlternatingMap.sum_apply, Finset.smul_sum]
  -- reindex the fibre sum on the left by `k ↦ (markedOut τ k, [restPerm τ k])`
  refine (Finset.sum_bij'
    (i := fun k _ => (markedOut τ k, Quotient.mk'' (restPerm τ k)))
    (j := fun p _ => (τ.symm (insSumEquiv.symm p.1)).elim id (fun _ => 0))
    (fun k _ => ?_) (fun p _ => Finset.mem_univ _) (fun k _ => ?_) (fun p hp => ?_)
    (fun k _ => ?_)).symm
  · -- membership in the fibre
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [proj_mk, insPerm_markedOut_restPerm, Quotient.eq'', QuotientGroup.leftRel_apply]
    refine ⟨(k.cycleRange, Equiv.refl (Fin n)), ?_⟩
    simp only [Equiv.Perm.sumCongrHom_apply]
    have hg : (τ * slotMove k)⁻¹ * τ = (slotMove k)⁻¹ := by group
    rw [hg, slotMove_inv]
  · -- right_inv: extractIdx (markedOut τ k) = k
    show (τ.symm (insSumEquiv.symm (markedOut τ k))).elim id (fun _ => 0) = k
    rw [markedOut, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Sum.elim_inl, id]
  · -- right_inv: `(markedOut τ i₀, [restPerm τ i₀]) = p` on the fibre
    obtain ⟨x, c⟩ := p
    induction c using Quotient.inductionOn' with
    | _ σ =>
      have hpe : proj (x, Quotient.mk'' σ) = Quotient.mk'' τ := by
        have := (Finset.mem_filter.mp hp).2
        exact this
      rw [proj_mk] at hpe
      have hpe2 : (insPerm x σ)⁻¹ * τ ∈ (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range := by
        rw [← QuotientGroup.leftRel_apply]; exact Quotient.exact' hpe
      obtain ⟨⟨sl, sr⟩, hsl⟩ := hpe2
      simp only [Equiv.Perm.sumCongrHom_apply] at hsl
      -- `τ = insPerm x σ * sumCongr sl sr`
      have hτ : τ = insPerm x σ * Equiv.sumCongr sl sr := by
        rw [show Equiv.sumCongr sl sr = sl.sumCongr sr from rfl, hsl, mul_inv_cancel_left]
      -- the marked slot index of `τ`
      have hmark : τ (Sum.inl (sl⁻¹ 0)) = insSumEquiv.symm x := by
        rw [hτ, Equiv.Perm.mul_apply, Equiv.sumCongr_apply, Sum.map_inl,
          Equiv.Perm.apply_inv_self, insPerm, Equiv.trans_apply, insHat_inl_zero]
      have hi0 : (τ.symm (insSumEquiv.symm x)).elim id (fun _ => 0) = sl⁻¹ 0 := by
        rw [← hmark, Equiv.symm_apply_apply, Sum.elim_inl, id]
      have hmx : markedOut τ (sl⁻¹ 0) = x := by rw [markedOut, hmark, Equiv.apply_symm_apply]
      show ((fun k _ => (markedOut τ k, Quotient.mk'' (restPerm τ k)))
        ((τ.symm (insSumEquiv.symm x)).elim id (fun _ => 0)) (Finset.mem_univ _)) = (x, _)
      rw [hi0]
      refine Prod.ext hmx ?_
      show Quotient.mk'' (restPerm τ (sl⁻¹ 0)) = Quotient.mk'' σ
      apply proj_left_injective (markedOut τ (sl⁻¹ 0))
      have hclass : Quotient.mk'' (insPerm (markedOut τ (sl⁻¹ 0)) (restPerm τ (sl⁻¹ 0)))
          = (Quotient.mk'' τ : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) := by
        rw [insPerm_markedOut_restPerm, Quotient.eq'', QuotientGroup.leftRel_apply]
        refine ⟨((sl⁻¹ 0).cycleRange, Equiv.refl (Fin n)), ?_⟩
        simp only [Equiv.Perm.sumCongrHom_apply]
        have hg : (τ * slotMove (sl⁻¹ 0))⁻¹ * τ = (slotMove (sl⁻¹ 0))⁻¹ := by group
        rw [hg, slotMove_inv]
      have hclass2 : Quotient.mk'' (insPerm (markedOut τ (sl⁻¹ 0)) σ)
          = (Quotient.mk'' τ : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) := by
        rw [hmx, Quotient.eq'', QuotientGroup.leftRel_apply]
        exact ⟨(sl, sr), by rw [Equiv.Perm.sumCongrHom_apply, hτ]; group⟩
      rw [hclass, ← hclass2]
  · -- term identity at index `k`
    simp only [ContinuousAlternatingMap.smul_apply]
    rw [summand_mk_eval]
    -- match the three arguments of `Φ`
    have hlin : u (markedOut τ k) = (u ∘ ⇑insSumEquiv) (τ (Sum.inl k)) := by
      rw [markedOut]; rfl
    have hleft : (fun i => ((Fin.removeNth (markedOut τ k) u) ∘ ⇑finSumFinEquiv)
          (restPerm τ k (Sum.inl i)))
        = (Fin.removeNth k fun i => (u ∘ ⇑insSumEquiv) (τ (Sum.inl i))) := by
      ext i
      simp only [Function.comp_apply, Fin.removeNth]
      rw [finSumFinEquiv_restPerm, succAbove_restHat]
      simp only [Sum.map_inl, id]
    have hright : (fun j => ((Fin.removeNth (markedOut τ k) u) ∘ ⇑finSumFinEquiv)
          (restPerm τ k (Sum.inr j)))
        = (fun j => (u ∘ ⇑insSumEquiv) (τ (Sum.inr j))) := by
      ext j
      simp only [Function.comp_apply, Fin.removeNth]
      rw [finSumFinEquiv_restPerm, succAbove_restHat (z := Sum.inr j)]
      simp only [Sum.map_inr, id]
    rw [hlin, hleft, hright]
    -- now equate the scalars via the sign identity (convert all `•` to `ℤ`-smul)
    rw [Units.smul_def (Equiv.Perm.sign τ), Units.smul_def (Equiv.Perm.sign (restPerm τ k)),
      smul_smul, smul_smul]
    congr 1
    have hs := sign_restPerm τ k
    have hs' : ((-1 : ℤ)) ^ (markedOut τ k : ℕ) * (Equiv.Perm.sign (restPerm τ k) : ℤ)
        = (Equiv.Perm.sign τ : ℤ) * (-1) ^ (k : ℕ) := by
      have := congrArg (Units.val) hs
      push_cast at this ⊢
      linear_combination this
    rw [← hs']

theorem uncurryFin_uncurryFinAdd_left_aux
    (Φ : E →L[𝕜] (E [⋀^Fin m]→L[𝕜] (E [⋀^Fin n]→L[𝕜] G)))
    (u : Fin (m + n + 1) → E) :
    ∑ x : Fin (m + n + 1), (-1) ^ (x : ℕ) • ∑ a : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
        uncurrySum.summand (Φ (u x)) a ((Fin.removeNth x u) ∘ ⇑finSumFinEquiv)
      = ∑ a' : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n),
        uncurrySum.summand (uncurryFin Φ) a' ((u ∘ ⇑finAddFlipAssoc) ∘ ⇑finSumFinEquiv) := by
  classical
  -- combine the double sum on the left into one sum over the product index set
  have hcombine :
      ∑ x : Fin (m + n + 1), (-1 : ℤ) ^ (x : ℕ) • ∑ a : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
          uncurrySum.summand (Φ (u x)) a ((Fin.removeNth x u) ∘ ⇑finSumFinEquiv)
        = ∑ p : Fin (m + n + 1) × Equiv.Perm.ModSumCongr (Fin m) (Fin n),
          (-1 : ℤ) ^ (p.1 : ℕ) • uncurrySum.summand (Φ (u p.1)) p.2
            ((Fin.removeNth p.1 u) ∘ ⇑finSumFinEquiv) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => by rw [Finset.smul_sum]
  rw [hcombine, ← Finset.sum_fiberwise Finset.univ proj
    (fun p => (-1 : ℤ) ^ (p.1 : ℕ) • uncurrySum.summand (Φ (u p.1)) p.2
      ((Fin.removeNth p.1 u) ∘ ⇑finSumFinEquiv))]
  refine Finset.sum_congr rfl fun a' _ => ?_
  induction a' using Quotient.inductionOn' with
  | _ τ => exact fibre_identity Φ u τ

/-- The abstract "uncurryFin commutes with uncurryFinAdd on the left factor" identity, with all the
wedge/pairing data abstracted into an arbitrary curried family `Φ`. This is the combinatorial core
of commutation lemma A: the value of `Ψ x` is the block-concatenation `uncurryFinAdd (Φ x)`, and
uncurrying `Ψ` (prepending a derivative slot) equals uncurrying `Φ` in its left factor first and
then block-concatenating, up to the index reshuffle `finAddFlipAssoc`. -/
theorem uncurryFin_uncurryFinAdd_left
    (Φ : E →L[𝕜] (E [⋀^Fin m]→L[𝕜] (E [⋀^Fin n]→L[𝕜] G)))
    (Ψ : E →L[𝕜] (E [⋀^Fin (m + n)]→L[𝕜] G))
    (hΨ : ∀ x, Ψ x = uncurryFinAdd (Φ x)) :
    uncurryFin Ψ = domDomCongr finAddFlipAssoc (uncurryFinAdd (uncurryFin Φ)) := by
  ext u
  rw [uncurryFin_apply]
  simp_rw [hΨ, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply]
  conv_rhs => erw [domDomCongr_apply, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply]
  exact uncurryFin_uncurryFinAdd_left_aux Φ u

/-- **Commutation lemma A (left slot).** Uncurrying (prepending a derivative slot) commutes with
wedging on the *left*: the new slot joins the `uncurryFin`-block, and the index reshuffling
`finAddFlipAssoc` records that this block sits before `h`'s block. No sign appears. -/
theorem uncurryFin_precompL_wedge (f : N →L[𝕜] N' →L[𝕜] N'')
    (A : E →L[𝕜] (E [⋀^Fin m]→L[𝕜] N)) (h : E [⋀^Fin n]→L[𝕜] N') :
    uncurryFin ((wedgeCLM (M := E) (m := m) (n := n) f).precompL E A h) =
      domDomCongr finAddFlipAssoc (wedge_product (uncurryFin A) h f) := by
  -- Abbreviate the fixed post-composition `L = ((compCAMCLM …).flip h).comp f`, so that
  -- `f.compCAM₂ · h = L.compCAM ·`, and set `Φ x = L.compCAM (A x)`.
  set L : N →L[𝕜] (E [⋀^Fin n]→L[𝕜] N'') :=
    ((ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E N' N'').flip h).comp f with hL
  set Φ : E →L[𝕜] (E [⋀^Fin m]→L[𝕜] (E [⋀^Fin n]→L[𝕜] N'')) :=
    (ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E N (E [⋀^Fin n]→L[𝕜] N'') L).comp A
    with hΦ
  -- The RHS: rewrite `wedge_product (uncurryFin A) h f` as `uncurryFinAdd (uncurryFin Φ)`.
  have hRHS : wedge_product (uncurryFin A) h f = uncurryFinAdd (uncurryFin Φ) := by
    rw [wedge_product, compContinuousAlternatingMap₂_eq_comp, hΦ, ← hL,
      uncurryFin_compContinuousAlternatingMapCLM]
  -- The LHS: identify `(wedgeCLM f).precompL E A h` with a `Ψ` satisfying `Ψ x = uncurryFinAdd (Φ x)`.
  rw [hRHS]
  refine uncurryFin_uncurryFinAdd_left Φ _ (fun x => ?_)
  simp only [ContinuousLinearMap.precompL_apply, wedgeCLM_apply]
  rw [wedge_product, compContinuousAlternatingMap₂_eq_comp, hΦ, ← hL]
  rfl

theorem domDomCongr_domDomCongr {ι ι' ι'' : Type*} (σ : ι ≃ ι') (τ : ι' ≃ ι'')
    (f : E [⋀^ι]→L[𝕜] G) :
    domDomCongr τ (domDomCongr σ f) = domDomCongr (σ.trans τ) f := by
  ext v; simp only [domDomCongr_apply, Function.comp_assoc, Equiv.coe_trans]

theorem domDomCongr_smul {ι ι' : Type*} (σ : ι ≃ ι') (c : 𝕜) (f : E [⋀^ι]→L[𝕜] G) :
    domDomCongr σ (c • f) = c • domDomCongr σ f := by
  ext v; simp only [domDomCongr_apply, smul_apply]

/-- Uncurrying intertwines with a scalar multiple of a (value-preserving) index recast: if
`Ψ' v = c • domDomCongr (finCongr hd) (ψ' v)` for all `v`, then `uncurryFin Ψ'` is the same
scalar multiple of the recast of `uncurryFin ψ'`. -/
theorem uncurryFin_smul_domDomCongr {d d' : ℕ} (c : 𝕜) (hd : d = d')
    (ψ' : E →L[𝕜] (E [⋀^Fin d]→L[𝕜] G)) (Ψ' : E →L[𝕜] (E [⋀^Fin d']→L[𝕜] G))
    (hΨ : ∀ v, Ψ' v = c • domDomCongr (finCongr hd) (ψ' v)) :
    uncurryFin Ψ' = c • domDomCongr (finCongr (by omega : d + 1 = d' + 1)) (uncurryFin ψ') := by
  subst hd
  have hΨ' : Ψ' = c • ψ' := by
    ext v w
    rw [hΨ]
    simp only [finCongr_refl, domDomCongr_refl, ContinuousLinearMap.smul_apply, smul_apply]
  rw [hΨ', uncurryFin_smul, finCongr_refl, domDomCongr_refl]

/-- **Commutation lemma B (right slot).** Uncurrying commutes with wedging on the *right*: the new
slot has to move past the `m` slots of `g`, producing the sign `(-1)^m`. -/
theorem uncurryFin_precompR_wedge (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : E [⋀^Fin m]→L[𝕜] N) (C : E →L[𝕜] (E [⋀^Fin n]→L[𝕜] N')) :
    uncurryFin ((wedgeCLM (M := E) (m := m) (n := n) f).precompR E g C) =
      (-1 : 𝕜) ^ m • wedge_product g (uncurryFin C) f := by
  -- `ψ v = wedge_product (C v) g f.flip`, the LEFT-factor wedge with the flipped pairing.
  set ψ : E →L[𝕜] (E [⋀^Fin (n + m)]→L[𝕜] N'') :=
    (wedgeCLM (M := E) (m := n) (n := m) f.flip).precompL E C g with hψ
  -- Step 3: `(wedgeCLM f).precompR E g C = c • domDomCongr (finCongr _) ∘ ψ`, with c = (-1)^(m*n).
  have hΨ : ∀ v, ((wedgeCLM (M := E) (m := m) (n := n) f).precompR E g C) v
      = (-1 : 𝕜) ^ (m * n) • domDomCongr (finCongr (Nat.add_comm n m)) (ψ v) := by
    intro v
    simp only [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, wedgeCLM_apply, hψ, ContinuousLinearMap.precompL_apply]
    rw [wedge_flip g (C v) f]
    ext w
    rw [domDomCongr_apply, smul_apply, smul_apply, domDomCongr_apply]
    rfl
  rw [uncurryFin_smul_domDomCongr ((-1 : 𝕜) ^ (m * n)) (Nat.add_comm n m) ψ _ hΨ]
  -- Step 4: `uncurryFin ψ` via Lemma A.
  rw [hψ, uncurryFin_precompL_wedge f.flip C g]
  -- Step 5: rewrite the goal RHS via `wedge_flip`.
  rw [wedge_flip g (uncurryFin C) f]
  rw [domDomCongr_domDomCongr, domDomCongr_smul]
  -- combine the two scalars and the two index recasts
  rw [smul_smul, ← pow_add]
  -- the two composite recasts agree (all value-preserving `finCongr`s)
  have heq : finAddFlipAssoc.trans (finCongr (show n + m + 1 = m + n + 1 from by omega))
      = finAddCongr (m := n + 1) (n := m) := by
    ext k
    simp only [Equiv.coe_trans, Function.comp_apply, finAddFlipAssoc, finAddCongr, finCongr_apply,
      Fin.coe_cast]
  rw [heq]
  congr 1
  have h2 : (-1 : 𝕜) ^ (2 * m) = 1 := by
    rw [pow_mul, neg_one_sq, one_pow]
  rw [show m + m * (n + 1) = m * n + 2 * m by ring, pow_add, h2, mul_one]


/-! ### The interior-product (slot-0 contraction) Leibniz rule -/

-- claim (b): right slots.
theorem claim_b (σ' : Equiv.Perm (Fin m ⊕ Fin (n + 1))) (x₀ : E) (y : Fin (m + (n + 1)) → E) :
    (fun j => ((Fin.cons x₀ y ∘ ⇑finAddFlipAssoc) ∘ ⇑finSumFinEquiv)
        (insPerm (0 : Fin (m + (n + 1) + 1)) σ' (Sum.inr j)))
      = (fun j => y (finSumFinEquiv (σ' (Sum.inr j)))) := by
  funext j
  show (Fin.cons x₀ y : Fin _ → E)
      (insSumEquiv (insPerm (0 : Fin (m + (n + 1) + 1)) σ' (Sum.inr j))) = _
  rw [insPerm, Equiv.trans_apply, Equiv.apply_symm_apply, insHat_inr, Fin.succAbove_zero,
    Fin.cons_succ]

-- claim (a): left slots.
theorem claim_a (σ' : Equiv.Perm (Fin m ⊕ Fin (n + 1))) (x₀ : E) (y : Fin (m + (n + 1)) → E) :
    (fun i => ((Fin.cons x₀ y ∘ ⇑finAddFlipAssoc) ∘ ⇑finSumFinEquiv)
        (insPerm (0 : Fin (m + (n + 1) + 1)) σ' (Sum.inl i)))
      = (Fin.cons x₀ (fun i => y (finSumFinEquiv (σ' (Sum.inl i)))) : Fin _ → E) := by
  funext i
  show (Fin.cons x₀ y : Fin _ → E)
      (insSumEquiv (insPerm (0 : Fin (m + (n + 1) + 1)) σ' (Sum.inl i))) = _
  rw [insPerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  induction i using Fin.cases with
  | zero => rw [insHat_inl_zero, Fin.cons_zero, Fin.cons_zero]
  | succ k => rw [insHat_inl_succ, Fin.succAbove_zero, Fin.cons_succ, Fin.cons_succ]

/-- Which factor the contracted slot `inl 0` feeds into, as a class invariant. -/
def isLeftClass : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin (n + 1)) → Bool :=
  fun q => Quotient.liftOn' q (fun σ => (σ⁻¹ (Sum.inl 0)).isLeft) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    obtain ⟨⟨sl, sr⟩, hb⟩ := hab
    simp only [Equiv.Perm.sumCongrHom_apply] at hb
    have hbb : b = a * Equiv.sumCongr sl sr := by
      rw [show Equiv.sumCongr sl sr = sl.sumCongr sr from rfl, hb, mul_inv_cancel_left]
    rw [hbb]
    simp only [mul_inv_rev, Equiv.Perm.coe_mul, Function.comp_apply]
    rcases h0 : a⁻¹ (Sum.inl 0) with i | j <;>
      simp [Equiv.sumCongr_symm, Equiv.sumCongr_apply, h0])

theorem summandA (g : E [⋀^Fin (m + 1)]→L[𝕜] N) (h : E [⋀^Fin (n + 1)]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') (x₀ : E) (y : Fin (m + (n + 1)) → E)
    (σ' : Equiv.Perm (Fin m ⊕ Fin (n + 1))) :
    uncurrySum.summand (f.compContinuousAlternatingMap₂ g h)
        (Quotient.mk'' (insPerm (0 : Fin (m + (n + 1) + 1)) σ'))
        ((Fin.cons x₀ y ∘ ⇑finAddFlipAssoc) ∘ ⇑finSumFinEquiv)
      = uncurrySum.summand (f.compContinuousAlternatingMap₂ (curryFin g x₀) h)
        (Quotient.mk'' σ') (y ∘ ⇑finSumFinEquiv) := by
  rw [summand_mk_eval, summand_mk_eval, sign_insPerm_zero]
  congr 1
  rw [ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    ContinuousLinearMap.compContinuousAlternatingMap₂_apply, curryFin_apply,
    claim_a σ' x₀ y, claim_b σ' x₀ y]
  rfl

-- Identity 1 (Part A): the left-classes reconstruct term1.
theorem identityA (g : E [⋀^Fin (m + 1)]→L[𝕜] N) (h : E [⋀^Fin (n + 1)]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') (x₀ : E) (y : Fin (m + (n + 1)) → E) :
    ∑ σ' : Equiv.Perm.ModSumCongr (Fin m) (Fin (n + 1)),
        uncurrySum.summand (f.compContinuousAlternatingMap₂ (curryFin g x₀) h) σ'
          (y ∘ ⇑finSumFinEquiv)
      = ∑ σ ∈ Finset.univ.filter (fun q => isLeftClass q = true),
        uncurrySum.summand (f.compContinuousAlternatingMap₂ g h) σ
          ((Fin.cons x₀ y ∘ ⇑finAddFlipAssoc) ∘ ⇑finSumFinEquiv) := by
  refine Finset.sum_bij (fun σ' _ => proj (0, σ')) ?_ ?_ ?_ ?_
  · -- maps into the left-classes
    intro a _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    induction a using Quotient.inductionOn' with
    | _ σ =>
      have key : (insPerm (0 : Fin (m + (n + 1) + 1)) σ)⁻¹ (Sum.inl 0) = Sum.inl 0 := by
        rw [Equiv.Perm.inv_eq_iff_eq]; symm
        rw [insPerm, Equiv.trans_apply, insHat_inl_zero,
          show (0 : Fin (m + (n + 1) + 1)) = insSumEquiv (Sum.inl 0) from insSumEquiv_inl_zero.symm,
          Equiv.symm_apply_apply]
      simp only [proj_mk, isLeftClass, Quotient.liftOn'_mk'', key, Sum.isLeft_inl]
  · -- injective
    intro a₁ _ a₂ _ heq
    induction a₁ using Quotient.inductionOn' with
    | _ σ₁ =>
    induction a₂ using Quotient.inductionOn' with
    | _ σ₂ =>
      simp only [proj_mk] at heq
      exact proj_left_injective 0 σ₁ σ₂ heq
  · -- surjective onto left-classes
    intro b hb
    rw [Finset.mem_filter] at hb
    induction b using Quotient.inductionOn' with
    | _ τ =>
      rcases h0 : τ⁻¹ (Sum.inl 0) with i₀ | j₀
      · refine ⟨Quotient.mk'' (restPerm τ i₀), Finset.mem_univ _, ?_⟩
        have hτ : τ (Sum.inl i₀) = Sum.inl 0 := by rw [← h0, Equiv.Perm.apply_inv_self]
        have hmark : markedOut τ i₀ = 0 := by rw [markedOut, hτ, insSumEquiv_inl_zero]
        simp only [proj_mk]
        rw [← hmark, insPerm_markedOut_restPerm, Quotient.eq'', QuotientGroup.leftRel_apply]
        refine ⟨(i₀.cycleRange, Equiv.refl (Fin (n + 1))), ?_⟩
        simp only [Equiv.Perm.sumCongrHom_apply]
        have hg : (τ * slotMove i₀)⁻¹ * τ = (slotMove i₀)⁻¹ := by group
        rw [hg, slotMove_inv]
      · have hb2 := hb.2
        simp only [isLeftClass, Quotient.liftOn'_mk'', h0, Sum.isLeft_inr,
          Bool.false_eq_true] at hb2
  · -- term identity
    intro a _
    induction a using Quotient.inductionOn' with
    | _ σ' => simp only [proj_mk]; exact (summandA g h f x₀ y σ').symm

/- ===================== Part B: right-block insertion ===================== -/

/-- `Fin (m+1) ⊕ Option (Fin n) ≃ Option (Fin (m+1) ⊕ Fin n)`. -/
def optSumR : Fin (m + 1) ⊕ Option (Fin n) ≃ Option (Fin (m + 1) ⊕ Fin n) where
  toFun := Sum.elim (fun i => some (Sum.inl i)) (fun o => o.map Sum.inr)
  invFun := fun o => o.elim (Sum.inr none) (Sum.elim Sum.inl (fun j => Sum.inr (some j)))
  left_inv := by rintro (i | (_ | j)) <;> rfl
  right_inv := by rintro (_ | (i | j)) <;> rfl

@[simp] theorem optSumR_inl (i : Fin (m + 1)) :
    (optSumR (n := n)) (Sum.inl i) = some (Sum.inl i) := rfl
@[simp] theorem optSumR_inr_none : (optSumR (m := m) (n := n)) (Sum.inr none) = none := rfl
@[simp] theorem optSumR_inr_some (j : Fin n) :
    (optSumR (m := m)) (Sum.inr (some j)) = some (Sum.inr j) := rfl

theorem fse0_symm_some {p : ℕ} (j : Fin p) :
    (finSuccEquiv' (0 : Fin (p + 1))).symm (some j) = j.succ := by
  rw [finSuccEquiv'_symm_some, Fin.succAbove_zero]
theorem fse0_symm_none {p : ℕ} : (finSuccEquiv' (0 : Fin (p + 1))).symm none = 0 :=
  finSuccEquiv'_symm_none 0
theorem fse0_succ {p : ℕ} (j : Fin p) : (finSuccEquiv' (0 : Fin (p + 1))) j.succ = some j := by
  rw [← Fin.succAbove_zero (n := p), finSuccEquiv'_succAbove]

/-- Drop the marked slot `inr 0` from the right block. -/
def dropR : Fin (m + 1) ⊕ Fin (n + 1) ≃ Option (Fin (m + 1) ⊕ Fin n) :=
  (Equiv.sumCongr (Equiv.refl (Fin (m + 1))) (finSuccEquiv' 0)).trans optSumR

@[simp] theorem dropR_inl (i : Fin (m + 1)) : (dropR (n := n)) (Sum.inl i) = some (Sum.inl i) := by
  simp [dropR]
@[simp] theorem dropR_inr_zero : (dropR (m := m) (n := n)) (Sum.inr 0) = none := by
  simp [dropR]
@[simp] theorem dropR_inr_succ (j : Fin n) :
    (dropR (m := m)) (Sum.inr j.succ) = some (Sum.inr j) := by
  simp only [dropR, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, fse0_succ,
    optSumR_inr_some]

@[simp] theorem dropR_symm_none : (dropR (m := m) (n := n)).symm none = Sum.inr 0 :=
  dropR.symm_apply_eq.mpr dropR_inr_zero.symm
@[simp] theorem dropR_symm_some_inl (i : Fin (m + 1)) :
    (dropR (n := n)).symm (some (Sum.inl i)) = Sum.inl i :=
  dropR.symm_apply_eq.mpr (dropR_inl i).symm
@[simp] theorem dropR_symm_some_inr (j : Fin n) :
    (dropR (m := m)).symm (some (Sum.inr j)) = Sum.inr j.succ :=
  dropR.symm_apply_eq.mpr (dropR_inr_succ j).symm

/-- Insert the marked slot `inr 0 ↦ output 0`, laying out the rest of `b` past output 0. -/
def insHatR (b : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    Fin (m + 1) ⊕ Fin (n + 1) ≃ Fin (m + 1 + (n + 1)) :=
  dropR.trans <| (Equiv.optionCongr b).trans <|
    (Equiv.optionCongr finSumFinEquiv).trans (finSuccEquiv' 0).symm

theorem insHatR_inr_zero (b : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    insHatR b (Sum.inr 0) = 0 := by
  simp only [insHatR, Equiv.trans_apply, dropR_inr_zero, Equiv.optionCongr_apply, Option.map_none]
  exact fse0_symm_none

theorem insHatR_inl (b : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) (i : Fin (m + 1)) :
    insHatR b (Sum.inl i) = (finSumFinEquiv (b (Sum.inl i))).succ := by
  simp only [insHatR, Equiv.trans_apply, dropR_inl, Equiv.optionCongr_apply, Option.map_some]
  exact fse0_symm_some _

theorem insHatR_inr_succ (b : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) (j : Fin n) :
    insHatR b (Sum.inr j.succ) = (finSumFinEquiv (b (Sum.inr j))).succ := by
  simp only [insHatR, Equiv.trans_apply, dropR_inr_succ, Equiv.optionCongr_apply, Option.map_some]
  exact fse0_symm_some _

/-- Right-block insertion as a permutation. -/
def insPermR (b : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)) :=
  (insHatR b).trans finSumFinEquiv.symm

theorem insPermR_inr_zero (b : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    insPermR b (Sum.inr 0) = Sum.inl 0 := by
  rw [insPermR, Equiv.trans_apply, insHatR_inr_zero, Equiv.symm_apply_eq]
  apply Fin.ext; simp

/- ---- sign of insPermR ---- -/

/-- The within-block conjugate of `b` used to factor `insPermR b = insPermR 1 * liftR b`. -/
def liftR (b : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)) :=
  dropR.trans ((Equiv.optionCongr b).trans dropR.symm)

theorem insPermR_eq_mul (b : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    insPermR b = insPermR 1 * liftR b := by
  ext x
  simp only [insPermR, liftR, insHatR, Equiv.Perm.mul_apply, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.optionCongr_apply, Equiv.Perm.coe_one, Option.map_id, id_eq]

theorem sign_liftR (b : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    Equiv.Perm.sign (liftR b) = Equiv.Perm.sign b := by
  rw [Equiv.Perm.sign_eq_sign_of_equiv (liftR b) (Equiv.optionCongr b) dropR ?_,
    Equiv.optionCongr_sign]
  intro x
  simp only [liftR, Equiv.trans_apply, Equiv.apply_symm_apply]

theorem sign_insPermR_one :
    Equiv.Perm.sign (insPermR (1 : Equiv.Perm (Fin (m + 1) ⊕ Fin n))) = (-1) ^ (m + 1) := by
  have hlt : m + 1 < m + 1 + (n + 1) := by omega
  set c : Fin (m + 1 + (n + 1)) := ⟨m + 1, hlt⟩ with hc
  have hsign : Equiv.Perm.sign (insPermR (1 : Equiv.Perm (Fin (m + 1) ⊕ Fin n)))
      = Equiv.Perm.sign (Fin.cycleRange c) := by
    refine Equiv.Perm.sign_eq_sign_of_equiv (insPermR 1) (Fin.cycleRange c) finSumFinEquiv ?_
    intro x
    have hfin : finSumFinEquiv (insPermR 1 x) = insHatR 1 x := by
      rw [insPermR, Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [hfin]
    rcases x with i | j
    · rw [insHatR_inl, Equiv.Perm.one_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_left]
      have hji : Fin.castAdd (n + 1) i < c := by
        rw [Fin.lt_iff_val_lt_val]; simp only [Fin.coe_castAdd, hc]; omega
      rw [Fin.cycleRange_of_lt hji, ← Fin.castSucc_castAdd, Fin.coeSucc_eq_succ]
    · induction j using Fin.cases with
      | zero =>
        rw [insHatR_inr_zero, finSumFinEquiv_apply_right]
        have heq : Fin.natAdd (m + 1) (0 : Fin (n + 1)) = c := by
          apply Fin.ext; simp only [Fin.coe_natAdd, hc, Fin.val_zero, Nat.add_zero]
        rw [Fin.cycleRange_of_eq heq]
      | succ k =>
        rw [insHatR_inr_succ, Equiv.Perm.one_apply, finSumFinEquiv_apply_right,
          finSumFinEquiv_apply_right]
        have hgt : c < Fin.natAdd (m + 1) k.succ := by
          rw [Fin.lt_iff_val_lt_val]; simp only [Fin.coe_natAdd, Fin.val_succ, hc]; omega
        rw [Fin.cycleRange_of_gt hgt]
        apply Fin.ext
        simp only [Fin.val_succ, Fin.coe_natAdd]
        omega
  rw [hsign, Fin.sign_cycleRange]

theorem sign_insPermR (b : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    Equiv.Perm.sign (insPermR b) = (-1) ^ (m + 1) * Equiv.Perm.sign b := by
  rw [insPermR_eq_mul, map_mul, sign_insPermR_one, sign_liftR]

/- ---- Part B term identity ---- -/

theorem finSumFinEquiv_insPermR (b : Equiv.Perm (Fin (m + 1) ⊕ Fin n))
    (s : Fin (m + 1) ⊕ Fin (n + 1)) : finSumFinEquiv (insPermR b s) = insHatR b s := by
  rw [insPermR, Equiv.trans_apply, Equiv.apply_symm_apply]

theorem wB_inl (b : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) (i : Fin (m + 1)) :
    finAddFlipAssoc (finSumFinEquiv (insPermR b (Sum.inl i)))
      = (finAddFlipAssoc (finSumFinEquiv (b (Sum.inl i)))).succ := by
  apply Fin.ext
  rw [finSumFinEquiv_insPermR, insHatR_inl]
  simp only [finAddFlipAssoc, finCongr_apply, Fin.coe_cast, Fin.val_succ]

theorem wB_inr_zero (b : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    finAddFlipAssoc (finSumFinEquiv (insPermR b (Sum.inr 0))) = 0 := by
  apply Fin.ext
  rw [finSumFinEquiv_insPermR, insHatR_inr_zero]
  simp only [finAddFlipAssoc, finCongr_apply, Fin.coe_cast, Fin.val_zero]

theorem wB_inr_succ (b : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) (k : Fin n) :
    finAddFlipAssoc (finSumFinEquiv (insPermR b (Sum.inr k.succ)))
      = (finAddFlipAssoc (finSumFinEquiv (b (Sum.inr k)))).succ := by
  apply Fin.ext
  rw [finSumFinEquiv_insPermR, insHatR_inr_succ]
  simp only [finAddFlipAssoc, finCongr_apply, Fin.coe_cast, Fin.val_succ]

theorem claim_g_B (b : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) (x₀ : E) (y : Fin (m + (n + 1)) → E) :
    (fun i => ((Fin.cons x₀ y ∘ ⇑finAddFlipAssoc) ∘ ⇑finSumFinEquiv) (insPermR b (Sum.inl i)))
      = (fun i => ((y ∘ ⇑finAddFlipAssoc) ∘ ⇑finSumFinEquiv) (b (Sum.inl i))) := by
  funext i
  simp only [Function.comp_apply]
  rw [wB_inl, Fin.cons_succ]

theorem claim_h_B (b : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) (x₀ : E) (y : Fin (m + (n + 1)) → E) :
    (fun j => ((Fin.cons x₀ y ∘ ⇑finAddFlipAssoc) ∘ ⇑finSumFinEquiv) (insPermR b (Sum.inr j)))
      = (Fin.cons x₀ (fun k => ((y ∘ ⇑finAddFlipAssoc) ∘ ⇑finSumFinEquiv) (b (Sum.inr k))) : Fin _ → E) := by
  funext j
  simp only [Function.comp_apply]
  induction j using Fin.cases with
  | zero => rw [wB_inr_zero, Fin.cons_zero, Fin.cons_zero]
  | succ k => rw [wB_inr_succ, Fin.cons_succ, Fin.cons_succ]

theorem summandB (g : E [⋀^Fin (m + 1)]→L[𝕜] N) (h : E [⋀^Fin (n + 1)]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') (x₀ : E) (y : Fin (m + (n + 1)) → E)
    (b : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    uncurrySum.summand (f.compContinuousAlternatingMap₂ g h) (Quotient.mk'' (insPermR b))
        ((Fin.cons x₀ y ∘ ⇑finAddFlipAssoc) ∘ ⇑finSumFinEquiv)
      = (-1 : 𝕜) ^ (m + 1) • uncurrySum.summand (f.compContinuousAlternatingMap₂ g (curryFin h x₀))
        (Quotient.mk'' b) ((y ∘ ⇑finAddFlipAssoc) ∘ ⇑finSumFinEquiv) := by
  rw [summand_mk_eval, summand_mk_eval,
    ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    ContinuousLinearMap.compContinuousAlternatingMap₂_apply, curryFin_apply,
    claim_g_B, claim_h_B, sign_insPermR, mul_smul]
  rw [Units.smul_def ((-1 : ℤˣ) ^ (m + 1)), Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    ← Int.cast_smul_eq_zsmul 𝕜, Int.cast_pow, Int.cast_neg, Int.cast_one]

/- ---- Part B descent + injectivity ---- -/

theorem insPermR_mul_sumCongr (b : Equiv.Perm (Fin (m + 1) ⊕ Fin n))
    (sl : Equiv.Perm (Fin (m + 1))) (sr : Equiv.Perm (Fin n)) :
    insPermR (b * Equiv.sumCongr sl sr)
      = insPermR b * Equiv.sumCongr sl (Equiv.Perm.decomposeFin.symm (0, sr)) := by
  ext z
  rw [Equiv.Perm.mul_apply, insPermR, Equiv.trans_apply, insPermR, Equiv.trans_apply]
  congr 1
  rcases z with i | j
  · rw [Equiv.sumCongr_apply, Sum.map_inl, insHatR_inl, insHatR_inl, Equiv.Perm.mul_apply,
      Equiv.sumCongr_apply, Sum.map_inl]
  · induction j using Fin.cases with
    | zero =>
      rw [Equiv.sumCongr_apply, Sum.map_inr, Equiv.Perm.decomposeFin_symm_apply_zero,
        insHatR_inr_zero, insHatR_inr_zero]
    | succ k =>
      rw [Equiv.sumCongr_apply, Sum.map_inr, Equiv.Perm.decomposeFin_symm_apply_succ,
        Equiv.swap_self, Equiv.refl_apply, insHatR_inr_succ, insHatR_inr_succ, Equiv.Perm.mul_apply,
        Equiv.sumCongr_apply, Sum.map_inr]

open Equiv.Perm in
theorem projR_spec (a b : Equiv.Perm (Fin (m + 1) ⊕ Fin n))
    (h : (QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range) a b) :
    (Quot.mk (⇑(QuotientGroup.leftRel (sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range))
        (insPermR a)) =
      (Quot.mk (⇑(QuotientGroup.leftRel (sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range))
        (insPermR b)) := by
  apply Quot.sound
  rw [QuotientGroup.leftRel_apply] at h ⊢
  obtain ⟨⟨sl, sr⟩, hb⟩ := h
  simp only [sumCongrHom_apply, MonoidHom.coe_mk, OneHom.coe_mk] at hb
  have hbb : b = a * Equiv.sumCongr sl sr := by
    rw [show Equiv.sumCongr sl sr = sl.sumCongr sr from rfl, hb, mul_inv_cancel_left]
  rw [hbb, insPermR_mul_sumCongr]
  refine ⟨(sl, Equiv.Perm.decomposeFin.symm (0, sr)), ?_⟩
  simp only [sumCongrHom_apply]
  group

/-- The descended right-block insertion `Q_B → Q`. -/
def projR (q : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) :
    Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin (n + 1)) :=
  Quotient.liftOn' q (fun b => Quotient.mk'' (insPermR b)) projR_spec

@[simp] theorem projR_mk (b : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    projR (Quotient.mk'' b) = Quotient.mk'' (insPermR b) := rfl

theorem insHatR_injective (b : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    Function.Injective (insHatR b) := (insHatR b).injective

theorem insPermR_left_injective :
    Function.Injective (insPermR : Equiv.Perm (Fin (m + 1) ⊕ Fin n) → _) := by
  intro b₁ b₂ h
  have h' : insHatR b₁ = insHatR b₂ := by
    have := congrArg (fun e => e.trans finSumFinEquiv) h
    simpa only [insPermR, Equiv.symm_trans_self, Equiv.trans_refl, Equiv.trans_assoc] using this
  ext z
  rcases z with i | j
  · have := Equiv.congr_fun h' (Sum.inl i)
    rw [insHatR_inl, insHatR_inl] at this
    exact finSumFinEquiv.injective (Fin.succ_injective _ this)
  · have := Equiv.congr_fun h' (Sum.inr j.succ)
    rw [insHatR_inr_succ, insHatR_inr_succ] at this
    exact finSumFinEquiv.injective (Fin.succ_injective _ this)

theorem projR_left_injective (b₁ b₂ : Equiv.Perm (Fin (m + 1) ⊕ Fin n))
    (h : Quotient.mk'' (insPermR b₁) =
      (Quotient.mk'' (insPermR b₂) : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin (n + 1)))) :
    (Quotient.mk'' b₁ : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) = Quotient.mk'' b₂ := by
  rw [Quotient.eq'', QuotientGroup.leftRel_apply] at h
  obtain ⟨⟨sl, sr⟩, hsl⟩ := h
  simp only [Equiv.Perm.sumCongrHom_apply] at hsl
  have hmul : insPermR b₂ = insPermR b₁ * Equiv.sumCongr sl sr := by
    rw [show Equiv.sumCongr sl sr = sl.sumCongr sr from rfl, hsl, mul_inv_cancel_left]
  -- evaluating at `inr 0` forces `sr 0 = 0`
  have hsr0 : sr 0 = 0 := by
    have e2 : insPermR b₂ (Sum.inr 0) = Sum.inl 0 := insPermR_inr_zero b₂
    rw [hmul, Equiv.Perm.mul_apply, Equiv.sumCongr_apply, Sum.map_inr] at e2
    have e1 : insPermR b₁ (Sum.inr 0) = Sum.inl 0 := insPermR_inr_zero b₁
    exact Sum.inr_injective ((insPermR b₁).injective (e2.trans e1.symm))
  set sr' := (Equiv.Perm.decomposeFin sr).2 with hsr'def
  have hsr_eq : sr = Equiv.Perm.decomposeFin.symm (0, sr') := by
    have hsplit : sr = Equiv.Perm.decomposeFin.symm (Equiv.Perm.decomposeFin sr) := by
      rw [Equiv.symm_apply_apply]
    have hp : (Equiv.Perm.decomposeFin sr).1 = 0 := by
      have h0 : Equiv.Perm.decomposeFin.symm (Equiv.Perm.decomposeFin sr) 0 = sr 0 := by
        rw [Equiv.symm_apply_apply]
      rw [Equiv.Perm.decomposeFin_symm_apply_zero] at h0
      rw [h0, hsr0]
    rw [hsplit]; congr 1; rw [← hp]
  rw [hsr_eq, ← insPermR_mul_sumCongr] at hmul
  have hb := insPermR_left_injective hmul
  rw [Quotient.eq'', QuotientGroup.leftRel_apply]
  exact ⟨(sl, sr'), by simp only [Equiv.Perm.sumCongrHom_apply]; rw [hb]; group⟩

/- ---- Part B surjectivity: restPermR ---- -/

/-- Remove the marked slot `inr 0`/output `0` from a `τ'` with `τ' (inr 0) = inl 0`. -/
def restOptR (τ' : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1))) :
    Option (Fin (m + 1) ⊕ Fin n) ≃ Option (Fin (m + 1 + n)) :=
  dropR.symm.trans (τ'.trans (finSumFinEquiv.trans (finSuccEquiv' 0)))

theorem restOptR_none {τ' : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1))}
    (hτ' : τ' (Sum.inr 0) = Sum.inl 0) : restOptR τ' none = none := by
  have hz : finSumFinEquiv (Sum.inl (0 : Fin (m + 1)) : Fin (m + 1) ⊕ Fin (n + 1)) = 0 := by
    apply Fin.ext; simp [finSumFinEquiv_apply_left]
  rw [restOptR, Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, dropR_symm_none, hτ', hz]
  exact finSuccEquiv'_at 0

def restHatR (τ' : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1))) :
    Fin (m + 1) ⊕ Fin n ≃ Fin (m + 1 + n) :=
  Equiv.removeNone (restOptR τ')

def restPermR (τ' : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1))) :
    Equiv.Perm (Fin (m + 1) ⊕ Fin n) :=
  (restHatR τ').trans finSumFinEquiv.symm

theorem finSumFinEquiv_restPermR (τ' : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (z : Fin (m + 1) ⊕ Fin n) : finSumFinEquiv (restPermR τ' z) = restHatR τ' z := by
  simp [restPermR]

theorem succ_restHatR (τ' : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hτ' : τ' (Sum.inr 0) = Sum.inl 0) (z : Fin (m + 1) ⊕ Fin n) :
    (restHatR τ' z).succ = finSumFinEquiv (τ' (Sum.map id Fin.succ z)) := by
  have hex : ∃ p, restOptR τ' (some z) = some p := by
    rcases h : restOptR τ' (some z) with _ | p
    · exact absurd ((restOptR τ').injective (h.trans (restOptR_none hτ').symm)) (by simp)
    · exact ⟨p, rfl⟩
  have hsome : some (restHatR τ' z) = restOptR τ' (some z) := Equiv.removeNone_some _ hex
  have hz : dropR.symm (some z) = Sum.map id Fin.succ z := by rcases z with k | j <;> simp
  rw [restOptR, Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, hz] at hsome
  apply (finSuccEquiv' (0 : Fin (m + 1 + n + 1))).injective
  rw [fse0_succ]
  exact hsome

theorem insPermR_restPermR (τ' : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hτ' : τ' (Sum.inr 0) = Sum.inl 0) : insPermR (restPermR τ') = τ' := by
  ext z
  rw [insPermR, Equiv.trans_apply, Equiv.symm_apply_eq]
  rcases z with i | j
  · rw [insHatR_inl, finSumFinEquiv_restPermR, succ_restHatR τ' hτ', Sum.map_inl, id]
  · induction j using Fin.cases with
    | zero =>
      rw [insHatR_inr_zero, hτ']
      apply Fin.ext; simp [finSumFinEquiv_apply_left]
    | succ k =>
      rw [insHatR_inr_succ, finSumFinEquiv_restPermR, succ_restHatR τ' hτ', Sum.map_inr]

/- ---- Identity 2 (Part B) ---- -/
theorem identityB (g : E [⋀^Fin (m + 1)]→L[𝕜] N) (h : E [⋀^Fin (n + 1)]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') (x₀ : E) (y : Fin (m + (n + 1)) → E) :
    (-1 : 𝕜) ^ (m + 1) • ∑ b : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n),
        uncurrySum.summand (f.compContinuousAlternatingMap₂ g (curryFin h x₀)) b
          ((y ∘ ⇑finAddFlipAssoc) ∘ ⇑finSumFinEquiv)
      = ∑ σ ∈ Finset.univ.filter (fun q => ¬ isLeftClass q = true),
        uncurrySum.summand (f.compContinuousAlternatingMap₂ g h) σ
          ((Fin.cons x₀ y ∘ ⇑finAddFlipAssoc) ∘ ⇑finSumFinEquiv) := by
  rw [Finset.smul_sum]
  refine Finset.sum_bij (fun b _ => projR b) ?_ ?_ ?_ ?_
  · -- maps into right-classes
    intro a _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    induction a using Quotient.inductionOn' with
    | _ b =>
      have key : (insPermR b)⁻¹ (Sum.inl 0) = Sum.inr 0 := by
        rw [Equiv.Perm.inv_eq_iff_eq]; exact (insPermR_inr_zero b).symm
      simp only [projR_mk, isLeftClass, Quotient.liftOn'_mk'', key, Sum.isLeft_inr,
        Bool.false_eq_true, not_false_eq_true]
  · -- injective
    intro a₁ _ a₂ _ heq
    induction a₁ using Quotient.inductionOn' with
    | _ b₁ =>
    induction a₂ using Quotient.inductionOn' with
    | _ b₂ =>
      simp only [projR_mk] at heq
      exact projR_left_injective b₁ b₂ heq
  · -- surjective onto right-classes
    intro c hc
    rw [Finset.mem_filter] at hc
    induction c using Quotient.inductionOn' with
    | _ τ =>
      rcases h0 : τ⁻¹ (Sum.inl 0) with i₀ | j₀
      · exfalso
        have hc2 := hc.2
        simp only [isLeftClass, Quotient.liftOn'_mk'', h0, Sum.isLeft_inl, not_true_eq_false] at hc2
      · set τ' := τ * Equiv.sumCongr (Equiv.refl (Fin (m + 1))) j₀.cycleRange.symm with hτ'def
        have hτ' : τ' (Sum.inr 0) = Sum.inl 0 := by
          rw [hτ'def, Equiv.Perm.mul_apply, Equiv.sumCongr_apply, Sum.map_inr,
            Fin.cycleRange_symm_zero, ← h0, Equiv.Perm.apply_inv_self]
        refine ⟨Quotient.mk'' (restPermR τ'), Finset.mem_univ _, ?_⟩
        simp only [projR_mk]
        rw [insPermR_restPermR τ' hτ', hτ'def, Quotient.eq'', QuotientGroup.leftRel_apply]
        refine ⟨(Equiv.refl (Fin (m + 1)), j₀.cycleRange), ?_⟩
        simp only [Equiv.Perm.sumCongrHom_apply]
        have hg : (τ * Equiv.sumCongr (Equiv.refl (Fin (m + 1))) j₀.cycleRange.symm)⁻¹ * τ
            = (Equiv.sumCongr (Equiv.refl (Fin (m + 1))) j₀.cycleRange.symm)⁻¹ := by group
        rw [hg, Equiv.Perm.inv_def, Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.symm_symm]
  · -- term identity
    intro a _
    induction a using Quotient.inductionOn' with
    | _ b => simp only [projR_mk]; exact (summandB g h f x₀ y b).symm

/- ===================== Assembly: curryFin_wedge ===================== -/
theorem curryFin_wedge (g : E [⋀^Fin (m + 1)]→L[𝕜] N) (h : E [⋀^Fin (n + 1)]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') (x₀ : E) :
    curryFin (domDomCongr finAddFlipAssoc (wedge_product g h f)) x₀ =
      wedge_product (curryFin g x₀) h f
      + (-1 : 𝕜) ^ (m + 1) • domDomCongr finAddFlipAssoc (wedge_product g (curryFin h x₀) f) := by
  ext y
  rw [curryFin_apply, domDomCongr_apply, wedge_product_apply_sum]
  show _ = (wedge_product (curryFin g x₀) h f) y
      + ((-1 : 𝕜) ^ (m + 1) • domDomCongr finAddFlipAssoc (wedge_product g (curryFin h x₀) f)) y
  rw [smul_apply, domDomCongr_apply, wedge_product_apply_sum, wedge_product_apply_sum,
    identityA, identityB]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

end commute

end ContinuousAlternatingMap
