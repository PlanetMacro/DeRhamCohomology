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

end commute

end ContinuousAlternatingMap
