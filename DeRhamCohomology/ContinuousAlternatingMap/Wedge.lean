import Mathlib.Analysis.NormedSpace.Alternating.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.Mul
import DeRhamCohomology.ContinuousAlternatingMap.Curry
import DeRhamCohomology.Alternating.Basic
import DeRhamCohomology.Equiv.Fin
import Mathlib.Algebra.GroupWithZero.Defs
import Init.Grind.Lemmas

noncomputable section
suppress_compilation

namespace ContinuousAlternatingMap

section wedge

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {M'' : Type*} [NormedAddCommGroup M''] [NormedSpace 𝕜 M'']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {m n p : ℕ}

/-- The wedge product of two continuous alternating maps `g` an `h` with respect to a
bilinear map `f`. -/
def wedge_product (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') : M [⋀^Fin (m + n)]→L[𝕜] N'' :=
  uncurryFinAdd (f.compContinuousAlternatingMap₂ g h)

-- TODO: change notation
notation g "∧["f"]" h => wedge_product g h f
notation g "∧["𝕜"]" h => wedge_product g h (ContinuousLinearMap.mul 𝕜 𝕜)

theorem wedge_product_def {g : M [⋀^Fin m]→L[𝕜] N} {h : M [⋀^Fin n]→L[𝕜] N'}
    {f : N →L[𝕜] N' →L[𝕜] N''} {x : Fin (m + n) → M}:
    (g ∧[f] h) x = uncurryFinAdd (f.compContinuousAlternatingMap₂ g h) x :=
  rfl

/- The wedge product wrt multiplication -/
theorem wedge_product_mul {g : M [⋀^Fin m]→L[𝕜] 𝕜} {h : M [⋀^Fin n]→L[𝕜] 𝕜} {x : Fin (m + n) → M} :
    (g ∧[ContinuousLinearMap.mul 𝕜 𝕜] h) x = uncurryFinAdd ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) x :=
  rfl

/- The wedge product wrt scalar multiplication -/
theorem wedge_product_lsmul {g : M [⋀^Fin m]→L[𝕜] 𝕜} {h : M [⋀^Fin n]→L[𝕜] N} {x : Fin (m + n) → M} :
    (g ∧[ContinuousLinearMap.lsmul 𝕜 𝕜] h) x = uncurryFinAdd ((ContinuousLinearMap.lsmul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) x :=
  rfl

@[simps!]
def addAssocPerm : Equiv.Perm ((Fin m ⊕ Fin n) ⊕ Fin p) ≃ Equiv.Perm (Fin m ⊕ Fin n ⊕ Fin p) :=
    Equiv.permCongr (Equiv.sumAssoc (Fin m) (Fin n) (Fin p))

@[simp]
lemma addAssocPerm_symm_addAssocPerm (σ₁ : Equiv.Perm ((Fin m ⊕ Fin n) ⊕ Fin p)) :
    addAssocPerm.symm (addAssocPerm σ₁) = σ₁ := by
  exact Equiv.symm_apply_apply addAssocPerm σ₁

-- open Equiv.Perm in
-- lemma addAssocPerm_spec (a b : Equiv.Perm ((Fin m ⊕ Fin n) ⊕ Fin p))
--     (h : (QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m ⊕ Fin n) (Fin p)).range) a b) :
--     (Quot.mk (QuotientGroup.leftRel (sumCongrHom (Fin n) (Fin m)).range) ∘ addAssocPerm) a =
--       (Quot.mk (QuotientGroup.leftRel (sumCongrHom (Fin n) (Fin m)).range) ∘ addAssocPerm) b := by
--   apply Quot.sound
--   rw [@QuotientGroup.leftRel_apply] at h ⊢
--   simp only [sumCommPerm, Equiv.permCongr_def]
--   rw [inv_def, mul_def]
--   sorry

@[simp]
lemma sign_addAssocPerm (σ₁ : Equiv.Perm ((Fin m ⊕ Fin n) ⊕ Fin p)) :
    Equiv.Perm.sign (addAssocPerm σ₁) = Equiv.Perm.sign σ₁ := by
  simp only [addAssocPerm, Equiv.Perm.sign_permCongr]

-- open Equiv.Perm in
-- @[simps!]
-- def finAssoc_equiv : ModSumCongr (Fin (m + n)) (Fin p) ≃ ModSumCongr (Fin m) (Fin (n + p)) where
--   toFun := Quot.lift (Quot.mk _ ∘ addAssocPerm) _
--   invFun := Quot.lift (Quot.mk _ ∘ addAssocPerm) _
--   left_inv := by
--     intro x
--     rcases x with ⟨σ₁⟩
--     simp
--   right_inv := by
--     intro x
--     rcases x with ⟨σ₁⟩
--     simp

/- Associativity of multiplication wedge product -/
theorem wedge_mul_assoc (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) (v : Fin (m + n + p) → M):
    ContinuousAlternatingMap.domDomCongr finAssoc.symm (g ∧[𝕜] h ∧[𝕜] l) v = ((g ∧[𝕜] h) ∧[𝕜] l) v := by
  rw[wedge_product_def, uncurryFinAdd, domDomCongr_apply, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply,
    uncurrySum_apply, ContinuousMultilinearMap.sum_apply]
  rw[wedge_product, wedge_product]
  rw[uncurryFinAdd, uncurryFinAdd]
  -- Want to have functionality to partially unpack
  sorry

/- Left distributivity of wedge product -/
theorem add_wedge (g₁ g₂ : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') :
    ((g₁ + g₂) ∧[f] h) = (g₁ ∧[f] h) + (g₂ ∧[f] h) := by
  ext x
  rw[add_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  repeat
    rw[uncurrySum.summand_mk]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
      Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
      coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
      ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw[← smul_add, add_apply, map_add, ContinuousLinearMap.add_apply, smul_add]

/- Right distributivity of wedge product -/
theorem wedge_add (g : M [⋀^Fin m]→L[𝕜] N) (h₁ h₂ : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') :
    (g ∧[f] (h₁ + h₂)) = (g ∧[f] h₁) + (g ∧[f] h₂) := by
  ext x
  rw[add_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  repeat
    rw[uncurrySum.summand_mk]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
      Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
      coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
      ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw[add_apply, map_add, smul_add]

theorem smul_wedge (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) (c : 𝕜) :
    c • (g ∧[𝕜] h) = (c • g) ∧[𝕜] h := by
  ext x
  rw[smul_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, Finset.smul_sum]
  rw[wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  rw[uncurrySum.summand_mk]
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    ContinuousLinearMap.compContinuousAlternatingMap₂_apply, ContinuousLinearMap.mul_apply', ← smul_assoc,
    smul_comm]
  rw[smul_assoc, smul_eq_mul, ← mul_assoc]
  rw[uncurrySum.summand_mk]
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    ContinuousLinearMap.compContinuousAlternatingMap₂_apply, ContinuousLinearMap.mul_apply', ← smul_assoc,
    smul_comm, smul_apply, smul_eq_mul]

theorem wedge_smul (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) (c : 𝕜) :
    c • (g ∧[𝕜] h) = g ∧[𝕜] (c • h) := by
  ext x
  rw[smul_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, Finset.smul_sum]
  rw[wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  rw[uncurrySum.summand_mk]
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    ContinuousLinearMap.compContinuousAlternatingMap₂_apply, ContinuousLinearMap.mul_apply', ← smul_assoc,
    smul_comm]
  rw[smul_assoc, smul_eq_mul, ← mul_assoc]
  rw[uncurrySum.summand_mk]
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    ContinuousLinearMap.compContinuousAlternatingMap₂_apply, ContinuousLinearMap.mul_apply', ← smul_assoc,
    smul_comm, smul_apply, smul_eq_mul, ← mul_assoc, mul_comm]

def finAddCongr : Fin (m + n) ≃ Fin (n + m) := finCongr (add_comm m n)

@[simp]
lemma finAddCongr_finAddCongr (i : Fin (m + n)) :
    finAddCongr (finAddCongr i) = i :=
  rfl

@[simp]
lemma finAddCongr_symm_finAddCongr_symm (i : Fin (m + n)) :
    finAddCongr.symm (finAddCongr.symm i) = i :=
  rfl

def finSumCongr : Fin m ⊕ Fin n ≃ Fin n ⊕ Fin m :=
  Equiv.sumComm (Fin m) (Fin n)

def addCongrPerm : Equiv.Perm (Fin (m + n)) ≃ Equiv.Perm (Fin (n + m)) :=
  Equiv.permCongr finAddCongr

def sumCongrPerm : Equiv.Perm (Fin m ⊕ Fin n) ≃ Equiv.Perm (Fin n ⊕ Fin m) :=
  Equiv.permCongr finSumCongr

@[simp]
lemma sumCongrPerm_sumCongrPerm (σ₁ : Equiv.Perm (Fin m ⊕ Fin n)) :
    sumCongrPerm (sumCongrPerm σ₁) = σ₁ := by
  ext i
  simp [sumCongrPerm, finSumCongr]

open Equiv.Perm in
lemma sumCongrPerm_spec (a b : Equiv.Perm (Fin m ⊕ Fin n))
    (h : (QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range) a b) :
    (Quot.mk (QuotientGroup.leftRel (sumCongrHom (Fin n) (Fin m)).range) ∘ sumCongrPerm) a =
      (Quot.mk (QuotientGroup.leftRel (sumCongrHom (Fin n) (Fin m)).range) ∘ sumCongrPerm) b := by
  apply Quot.sound
  rw [@QuotientGroup.leftRel_apply] at h ⊢
  simp only [sumCongrPerm, finSumCongr, Equiv.permCongr_def]
  rw [inv_def, mul_def]
  simp at h
  rcases h with ⟨ σ, τ, h ⟩
  simp
  use τ , σ
  ext (x | y)
  · simp
    apply_fun (fun f => f (Sum.inr x)) at h
    simp [inv_def] at h
    rw[← h]; rfl
  · simp
    apply_fun (fun f => f (Sum.inl y)) at h
    simp [inv_def] at h
    rw[← h]; rfl

@[simp]
lemma sign_sumCongrPerm (σ₁ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Equiv.Perm.sign (sumCongrPerm σ₁) = Equiv.Perm.sign σ₁ := by
  simp only [sumCongrPerm, Equiv.Perm.sign_permCongr]

open Equiv.Perm in
@[simps!]
def finAddCongr_equiv : ModSumCongr (Fin m) (Fin n) ≃ ModSumCongr (Fin n) (Fin m) where
  toFun := Quot.lift (Quot.mk _ ∘ sumCongrPerm) sumCongrPerm_spec
  invFun := Quot.lift (Quot.mk _ ∘ sumCongrPerm) sumCongrPerm_spec
  left_inv := by
    intro x
    rcases x with ⟨σ₁⟩
    simp
  right_inv := by
    intro x
    rcases x with ⟨σ₁⟩
    simp

@[simps!]
def sumCommPerm : Equiv.Perm (Fin m ⊕ Fin n) ≃ Equiv.Perm (Fin n ⊕ Fin m) :=
  Equiv.permCongr (Equiv.sumComm (Fin m) (Fin n))

@[simp]
lemma sumCommPerm_sumCommPerm (σ₁ : Equiv.Perm (Fin m ⊕ Fin n)) :
    sumCommPerm (sumCommPerm σ₁) = σ₁ := by
  ext i
  simp

open Equiv.Perm in
lemma sumCommPerm_spec (a b : Equiv.Perm (Fin m ⊕ Fin n))
    (h : (QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range) a b) :
    (Quot.mk (QuotientGroup.leftRel (sumCongrHom (Fin n) (Fin m)).range) ∘ sumCommPerm) a =
      (Quot.mk (QuotientGroup.leftRel (sumCongrHom (Fin n) (Fin m)).range) ∘ sumCommPerm) b := by
  apply Quot.sound
  rw [@QuotientGroup.leftRel_apply] at h ⊢
  simp only [sumCommPerm, Equiv.permCongr_def]
  rw [inv_def, mul_def]
  simp at h
  rcases h with ⟨ σ, τ, h ⟩
  simp
  use τ , σ
  ext (x | y)
  · simp
    apply_fun (fun f => f (Sum.inr x)) at h
    simp [inv_def] at h
    rw[← h]
    rfl
  · simp
    apply_fun (fun f => f (Sum.inl y)) at h
    simp [inv_def] at h
    rw[← h]
    rfl

@[simp]
lemma sign_sumCommPerm (σ₁ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Equiv.Perm.sign (sumCommPerm σ₁) = Equiv.Perm.sign σ₁ := by
  simp only [sumCommPerm, Equiv.Perm.sign_permCongr]

open Equiv.Perm in
@[simps!]
def finAddFlip_equiv : ModSumCongr (Fin m) (Fin n) ≃ ModSumCongr (Fin n) (Fin m) where
  toFun := Quot.lift (Quot.mk _ ∘ sumCommPerm) sumCommPerm_spec
  invFun := Quot.lift (Quot.mk _ ∘ sumCommPerm) sumCommPerm_spec
  left_inv := by
    intro x
    rcases x with ⟨σ₁⟩
    simp
  right_inv := by
    intro x
    rcases x with ⟨σ₁⟩
    simp

lemma finRotate_pow_apply {N : ℕ} [NeZero N] (k : ℕ) (i : Fin N) :
    ((finRotate N) ^ k) i = i + (k : Fin N) := by
  induction k with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    obtain ⟨N', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
    rw [finRotate_succ_apply]
    push_cast
    ring

lemma sign_finRotate_pow (n m : ℕ) :
    Equiv.Perm.sign ((finRotate (n+m)) ^ m) = (-1)^(m*n) := by
  rw [map_pow]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    rw [show n + (m'+1) = (n+m') + 1 by omega, sign_finRotate, ← pow_mul]
    apply neg_one_pow_congr
    rw [Nat.even_mul, Nat.even_mul, Nat.even_add, Nat.even_add_one]
    tauto

/-- The value-preserving relabelling `Fin m ⊕ Fin n ≃ Fin n ⊕ Fin m`, i.e. the conjugate of
`finAddCongr` by `finSumFinEquiv`. In contrast to `finSumCongr` (the block swap) this does not
map the `Fin m` block to the `Fin m` block. -/
def finSumAddCongr : Fin m ⊕ Fin n ≃ Fin n ⊕ Fin m :=
  finSumFinEquiv.trans (finAddCongr.trans finSumFinEquiv.symm)

/-- The block-rotation permutation of `Fin n ⊕ Fin m`: block swap followed by the
value-preserving relabelling. Conjugate to rotation by `m` on `Fin (n + m)`, hence of
sign `(-1)^(m*n)`. -/
def sumRotatePerm : Equiv.Perm (Fin n ⊕ Fin m) :=
  (Equiv.sumComm (Fin n) (Fin m)).trans finSumAddCongr

lemma sumRotatePerm_conj (x : Fin n ⊕ Fin m) :
    finSumFinEquiv (sumRotatePerm x) = ((finRotate (n+m))^m) (finSumFinEquiv x) := by
  rcases x with k | j
  · haveI : NeZero (n+m) := ⟨by have := k.2; omega⟩
    have hk : (k:ℕ) < n := k.2
    rw [finRotate_pow_apply]
    simp only [sumRotatePerm, finSumAddCongr, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inl,
      finSumFinEquiv_apply_right, finSumFinEquiv_apply_left, Equiv.apply_symm_apply]
    rw [Fin.ext_iff, Fin.val_add, Fin.val_natCast]
    simp only [finAddCongr, finCongr_apply, Fin.coe_cast, Fin.coe_natAdd, Fin.coe_castAdd]
    rw [Nat.mod_eq_of_lt (show m < n + m by omega),
      Nat.mod_eq_of_lt (show (k:ℕ) + m < n + m by omega)]
    omega
  · haveI : NeZero (n+m) := ⟨by have := j.2; omega⟩
    have hj : (j:ℕ) < m := j.2
    rw [finRotate_pow_apply]
    simp only [sumRotatePerm, finSumAddCongr, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inr,
      finSumFinEquiv_apply_right, finSumFinEquiv_apply_left, Equiv.apply_symm_apply]
    rw [Fin.ext_iff, Fin.val_add, Fin.val_natCast]
    simp only [finAddCongr, finCongr_apply, Fin.coe_cast, Fin.coe_natAdd, Fin.coe_castAdd]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [Nat.zero_add, Nat.mod_self, Nat.add_zero]
      rw [Nat.mod_eq_of_lt hj]
    · rw [Nat.mod_eq_of_lt (show m < n + m by omega),
        show n + (j:ℕ) + m = (n+m) + (j:ℕ) by omega, Nat.add_mod_left,
        Nat.mod_eq_of_lt (show (j:ℕ) < n + m by omega)]

@[simp]
lemma sign_sumRotatePerm : Equiv.Perm.sign (sumRotatePerm (m:=m) (n:=n)) = (-1)^(m*n) := by
  rw [Equiv.Perm.sign_eq_sign_of_equiv sumRotatePerm _ finSumFinEquiv sumRotatePerm_conj,
    sign_finRotate_pow]

open Equiv.Perm in
/-- The reindexing of `ModSumCongr` used in `wedge_antisymm`: the block swap `finAddFlip_equiv`
followed by left multiplication with the block rotation `sumRotatePerm`. On representatives it
sends `σ` to `sumRotatePerm * sumCommPerm σ`, which composes with `finAddCongr` to permute the
arguments of the two factors of the wedge product exactly. -/
def wedgeFlipEquiv : ModSumCongr (Fin m) (Fin n) ≃ ModSumCongr (Fin n) (Fin m) :=
  finAddFlip_equiv.trans (MulAction.toPerm (sumRotatePerm : Equiv.Perm (Fin n ⊕ Fin m)))

lemma wedgeFlipEquiv_mk (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    wedgeFlipEquiv (Quot.mk _ σ) = Quot.mk _ (sumRotatePerm * sumCommPerm σ) := by
  simp only [wedgeFlipEquiv, Equiv.trans_apply, finAddFlip_equiv_apply, Function.comp_apply,
    MulAction.toPerm_apply]
  exact MulAction.Quotient.smul_mk _ _ _

lemma wedgeFlip_arg_inl (σ : Equiv.Perm (Fin m ⊕ Fin n)) (k : Fin n) :
    finAddCongr (finSumFinEquiv
        ((sumRotatePerm * sumCommPerm σ : Equiv.Perm (Fin n ⊕ Fin m)) (Sum.inl k)))
      = finSumFinEquiv (σ (Sum.inr k)) := by
  simp only [Equiv.Perm.mul_apply, sumRotatePerm, finSumAddCongr, sumCommPerm, finSumCongr,
    Equiv.permCongr_apply, Equiv.trans_apply, Equiv.sumComm_apply, Equiv.sumComm_symm,
    Sum.swap_inl, Sum.swap_swap, Equiv.apply_symm_apply, finAddCongr_finAddCongr]

lemma wedgeFlip_arg_inr (σ : Equiv.Perm (Fin m ⊕ Fin n)) (j : Fin m) :
    finAddCongr (finSumFinEquiv
        ((sumRotatePerm * sumCommPerm σ : Equiv.Perm (Fin n ⊕ Fin m)) (Sum.inr j)))
      = finSumFinEquiv (σ (Sum.inl j)) := by
  simp only [Equiv.Perm.mul_apply, sumRotatePerm, finSumAddCongr, sumCommPerm, finSumCongr,
    Equiv.permCongr_apply, Equiv.trans_apply, Equiv.sumComm_apply, Equiv.sumComm_symm,
    Sum.swap_inr, Sum.swap_swap, Equiv.apply_symm_apply, finAddCongr_finAddCongr]

/- Antisymmetry of multiplication wedge product -/
theorem wedge_antisymm (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) :
    (g ∧[𝕜] h) = ((-1 : 𝕜)^(m*n) • (h ∧[𝕜] g)).domDomCongr finAddCongr := by
  ext x
  rw[domDomCongr_apply, smul_apply, wedge_product_mul, uncurryFinAdd, domDomCongr_apply,
    uncurrySum_apply, ContinuousMultilinearMap.sum_apply, wedge_product_mul,
    uncurryFinAdd, domDomCongr_apply, uncurrySum_apply, ContinuousMultilinearMap.sum_apply]
  conv_rhs => rw[← Equiv.sum_comp wedgeFlipEquiv]
  rw[Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  rw[wedgeFlipEquiv_mk]
  rw[uncurrySum.summand_mk]
  rw[ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    coe_toContinuousMultilinearMap, ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    ContinuousLinearMap.mul_apply']
  rw[uncurrySum.summand_mk]
  rw[ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    coe_toContinuousMultilinearMap, ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    ContinuousLinearMap.mul_apply']
  have harg1 : ((fun i => ((x ∘ ⇑finAddCongr) ∘ ⇑finSumFinEquiv)
        ((sumRotatePerm * sumCommPerm σ₁ : Equiv.Perm (Fin n ⊕ Fin m)) i)) ∘ Sum.inl)
      = ((fun i => (x ∘ ⇑finSumFinEquiv) (σ₁ i)) ∘ Sum.inr) :=
    funext fun k => congrArg x (wedgeFlip_arg_inl σ₁ k)
  have harg2 : ((fun i => ((x ∘ ⇑finAddCongr) ∘ ⇑finSumFinEquiv)
        ((sumRotatePerm * sumCommPerm σ₁ : Equiv.Perm (Fin n ⊕ Fin m)) i)) ∘ Sum.inr)
      = ((fun i => (x ∘ ⇑finSumFinEquiv) (σ₁ i)) ∘ Sum.inl) :=
    funext fun j => congrArg x (wedgeFlip_arg_inr σ₁ j)
  rw [harg1, harg2, map_mul, sign_sumRotatePerm, sign_sumCommPerm,
    mul_comm (h _) (g _), mul_smul]
  rw [Units.smul_def ((-1:ℤˣ)^(m*n)), Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, smul_eq_mul, ← mul_assoc,
    ← pow_add, Even.neg_one_pow ⟨m*n, rfl⟩, one_mul]

/-- General-`f` antisymmetry of the wedge product: swapping the two factors swaps the bilinear
pairing to its flip, costs the Koszul sign `(-1)^(m*n)`, and reindexes by `finAddCongr`.
This generalises `wedge_antisymm` from the scalar-multiplication pairing to an arbitrary `f`. -/
theorem wedge_flip (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') :
    (g ∧[f] h) = ((-1 : 𝕜) ^ (m * n) • (h ∧[f.flip] g)).domDomCongr finAddCongr := by
  ext x
  rw [domDomCongr_apply, smul_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply,
    uncurrySum_apply, ContinuousMultilinearMap.sum_apply, wedge_product_def,
    uncurryFinAdd, domDomCongr_apply, uncurrySum_apply, ContinuousMultilinearMap.sum_apply]
  conv_rhs => rw [← Equiv.sum_comp wedgeFlipEquiv]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  rw [wedgeFlipEquiv_mk]
  rw [uncurrySum.summand_mk]
  rw [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    coe_toContinuousMultilinearMap, ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw [uncurrySum.summand_mk]
  rw [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    coe_toContinuousMultilinearMap, ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  have harg1 : ((fun i => ((x ∘ ⇑finAddCongr) ∘ ⇑finSumFinEquiv)
        ((sumRotatePerm * sumCommPerm σ₁ : Equiv.Perm (Fin n ⊕ Fin m)) i)) ∘ Sum.inl)
      = ((fun i => (x ∘ ⇑finSumFinEquiv) (σ₁ i)) ∘ Sum.inr) :=
    funext fun k => congrArg x (wedgeFlip_arg_inl σ₁ k)
  have harg2 : ((fun i => ((x ∘ ⇑finAddCongr) ∘ ⇑finSumFinEquiv)
        ((sumRotatePerm * sumCommPerm σ₁ : Equiv.Perm (Fin n ⊕ Fin m)) i)) ∘ Sum.inr)
      = ((fun i => (x ∘ ⇑finSumFinEquiv) (σ₁ i)) ∘ Sum.inl) :=
    funext fun j => congrArg x (wedgeFlip_arg_inr σ₁ j)
  rw [harg1, harg2, ContinuousLinearMap.flip_apply, map_mul, sign_sumRotatePerm,
    sign_sumCommPerm, mul_smul]
  rw [Units.smul_def ((-1 : ℤˣ) ^ (m * n)), Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one, ← Int.cast_smul_eq_zsmul 𝕜, Int.cast_pow, Int.cast_neg, Int.cast_one, smul_smul,
    ← pow_add, Even.neg_one_pow ⟨m * n, rfl⟩, one_smul]

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]

-- UNUSED functionality
@[simps!]
def sumCommPerm_eqFin : Equiv.Perm (Fin m ⊕ Fin m) ≃ Equiv.Perm (Fin m ⊕ Fin m) :=
  MulAut.conj (Equiv.sumComm (Fin m) (Fin m))

-- UNUSED functionality
@[simp]
lemma sumComm_inv : (Equiv.sumComm (Fin m) (Fin m))⁻¹ = (Equiv.sumComm (Fin m) (Fin m)) := by
  ext i
  simp [Equiv.Perm.inv_def]

-- UNUSED functionality
@[simp]
lemma sumCommPerm_eqFin_sumCommPerm_eqFin (σ₁ : Equiv.Perm (Fin m ⊕ Fin m)) :
    sumCommPerm_eqFin (sumCommPerm_eqFin σ₁) = σ₁ := by
  ext i
  simp

-- UNUSED functionality
open Equiv.Perm in
lemma sumCommPerm_eqFin_spec (a b : Equiv.Perm (Fin m ⊕ Fin m))
    (h : (QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin m)).range) a b) :
    (Quot.mk (QuotientGroup.leftRel (sumCongrHom (Fin m) (Fin m)).range) ∘ sumCommPerm_eqFin) a =
      (Quot.mk (QuotientGroup.leftRel (sumCongrHom (Fin m) (Fin m)).range) ∘ sumCommPerm_eqFin) b := by
  apply Quot.sound
  rw [@QuotientGroup.leftRel_apply] at h ⊢
  simp only [sumCommPerm_eqFin, EquivLike.coe_coe, MulAut.conj_apply, sumComm_inv,
    mul_assoc, mul_inv_rev, sumCongrHom_apply, Prod.exists]
  have (c) : Equiv.sumComm (Fin m) (Fin m) * (Equiv.sumComm (Fin m) (Fin m) * c) = c := by
    ext
    simp [mul_def]
  rw[this]
  simp at h
  rcases h with ⟨σ, τ, h⟩
  rw[← mul_assoc _ b, ← h]
  simp
  use τ, σ
  ext (x|y) <;> simp

-- UNUSED functionality
@[simp]
lemma sign_sumCommPerm_eqFin (σ₁ : Equiv.Perm (Fin m ⊕ Fin m)) :
    Equiv.Perm.sign (sumCommPerm_eqFin σ₁) = Equiv.Perm.sign σ₁ := by
  simp [sumCommPerm_eqFin]
  rw[mul_comm, ← mul_assoc]
  simp

-- UNUSED functionality
open Equiv.Perm in
@[simps]
def finAddFlip_equiv_eqFin : ModSumCongr (Fin m) (Fin m) ≃ ModSumCongr (Fin m) (Fin m) where
  toFun := Quot.lift (Quot.mk _ ∘ sumCommPerm_eqFin) sumCommPerm_eqFin_spec
  invFun := Quot.lift (Quot.mk _ ∘ sumCommPerm_eqFin) sumCommPerm_eqFin_spec
  left_inv := by
    intro x
    rcases x with ⟨σ₁⟩
    simp
  right_inv := by
    intro x
    rcases x with ⟨σ₁⟩
    simp

-- UNUSED functionality
lemma domDomCongr_finAddFlip_wedge_self (g : M [⋀^Fin m]→L[ℝ] ℝ) :
    domDomCongr finAddFlip (g∧[ℝ]g) = (g∧[ℝ]g) := by
  ext x
  rw[wedge_product_mul, uncurryFinAdd, domDomCongr_apply, domDomCongr_apply, uncurrySum_apply, ContinuousMultilinearMap.sum_apply,
    wedge_product_mul, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply, ContinuousMultilinearMap.sum_apply]
  conv_rhs => rw[← Equiv.sum_comp finAddFlip_equiv_eqFin]
  apply Finset.sum_congr rfl
  rintro σ -
  rcases σ with ⟨σ₁⟩
  simp only [Function.comp_apply, finAddFlip_equiv_eqFin_apply]
  rw[uncurrySum.summand_mk]
  rw[uncurrySum.summand_mk]
  rw[ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    coe_toContinuousMultilinearMap, ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    ContinuousLinearMap.mul_apply']
  rw[ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    coe_toContinuousMultilinearMap, ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    ContinuousLinearMap.mul_apply']
  simp [Function.comp_def, finAddFlip, mul_comm]

/- Corollary of `wedge_antisymm` saying that a wedge of g with itself is
zero if m is odd. -/
theorem wedge_self_odd_zero (g : M [⋀^Fin m]→L[ℝ] ℝ) (m_odd : Odd m) :
    (g ∧[ℝ] g) = 0 := by
  let h := wedge_antisymm g g
  rw[Odd.neg_one_pow (Odd.mul m_odd m_odd)] at h
  suffices (g ∧[ℝ] g) = -(g ∧[ℝ] g) by
    rw[← sub_eq_zero, sub_neg_eq_add, DFunLike.ext_iff] at this
    ext x
    simpa using this x
  simp [finAddCongr] at h
  exact h

end wedge
