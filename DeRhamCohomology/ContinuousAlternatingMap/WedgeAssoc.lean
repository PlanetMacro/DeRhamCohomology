import DeRhamCohomology.ContinuousAlternatingMap.WedgeFDeriv

/-!
# Associativity of the wedge product

This file proves `wedge_mul_assoc`, the associativity of the (multiplication) wedge product on
continuous alternating maps, the thesis's Prop. 4.27 / §5.2.1.

The heart is `core_assoc`: an abstract associativity of the alternatization shuffle product over
arbitrary `Sum` index types, proved by exhibiting both nested shuffle sums as a single sum over the
triple Young quotient `T ι κ μ` via two fibrations (`lcore_eq_sumT`, `rcore_eq_sumT`). The two
`pullout` lemmas move the `finSumFinEquiv` reindexings out of the wedge factors, reducing the Fin
statement to `core_assoc` after the value-preserving recast reconciliation `eR3_eq_sumAssoc_eL3`.
-/

noncomputable section
suppress_compilation

namespace ContinuousAlternatingMap

open scoped BigOperators
open Equiv Equiv.Perm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {m n p : ℕ}

/-- Value-preserving linearization of the right-nested triple `Fin m ⊕ (Fin n ⊕ Fin p)`. -/
def eL3 : Fin m ⊕ (Fin n ⊕ Fin p) ≃ Fin (m + n + p) :=
  ((Equiv.sumCongr (Equiv.refl (Fin m)) finSumFinEquiv).trans finSumFinEquiv).trans finAssoc.symm

/-- Value-preserving linearization of the left-nested triple `(Fin m ⊕ Fin n) ⊕ Fin p`. -/
def eR3 : (Fin m ⊕ Fin n) ⊕ Fin p ≃ Fin (m + n + p) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin p))).trans finSumFinEquiv

@[simp] theorem eL3_inl (i : Fin m) : (eL3 (n := n) (p := p) (Sum.inl i) : ℕ) = i := by
  simp only [eL3, finAssoc, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply,
    finSumFinEquiv_apply_left, finCongr_symm, finCongr_apply, Fin.coe_cast, Fin.coe_castAdd]

@[simp] theorem eL3_inr_inl (j : Fin n) : (eL3 (m := m) (p := p) (Sum.inr (Sum.inl j)) : ℕ) = m + j := by
  simp only [eL3, finAssoc, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_symm, finCongr_apply,
    Fin.coe_cast, Fin.coe_natAdd, Fin.coe_castAdd]

@[simp] theorem eL3_inr_inr (k : Fin p) : (eL3 (m := m) (n := n) (Sum.inr (Sum.inr k)) : ℕ) = m + n + k := by
  simp only [eL3, finAssoc, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply,
    finSumFinEquiv_apply_right, finCongr_symm, finCongr_apply, Fin.coe_cast, Fin.coe_natAdd]
  omega

@[simp] theorem eR3_inl_inl (i : Fin m) : (eR3 (n := n) (p := p) (Sum.inl (Sum.inl i)) : ℕ) = i := by
  simp only [eR3, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left,
    Fin.coe_castAdd]

@[simp] theorem eR3_inl_inr (j : Fin n) : (eR3 (m := m) (p := p) (Sum.inl (Sum.inr j)) : ℕ) = m + j := by
  simp only [eR3, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    Equiv.refl_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.coe_castAdd,
    Fin.coe_natAdd]

@[simp] theorem eR3_inr (k : Fin p) : (eR3 (m := m) (n := n) (Sum.inr k) : ℕ) = m + n + k := by
  simp only [eR3, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply,
    finSumFinEquiv_apply_right, Fin.coe_natAdd]

/-- The two linearizations agree after `Equiv.sumAssoc`: `eR3 = sumAssoc.trans eL3`. -/
theorem eR3_eq_sumAssoc_eL3 :
    eR3 = (Equiv.sumAssoc (Fin m) (Fin n) (Fin p)).trans eL3 := by
  ext x
  rcases x with (i | j) | k
  · simp
  · simp
  · simp

/-! ### Abstract core: associativity of the alternatization shuffle over `Sum` index types -/

section core

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Applying a continuous alternating map to a permuted argument tuple picks up the sign. -/
theorem cam_apply_perm {ν : Type*} [Fintype ν] [DecidableEq ν]
    (a : E [⋀^ν]→L[𝕜] 𝕜) (w : ν → E) (s : Equiv.Perm ν) :
    a (w ∘ s) = Equiv.Perm.sign s • a w := by
  have h := a.toAlternatingMap.map_congr_perm (v := w) s
  have hcoe : ∀ x : ν → E, a.toAlternatingMap x = a x := fun _ => rfl
  rw [hcoe, hcoe] at h
  rw [h, smul_smul, Int.units_mul_self, one_smul]

/-- The Young subgroup hom: `(sι, sκ, sμ) ↦ sumCongr sι (sumCongr sκ sμ)`, embedding
`Perm ι × Perm κ × Perm μ` block-diagonally into `Perm (ι ⊕ κ ⊕ μ)`. -/
def youngHom (ι κ μ : Type*) :
    Equiv.Perm ι × Equiv.Perm κ × Equiv.Perm μ →* Equiv.Perm (ι ⊕ κ ⊕ μ) :=
  (Equiv.Perm.sumCongrHom ι (κ ⊕ μ)).comp
    ((MonoidHom.id (Equiv.Perm ι)).prodMap (Equiv.Perm.sumCongrHom κ μ))

@[simp] theorem youngHom_apply (sι : Equiv.Perm ι) (sκ : Equiv.Perm κ) (sμ : Equiv.Perm μ) :
    youngHom ι κ μ (sι, sκ, sμ) = Equiv.sumCongr sι (Equiv.sumCongr sκ sμ) := rfl

/-- Membership in the Young range is decidable (the lambda is needed for instance synthesis,
mirroring `Equiv.Perm.sumCongrHom.decidableMemRange`). -/
instance youngHom.decidableMemRange : DecidablePred (· ∈ (youngHom ι κ μ).range) :=
  fun _ => inferInstance

instance decidableMemRange_sumCongrHom_right :
    DecidablePred (· ∈ (Equiv.Perm.sumCongrHom ι (κ ⊕ μ)).range) := fun _ => inferInstance

instance decidableMemRange_sumCongrHom_left :
    DecidablePred (· ∈ (Equiv.Perm.sumCongrHom (ι ⊕ κ) μ).range) := fun _ => inferInstance

/-- The triple shuffle quotient: permutations of `ι ⊕ κ ⊕ μ` modulo block-diagonal relabellings. -/
abbrev T (ι κ μ : Type*) := Equiv.Perm (ι ⊕ κ ⊕ μ) ⧸ (youngHom ι κ μ).range

/-- The triple-shuffle summand at a representative `A`: the signed product `g·h·l`. -/
def ttermFun (a : E [⋀^ι]→L[𝕜] 𝕜) (b : E [⋀^κ]→L[𝕜] 𝕜) (c : E [⋀^μ]→L[𝕜] 𝕜)
    (v : ι ⊕ κ ⊕ μ → E) (A : Equiv.Perm (ι ⊕ κ ⊕ μ)) : 𝕜 :=
  Equiv.Perm.sign A •
    (a (fun i => v (A (Sum.inl i)))
      * b (fun j => v (A (Sum.inr (Sum.inl j))))
      * c (fun k => v (A (Sum.inr (Sum.inr k)))))

/-- `ttermFun` is invariant under right multiplication by the Young subgroup. -/
theorem ttermFun_young (a : E [⋀^ι]→L[𝕜] 𝕜) (b : E [⋀^κ]→L[𝕜] 𝕜) (c : E [⋀^μ]→L[𝕜] 𝕜)
    (v : ι ⊕ κ ⊕ μ → E) (A : Equiv.Perm (ι ⊕ κ ⊕ μ))
    (sι : Equiv.Perm ι) (sκ : Equiv.Perm κ) (sμ : Equiv.Perm μ) :
    ttermFun a b c v (A * Equiv.sumCongr sι (Equiv.sumCongr sκ sμ)) = ttermFun a b c v A := by
  have ha : (fun i => v ((A * Equiv.sumCongr sι (Equiv.sumCongr sκ sμ)) (Sum.inl i)))
      = (fun i => v (A (Sum.inl i))) ∘ sι := by
    funext i; simp [Equiv.Perm.mul_apply]
  have hb : (fun j => v ((A * Equiv.sumCongr sι (Equiv.sumCongr sκ sμ)) (Sum.inr (Sum.inl j))))
      = (fun j => v (A (Sum.inr (Sum.inl j)))) ∘ sκ := by
    funext j; simp [Equiv.Perm.mul_apply]
  have hc : (fun k => v ((A * Equiv.sumCongr sι (Equiv.sumCongr sκ sμ)) (Sum.inr (Sum.inr k))))
      = (fun k => v (A (Sum.inr (Sum.inr k)))) ∘ sμ := by
    funext k; simp [Equiv.Perm.mul_apply]
  rw [ttermFun, ttermFun, ha, hb, hc, cam_apply_perm, cam_apply_perm, cam_apply_perm, map_mul,
    Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_sumCongr]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  have hinv : ∀ u : ℤˣ, u⁻¹ = u := fun u => inv_eq_of_mul_eq_one_right (Int.units_mul_self u)
  have hkey : (Equiv.Perm.sign sι * (Equiv.Perm.sign sκ * Equiv.Perm.sign sμ)) *
      (Equiv.Perm.sign sμ * (Equiv.Perm.sign sκ * Equiv.Perm.sign sι)) = 1 := by
    rw [mul_eq_one_iff_eq_inv, mul_inv_rev, mul_inv_rev, hinv, hinv, hinv, mul_assoc]
  rw [mul_assoc (Equiv.Perm.sign A), hkey, mul_one]

/-- The triple-shuffle summand, descended to the quotient `T`. -/
def tterm (a : E [⋀^ι]→L[𝕜] 𝕜) (b : E [⋀^κ]→L[𝕜] 𝕜) (c : E [⋀^μ]→L[𝕜] 𝕜)
    (v : ι ⊕ κ ⊕ μ → E) : T ι κ μ → 𝕜 :=
  fun q => Quotient.liftOn' q (ttermFun a b c v) (by
    intro A₁ A₂ hA
    rw [QuotientGroup.leftRel_apply] at hA
    obtain ⟨⟨sι, sκ, sμ⟩, h⟩ := hA
    rw [youngHom_apply] at h
    have hA₂ : A₂ = A₁ * Equiv.sumCongr sι (Equiv.sumCongr sκ sμ) := by
      rw [h, mul_inv_cancel_left]
    rw [hA₂, ttermFun_young])

@[simp] theorem tterm_mk (a : E [⋀^ι]→L[𝕜] 𝕜) (b : E [⋀^κ]→L[𝕜] 𝕜) (c : E [⋀^μ]→L[𝕜] 𝕜)
    (v : ι ⊕ κ ⊕ μ → E) (A : Equiv.Perm (ι ⊕ κ ⊕ μ)) :
    tterm a b c v (Quotient.mk'' A) = ttermFun a b c v A := rfl

/-- Forget the `κ`/`μ` split: the quotient projection `T ι κ μ → ModSumCongr ι (κ ⊕ μ)`. -/
def projL : T ι κ μ → Equiv.Perm.ModSumCongr ι (κ ⊕ μ) :=
  fun q => Quotient.liftOn' q (fun A => (Quotient.mk'' A : Equiv.Perm.ModSumCongr ι (κ ⊕ μ))) (by
    intro A₁ A₂ hA
    rw [QuotientGroup.leftRel_apply] at hA
    obtain ⟨⟨sι, sκ, sμ⟩, h⟩ := hA
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    exact ⟨(sι, Equiv.sumCongr sκ sμ), by
      rw [Equiv.Perm.sumCongrHom_apply, ← h, youngHom_apply]⟩)

@[simp] theorem projL_mk (A : Equiv.Perm (ι ⊕ κ ⊕ μ)) :
    projL (Quotient.mk'' A) = (Quotient.mk'' A : Equiv.Perm.ModSumCongr ι (κ ⊕ μ)) := rfl

/-- Insert a `κ`/`μ` split `ρ` into the right block, fibrewise over `projL`. -/
def fibI (σ : Equiv.Perm (ι ⊕ κ ⊕ μ)) : Equiv.Perm.ModSumCongr κ μ → T ι κ μ :=
  fun r => Quotient.liftOn' r
    (fun ρ => Quotient.mk'' (σ * Equiv.sumCongr (1 : Equiv.Perm ι) ρ)) (by
    intro ρ₁ ρ₂ hρ
    rw [QuotientGroup.leftRel_apply] at hρ
    obtain ⟨⟨sκ, sμ⟩, h⟩ := hρ
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    refine ⟨(1, sκ, sμ), ?_⟩
    rw [youngHom_apply, mul_inv_rev, mul_assoc, ← mul_assoc σ⁻¹ σ, inv_mul_cancel, one_mul,
      Equiv.Perm.sumCongr_inv, inv_one, Equiv.Perm.sumCongr_mul, one_mul, ← h,
      Equiv.Perm.sumCongrHom_apply])

@[simp] theorem fibI_mk (σ : Equiv.Perm (ι ⊕ κ ⊕ μ)) (ρ : Equiv.Perm (κ ⊕ μ)) :
    fibI σ (Quotient.mk'' ρ) = Quotient.mk'' (σ * Equiv.sumCongr (1 : Equiv.Perm ι) ρ) := rfl

/-- Evaluate a scalar-`mul` wedge `summand` over an abstract sum index type at a representative. -/
theorem mul_summand_eval' {ν ν' : Type*} [Fintype ν] [Fintype ν'] [DecidableEq ν] [DecidableEq ν']
    (b : E [⋀^ν]→L[𝕜] 𝕜) (c : E [⋀^ν']→L[𝕜] 𝕜) (ρ : Equiv.Perm (ν ⊕ ν')) (w : ν ⊕ ν' → E) :
    uncurrySum.summand ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ b c)
        (Quotient.mk'' ρ) w
      = Equiv.Perm.sign ρ •
          (b (fun j => w (ρ (Sum.inl j))) * c (fun k => w (ρ (Sum.inr k)))) := by
  rw [summand_mk_eval]
  simp only [ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    ContinuousLinearMap.mul_apply']

/-- Expand the abstract scalar wedge `uncurrySum (mul.compCAM₂ b c)` as a sum over `ModSumCongr`. -/
theorem uncurrySum_mul_apply {ν ν' : Type*} [Fintype ν] [Fintype ν'] [DecidableEq ν] [DecidableEq ν']
    (b : E [⋀^ν]→L[𝕜] 𝕜) (c : E [⋀^ν']→L[𝕜] 𝕜) (w : ν ⊕ ν' → E) :
    uncurrySum ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ b c) w
      = ∑ ρ : Equiv.Perm.ModSumCongr ν ν',
          uncurrySum.summand ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ b c) ρ w := by
  rw [uncurrySum_apply, ContinuousMultilinearMap.sum_apply]

/-- The per-fibre identity for the LHS (right) fibration. -/
theorem lcore_fiber (a : E [⋀^ι]→L[𝕜] 𝕜) (b : E [⋀^κ]→L[𝕜] 𝕜) (c : E [⋀^μ]→L[𝕜] 𝕜)
    (v : ι ⊕ κ ⊕ μ → E) (σ : Equiv.Perm (ι ⊕ κ ⊕ μ)) :
    uncurrySum.summand ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ a
        (uncurrySum ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ b c)))
        (Quotient.mk'' σ) v
      = ∑ A ∈ Finset.univ.filter (fun q : T ι κ μ => projL q = Quotient.mk'' σ),
          tterm a b c v A := by
  rw [summand_mk_eval]
  simp only [ContinuousLinearMap.compContinuousAlternatingMap₂_apply, ContinuousLinearMap.mul_apply']
  rw [uncurrySum_mul_apply, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_bij (fun (r : Equiv.Perm.ModSumCongr κ μ) _ => fibI σ r) ?_ ?_ ?_ ?_
  · -- maps into the fibre
    intro r _
    induction r using Quotient.inductionOn' with
    | _ ρ =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, fibI_mk, projL_mk]
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply]
      exact ⟨(1, ρ⁻¹), by rw [Equiv.Perm.sumCongrHom_apply, mul_inv_rev, mul_assoc,
        inv_mul_cancel, mul_one, Equiv.Perm.sumCongr_inv, inv_one]⟩
  · -- injective
    intro r₁ _ r₂ _ heq
    induction r₁ using Quotient.inductionOn' with
    | _ ρ₁ =>
    induction r₂ using Quotient.inductionOn' with
    | _ ρ₂ =>
      simp only [fibI_mk] at heq
      rw [Quotient.eq'', QuotientGroup.leftRel_apply] at heq ⊢
      obtain ⟨⟨sι, sκ, sμ⟩, h⟩ := heq
      rw [youngHom_apply, mul_inv_rev, mul_assoc, inv_mul_cancel_left,
        Equiv.Perm.sumCongr_inv, inv_one, Equiv.Perm.sumCongr_mul, one_mul] at h
      -- h : sumCongr sι (sumCongr sκ sμ) = sumCongr 1 (ρ₁⁻¹ * ρ₂)
      have hX : ρ₁⁻¹ * ρ₂ = Equiv.sumCongr sκ sμ := by
        ext y
        have := congrArg (fun e => e (Sum.inr y)) h
        simpa using this.symm
      exact ⟨(sκ, sμ), by simp only [Equiv.Perm.sumCongrHom_apply]; exact hX.symm⟩
  · -- surjective
    intro b hb
    induction b using Quotient.inductionOn' with
    | _ A =>
      rw [Finset.mem_filter] at hb
      have hcl : (Quotient.mk'' A : Equiv.Perm.ModSumCongr ι (κ ⊕ μ)) = Quotient.mk'' σ := by
        have := hb.2; rwa [projL_mk] at this
      rw [Quotient.eq'', QuotientGroup.leftRel_apply] at hcl
      have hcl' : σ⁻¹ * A ∈ (Equiv.Perm.sumCongrHom ι (κ ⊕ μ)).range := by
        have := (Equiv.Perm.sumCongrHom ι (κ ⊕ μ)).range.inv_mem hcl
        rwa [mul_inv_rev, inv_inv] at this
      obtain ⟨⟨sι, w⟩, hw⟩ := hcl'
      simp only [Equiv.Perm.sumCongrHom_apply] at hw
      have hA : A = σ * Equiv.sumCongr sι w := eq_mul_of_inv_mul_eq hw.symm
      refine ⟨Quotient.mk'' w, Finset.mem_univ _, ?_⟩
      simp only [fibI_mk]
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply]
      refine ⟨(sι, 1, 1), ?_⟩
      rw [hA, mul_inv_rev, mul_assoc, inv_mul_cancel_left, Equiv.Perm.sumCongr_inv, inv_one,
        Equiv.Perm.sumCongr_mul, one_mul, inv_mul_cancel]
      simp [youngHom_apply]
  · -- term identity
    intro r _
    induction r using Quotient.inductionOn' with
    | _ ρ =>
      have hsign : Equiv.Perm.sign (σ * Equiv.sumCongr (1 : Equiv.Perm ι) ρ)
          = Equiv.Perm.sign σ * Equiv.Perm.sign ρ := by
        rw [map_mul, Equiv.Perm.sign_sumCongr, map_one, one_mul]
      simp only [fibI_mk, tterm_mk, ttermFun, mul_summand_eval', hsign,
        Equiv.Perm.mul_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
        Equiv.Perm.coe_one, id_eq, mul_smul_comm, smul_smul, mul_assoc]

/-- **LHS core = sum over the triple quotient** (right fibration over `projL`). -/
theorem lcore_eq_sumT (a : E [⋀^ι]→L[𝕜] 𝕜) (b : E [⋀^κ]→L[𝕜] 𝕜) (c : E [⋀^μ]→L[𝕜] 𝕜)
    (v : ι ⊕ κ ⊕ μ → E) :
    uncurrySum ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ a
        (uncurrySum ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ b c))) v
      = ∑ q : T ι κ μ, tterm a b c v q := by
  rw [uncurrySum_apply, ContinuousMultilinearMap.sum_apply,
    ← Finset.sum_fiberwise Finset.univ projL (tterm a b c v)]
  refine Finset.sum_congr rfl fun σ' _ => ?_
  induction σ' using Quotient.inductionOn' with
  | _ σ => exact lcore_fiber a b c v σ

/-! #### Right (left-nested) fibration -/

/-- Conjugation by an equiv is multiplicative on permutations. -/
theorem permCongr_mul {α β : Type*} (e : α ≃ β) (p q : Equiv.Perm α) :
    e.permCongr (p * q) = e.permCongr p * e.permCongr q := by
  ext x; simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply]

theorem permCongr_one {α β : Type*} (e : α ≃ β) : e.permCongr (1 : Equiv.Perm α) = 1 := by
  ext x; simp [Equiv.permCongr_apply]

theorem permCongr_inv {α β : Type*} (e : α ≃ β) (p : Equiv.Perm α) :
    e.permCongr p⁻¹ = (e.permCongr p)⁻¹ :=
  (inv_eq_of_mul_eq_one_right (by rw [← permCongr_mul, mul_inv_cancel, permCongr_one])).symm

@[simp] theorem permCongr_symm_permCongr {α β : Type*} (e : α ≃ β) (p : Equiv.Perm α) :
    e.symm.permCongr (e.permCongr p) = p := by
  rw [← Equiv.permCongr_symm, Equiv.symm_apply_apply]

@[simp] theorem permCongr_permCongr_symm {α β : Type*} (e : α ≃ β) (p : Equiv.Perm β) :
    e.permCongr (e.symm.permCongr p) = p := by
  rw [← Equiv.permCongr_symm, Equiv.apply_symm_apply]

/-- Conjugating a right-nested Young element by `sumAssoc⁻¹` gives the left-nested one. -/
theorem permCongr_sumAssoc_symm_young (sι : Equiv.Perm ι) (sκ : Equiv.Perm κ) (sμ : Equiv.Perm μ) :
    (Equiv.sumAssoc ι κ μ).symm.permCongr (Equiv.sumCongr sι (Equiv.sumCongr sκ sμ))
      = Equiv.sumCongr (Equiv.sumCongr sι sκ) sμ := by
  ext x; rcases x with (i | j) | k <;> simp [Equiv.permCongr_apply]

/-- Conjugating a left-nested Young element by `sumAssoc` gives the right-nested one. -/
theorem permCongr_sumAssoc_young (sι : Equiv.Perm ι) (sκ : Equiv.Perm κ) (sμ : Equiv.Perm μ) :
    (Equiv.sumAssoc ι κ μ).permCongr (Equiv.sumCongr (Equiv.sumCongr sι sκ) sμ)
      = Equiv.sumCongr sι (Equiv.sumCongr sκ sμ) := by
  ext x; rcases x with i | j | k <;> simp [Equiv.permCongr_apply]

theorem youngHom_one_one (sμ : Equiv.Perm μ) :
    youngHom ι κ μ (1, 1, sμ)
      = (Equiv.sumAssoc ι κ μ).permCongr (Equiv.sumCongr (1 : Equiv.Perm (ι ⊕ κ)) sμ) := by
  rw [youngHom_apply]
  ext x; rcases x with i | j | k <;> simp [Equiv.permCongr_apply]

/-- Forget the `ι`/`κ` split: the projection `T ι κ μ → ModSumCongr (ι ⊕ κ) μ` (via `sumAssoc`). -/
def projAssocR : T ι κ μ → Equiv.Perm.ModSumCongr (ι ⊕ κ) μ :=
  fun q => Quotient.liftOn' q
    (fun A => (Quotient.mk'' ((Equiv.sumAssoc ι κ μ).symm.permCongr A) :
      Equiv.Perm.ModSumCongr (ι ⊕ κ) μ)) (by
    intro A₁ A₂ hA
    rw [QuotientGroup.leftRel_apply] at hA
    obtain ⟨⟨sι, sκ, sμ⟩, h⟩ := hA
    have hA₂ : A₂ = A₁ * Equiv.sumCongr sι (Equiv.sumCongr sκ sμ) :=
      eq_mul_of_inv_mul_eq h.symm
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    refine ⟨(Equiv.sumCongr sι sκ, sμ), ?_⟩
    simp only [Equiv.Perm.sumCongrHom_apply, hA₂, permCongr_mul, permCongr_sumAssoc_symm_young]
    rw [inv_mul_cancel_left])

@[simp] theorem projAssocR_mk (A : Equiv.Perm (ι ⊕ κ ⊕ μ)) :
    projAssocR (Quotient.mk'' A) =
      (Quotient.mk'' ((Equiv.sumAssoc ι κ μ).symm.permCongr A) :
        Equiv.Perm.ModSumCongr (ι ⊕ κ) μ) := rfl

/-- Insert an `ι`/`κ` split `π` into the left block, fibrewise over `projAssocR`. -/
def fibAssocR (τ : Equiv.Perm ((ι ⊕ κ) ⊕ μ)) : Equiv.Perm.ModSumCongr ι κ → T ι κ μ :=
  fun r => Quotient.liftOn' r
    (fun π => Quotient.mk''
      ((Equiv.sumAssoc ι κ μ).permCongr (τ * Equiv.sumCongr π (1 : Equiv.Perm μ)))) (by
    intro π₁ π₂ hπ
    rw [QuotientGroup.leftRel_apply] at hπ
    obtain ⟨⟨sι, sκ⟩, h⟩ := hπ
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    refine ⟨(sι, sκ, 1), ?_⟩
    have hkey : (τ * Equiv.sumCongr π₁ (1 : Equiv.Perm μ))⁻¹ *
          (τ * Equiv.sumCongr π₂ (1 : Equiv.Perm μ))
        = Equiv.sumCongr (Equiv.sumCongr sι sκ) (1 : Equiv.Perm μ) := by
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left, Equiv.Perm.sumCongr_inv, inv_one,
        Equiv.Perm.sumCongr_mul, one_mul, ← h, Equiv.Perm.sumCongrHom_apply]
    rw [youngHom_apply, ← permCongr_sumAssoc_young sι sκ 1, ← hkey, ← permCongr_inv,
      ← permCongr_mul])

@[simp] theorem fibAssocR_mk (τ : Equiv.Perm ((ι ⊕ κ) ⊕ μ)) (π : Equiv.Perm (ι ⊕ κ)) :
    fibAssocR τ (Quotient.mk'' π) =
      Quotient.mk'' ((Equiv.sumAssoc ι κ μ).permCongr (τ * Equiv.sumCongr π (1 : Equiv.Perm μ))) :=
  rfl

/-- The per-fibre identity for the RHS (left) fibration. -/
theorem rcore_fiber (a : E [⋀^ι]→L[𝕜] 𝕜) (b : E [⋀^κ]→L[𝕜] 𝕜) (c : E [⋀^μ]→L[𝕜] 𝕜)
    (v : ι ⊕ κ ⊕ μ → E) (τ : Equiv.Perm ((ι ⊕ κ) ⊕ μ)) :
    uncurrySum.summand ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂
        (uncurrySum ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ a b)) c)
        (Quotient.mk'' τ) (v ∘ ⇑(Equiv.sumAssoc ι κ μ))
      = ∑ A ∈ Finset.univ.filter (fun q : T ι κ μ => projAssocR q = Quotient.mk'' τ),
          tterm a b c v A := by
  rw [summand_mk_eval]
  simp only [ContinuousLinearMap.compContinuousAlternatingMap₂_apply, ContinuousLinearMap.mul_apply']
  rw [uncurrySum_mul_apply, Finset.sum_mul, Finset.smul_sum]
  refine Finset.sum_bij (fun (r : Equiv.Perm.ModSumCongr ι κ) _ => fibAssocR τ r) ?_ ?_ ?_ ?_
  · -- maps into the fibre
    intro r _
    induction r using Quotient.inductionOn' with
    | _ π =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, fibAssocR_mk, projAssocR_mk,
        permCongr_symm_permCongr]
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply]
      refine ⟨(π⁻¹, 1), ?_⟩
      rw [Equiv.Perm.sumCongrHom_apply, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one,
        Equiv.Perm.sumCongr_inv, inv_one]
  · -- injective
    intro r₁ _ r₂ _ heq
    induction r₁ using Quotient.inductionOn' with
    | _ π₁ =>
    induction r₂ using Quotient.inductionOn' with
    | _ π₂ =>
      simp only [fibAssocR_mk] at heq
      rw [Quotient.eq'', QuotientGroup.leftRel_apply] at heq ⊢
      obtain ⟨⟨sι, sκ, sμ⟩, h⟩ := heq
      rw [youngHom_apply, ← permCongr_inv, ← permCongr_mul,
        show (τ * Equiv.sumCongr π₁ (1 : Equiv.Perm μ))⁻¹ *
            (τ * Equiv.sumCongr π₂ (1 : Equiv.Perm μ))
          = Equiv.sumCongr (π₁⁻¹ * π₂) (1 : Equiv.Perm μ) from by
          rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left, Equiv.Perm.sumCongr_inv, inv_one,
            Equiv.Perm.sumCongr_mul, one_mul]] at h
      have h2 := congrArg (Equiv.sumAssoc ι κ μ).symm.permCongr h
      rw [permCongr_sumAssoc_symm_young, permCongr_symm_permCongr] at h2
      have hX : Equiv.sumCongr sι sκ = π₁⁻¹ * π₂ := by
        ext x
        have := congrArg (fun e => e (Sum.inl x)) h2
        simpa using this
      exact ⟨(sι, sκ), by simp only [Equiv.Perm.sumCongrHom_apply]; exact hX⟩
  · -- surjective
    intro b hb
    induction b using Quotient.inductionOn' with
    | _ A =>
      rw [Finset.mem_filter] at hb
      have hcl : (Quotient.mk'' ((Equiv.sumAssoc ι κ μ).symm.permCongr A) :
          Equiv.Perm.ModSumCongr (ι ⊕ κ) μ) = Quotient.mk'' τ := by
        have := hb.2; rwa [projAssocR_mk] at this
      rw [Quotient.eq'', QuotientGroup.leftRel_apply] at hcl
      have hcl' : τ⁻¹ * ((Equiv.sumAssoc ι κ μ).symm.permCongr A)
          ∈ (Equiv.Perm.sumCongrHom (ι ⊕ κ) μ).range := by
        have := (Equiv.Perm.sumCongrHom (ι ⊕ κ) μ).range.inv_mem hcl
        rwa [mul_inv_rev, inv_inv] at this
      obtain ⟨⟨π, sμ⟩, hπ⟩ := hcl'
      simp only [Equiv.Perm.sumCongrHom_apply] at hπ
      have hB : (Equiv.sumAssoc ι κ μ).symm.permCongr A = τ * Equiv.sumCongr π sμ :=
        eq_mul_of_inv_mul_eq hπ.symm
      refine ⟨Quotient.mk'' π, Finset.mem_univ _, ?_⟩
      simp only [fibAssocR_mk]
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply]
      refine ⟨(1, 1, sμ), ?_⟩
      have hAeq : A = (Equiv.sumAssoc ι κ μ).permCongr (τ * Equiv.sumCongr π sμ) := by
        rw [← hB, permCongr_permCongr_symm]
      have hinner : (τ * Equiv.sumCongr π (1 : Equiv.Perm μ))⁻¹ * (τ * Equiv.sumCongr π sμ)
          = Equiv.sumCongr (1 : Equiv.Perm (ι ⊕ κ)) sμ := by
        rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left, Equiv.Perm.sumCongr_inv, inv_one,
          Equiv.Perm.sumCongr_mul, one_mul, inv_mul_cancel]
      rw [youngHom_one_one, hAeq, ← permCongr_inv, ← permCongr_mul]
      exact congrArg _ hinner.symm
  · -- term identity
    intro r _
    induction r using Quotient.inductionOn' with
    | _ π =>
      have hsign : Equiv.Perm.sign ((Equiv.sumAssoc ι κ μ).permCongr
            (τ * Equiv.sumCongr π (1 : Equiv.Perm μ)))
          = Equiv.Perm.sign τ * Equiv.Perm.sign π := by
        rw [Equiv.Perm.sign_permCongr, map_mul, Equiv.Perm.sign_sumCongr, map_one, mul_one]
      simp only [fibAssocR_mk, tterm_mk, ttermFun, mul_summand_eval', hsign,
        Equiv.permCongr_apply, Equiv.sumAssoc_symm_apply_inl, Equiv.sumAssoc_symm_apply_inr_inl,
        Equiv.sumAssoc_symm_apply_inr_inr, Equiv.Perm.mul_apply, Equiv.sumCongr_apply, Sum.map_inl,
        Sum.map_inr, Equiv.Perm.coe_one, id_eq, Function.comp_apply, smul_mul_assoc,
        mul_smul_comm, smul_smul, mul_assoc]

/-- **RHS core = sum over the triple quotient** (left fibration over `projAssocR`, via `sumAssoc`). -/
theorem rcore_eq_sumT (a : E [⋀^ι]→L[𝕜] 𝕜) (b : E [⋀^κ]→L[𝕜] 𝕜) (c : E [⋀^μ]→L[𝕜] 𝕜)
    (v : ι ⊕ κ ⊕ μ → E) :
    domDomCongr (Equiv.sumAssoc ι κ μ)
        (uncurrySum ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂
          (uncurrySum ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ a b)) c)) v
      = ∑ q : T ι κ μ, tterm a b c v q := by
  rw [domDomCongr_apply, uncurrySum_apply, ContinuousMultilinearMap.sum_apply,
    ← Finset.sum_fiberwise Finset.univ projAssocR (tterm a b c v)]
  refine Finset.sum_congr rfl fun τ' _ => ?_
  induction τ' using Quotient.inductionOn' with
  | _ τ => exact rcore_fiber a b c v τ

/-- **Abstract associativity of the alternatization shuffle product.** -/
theorem core_assoc (a : E [⋀^ι]→L[𝕜] 𝕜) (b : E [⋀^κ]→L[𝕜] 𝕜) (c : E [⋀^μ]→L[𝕜] 𝕜) :
    uncurrySum ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ a
        (uncurrySum ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ b c)))
      = domDomCongr (Equiv.sumAssoc ι κ μ)
        (uncurrySum ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂
          (uncurrySum ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ a b)) c)) := by
  ext v
  rw [lcore_eq_sumT, rcore_eq_sumT]

end core

/-! ### Pullout lemmas: reindexing a wedge factor commutes with `uncurrySum` -/

section pullout

variable {ι₁ ι₂ ν₁ ν₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ν₁] [Fintype ν₂]
  [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ν₁] [DecidableEq ν₂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem permCongr_sumCongr (eL : ι₁ ≃ ι₂) (eR : ν₁ ≃ ν₂) (s₁ : Equiv.Perm ι₁) (s₂ : Equiv.Perm ν₁) :
    (Equiv.sumCongr eL eR).permCongr (Equiv.sumCongr s₁ s₂)
      = Equiv.sumCongr (eL.permCongr s₁) (eR.permCongr s₂) := by
  ext x; rcases x with i | j <;> simp [Equiv.permCongr_apply]

open Equiv.Perm in
theorem mscCongr_spec (eL : ι₁ ≃ ι₂) (eR : ν₁ ≃ ν₂) (a b : Equiv.Perm (ι₁ ⊕ ν₁))
    (h : (QuotientGroup.leftRel (Equiv.Perm.sumCongrHom ι₁ ν₁).range) a b) :
    (Quot.mk _ ∘ (Equiv.sumCongr eL eR).permCongr) a
      = (Quot.mk (⇑(QuotientGroup.leftRel (sumCongrHom ι₂ ν₂).range))
          ∘ (Equiv.sumCongr eL eR).permCongr) b := by
  apply Quot.sound
  rw [QuotientGroup.leftRel_apply] at h ⊢
  obtain ⟨⟨s₁, s₂⟩, hab⟩ := h
  refine ⟨(eL.permCongr s₁, eR.permCongr s₂), ?_⟩
  have hab' : Equiv.sumCongr s₁ s₂ = a⁻¹ * b := hab
  simp only [Equiv.Perm.sumCongrHom_apply]
  rw [← permCongr_inv, ← permCongr_mul, ← hab', permCongr_sumCongr]

/-- Relabel both blocks of a `ModSumCongr` quotient by equivs. -/
def mscCongr (eL : ι₁ ≃ ι₂) (eR : ν₁ ≃ ν₂) :
    Equiv.Perm.ModSumCongr ι₁ ν₁ ≃ Equiv.Perm.ModSumCongr ι₂ ν₂ where
  toFun := Quot.lift (Quot.mk _ ∘ (Equiv.sumCongr eL eR).permCongr) (mscCongr_spec eL eR)
  invFun := Quot.lift (Quot.mk _ ∘ (Equiv.sumCongr eL.symm eR.symm).permCongr)
    (mscCongr_spec eL.symm eR.symm)
  left_inv := by rintro ⟨σ⟩; simp [← Equiv.sumCongr_symm]
  right_inv := by rintro ⟨σ⟩; simp [← Equiv.sumCongr_symm]

@[simp] theorem mscCongr_mk (eL : ι₁ ≃ ι₂) (eR : ν₁ ≃ ν₂) (σ : Equiv.Perm (ι₁ ⊕ ν₁)) :
    mscCongr eL eR (Quotient.mk'' σ) = Quotient.mk'' ((Equiv.sumCongr eL eR).permCongr σ) := rfl

/-- Reindexing the **right** factor of a scalar wedge by `e` commutes with `uncurrySum`,
producing a `sumCongr (refl) e` reindex of the whole. -/
theorem pullout_right (g : E [⋀^ι₁]→L[𝕜] 𝕜) (X : E [⋀^ν₁]→L[𝕜] 𝕜) (e : ν₁ ≃ ν₂) :
    uncurrySum ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g (domDomCongr e X))
      = domDomCongr (Equiv.sumCongr (Equiv.refl ι₁) e)
        (uncurrySum ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g X)) := by
  ext w
  rw [domDomCongr_apply, uncurrySum_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply]
  refine (Fintype.sum_equiv (mscCongr (Equiv.refl ι₁) e)
    (fun σ' => uncurrySum.summand
      ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g X) σ'
      (w ∘ ⇑(Equiv.sumCongr (Equiv.refl ι₁) e)))
    (fun σ => uncurrySum.summand
      ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g (domDomCongr e X)) σ w)
    ?_).symm
  intro σ'
  induction σ' using Quotient.inductionOn' with
  | _ σ =>
    simp only [mscCongr_mk, mul_summand_eval', Equiv.Perm.sign_permCongr, domDomCongr_apply,
      Equiv.permCongr_apply, Equiv.sumCongr_apply, Equiv.sumCongr_symm, Equiv.refl_symm,
      Sum.map_inl, Sum.map_inr, Equiv.refl_apply, Equiv.symm_apply_apply, Function.comp_apply,
      Function.comp_def]

/-- Reindexing the **left** factor of a scalar wedge by `e` commutes with `uncurrySum`. -/
theorem pullout_left (X : E [⋀^ι₁]→L[𝕜] 𝕜) (c : E [⋀^ν₁]→L[𝕜] 𝕜) (e : ι₁ ≃ ι₂) :
    uncurrySum ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ (domDomCongr e X) c)
      = domDomCongr (Equiv.sumCongr e (Equiv.refl ν₁))
        (uncurrySum ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ X c)) := by
  ext w
  rw [domDomCongr_apply, uncurrySum_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply]
  refine (Fintype.sum_equiv (mscCongr e (Equiv.refl ν₁))
    (fun σ' => uncurrySum.summand
      ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ X c) σ'
      (w ∘ ⇑(Equiv.sumCongr e (Equiv.refl ν₁))))
    (fun σ => uncurrySum.summand
      ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ (domDomCongr e X) c) σ w)
    ?_).symm
  intro σ'
  induction σ' using Quotient.inductionOn' with
  | _ σ =>
    simp only [mscCongr_mk, mul_summand_eval', Equiv.Perm.sign_permCongr, domDomCongr_apply,
      Equiv.permCongr_apply, Equiv.sumCongr_apply, Equiv.sumCongr_symm, Equiv.refl_symm,
      Sum.map_inl, Sum.map_inr, Equiv.refl_apply, Equiv.symm_apply_apply, Function.comp_apply,
      Function.comp_def]

end pullout

/-! ### Assembly: associativity of the wedge product -/

section assemble

variable {N N' N'' : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  [NormedAddCommGroup N'] [NormedSpace 𝕜 N'] [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {a b : ℕ}

/-- Unfold the wedge as `domDomCongr finSumFinEquiv ∘ uncurrySum ∘ compCAM₂`. -/
theorem wedge_eq_dDC (g : M [⋀^Fin a]→L[𝕜] N) (h : M [⋀^Fin b]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') :
    wedge_product g h f
      = domDomCongr finSumFinEquiv (uncurrySum (f.compContinuousAlternatingMap₂ g h)) := rfl

/-- **Associativity of the wedge product** (CAM level). -/
theorem wedge_mul_assoc' (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) :
    domDomCongr finAssoc.symm (g ∧[𝕜] h ∧[𝕜] l) = (g ∧[𝕜] h) ∧[𝕜] l := by
  have hL : (g ∧[𝕜] h ∧[𝕜] l)
      = domDomCongr ((Equiv.sumCongr (Equiv.refl (Fin m)) finSumFinEquiv).trans finSumFinEquiv)
        (uncurrySum ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g
          (uncurrySum ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ h l)))) := by
    rw [wedge_eq_dDC g (h ∧[𝕜] l) (ContinuousLinearMap.mul 𝕜 𝕜), wedge_eq_dDC h l,
      pullout_right, domDomCongr_domDomCongr]
  have hR : ((g ∧[𝕜] h) ∧[𝕜] l)
      = domDomCongr ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin p))).trans finSumFinEquiv)
        (uncurrySum ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂
          (uncurrySum ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h)) l)) := by
    rw [wedge_eq_dDC (g ∧[𝕜] h) l (ContinuousLinearMap.mul 𝕜 𝕜), wedge_eq_dDC g h,
      pullout_left, domDomCongr_domDomCongr]
  rw [hL, hR, domDomCongr_domDomCongr, core_assoc, domDomCongr_domDomCongr]
  have heq : (Equiv.sumAssoc (Fin m) (Fin n) (Fin p)).trans
        (((Equiv.sumCongr (Equiv.refl (Fin m)) finSumFinEquiv).trans finSumFinEquiv).trans
          finAssoc.symm)
      = (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin p))).trans finSumFinEquiv :=
    (eR3_eq_sumAssoc_eL3).symm
  rw [heq]

end assemble

/-- **Associativity of the multiplication wedge product** (the thesis's Prop. 4.27). -/
theorem wedge_mul_assoc (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) (v : Fin (m + n + p) → M) :
    ContinuousAlternatingMap.domDomCongr finAssoc.symm (g ∧[𝕜] h ∧[𝕜] l) v
      = ((g ∧[𝕜] h) ∧[𝕜] l) v :=
  congrFun (congrArg _ (wedge_mul_assoc' g h l)) v

end ContinuousAlternatingMap

