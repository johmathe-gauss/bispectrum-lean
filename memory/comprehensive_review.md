# Comprehensive Review: Papers + Codebase

*Written after full review of both papers and repo.*

---

## Paper 1: "The Selective G-Bispectrum and its Inversion" (NeurIPS 2024)

### What the paper achieves

The paper solves a fundamental tension in G-equivariant networks: you want G-invariance *without* losing information. Prior approaches:
- **Max/avg pooling**: G-invariant but *excessively* invariant — can't distinguish signals from different classes that happen to share a maximum
- **G-Triple Correlation**: Complete invariant, but O(|G|³) time and O(|G|²) space — unusable at scale
- **Full G-Bispectrum**: Same completeness, O(|G|²) time/space — still quadratic

**The insight**: The full G-Bispectrum has deep redundancies. The Clebsch-Gordan decomposition ρ₁ ⊗ ρ₂ = ⊕ρ means many bispectral coefficients encode the *same* information. By exploiting this structure, you can select O(|G|) coefficients that are *still* complete.

### Core mathematical machinery

**The G-Bispectrum** (Theorem 1):
```
β(Θ)_{ρ₁,ρ₂} = [F(Θ)_{ρ₁} ⊗ F(Θ)_{ρ₂}] C_{ρ₁,ρ₂} [⊕_{ρ∈ρ₁⊗ρ₂} F(Θ)_ρ†] C†_{ρ₁,ρ₂}
```

For *commutative* groups, this simplifies dramatically to scalars:
```
β(Θ)_{ρ₁,ρ₂} = F(Θ)_{ρ₁} · F(Θ)_{ρ₂} · F(Θ)†_{ρ₁⊗ρ₂}
```

**The key inversion algorithms** (Appendix):

*Cyclic groups C_n* (Algorithm 1):
1. β_{ρ₀,ρ₀} → recover F(Θ)_{ρ₀} (trivial irrep, fully determined)
2. β_{ρ₀,ρ₁} → recover |F(Θ)_{ρ₁}|² (phase set to 0 by convention)
3. For k = 1,...,n-2: F(Θ)_{ρ_{k+1}} = (β_{ρ₁,ρₖ} / F_{ρ₁}·F_{ρₖ})†
4. Correct phase: find φ ∈ [0, 2π/n) such that inverse FT is real
→ Total: n = |G| coefficients. Elegant!

*Commutative groups* (Algorithm 2):
- Use fundamental theorem: G ≅ ⊕ ℤ/nₗℤ
- Iteratively build a hypercuboid in frequency space
- Edge directions come from basis vectors eˡ
- Fill face-by-face: l=1 gives edge, l=2 gives face, l=3 gives cube, etc.
→ Total: exactly |G| coefficients

*Dihedral groups D_n* (Algorithm 3, new contribution):
- Non-commutative: Fourier coefficients are 2×2 matrices
- F(Θ)_{ρ₀} from β_{ρ₀,ρ₀} (scalar)
- F(Θ)_{ρ₁} from β_{ρ₀,ρ₁} via eigenvalue decomposition: β/F₀ = VΛV†, then F_{ρ₁} = VΛ^½V†·U
- Iterate: ⊕_{ρ∈ρ₁⊗ρₖ₋₁} F_{ρ} = (C†_{ρ₁,ρₖ₋₁} [F_{ρ₁} ⊗ F_{ρₖ₋₁}]⁻¹ β_{ρ₁,ρₖ₋₁} C_{ρ₁,ρₖ₋₁})†
→ Total: 1 + 4 + 16·⌊(n-1)/2⌋ ≈ 4|G| scalar values

Key result for D_n: ρ₁ generates all irreps via Kronecker products (proven via character theory).

### Important subtleties

1. **Indeterminacy is exact, not approximate**: The bispectrum is invariant to the *full* continuous SO(2), not just the discrete C_n. The "valid phase correction" step in Algorithm 1 handles this — it finds the unique φ that makes the inverse FT real.

2. **Generic position assumption**: Inversion requires F(Θ)_ρ ≠ 0 for all irreps. This holds with probability 1 for random signals, but could fail for structured signals. Not a practical issue for neural network feature maps.

3. **Non-commutative case requires matrix inversion**: For D_n, solving the system involves [F_{ρ₁} ⊗ F_{ρₖ}]⁻¹, requiring invertible Fourier matrices. Equivalent to the generic position assumption.

4. **The "valid U" problem**: For D_n, computing the correct U in F_{ρ₁} = VΛ^½V†U is non-trivial (the paper says "existence ensured but not computed easily"). This is a practical gap.

---

## Paper 2: "Bispectral Signatures of Data" (Colleague's Draft, 43 pages)

### What this draft provides

This is a detailed reference on the mathematics, with explicit formulas at a level ready for implementation. It complements the NeurIPS paper by:
- Working through formulas step-by-step with all indices explicit
- Covering continuous groups (like SO(2), O(2)) as well as finite
- Providing the steerable basis perspective
- Including explicit TC symmetries (useful for optimization)

### Key content by section

**Cyclic groups (Sections 4.1-4.10)**:
- DFT: f̂ₖ = Σ e^{-i2πkx/n} f(x)
- Triple correlation: T(f)_{x₁,x₂} = (1/n)Σ f*(x)f(x+x₁)f(x+x₂)
- TC symmetries: T_{x₁,x₂} = T_{x₂,x₁} = T_{-x₁,x₂-x₁} = ... (6 equivalent forms)
- Bispectrum: β_{k₁,k₂} = f̂_{k₁}f̂_{k₂}f̂*_{k₁+k₂}
- Inversion: n+1 coefficients β_{k,0} and β_{1,k} suffice
- Reconstruction: iterative, from DC to high frequencies

**Finite groups (Sections 5.1-5.9)**:
- Matrix-valued FT: F(ω) = (1/|G|) Σ f(g)D_ω(g)†
- Steerable bispectrum: computable directly from G-conv output Θₗ coefficients
- General bispectrum formula (Kakarala): β_{ρ₁,ρ₂} = [F_{ρ₁} ⊗ F_{ρ₂}]C_{ρ₁ρ₂}[⊕F_ρ]†C†_{ρ₁ρ₂}
- **Lemma 2** (key for implementation): For trivial ρ₀ and any irrep ρ of dimension D:
  - β_{ρ₀,ρ₀} = |F_{ρ₀}|²F_{ρ₀} ∈ ℂ (scalar)
  - β_{ρ,ρ₀} = F†_ρ F_ρ F_{ρ₀} ∈ ℂ^{D×D}
  This simplification comes from CG matrices for (ρ, ρ₀) being identity matrices.
- **Proposition 6**: L bispectral coefficients (from Kronecker table) suffice to recover all Fourier coefficients

**Steerable basis connection** (Section 4.3, 5.3):
After G-convolution, features live on G. The bispectrum can be computed directly from the steerable coefficients Θₗ without going back to spatial domain. This is potentially more efficient in practice.

### Things the draft adds beyond the NeurIPS paper

1. **Explicit TC symmetries**: 6 equivalent forms of T_{x₁,x₂} — useful for reducing computation
2. **Steerable formulation**: Direct computation from conv output, bypassing spatial domain
3. **More continuous groups**: SO(2), O(2) coverage for future extension
4. **"TODO" markers**: Honest about what's still unproven (e.g., commutative simplification proof)

---

## Codebase Review

### Current implementation: `SO3onS2` for spherical harmonics

The code is **mathematically correct** for the SO(3) case. The formula implemented is exactly:
```
β_{l₁,l₂}[l] = (F_{l₁} ⊗ F_{l₂}) @ C_{l₁,l₂} @ F̂_l†
```

Where:
- l₁, l₂ are spherical harmonic degrees (playing the role of irreps for SO(3))
- C_{l₁,l₂} is the Clebsch-Gordan matrix (pre-computed, stored in JSON)
- F̂_l is F_l zero-padded to size (2l₁+1)(2l₂+1)

*Mapping to paper notation*: This is the full bispectrum, not selective. For lmax=5, it computes ~150 output values. The *selective* version for SO(3) would pick a subset based on Algorithm 1's logic adapted to the SO(3) Kronecker rules.

### What's built well
- Clean PyTorch module, GPU-compatible
- Pre-computed CG matrices (avoids expensive runtime computation)
- Good test suite (rotation invariance verified numerically)
- Correct handling of real SH symmetry F_l^{-m} = (-1)^m conj(F_l^m)
- Rotation utility with proper Haar measure (QR method)
- Spherical grid + bilinear interpolation for spatial rotation

### What's missing

**1. Selective coefficient selection for SO(3)**

The current code computes ALL (l₁, l₂, l) combinations where l₁ ≤ l₂ ≤ lmax. For the selective version, you'd apply Algorithm 1: start with l₁=0, find which l values it generates via 0⊗l→l, then use the Kronecker rule for SO(3):

```
l₁ ⊗ l₂ → |l₁-l₂|, |l₁-l₂|+1, ..., l₁+l₂
```

The generator is l=1 (generates all others). The selective set would be:
- β_{0,0} (trivial pair)
- β_{0,1} (seeds l=1)
- β_{1,k} for k=1,...,lmax-1 (propagates chain)

→ Only O(lmax) pairs instead of O(lmax²). This is directly analogous to Algorithm 1.

**2. Finite group implementations**

No cyclic, dihedral, or octahedral group implementations. These are the paper's main contribution and have practical importance:
- C_n: discrete rotations (digital images)
- D_n: rotations + reflections (2D images with flip symmetry)
- Octahedral: 3D rotations of cube/molecule symmetry

**3. Functional CG coefficient computation**

`clebsch_gordan.py` raises `NotImplementedError`. The SO3onS2 class sidesteps this by loading from JSON. For general finite groups you need:
- Integration with `escnn` library (preferred), OR
- Analytical computation (doable for C_n, D_n)

**4. Inversion / reconstruction**

No inversion algorithms implemented. These are critical for:
- Verifying completeness (can you round-trip through bispectrum?)
- Adversarial testing
- Novel applications requiring signal recovery

**5. Benchmarking**

No code to reproduce the paper's experiments:
- Time comparison: selective vs full vs G-TC
- Accuracy: G-CNN with bispectrum pooling vs max pooling
- Robustness: adversarial attack experiment

---

## Synthesis: What Matters Most

### The gap that matters

The codebase has SO(3) working for spherical functions. The paper's contribution is about *finite* groups (C_n, D_n, O) and the *selective* strategy. These two things are the missing piece.

### The right order of attack

*Phase 1: Cyclic groups (C_n)* — Start here because:
- Formulas are explicit: β_{k₁,k₂} = F̂_{k₁}F̂_{k₂}F̂*_{k₁+k₂}
- No CG matrices needed (commutative → scalars)
- Inversion is clean: Algorithm 1 is just 10 lines of code
- Natural FFT available (torch.fft)
- Great for testing completeness numerically

*Phase 2: Verify selective SO(3)* — Apply the selection logic to the existing SO(3) implementation:
- Identify the selective (l₁, l₂, l) subset
- Show it's still complete (numerically: can you recover F from β_sel?)
- Benchmark: how much faster is it?

*Phase 3: Dihedral groups D_n* — The main new contribution:
- 2D irreps as 2×2 rotation matrices
- CG matrices needed (but can be computed analytically for D_n)
- Most important for 2D image applications
- The "valid U" issue needs a practical solution

*Phase 4: Inversion algorithms* — Implement Algorithms 1, 2, 3 explicitly:
- Critical for verifying completeness
- Enables novel applications
- Clean test: invert → compare to original signal

### Open technical questions

**Q1: Valid U for D_n inversion**
The paper says the correct U in F_{ρ₁} = VΛ^½V†U "can be found" but doesn't give an algorithm. In practice, for a neural network, you don't need to invert — you just need the bispectrum to be G-invariant and complete. But if you want the inversion algorithm, this needs to be resolved.

*My read*: For neural network use, skip inversion for now. The forward map (signal → bispectrum) is what matters. The completeness proof guarantees the representation is lossless.

**Q2: Steerable vs spatial computation**
The colleague's draft mentions computing bispectrum directly from steerable coefficients (Section 5.3). This bypasses the spatial domain entirely and could be significantly faster. This connection to the current escnn ecosystem should be explored.

**Q3: FFT on D_n**
The paper claims O(|G| log|G|) complexity with FFT. For D_n, the FFT isn't the standard DFT — you need a group FFT (Diaconis-Rockmore 1990). Is this available in PyTorch or a library? If not, we'd fall back to O(|G|²) DFT, which still beats the current O(|G|³) or O(|G|²) full bispectrum.

**Q4: CG matrices for finite groups**
For D_n, the CG matrices C_{ρ₁,ρ₂} can be computed analytically from the 2D irrep formulas (Eq. 2D_irreps_dn in paper). The escnn library should have these. Verify before implementing from scratch.

### My recommendation

*For the next work session*: Start with cyclic groups — implement a complete, tested `CyclicBispectrum` module with:
1. Forward pass: β_{k₁,k₂} = F̂_{k₁}F̂_{k₂}F̂*_{k₁+k₂}
2. Selective version: only Algorithm 1's n coefficients
3. Inversion: Algorithm 1 implemented
4. Tests: rotation invariance, reconstruction accuracy, speed benchmark

This is the clearest path to validating the paper's claims in code and building confidence before tackling the harder non-commutative case.

---

## Key formulas for quick reference

### Cyclic C_n
```
DFT:       f̂_k = Σ_{x=0}^{n-1} e^{-i2πkx/n} f(x)
Bispectrum: β_{k₁,k₂} = f̂_{k₁} · f̂_{k₂} · f̂*_{k₁+k₂}
Selective:  {β_{0,0}, β_{0,1}, β_{1,1}, β_{1,2}, ..., β_{1,n-2}}
Inversion:  F̂_{k+1} = (β_{1,k} / (f̂₁ · f̂_k))†
```

### General finite group G
```
FT:        F(Θ)_ρ = (1/|G|) Σ_{g∈G} Θ(g) ρ(g)†
Bispectrum: β(Θ)_{ρ₁,ρ₂} = [F_{ρ₁} ⊗ F_{ρ₂}] C_{ρ₁,ρ₂} [⊕_ρ F_ρ†] C†_{ρ₁,ρ₂}
Selective:  Use Algorithm 1/2/3 to select O(|G|) coefficients
```

### Dihedral D_n irreps
```
2D irreps: ρ_k(a^l x^m) = Rot(ω_l k) · Refl^m,   k=1,...,⌊(n-1)/2⌋
1D irreps: ρ₀ (trivial), ρ₀₁ (rotation sign), ρ₀₂, ρ₀₃ (n even only)
```

### SO(3) / Spherical Harmonics (current code)
```
FT:        F_l^m = ∫ f(θ,φ) Y_l^m*(θ,φ) dΩ
Bispectrum: β_{l₁,l₂}[l] = (F_{l₁} ⊗ F_{l₂}) @ C_{l₁,l₂} @ F̂_l†
Selective:  {β_{0,0}, β_{0,1}, β_{1,k} for k=1,...,lmax-1}
```
