# Current Implementation Analysis

**Repository**: https://github.com/geometric-intelligence/bispectrum
**Version**: 0.1.0 (Alpha)
**Python**: 3.12
**Key Dependencies**: torch>=2.4.0, torch-harmonics, numpy

## Overview

The current implementation focuses on **SO(3) rotations on S²** (spherical functions). This is a specific case - continuous rotation group acting on the 2-sphere.

**Status**: Working implementation for SO(3), but not yet covering the selective bispectrum for *finite* groups from the paper.

## Current Architecture

### Core Modules

**1. `so3.py` - SO3onS2 Class**
- Main `torch.nn.Module` for computing bispectra
- Computes β_{l1,l2}[l] for all (l1, l2) pairs where l1 ≤ l2 ≤ lmax
- Uses pre-computed Clebsch-Gordan matrices from JSON
- Formula: `beta_{l1,l2}[l] = (F_l1 ⊗ F_l2) @ C_{l1,l2} @ F_hat_l^†`

**Key implementation details**:
- Loads CG matrices from `data/cg_lmax5.json` (1.3MB file)
- Registers CG matrices as buffers for all (l1, l2) pairs
- Index map: maps flat output → (l1, l2, l) tuple
- Caches transformed tensor products to avoid recomputation
- Output size: number of valid (l1, l2, l) combinations

**2. `spherical.py` - Core Utilities**
- `get_full_sh_coefficients()`: Extends m ≥ 0 to full m ∈ [-l, l] using symmetry
  - Relation: F_l^{-m} = (-1)^m * conj(F_l^m)
- `compute_padding_indices()`: Computes zero-padding positions
- `pad_sh_coefficients()`: Creates F_hat_l with zeros before/after
- `bispectrum()`: Functional API for computing bispectrum

**3. `clebsch_gordan.py` - Placeholder**
- Currently raises `NotImplementedError`
- CG matrices actually loaded from JSON in SO3onS2

**4. `rotation.py` - Rotation Utilities**
- `random_rotation_matrix()`: Generate random SO(3) rotations
- `rotate_spherical_function()`: Apply rotation to spherical function

### Data Files

**`data/cg_lmax5.json`** (1.3MB)
- Pre-computed Clebsch-Gordan matrices for lmax=5
- Structure:
  ```json
  {
    "metadata": {"l1_max": 5, "l2_max": 5},
    "matrices": {
      "0_0": {"matrix": [...]},
      "0_1": {"matrix": [...]},
      ...
    }
  }
  ```
- Each matrix is (2l1+1)*(2l2+1) × (2l1+1)*(2l2+1)
- Stored as float64

## What's Missing for Selective G-Bispectrum

### 1. Finite Group Support

**Current**: Only SO(3) on sphere (continuous group)
**Needed**: Cyclic groups (C_n), Dihedral groups (D_n), Octahedral (O, FO)

**Gap**: The paper's Algorithm 1 is for finite groups with:
- Discrete group elements
- Irreducible representations (irreps)
- Kronecker table for tensor product decomposition
- Strategic selection of bispectral coefficients

### 2. Selective Coefficient Selection

**Current**: Computes ALL bispectral coefficients for all (l1, l2, l) combinations
**Needed**: Algorithm 1 from paper - select only O(|G|) coefficients

**The selective algorithm**:
1. Start with β_{ρ0,ρ0} (trivial irrep)
2. Find ρ̃1 such that ρ̃1 ⊗ ρ̃1 generates new irreps
3. Iteratively add pairs (ρ',ρ'') that generate remaining irreps
4. Stop when all irreps covered

### 3. General CG Coefficient Computation

**Current**: Pre-computed for SO(3) up to lmax=5, stored in JSON
**Needed**:
- Runtime computation for arbitrary finite groups
- Integration with `escnn` library for general groups
- CG matrices for cyclic, dihedral, octahedral groups

### 4. FFT for Finite Groups

**Current**: Uses torch-harmonics for spherical harmonics transform (continuous case)
**Needed**:
- Discrete Fourier Transform on finite groups
- Cooley-Tukey FFT extension for groups (exists for dihedral, etc.)
- Falls back to O(|G|²) DFT if FFT not available

### 5. Kronecker Table Management

**Current**: Implicit in SO(3) Clebsch-Gordan structure
**Needed**: Explicit Kronecker product tables for finite groups
- For each pair (ρ1, ρ2), which irreps appear in ρ1 ⊗ ρ2?
- Used by Algorithm 1 to determine coefficient selection

## Code Quality Observations

**Strengths**:
✓ Clean, well-documented code
✓ Comprehensive tests (rotation invariance, padding, symmetries)
✓ Type hints throughout
✓ Pre-commit hooks (ruff, mypy)
✓ Good separation of concerns

**Opportunities**:
- CG placeholder should be implemented or removed
- Could benefit from group-agnostic base class
- Performance profiling not yet done
- No benchmarking against paper's experiments

## Mapping to Paper

### What Exists:

**Paper Formula** (Theorem in Section 2):
```
β(Θ)_{ρ1,ρ2} = [F(Θ)_{ρ1} ⊗ F(Θ)_{ρ2}]C_{ρ1,ρ2}[⊕_{ρ∈ρ1⊗ρ2} F(Θ)_ρ†]C†_{ρ1,ρ2}
```

**Current Code** (`so3.py:144-160`):
```python
outer = torch.einsum('bi,bj->bij', f_l1, f_l2)  # Tensor product
tensor_product = outer.reshape(batch_size, -1)
transformed = tensor_product @ cg_matrix  # Apply C_{l1,l2}
result[:, out_idx] = torch.sum(transformed * torch.conj(f_hat_l), dim=-1)  # Inner product with F_l^†
```

**Match**: ✓ The math is correct for SO(3) case!

### What's Different:

**Paper**: Focuses on *finite* groups with selective coefficients
**Current**: Implements *continuous* SO(3) with full coefficients

**Paper**: O(|G|) space complexity
**Current**: O(lmax²) space complexity (all pairs l1 ≤ l2 ≤ lmax)

**Paper**: Uses Kronecker table to select coefficients
**Current**: Computes all possible (l1, l2, l) combinations

## Performance Characteristics

### Current Complexity (SO(3) Implementation)

**Space**:
- CG matrices: O(lmax⁴) stored (all pairs, each (2l+1)² × (2l+1)²)
- Output: O(lmax³) bispectral values
- For lmax=5: ~150 bispectrum values

**Time** (per forward pass):
- Tensor products: O(batch * lmax² * lmax²) = O(batch * lmax⁴)
- CG multiplication: O(batch * lmax² * lmax⁴) = O(batch * lmax⁶)
- Dominant: CG matrix multiplication

### Target Complexity (From Paper)

**Space**: O(|G|) bispectral coefficients
**Time**: O(|G| log|G|) with FFT, O(|G|²) with DFT

### Gap

For finite groups with |G| ~ lmax²:
- Current: O(lmax⁶) time
- Target: O(lmax² log(lmax)) time
- **Speedup potential**: ~lmax⁴ / log(lmax)

## Next Steps for Implementation

### Short Term (Selective SO(3))
1. Implement coefficient selection for SO(3) case
2. Profile current implementation
3. Add benchmarks matching paper's experiments

### Medium Term (Finite Groups)
1. Add cyclic group (C_n) implementation
   - Simple DFT: F_k = Σ e^(-i2πkn/N) f(n)
   - Bispectrum: β_{k1,k2} = f̂_{k1} f̂_{k2} f̂*_{k1+k2}
   - Use draft formulas from colleague's PDF
2. Add Clebsch-Gordan computation
   - Integrate with escnn for general groups
   - Or implement analytical formulas for specific groups
3. Implement Algorithm 1 from paper
   - Kronecker table input
   - Selective coefficient generation

### Long Term (Full Paper Implementation)
1. Dihedral groups (D_n)
2. Octahedral groups (O, FO)
3. FFT implementations
4. Full benchmark suite from paper
5. Inversion algorithms (signal reconstruction)

## Integration Points

**With escnn**:
- CG coefficient computation
- Irrep decomposition
- Group structure utilities

**With torch-harmonics**:
- Already used for SO(3) spherical harmonics
- Could extend pattern to other groups

**With colleague's draft**:
- Explicit formulas for cyclic groups (Section 4)
- Explicit formulas for finite groups (Section 5)
- Inversion algorithms

## Questions for Discussion

1. **Priority**: Should we optimize SO(3) first or add finite groups?
2. **CG source**: Compute at runtime (escnn) or pre-compute + store (current approach)?
3. **Groups**: Which finite groups are most important? (Cyclic, Dihedral, both?)
4. **Compatibility**: Keep SO(3) implementation or refactor to unified finite group approach?
5. **Testing**: What validation experiments should we run first?
